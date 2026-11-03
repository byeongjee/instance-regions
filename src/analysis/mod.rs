mod closures;
mod constraints;
mod convert;
mod graph;
mod infer;
mod liveness;
mod opaque;
mod placeholders;
mod relations;
mod renumber;
mod typeck;
mod universal;
mod values;

use std::mem;

use preborrowck_mir::{RecordedMir, TypeckData, typing_env};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_infer::infer::OpaqueTypeStorageEntries;
use rustc_middle::mir::{Body, Promoted};
use rustc_middle::ty::{GenericArgsRef, TyCtxt, TypingEnv};
use rustc_span::DUMMY_SP;

use self::closures::{ClosureRequirements, RegionErrors};
use self::constraints::{Constraints, Outlives};
use self::convert::Conversion;
use self::graph::RegionDefinition;
use self::infer::Infer;
use self::opaque::{DeferredError, DefinitionSiteHiddenTypes, HiddenTypeInference, OpaqueUses};
use self::relations::Relations;
use self::universal::Universal;
use crate::Error;
use crate::facts::InstanceFacts;
use crate::instantiate::instantiate;

// A body whose constraints are collected but not yet final.
struct BodyState<'tcx> {
    def: DefId,
    infer: Infer<'tcx>,
    body: Body<'tcx>,
    promoted: IndexVec<Promoted, Body<'tcx>>,
    relations: Relations<'tcx>,
    constraints: Constraints<'tcx>,
    deferred: Vec<(DefId, GenericArgsRef<'tcx>)>,
}

type Finished<'tcx> = (InstanceFacts<'tcx>, Option<ClosureRequirements<'tcx>>);

// Analyzes every body of a typeck root instantiated with the args of an instance of
// the root, in the order of rustc: the constraints of every body are collected, the
// requirements of nested bodies reach their parents, the opaque types defined by the
// bodies are inferred, and then the constraints of each body are final.
pub(crate) fn analyze<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: DefId,
    instance_args: GenericArgsRef<'tcx>,
    set: &RecordedMir<'tcx>,
) -> Result<FxHashMap<DefId, InstanceFacts<'tcx>>, Error> {
    let mut states: Vec<BodyState<'tcx>> = Vec::with_capacity(set.order.len());
    for &def in &set.order {
        states.push(collect(tcx, root, def, instance_args, set)?);
    }
    let mut finished: FxHashMap<DefId, Finished<'tcx>> = FxHashMap::default();
    let mut modulo_opaques: FxHashMap<DefId, Option<ClosureRequirements<'tcx>>> =
        FxHashMap::default();
    let mut remaining: Vec<BodyState<'tcx>> = Vec::new();
    for mut state in states {
        let mut depends_on_opaques: bool = state.infer.has_opaque_types_in_storage();
        for (nested, args) in mem::take(&mut state.deferred) {
            let requirements: Option<&ClosureRequirements<'tcx>> =
                if let Some((_, requirements)) = finished.get(&nested) {
                    requirements.as_ref()
                } else {
                    depends_on_opaques = true;
                    state.deferred.push((nested, args));
                    modulo_opaques
                        .get(&nested)
                        .ok_or_else(|| Error::new("nested closure facts are unavailable"))?
                        .as_ref()
                };
            apply_closure_requirements(
                &state.infer,
                &state.relations,
                &mut state.constraints,
                requirements,
                nested,
                args,
                set,
            );
        }
        state.infer.check()?;
        if depends_on_opaques {
            if state.def != root {
                modulo_opaques.insert(state.def, requirements_modulo_opaques(&state)?);
            }
            remaining.push(state);
        } else {
            assert!(state.deferred.is_empty());
            let def: DefId = state.def;
            finished.insert(def, finish(state)?);
        }
    }
    resolve_opaque_types(&mut remaining, tcx.generics_of(root).requires_monomorphization(tcx))?;
    for mut state in remaining {
        for (nested, args) in mem::take(&mut state.deferred) {
            let (_, requirements) = finished
                .get(&nested)
                .ok_or_else(|| Error::new("nested closure facts are unavailable"))?;
            apply_closure_requirements(
                &state.infer,
                &state.relations,
                &mut state.constraints,
                requirements.as_ref(),
                nested,
                args,
                set,
            );
        }
        state.infer.check()?;
        let def: DefId = state.def;
        finished.insert(def, finish(state)?);
    }
    Ok(finished.into_iter().map(|(def, (facts, _))| (def, facts)).collect())
}

// Infers the hidden types of the opaque types from the bodies that depend on them, and
// equates every use of an opaque type with the hidden type. For an instance of a generic
// root, the hidden types rustc recorded for the root are the answer, so none is inferred.
fn resolve_opaque_types<'tcx>(
    remaining: &mut [BodyState<'tcx>],
    monomorphized: bool,
) -> Result<(), Error> {
    let mut inference: HiddenTypeInference<'tcx> = HiddenTypeInference::default();
    let mut uses: Vec<(OpaqueTypeStorageEntries, OpaqueUses<'tcx>, Vec<DeferredError>)> =
        Vec::new();
    for state in &mut *remaining {
        let (entries, opaque_types) = opaque::clone_and_resolve_opaque_types(
            &state.infer,
            &state.relations,
            &mut state.constraints,
        );
        let errors: Vec<DeferredError> = if monomorphized {
            Vec::new()
        } else {
            let definitions: IndexVec<_, RegionDefinition<'tcx>> =
                graph::region_definitions(&state.infer);
            opaque::compute_definition_site_hidden_types(
                state.def,
                &state.infer,
                &state.relations,
                &definitions,
                &state.constraints.outlives,
                &mut inference,
                &opaque_types,
            )?
        };
        uses.push((entries, opaque_types, errors));
    }
    for def in inference.unresolved_bodies() {
        let index: usize = remaining
            .iter()
            .position(|state| state.def == def)
            .expect("an unconstrained hidden type comes from a body that depends on opaque types");
        uses[index].2.push(DeferredError::UnexpectedHiddenRegion);
    }
    let hidden_types: DefinitionSiteHiddenTypes<'_, 'tcx> = if monomorphized {
        DefinitionSiteHiddenTypes::Recorded
    } else {
        DefinitionSiteHiddenTypes::Inferred(&inference.hidden_types)
    };
    for (state, (entries, opaque_types, errors)) in std::iter::zip(&mut *remaining, uses) {
        if errors.is_empty() {
            opaque::apply_definition_site_hidden_types(
                &state.infer,
                &state.relations,
                &mut state.constraints,
                hidden_types,
                &opaque_types,
            )?;
        }
        opaque::finish_opaque_types(&state.infer, entries)?;
    }
    Ok(())
}

fn collect<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: DefId,
    def: DefId,
    instance_args: GenericArgsRef<'tcx>,
    set: &RecordedMir<'tcx>,
) -> Result<BodyState<'tcx>, Error> {
    let (body, promoted) = set.bodies.get(&def).ok_or_else(|| {
        Error::new(format!("captured MIR body is missing for `{}`", tcx.def_path_str(def)))
    })?;
    let typeck: &TypeckData<'tcx> = set.typeck.get(&def).ok_or_else(|| {
        Error::new(format!("the typeck data of `{}` is not recorded", tcx.def_path_str(def)))
    })?;
    if body.tainted_by_errors.is_some() || promoted.iter().any(|b| b.tainted_by_errors.is_some()) {
        return Err(Error::new("captured MIR is tainted by compiler errors"));
    }
    if body.should_skip() {
        return Err(Error::unavailable("rustc skips the borrow check of injected MIR"));
    }
    if body.coroutine.is_some() && !def.is_local() {
        return Err(Error::unavailable(
            "no oracle validates the analysis of an external coroutine",
        ));
    }
    if tcx.def_kind(def) == DefKind::Closure && typeck.closure_sig.is_none() {
        return Err(Error::new("captured closure signature is unavailable"));
    }
    if tcx.def_kind(def) == DefKind::InlineConst && typeck.inline_const_ty.is_none() {
        return Err(Error::new("captured inline-const defining type is unavailable"));
    }
    let args: GenericArgsRef<'tcx> = set.args_of_body(tcx, def, instance_args)?;
    let typing_env: TypingEnv<'tcx> = typing_env(def);
    let mut body: Body<'tcx> = instantiate(tcx, body, args, typing_env)?;
    let mut promoted: IndexVec<Promoted, Body<'tcx>> = promoted
        .iter()
        .map(|body| instantiate(tcx, body, args, typing_env))
        .collect::<Result<_, _>>()?;
    let infer: Infer<'tcx> = Infer::new(tcx, def, root);
    let universal: Universal<'tcx> = Universal::new(&infer, def, args, set)?;
    renumber::renumber_mir(&infer, &mut body, &mut promoted);
    let mut constraints: Constraints<'tcx> = Constraints::default();
    let relations: Relations<'tcx> = relations::create(&infer, universal, &mut constraints, set);
    infer.check()?;
    let deferred: Vec<(DefId, GenericArgsRef<'tcx>)> =
        typeck::type_check(&infer, &body, &promoted, &relations, &mut constraints, set);
    infer.check()?;
    Ok(BodyState { def, infer, body, promoted, relations, constraints, deferred })
}

fn apply_closure_requirements<'tcx>(
    infer: &Infer<'tcx>,
    relations: &Relations<'tcx>,
    constraints: &mut Constraints<'tcx>,
    requirements: Option<&ClosureRequirements<'tcx>>,
    nested: DefId,
    args: GenericArgsRef<'tcx>,
    set: &RecordedMir<'tcx>,
) {
    let Some(requirements) = requirements else {
        return;
    };
    Conversion::new(
        infer,
        &relations.universal,
        &relations.region_bound_pairs,
        &relations.known_type_outlives,
        DUMMY_SP,
        constraints,
    )
    .apply_closure_requirements(requirements, nested, args, set);
}

// The requirements of a nested body before its opaque types are handled.
fn requirements_modulo_opaques<'tcx>(
    state: &BodyState<'tcx>,
) -> Result<Option<ClosureRequirements<'tcx>>, Error> {
    let definitions: IndexVec<_, RegionDefinition<'tcx>> = graph::region_definitions(&state.infer);
    let mut outlives: Vec<Outlives> = state.constraints.outlives.clone();
    placeholders::lower(&mut outlives, &definitions, state.relations.universal.fr_static);
    closures::closure_requirements(
        state.infer.tcx,
        &state.relations,
        &definitions,
        &outlives,
        &state.constraints.type_tests,
        RegionErrors::Discard,
    )
}

fn finish<'tcx>(state: BodyState<'tcx>) -> Result<Finished<'tcx>, Error> {
    let BodyState { def, infer, body, promoted, relations, constraints, deferred } = state;
    assert!(deferred.is_empty());
    let definitions: IndexVec<_, RegionDefinition<'tcx>> = graph::region_definitions(&infer);
    let Constraints { mut outlives, type_tests, .. } = constraints;
    placeholders::lower(&mut outlives, &definitions, relations.universal.fr_static);
    let requirements: Option<ClosureRequirements<'tcx>> = if infer.tcx.is_typeck_child(def) {
        closures::closure_requirements(
            infer.tcx,
            &relations,
            &definitions,
            &outlives,
            &type_tests,
            RegionErrors::Reject,
        )?
    } else {
        None
    };
    let facts: InstanceFacts<'tcx> = InstanceFacts {
        body,
        promoted,
        outlives: outlives.iter().map(|constraint| (constraint.sup, constraint.sub)).collect(),
    };
    Ok((facts, requirements))
}
