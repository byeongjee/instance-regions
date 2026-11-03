use std::{iter, mem};

use rustc_data_structures::fx::{FxHashMap, FxIndexMap};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_infer::infer::{NllRegionVariableOrigin, OpaqueTypeStorageEntries};
use rustc_middle::traits::ObligationCause;
use rustc_middle::ty::{
    self, DefiningScopeKind, DefinitionSiteHiddenType, FallibleTypeFolder, Flags, GenericArg,
    GenericArgsRef, OpaqueTypeKey, ProvisionalHiddenType, Region, RegionVid, Ty, TyCtxt,
    TypeFoldable, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitableExt,
    TypeVisitor, Unnormalized, fold_regions,
};
use rustc_trait_selection::opaque_types::opaque_type_has_defining_use_args;
use rustc_trait_selection::solve::NoSolution;

use super::constraints::Constraints;
use super::convert::Conversion;
use super::graph::{RegionDefinition, SccIndex};
use super::infer::Infer;
use super::relations::Relations;
use super::values::RegionValues;
use crate::Error;

pub(crate) type OpaqueUses<'tcx> = Vec<(OpaqueTypeKey<'tcx>, ProvisionalHiddenType<'tcx>)>;
pub(crate) type HiddenTypes<'tcx> = FxIndexMap<LocalDefId, DefinitionSiteHiddenType<'tcx>>;

// Where the hidden type of an opaque type a body uses comes from: the defining uses in
// the bodies of the root, or, for an instance of a generic root, the hidden type rustc
// recorded for the root, which is the answer for every instance.
#[derive(Clone, Copy)]
pub(crate) enum DefinitionSiteHiddenTypes<'a, 'tcx> {
    Inferred(&'a HiddenTypes<'tcx>),
    Recorded,
}

// The uses of opaque types the type check registered, with every region mapped to
// a region variable.
pub(crate) fn clone_and_resolve_opaque_types<'tcx>(
    infer: &Infer<'tcx>,
    relations: &Relations<'tcx>,
    constraints: &mut Constraints<'tcx>,
) -> (OpaqueTypeStorageEntries, OpaqueUses<'tcx>) {
    let opaque_types: Vec<(OpaqueTypeKey<'tcx>, ProvisionalHiddenType<'tcx>)> =
        infer.clone_opaque_types();
    let entries: OpaqueTypeStorageEntries = infer.inner.borrow_mut().opaque_types().num_entries();
    let opaque_types: OpaqueUses<'tcx> = opaque_types
        .into_iter()
        .map(|entry| {
            fold_regions(infer.tcx, infer.resolve_vars_if_possible(entry), |r, _| {
                let vid: RegionVid = if let ty::RePlaceholder(placeholder) = r.kind() {
                    constraints.placeholder_region(infer, placeholder).as_var()
                } else {
                    relations.universal.to_region_vid(r)
                };
                Region::new_var(infer.tcx, vid)
            })
        })
        .collect();
    (entries, opaque_types)
}

// The region values of a body while its opaque types are inferred: the constraints
// with placeholders lowered, not yet propagated.
struct RegionCtxt<'a, 'tcx> {
    infer: &'a Infer<'tcx>,
    relations: &'a Relations<'tcx>,
    definitions: &'a IndexVec<RegionVid, RegionDefinition<'tcx>>,
    values: RegionValues,
}

impl<'tcx> RegionCtxt<'_, 'tcx> {
    fn eval_equal(&self, r1_vid: RegionVid, r2_vid: RegionVid) -> bool {
        let r1: SccIndex = self.values.scc(r1_vid);
        let r2: SccIndex = self.values.scc(r2_vid);
        if r1 == r2 {
            return true;
        }
        let universal_outlives = |sub: SccIndex, sup: SccIndex| {
            self.values.universal_regions_outlived_by(sub).all(|r1| {
                self.values
                    .universal_regions_outlived_by(sup)
                    .any(|r2| self.relations.outlives(r2, r1))
            })
        };
        universal_outlives(r1, r2) && universal_outlives(r2, r1)
    }

    // A universal region equal to the region variable, chosen deterministically.
    fn nll_var_to_universal_region(&self, r: RegionVid) -> Option<Region<'tcx>> {
        let vid: RegionVid = self.values.representative(r).rvid();
        match self.definitions[vid].origin {
            NllRegionVariableOrigin::FreeRegion => self
                .relations
                .universal
                .universal_regions_iter()
                .filter(|&ur| !self.relations.universal.is_external_region(ur))
                .find(|&ur| self.relations.equal(vid, ur))
                .map(|ur| {
                    self.relations
                        .universal
                        .external_name(ur)
                        .expect("a universal region equal to a hidden type region has a name")
                }),
            NllRegionVariableOrigin::Placeholder(placeholder) => {
                Some(ty::Region::new_placeholder(self.infer.tcx, placeholder))
            }
            NllRegionVariableOrigin::Existential { .. } => None,
        }
    }
}

#[derive(Debug)]
struct DefiningUse<'tcx> {
    opaque_type_key: OpaqueTypeKey<'tcx>,
    arg_regions: Vec<RegionVid>,
    hidden_type: ProvisionalHiddenType<'tcx>,
}

// A use of an opaque type that rustc reports as an error; the hidden types of the
// body are then not applied, as in rustc.
#[derive(Debug)]
pub(crate) enum DeferredError {
    InvalidOpaqueTypeArgs,
    UnexpectedHiddenRegion,
    LifetimeMismatchOpaqueParam,
}

// A hidden type with a region equal to no arg region of the opaque type. In the new
// solver another body may define the opaque type fully, and rustc reports the error
// only when none does.
struct UnconstrainedHiddenType<'tcx> {
    def: DefId,
    opaque_type_key: OpaqueTypeKey<'tcx>,
}

// The hidden types inferred at the definition sites of the opaque types from the
// bodies of a root, with the uses that await a defining use in another body.
#[derive(Default)]
pub(crate) struct HiddenTypeInference<'tcx> {
    pub(crate) hidden_types: HiddenTypes<'tcx>,
    unconstrained: Vec<UnconstrainedHiddenType<'tcx>>,
}

impl HiddenTypeInference<'_> {
    // The bodies with an unconstrained hidden type of an opaque type no body defines,
    // as in rustc's `handle_unconstrained_hidden_type_errors`.
    pub(crate) fn unresolved_bodies(&mut self) -> Vec<DefId> {
        mem::take(&mut self.unconstrained)
            .into_iter()
            .filter(|hidden| !self.hidden_types.contains_key(&hidden.opaque_type_key.def_id))
            .map(|hidden| hidden.def)
            .collect()
    }
}

// Computes the hidden types of the opaque types at their definition sites from the
// defining uses in this body.
pub(crate) fn compute_definition_site_hidden_types<'tcx>(
    def: DefId,
    infer: &Infer<'tcx>,
    relations: &Relations<'tcx>,
    definitions: &IndexVec<RegionVid, RegionDefinition<'tcx>>,
    outlives: &[super::constraints::Outlives],
    inference: &mut HiddenTypeInference<'tcx>,
    opaque_types: &OpaqueUses<'tcx>,
) -> Result<Vec<DeferredError>, Error> {
    let mut errors: Vec<DeferredError> = Vec::new();
    let mut lowered: Vec<super::constraints::Outlives> = outlives.to_vec();
    super::placeholders::lower(&mut lowered, definitions, relations.universal.fr_static);
    let mut rcx = RegionCtxt {
        infer,
        relations,
        definitions,
        values: RegionValues::new(&lowered, definitions, &relations.universal),
    };
    let defining_uses: Vec<DefiningUse<'tcx>> =
        collect_defining_uses(&rcx, opaque_types, &mut errors)?;
    apply_member_constraints(&mut rcx, &defining_uses);
    compute_definition_site_hidden_types_from_defining_uses(
        def,
        &rcx,
        &mut inference.hidden_types,
        &mut inference.unconstrained,
        &defining_uses,
        &mut errors,
    )?;
    Ok(errors)
}

fn collect_defining_uses<'tcx>(
    rcx: &RegionCtxt<'_, 'tcx>,
    opaque_types: &OpaqueUses<'tcx>,
    errors: &mut Vec<DeferredError>,
) -> Result<Vec<DefiningUse<'tcx>>, Error> {
    let tcx: TyCtxt<'tcx> = rcx.infer.tcx;
    let mut defining_uses: Vec<DefiningUse<'tcx>> = vec![];
    for &(opaque_type_key, hidden_type) in opaque_types {
        let non_nll_opaque_type_key: OpaqueTypeKey<'tcx> = opaque_type_key
            .fold_captured_lifetime_args(tcx, |r| {
                rcx.nll_var_to_universal_region(r.as_var()).unwrap_or(r)
            });
        if let Err(err) = opaque_type_has_defining_use_args(
            &rcx.infer.infcx,
            non_nll_opaque_type_key,
            hidden_type.span,
            DefiningScopeKind::MirBorrowck,
        ) {
            if tcx.use_typing_mode_borrowck() {
                if let rustc_trait_selection::opaque_types::NonDefiningUseReason::Tainted(_) = err {
                    return Err(Error::new("a tainted use of an opaque type"));
                }
            } else {
                errors.push(DeferredError::InvalidOpaqueTypeArgs);
            }
            continue;
        }
        let arg_regions: Vec<RegionVid> = iter::once(rcx.relations.universal.fr_static)
            .chain(
                opaque_type_key
                    .iter_captured_args(tcx)
                    .filter_map(|(_, arg)| arg.as_region())
                    .map(Region::as_var),
            )
            .collect();
        defining_uses.push(DefiningUse {
            opaque_type_key: non_nll_opaque_type_key,
            arg_regions,
            hidden_type,
        });
    }
    Ok(defining_uses)
}

fn compute_definition_site_hidden_types_from_defining_uses<'tcx>(
    def: DefId,
    rcx: &RegionCtxt<'_, 'tcx>,
    hidden_types: &mut HiddenTypes<'tcx>,
    unconstrained: &mut Vec<UnconstrainedHiddenType<'tcx>>,
    defining_uses: &[DefiningUse<'tcx>],
    errors: &mut Vec<DeferredError>,
) -> Result<(), Error> {
    let tcx: TyCtxt<'tcx> = rcx.infer.tcx;
    let mut decls_modulo_regions: FxIndexMap<OpaqueTypeKey<'tcx>, OpaqueTypeKey<'tcx>> =
        FxIndexMap::default();
    for &DefiningUse { opaque_type_key, ref arg_regions, hidden_type } in defining_uses {
        let hidden_type: ProvisionalHiddenType<'tcx> = match hidden_type
            .try_fold_with(&mut ToArgRegionsFolder::new(rcx, arg_regions))
        {
            Ok(hidden_type) => hidden_type,
            Err(_) if tcx.use_typing_mode_borrowck() => {
                unconstrained.push(UnconstrainedHiddenType { def, opaque_type_key });
                continue;
            }
            Err(_) => {
                return Err(Error::new("an opaque type has a hidden region that is not universal"));
            }
        };
        let Ok(()) = opaque_type_has_defining_use_args(
            &rcx.infer.infcx,
            opaque_type_key,
            hidden_type.span,
            DefiningScopeKind::MirBorrowck,
        ) else {
            return Err(Error::new("a defining use of an opaque type has invalid args"));
        };
        let hidden_type: DefinitionSiteHiddenType<'tcx> = hidden_type
            .remap_generic_params_to_declaration_params(
                opaque_type_key,
                tcx,
                DefiningScopeKind::MirBorrowck,
            );
        if hidden_type.ty.skip_binder().error_reported().is_err() {
            return Err(Error::new("the hidden type of an opaque type has an error"));
        }
        if !tcx.use_typing_mode_borrowck()
            && let &ty::Alias(ty::AliasTy { kind: ty::Opaque { def_id }, args, .. }) =
                hidden_type.ty.skip_binder().kind()
            && def_id == opaque_type_key.def_id.to_def_id()
            && args == opaque_type_key.args
        {
            continue;
        }
        if let Some(prev_decl_key) = decls_modulo_regions
            .insert(tcx.erase_and_anonymize_regions(opaque_type_key), opaque_type_key)
            && iter::zip(
                prev_decl_key.iter_captured_args(tcx).map(|(_, arg)| arg),
                opaque_type_key.iter_captured_args(tcx).map(|(_, arg)| arg),
            )
            .any(|(arg1, arg2)| arg1 != arg2)
        {
            errors.push(DeferredError::LifetimeMismatchOpaqueParam);
        }
        match hidden_types.get_mut(&opaque_type_key.def_id) {
            Some(prev) => {
                if prev.ty != hidden_type.ty {
                    return Err(Error::new("an opaque type has two different hidden types"));
                }
                prev.span = prev.span.substitute_dummy(hidden_type.span);
            }
            None => {
                hidden_types.insert(opaque_type_key.def_id, hidden_type);
            }
        }
    }
    Ok(())
}

// Equates every region of a hidden type with the arg region it is equal to.
struct ToArgRegionsFolder<'a, 'tcx> {
    rcx: &'a RegionCtxt<'a, 'tcx>,
    erase_unknown_regions: bool,
    arg_regions: &'a [RegionVid],
}

impl<'a, 'tcx> ToArgRegionsFolder<'a, 'tcx> {
    fn new(rcx: &'a RegionCtxt<'a, 'tcx>, arg_regions: &'a [RegionVid]) -> Self {
        ToArgRegionsFolder { rcx, erase_unknown_regions: false, arg_regions }
    }

    fn fold_non_member_arg(&mut self, arg: GenericArg<'tcx>) -> GenericArg<'tcx> {
        let prev: bool = self.erase_unknown_regions;
        self.erase_unknown_regions = true;
        let res: GenericArg<'tcx> = arg.try_fold_with(self).expect("unknown regions are erased");
        self.erase_unknown_regions = prev;
        res
    }

    fn fold_closure_args(
        &mut self,
        def_id: DefId,
        args: GenericArgsRef<'tcx>,
    ) -> Result<GenericArgsRef<'tcx>, RegionVid> {
        let generics: &'tcx ty::Generics = self.cx().generics_of(def_id);
        self.cx().mk_args_from_iter(args.iter().enumerate().map(|(index, arg)| {
            if index < generics.parent_count {
                Ok(self.fold_non_member_arg(arg))
            } else {
                arg.try_fold_with(self)
            }
        }))
    }
}

impl<'tcx> FallibleTypeFolder<TyCtxt<'tcx>> for ToArgRegionsFolder<'_, 'tcx> {
    type Error = RegionVid;

    fn cx(&self) -> TyCtxt<'tcx> {
        self.rcx.infer.tcx
    }

    fn try_fold_region(&mut self, r: Region<'tcx>) -> Result<Region<'tcx>, RegionVid> {
        if let ty::ReBound(_, _) = r.kind() {
            Ok(r)
        } else {
            let r: RegionVid = r.as_var();
            if let Some(arg_region) = self
                .arg_regions
                .iter()
                .copied()
                .find(|&arg_vid| self.rcx.eval_equal(r, arg_vid))
                .and_then(|r| self.rcx.nll_var_to_universal_region(r))
            {
                Ok(arg_region)
            } else if self.erase_unknown_regions {
                Ok(self.cx().lifetimes.re_erased)
            } else {
                Err(r)
            }
        }
    }

    fn try_fold_ty(&mut self, ty: Ty<'tcx>) -> Result<Ty<'tcx>, RegionVid> {
        if !ty.flags().intersects(ty::TypeFlags::HAS_FREE_REGIONS) {
            return Ok(ty);
        }
        let tcx: TyCtxt<'tcx> = self.cx();
        Ok(match *ty.kind() {
            ty::Closure(def_id, args) => {
                Ty::new_closure(tcx, def_id, self.fold_closure_args(def_id, args)?)
            }
            ty::CoroutineClosure(def_id, args) => {
                Ty::new_coroutine_closure(tcx, def_id, self.fold_closure_args(def_id, args)?)
            }
            ty::Coroutine(def_id, args) => {
                Ty::new_coroutine(tcx, def_id, self.fold_closure_args(def_id, args)?)
            }
            ty::Alias(ty::AliasTy { kind, args, .. })
                if let Some(variances) = tcx.opt_alias_variances(kind) =>
            {
                let args: GenericArgsRef<'tcx> =
                    tcx.mk_args_from_iter(iter::zip(variances, args.iter()).map(|(&v, s)| {
                        if v == ty::Bivariant {
                            Ok(self.fold_non_member_arg(s))
                        } else {
                            s.try_fold_with(self)
                        }
                    }))?;
                ty::AliasTy::new_from_args(tcx, kind, args).to_ty(tcx)
            }
            _ => ty.try_super_fold_with(self)?,
        })
    }
}

// Grows every member region of a hidden type to the smallest arg region it can equal.
fn apply_member_constraints<'tcx>(
    rcx: &mut RegionCtxt<'_, 'tcx>,
    defining_uses: &[DefiningUse<'tcx>],
) {
    let mut member_constraints: FxHashMap<SccIndex, Vec<&DefiningUse<'tcx>>> = FxHashMap::default();
    for defining_use in defining_uses {
        let mut visitor = CollectMemberConstraintsVisitor {
            rcx,
            defining_use,
            member_constraints: &mut member_constraints,
        };
        defining_use.hidden_type.ty.visit_with(&mut visitor);
    }
    for scc_a in rcx.values.sccs.sccs.all_sccs() {
        let successors: Vec<SccIndex> = rcx.values.sccs.sccs.successors(scc_a).to_vec();
        for scc_b in successors {
            rcx.values.add_region(scc_a, scc_b);
        }
        for defining_use in member_constraints.get(&scc_a).into_iter().flatten() {
            apply_member_constraint(rcx, scc_a, &defining_use.arg_regions);
        }
    }
}

fn apply_member_constraint(
    rcx: &mut RegionCtxt<'_, '_>,
    member: SccIndex,
    arg_regions: &[RegionVid],
) {
    if !rcx.values.max_placeholder_universe_reached(member).is_root() {
        return;
    }
    let mut choice_regions: Vec<RegionVid> = arg_regions
        .iter()
        .copied()
        .map(|r| rcx.values.representative(r).rvid())
        .filter(|&choice_region| {
            rcx.values
                .universal_regions_outlived_by(member)
                .all(|lower_bound| rcx.relations.outlives(choice_region, lower_bound))
        })
        .collect();
    let upper_bounds: Vec<RegionVid> = rcx.values.upper_bounds(member).collect();
    for ub in upper_bounds {
        choice_regions.retain(|&choice_region| rcx.relations.outlives(ub, choice_region));
    }
    let totally_ordered_subset = choice_regions.iter().copied().filter(|&r1| {
        choice_regions
            .iter()
            .all(|&r2| rcx.relations.outlives(r1, r2) || rcx.relations.outlives(r2, r1))
    });
    let Some(min_choice) = totally_ordered_subset.reduce(|r1, r2| {
        let r1_outlives_r2: bool = rcx.relations.outlives(r1, r2);
        let r2_outlives_r1: bool = rcx.relations.outlives(r2, r1);
        match (r1_outlives_r2, r2_outlives_r1) {
            (true, true) => r1.min(r2),
            (true, false) => r2,
            (false, true) => r1,
            (false, false) => unreachable!("incomparable regions in total order"),
        }
    }) else {
        return;
    };
    let min_choice_scc: SccIndex = rcx.values.scc(min_choice);
    rcx.values.add_region(member, min_choice_scc);
}

struct CollectMemberConstraintsVisitor<'a, 'b, 'tcx> {
    rcx: &'a RegionCtxt<'a, 'tcx>,
    defining_use: &'b DefiningUse<'tcx>,
    member_constraints: &'a mut FxHashMap<SccIndex, Vec<&'b DefiningUse<'tcx>>>,
}

impl<'tcx> CollectMemberConstraintsVisitor<'_, '_, 'tcx> {
    fn visit_closure_args(&mut self, def_id: DefId, args: GenericArgsRef<'tcx>) {
        let generics: &'tcx ty::Generics = self.rcx.infer.tcx.generics_of(def_id);
        for arg in args.iter().skip(generics.parent_count) {
            arg.visit_with(self);
        }
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for CollectMemberConstraintsVisitor<'_, '_, 'tcx> {
    fn visit_region(&mut self, r: Region<'tcx>) {
        match r.kind() {
            ty::ReBound(..) => {}
            ty::ReVar(vid) => {
                let scc: SccIndex = self.rcx.values.scc(vid);
                self.member_constraints.entry(scc).or_default().push(self.defining_use);
            }
            _ => unreachable!(),
        }
    }

    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        if !ty.flags().intersects(ty::TypeFlags::HAS_FREE_REGIONS) {
            return;
        }
        match *ty.kind() {
            ty::Closure(def_id, args)
            | ty::CoroutineClosure(def_id, args)
            | ty::Coroutine(def_id, args) => {
                self.visit_closure_args(def_id, args);
            }
            ty::Alias(ty::AliasTy { kind, args, .. })
                if let Some(variances) = self.rcx.infer.tcx.opt_alias_variances(kind) =>
            {
                for (&v, arg) in iter::zip(variances, args.iter()) {
                    if v != ty::Bivariant {
                        arg.visit_with(self);
                    }
                }
            }
            _ => ty.super_visit_with(self),
        }
    }
}

// Equates the hidden type of every use of an opaque type in this body with the
// hidden type at its definition site.
pub(crate) fn apply_definition_site_hidden_types<'tcx>(
    infer: &Infer<'tcx>,
    relations: &Relations<'tcx>,
    constraints: &mut Constraints<'tcx>,
    hidden_types: DefinitionSiteHiddenTypes<'_, 'tcx>,
    opaque_types: &OpaqueUses<'tcx>,
) -> Result<(), Error> {
    let tcx: TyCtxt<'tcx> = infer.tcx;
    for &(key, hidden_type) in opaque_types {
        let expected_ty: Ty<'tcx> = match hidden_types {
            DefinitionSiteHiddenTypes::Recorded => {
                tcx.type_of(key.def_id).instantiate(tcx, key.args).skip_norm_wip()
            }
            DefinitionSiteHiddenTypes::Inferred(hidden_types) => {
                let Some(expected) = hidden_types.get(&key.def_id) else {
                    if !tcx.use_typing_mode_borrowck() {
                        if let &ty::Alias(ty::AliasTy { kind: ty::Opaque { def_id }, args, .. }) =
                            hidden_type.ty.kind()
                            && def_id == key.def_id.to_def_id()
                            && args == key.args
                        {
                            continue;
                        }
                        return Err(Error::new("non-defining use in defining scope"));
                    }
                    return Err(Error::new("a use of an opaque type with no defining use"));
                };
                expected.ty.instantiate(tcx, key.args).skip_norm_wip()
            }
        };
        let expected_ty: Ty<'tcx> = fold_regions(tcx, expected_ty, |re, _| match re.kind() {
            ty::ReErased => {
                infer.next_nll_region_var(NllRegionVariableOrigin::Existential { name: None })
            }
            _ => re,
        });
        let param_env: ty::ParamEnv<'tcx> = infer.param_env;
        let cause: ObligationCause<'tcx> = infer.cause(hidden_type.span);
        let Ok(((), scraped)) = infer.scrape(
            || "equating opaque types".to_owned(),
            |ocx| {
                let actual_ty: Ty<'tcx> =
                    ocx.normalize(&cause, param_env, Unnormalized::new_wip(hidden_type.ty));
                let expected_ty: Ty<'tcx> =
                    ocx.normalize(&cause, param_env, Unnormalized::new_wip(expected_ty));
                ocx.eq(&cause, param_env, actual_ty, expected_ty).map_err(|_| NoSolution)
            },
        ) else {
            return Err(Error::new("the hidden type of an opaque type does not equal its use"));
        };
        if let Some(scraped) = scraped {
            Conversion::new(
                infer,
                &relations.universal,
                &relations.region_bound_pairs,
                &relations.known_type_outlives,
                hidden_type.span,
                constraints,
            )
            .convert_all(scraped);
        }
    }
    Ok(())
}

// Applying hidden types must not register new uses of opaque types. The storage of
// the inference context is emptied afterwards, as it must be before it is dropped.
pub(crate) fn finish_opaque_types(
    infer: &Infer<'_>,
    entries: OpaqueTypeStorageEntries,
) -> Result<(), Error> {
    let added: usize =
        infer.inner.borrow_mut().opaque_types().opaque_types_added_since(entries).count();
    let _ = infer.take_opaque_types();
    if added > 0 {
        return Err(Error::new("an opaque type is defined cyclically"));
    }
    Ok(())
}
