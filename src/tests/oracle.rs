// The oracle of the facts: the borrow checker of rustc, for the bodies of the typeck
// roots that are not generic and for the twins of generic functions.
use std::fmt::Write;

use preborrowck_mir::{RecordedMir, borrowck_facts, instances_within, recorded_mir};
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_index::IndexSlice;
use rustc_middle::mir::visit::{TyContext, Visitor};
use rustc_middle::mir::{
    Body, Const, ConstOperand, Location, Promoted, RETURN_PLACE, VarDebugInfoContents,
};
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::{
    self, GenericArgs, GenericArgsRef, GenericParamDefKind, Instance, InstanceKind, RegionVid, Ty,
    TyCtxt, TypeSuperVisitable, TypeVisitable,
};

use crate::facts::{InstanceFacts, instance_facts};

// The number of bodies compared and the differences found.
pub(super) struct Comparison {
    pub(super) checked: usize,
    pub(super) report: String,
}

// The regions of a body in the order a visitor meets them. Two renumberings of one
// body give sequences that correspond element by element.
struct RegionSequence<'tcx> {
    tcx: TyCtxt<'tcx>,
    regions: Vec<RegionVid>,
}

impl<'tcx> RegionSequence<'tcx> {
    fn of(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        promoted: &IndexSlice<Promoted, Body<'tcx>>,
    ) -> Vec<RegionVid> {
        let mut sequence = RegionSequence { tcx, regions: Vec::new() };
        for body in promoted {
            sequence.visit_body(body);
        }
        sequence.visit_body(body);
        sequence.regions
    }

    fn collect<T: ty::TypeVisitable<TyCtxt<'tcx>>>(&mut self, value: &T) {
        self.tcx.for_each_free_region(value, |region| self.regions.push(region.as_var()));
    }
}

impl<'tcx> Visitor<'tcx> for RegionSequence<'tcx> {
    fn visit_ty(&mut self, ty: Ty<'tcx>, ty_context: TyContext) {
        if matches!(ty_context, TyContext::ReturnTy(_)) {
            return;
        }
        self.collect(&ty);
    }

    fn visit_args(&mut self, args: &GenericArgsRef<'tcx>, _: Location) {
        self.collect(args);
    }

    fn visit_region(&mut self, region: ty::Region<'tcx>, _: Location) {
        self.regions.push(region.as_var());
    }

    fn visit_ty_const(&mut self, ct: ty::Const<'tcx>, _: Location) {
        self.collect(&ct);
    }

    // The args of an unevaluated constant of a closure body name the closure's own
    // generic parameters, which an instance substitutes with types that may have
    // regions. Those regions appear in no constraint.
    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, _: Location) {
        match constant.const_ {
            Const::Unevaluated(_, ty) => self.collect(&ty),
            const_ => self.collect(&const_),
        }
    }
}

fn reachable(outlives: &[(RegionVid, RegionVid)], from: RegionVid) -> FxHashSet<RegionVid> {
    let mut successors: FxHashMap<RegionVid, Vec<RegionVid>> = FxHashMap::default();
    for &(sup, sub) in outlives {
        successors.entry(sup).or_default().push(sub);
    }
    let mut seen: FxHashSet<RegionVid> = FxHashSet::default();
    let mut stack: Vec<RegionVid> = vec![from];
    while let Some(region) = stack.pop() {
        if !seen.insert(region) {
            continue;
        }
        if let Some(next) = successors.get(&region) {
            stack.extend(next.iter().copied());
        }
    }
    seen
}

// The facts another borrow checker computed for a body.
struct Expected<'a, 'tcx> {
    body: &'a Body<'tcx>,
    promoted: &'a IndexSlice<Promoted, Body<'tcx>>,
    outlives: Vec<(RegionVid, RegionVid)>,
}

// The regions in the types of the return place and the user variables of a body, in the
// order of its debug info. A twin has the user variables of the instance, while its
// temporaries differ: rustc copies and reborrows a reference where it moves a type
// param, and drops a type param where a reference needs no drop. The parent args of a
// nested body are left out: the instance names its type args there, where the twin
// names the late-bound lifetimes of its signature nowhere.
fn user_regions<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<RegionVid> {
    let mut sequence = UserRegionSequence { tcx, regions: Vec::new() };
    body.local_decls[RETURN_PLACE].ty.visit_with(&mut sequence);
    for info in &body.var_debug_info {
        if let VarDebugInfoContents::Place(place) = info.value {
            place.ty(body, tcx).ty.visit_with(&mut sequence);
        }
    }
    sequence.regions
}

struct UserRegionSequence<'tcx> {
    tcx: TyCtxt<'tcx>,
    regions: Vec<RegionVid>,
}

impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for UserRegionSequence<'tcx> {
    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        let (ty::Closure(def, args) | ty::CoroutineClosure(def, args) | ty::Coroutine(def, args)) =
            *ty.kind()
        else {
            return ty.super_visit_with(self);
        };
        let parent_count: usize = self.tcx.generics_of(def).parent_count;
        for arg in args.iter().skip(parent_count) {
            arg.visit_with(self);
        }
    }

    fn visit_region(&mut self, region: ty::Region<'tcx>) {
        if !region.is_bound() {
            self.regions.push(region.as_var());
        }
    }
}

// The differences between the outlives relation of the expected facts and ours on the
// regions of the body, closed transitively.
fn differences<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
    expected: &Expected<'_, 'tcx>,
    actual: &InstanceFacts<'tcx>,
) -> String {
    let expected_regions: Vec<RegionVid> =
        RegionSequence::of(tcx, expected.body, expected.promoted);
    let actual_regions: Vec<RegionVid> = RegionSequence::of(tcx, &actual.body, &actual.promoted);
    differences_between(name, &expected_regions, &expected.outlives, &actual_regions, actual)
}

// The differences on the regions of the user variables only.
fn user_differences<'tcx>(
    tcx: TyCtxt<'tcx>,
    name: &str,
    expected: &Expected<'_, 'tcx>,
    actual: &InstanceFacts<'tcx>,
) -> String {
    let expected_regions: Vec<RegionVid> = user_regions(tcx, expected.body);
    let actual_regions: Vec<RegionVid> = user_regions(tcx, &actual.body);
    differences_between(name, &expected_regions, &expected.outlives, &actual_regions, actual)
}

fn differences_between(
    name: &str,
    expected_regions: &[RegionVid],
    expected_outlives: &[(RegionVid, RegionVid)],
    actual_regions: &[RegionVid],
    actual: &InstanceFacts<'_>,
) -> String {
    assert_eq!(
        expected_regions.len(),
        actual_regions.len(),
        "{name}: the bodies have the same regions"
    );
    let r#static: RegionVid = RegionVid::from_u32(0);
    let mut mapping: FxHashMap<RegionVid, RegionVid> = FxHashMap::default();
    mapping.insert(r#static, r#static);
    for (&from, &to) in std::iter::zip(expected_regions, actual_regions) {
        assert_eq!(
            *mapping.entry(from).or_insert(to),
            to,
            "{name}: the regions correspond one to one"
        );
    }
    // `'static` outlives every region implicitly: the inference context drops
    // `'static: r` constraints, and the region graph of rustc adds them back.
    let mut expected_outlives: Vec<(RegionVid, RegionVid)> = expected_outlives.to_vec();
    let mut actual_outlives: Vec<(RegionVid, RegionVid)> = actual.outlives.clone();
    for (&from, &to) in &mapping {
        expected_outlives.push((r#static, from));
        actual_outlives.push((r#static, to));
    }
    let expected_outlives: &[(RegionVid, RegionVid)] = &expected_outlives;
    let actual_outlives: &[(RegionVid, RegionVid)] = &actual_outlives;
    let mut report: String = String::new();
    let mut sources: Vec<RegionVid> = mapping.keys().copied().collect();
    sources.sort();
    for &from in &sources {
        let expected_reach: FxHashSet<RegionVid> = reachable(expected_outlives, from);
        let actual_reach: FxHashSet<RegionVid> = reachable(actual_outlives, mapping[&from]);
        for &to in &sources {
            let expected_holds: bool = expected_reach.contains(&to);
            let actual_holds: bool = actual_reach.contains(&mapping[&to]);
            if expected_holds != actual_holds {
                writeln!(
                    report,
                    "{name}: {from:?}: {to:?} is {expected_holds} for rustc but {:?}: {:?} is {actual_holds} for us",
                    mapping[&from], mapping[&to]
                )
                .expect("writing to a string succeeds");
            }
        }
    }
    if !report.is_empty() && std::env::var_os("INSTANCE_REGIONS_DEBUG").is_some() {
        let mut expected_sorted: Vec<(RegionVid, RegionVid)> = expected_outlives.to_vec();
        expected_sorted.sort();
        expected_sorted.dedup();
        let mut actual_sorted: Vec<(RegionVid, RegionVid)> = actual.outlives.clone();
        actual_sorted.sort();
        actual_sorted.dedup();
        eprintln!("==== {name}: expected regions {expected_regions:?}");
        eprintln!("==== {name}: expected outlives {expected_sorted:?}");
        eprintln!("==== {name}: actual regions {actual_regions:?}");
        eprintln!("==== {name}: actual body\n{:#?}", actual.body);
        eprintln!("==== {name}: actual promoted\n{:#?}", actual.promoted);
        eprintln!("==== {name}: actual outlives {actual_sorted:?}");
        eprintln!("==== {name}: mapping {:?}", {
            let mut pairs: Vec<(RegionVid, RegionVid)> =
                mapping.iter().map(|(&a, &b)| (a, b)).collect();
            pairs.sort();
            pairs
        });
    }
    report
}

fn expected<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> Expected<'tcx, 'tcx> {
    let body_with_facts: &'tcx BodyWithBorrowckFacts<'tcx> = borrowck_facts(tcx, def);
    Expected {
        body: &body_with_facts.body,
        promoted: &body_with_facts.promoted,
        outlives: body_with_facts
            .input_facts
            .as_ref()
            .expect("the borrow checker computes the input facts")
            .subset_base
            .iter()
            .map(|&(sup, sub, _)| (RegionVid::from(sup), RegionVid::from(sub)))
            .collect(),
    }
}

pub(super) fn body_owner(tcx: TyCtxt<'_>, name: &str) -> LocalDefId {
    tcx.hir_body_owners()
        .find(|&def| tcx.def_path_str(def) == name)
        .unwrap_or_else(|| panic!("the source defines `{name}`"))
}

// Compares the facts of every body of an instance of a generic function with the facts
// rustc computes for its twin: the same function written with the type args in place of
// the params.
pub(super) fn compare_instance_with_twin<'tcx>(
    tcx: TyCtxt<'tcx>,
    generic: &str,
    type_args: &[Ty<'tcx>],
    twin: &str,
) -> String {
    let generic: LocalDefId = body_owner(tcx, generic);
    let mut type_args = type_args.iter().copied();
    let args: GenericArgsRef<'tcx> =
        GenericArgs::for_item(tcx, generic.to_def_id(), |param, _| match param.kind {
            GenericParamDefKind::Lifetime => tcx.lifetimes.re_erased.into(),
            GenericParamDefKind::Type { .. } => {
                type_args.next().expect("a type arg for every type param").into()
            }
            GenericParamDefKind::Const { .. } => panic!("const params are not instantiated"),
        });
    assert!(type_args.next().is_none(), "a type param for every type arg");
    compare_with_twin(tcx, Instance::new_raw(generic.to_def_id(), args), twin)
}

// The instances of the generic functions of this crate that the crate creates.
fn generic_instances(tcx: TyCtxt<'_>) -> FxHashSet<Instance<'_>> {
    let mut instances: FxHashSet<Instance<'_>> = FxHashSet::default();
    for unit in tcx.collect_and_partition_mono_items(()).codegen_units {
        for item in unit.items().keys() {
            let MonoItem::Fn(instance) = *item else { continue };
            let InstanceKind::Item(def) = instance.def else { continue };
            let Some(def) = def.as_local() else { continue };
            if tcx.hir_maybe_body_owned_by(def).is_some()
                && tcx.generics_of(tcx.typeck_root_def_id_local(def)).requires_monomorphization(tcx)
            {
                instances.insert(instance);
            }
        }
    }
    instances
}

// Compares the one instance of a generic function that the crate creates with the facts
// rustc computes for its twin.
pub(super) fn compare_created_instance_with_twin(
    tcx: TyCtxt<'_>,
    generic: &str,
    twin: &str,
) -> String {
    let instances: Vec<Instance<'_>> = generic_instances(tcx)
        .into_iter()
        .filter(|instance| tcx.def_path_str(instance.def_id()) == generic)
        .collect();
    let [instance] = instances[..] else {
        let created: Vec<String> = generic_instances(tcx).iter().map(ToString::to_string).collect();
        panic!("the crate creates one instance of `{generic}`; it creates {created:?}");
    };
    compare_with_twin(tcx, instance, twin)
}

fn compare_with_twin<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>, twin: &str) -> String {
    let twin: LocalDefId = body_owner(tcx, twin);
    let instances: Vec<Instance<'tcx>> =
        instances_within(tcx, instance).unwrap_or_else(|error| panic!("{instance}: {error}"));
    let twins: Vec<LocalDefId> = tcx
        .nested_bodies_within(twin)
        .iter()
        .chain([twin])
        .filter(|&def| tcx.def_kind(def).is_fn_like())
        .collect();
    assert_eq!(instances.len(), twins.len(), "{instance}: the twin has the same bodies");
    let mut report: String = String::new();
    for (instance, twin) in std::iter::zip(instances, twins) {
        let name: String = instance.to_string();
        let actual: &InstanceFacts<'tcx> = match instance_facts(tcx, instance) {
            Ok(actual) => actual,
            Err(error) => panic!("{name}: {error}"),
        };
        report.push_str(&user_differences(tcx, &name, &expected(tcx, twin), actual));
    }
    report
}

// Analyzes every instance of a generic function of this crate that the crate creates.
// rustc computes no facts for them, so only the success of the analysis is checked.
fn analyze_generic_instances(tcx: TyCtxt<'_>) {
    for instance in generic_instances(tcx) {
        if let Err(error) = instance_facts(tcx, instance) {
            panic!("{instance}: {error}");
        }
    }
}

// Compares every function-like body whose typeck root is not generic with the facts
// rustc computes, and analyzes the instances of the generic ones.
pub(super) fn compare_local_bodies(tcx: TyCtxt<'_>) -> Comparison {
    let mut report: String = String::new();
    let mut checked: usize = 0;
    for def in tcx.hir_body_owners() {
        let root: LocalDefId = tcx.typeck_root_def_id_local(def);
        if !tcx.def_kind(def).is_fn_like() || tcx.generics_of(root).requires_monomorphization(tcx) {
            continue;
        }
        let expected: Expected<'_, '_> = expected(tcx, def);
        let args: GenericArgsRef<'_> =
            tcx.erase_and_anonymize_regions(GenericArgs::identity_for_item(tcx, root));
        let set: &RecordedMir<'_> =
            recorded_mir(tcx, def.to_def_id()).expect("record_mir records every local body");
        let instance: Instance<'_> = Instance::new_raw(
            def.to_def_id(),
            set.args_of_body(tcx, def.to_def_id(), args)
                .expect("a body within a typeck root is a closure or an inline const"),
        );
        let name: String = tcx.def_path_str(def);
        let actual: &InstanceFacts<'_> = match instance_facts(tcx, instance) {
            Ok(actual) => actual,
            Err(error) => panic!("{name}: {error}"),
        };
        report.push_str(&differences(tcx, &name, &expected, actual));
        checked += 1;
    }
    analyze_generic_instances(tcx);
    Comparison { checked, report }
}
