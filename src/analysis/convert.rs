use preborrowck_mir::RecordedMir;
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_infer::infer::SubregionOrigin;
use rustc_infer::infer::canonical::QueryRegionConstraints;
use rustc_infer::infer::outlives::env::RegionBoundPairs;
use rustc_infer::infer::outlives::obligations::{TypeOutlives, TypeOutlivesDelegate};
use rustc_infer::infer::region_constraints::{GenericKind, VerifyBound};
use rustc_infer::traits::query::type_op::DeeplyNormalize;
use rustc_middle::mir::ConstraintCategory;
use rustc_middle::ty::{
    self, GenericArgKind, RegionVid, Ty, TyCtxt, TypeFoldable, TypeVisitableExt, elaborate,
    fold_regions,
};
use rustc_span::Span;

use super::closures::{ClosureRequirements, ClosureSubject};
use super::constraints::{Constraints, TypeTest};
use super::infer::Infer;
use super::universal::Universal;

// Converts the region constraints of type operations into outlives constraints
// between region variables and into type tests.
pub(crate) struct Conversion<'a, 'tcx> {
    infer: &'a Infer<'tcx>,
    universal: &'a Universal<'tcx>,
    region_bound_pairs: &'a RegionBoundPairs<'tcx>,
    known_type_outlives: &'a [ty::PolyTypeOutlivesPredicate<'tcx>],
    span: Span,
    constraints: &'a mut Constraints<'tcx>,
}

impl<'a, 'tcx> Conversion<'a, 'tcx> {
    pub(crate) fn new(
        infer: &'a Infer<'tcx>,
        universal: &'a Universal<'tcx>,
        region_bound_pairs: &'a RegionBoundPairs<'tcx>,
        known_type_outlives: &'a [ty::PolyTypeOutlivesPredicate<'tcx>],
        span: Span,
        constraints: &'a mut Constraints<'tcx>,
    ) -> Self {
        Self { infer, universal, region_bound_pairs, known_type_outlives, span, constraints }
    }

    pub(crate) fn convert_all(&mut self, query_constraints: &QueryRegionConstraints<'tcx>) {
        let QueryRegionConstraints { constraints, assumptions } = query_constraints;
        let assumptions =
            elaborate::elaborate_outlives_assumptions(self.infer.tcx, assumptions.iter().copied());
        for &(constraint, _) in constraints {
            constraint.iter_outlives().for_each(|predicate| {
                self.convert(predicate, &assumptions);
            });
        }
    }

    // Instantiates the requirements of a closure body with the regions of the
    // closure type at the point where the closure is created.
    pub(crate) fn apply_closure_requirements(
        &mut self,
        requirements: &ClosureRequirements<'tcx>,
        closure_def_id: DefId,
        closure_args: ty::GenericArgsRef<'tcx>,
        set: &RecordedMir<'tcx>,
    ) {
        let closure_mapping: IndexVec<RegionVid, ty::Region<'tcx>> = Universal::closure_mapping(
            self.infer.tcx,
            closure_args,
            requirements.num_external_vids,
            closure_def_id,
            set,
        );
        for requirement in &requirements.outlives {
            let outlived_region: ty::Region<'tcx> =
                closure_mapping[requirement.outlived_free_region];
            let subject: ty::GenericArg<'tcx> = match requirement.subject {
                ClosureSubject::Region(re) => closure_mapping[re].into(),
                ClosureSubject::Ty(subject_ty) => {
                    fold_regions(self.infer.tcx, subject_ty, |r, _| closure_mapping[r.as_var()])
                        .into()
                }
            };
            self.span = requirement.blame_span;
            self.convert(ty::OutlivesPredicate(subject, outlived_region), &FxHashSet::default());
        }
    }

    fn convert(
        &mut self,
        predicate: ty::ArgOutlivesPredicate<'tcx>,
        higher_ranked_assumptions: &FxHashSet<ty::ArgOutlivesPredicate<'tcx>>,
    ) {
        let tcx: TyCtxt<'tcx> = self.infer.tcx;
        let Conversion { infer, universal, region_bound_pairs, known_type_outlives, .. } = *self;
        let mut outlives_predicates: Vec<ty::ArgOutlivesPredicate<'tcx>> = vec![predicate];
        for iteration in 0.. {
            if outlives_predicates.is_empty() {
                break;
            }
            assert!(
                tcx.recursion_limit().value_within_limit(iteration),
                "unexpected overflowed when processing region obligations: {outlives_predicates:#?}"
            );
            let mut next_outlives_predicates: Vec<ty::ArgOutlivesPredicate<'tcx>> = vec![];
            for pred in outlives_predicates {
                if tcx.sess.opts.unstable_opts.higher_ranked_assumptions
                    && higher_ranked_assumptions.contains(&pred)
                {
                    continue;
                }
                let ty::OutlivesPredicate(k1, r2) = pred;
                match k1.kind() {
                    GenericArgKind::Lifetime(r1) => {
                        let r1_vid: RegionVid = self.region_vid(r1);
                        let r2_vid: RegionVid = self.region_vid(r2);
                        self.constraints.push(r1_vid, r2_vid);
                    }
                    GenericArgKind::Type(mut t1) => {
                        t1 = infer.resolve_vars_if_possible(t1);
                        if infer.next_trait_solver() {
                            t1 = self.normalize_and_add_type_outlives_constraints(
                                t1,
                                &mut next_outlives_predicates,
                            );
                        }
                        let implicit_region_bound: ty::Region<'tcx> =
                            ty::Region::new_var(tcx, universal.implicit_region_bound());
                        let origin: SubregionOrigin<'tcx> =
                            SubregionOrigin::RelateParamBound(self.span, t1, None);
                        TypeOutlives::new(
                            &mut *self,
                            tcx,
                            region_bound_pairs,
                            Some(implicit_region_bound),
                            known_type_outlives,
                        )
                        .type_must_outlive(
                            origin,
                            t1,
                            r2,
                            ConstraintCategory::Boring,
                        );
                    }
                    GenericArgKind::Const(_) => unreachable!(),
                }
            }
            outlives_predicates = next_outlives_predicates;
        }
    }

    fn replace_placeholders_with_nll<T: TypeFoldable<TyCtxt<'tcx>>>(&mut self, value: T) -> T {
        if value.has_placeholders() {
            fold_regions(self.infer.tcx, value, |r, _| match r.kind() {
                ty::RePlaceholder(placeholder) => {
                    self.constraints.placeholder_region(self.infer, placeholder)
                }
                _ => r,
            })
        } else {
            value
        }
    }

    fn region_vid(&mut self, r: ty::Region<'tcx>) -> RegionVid {
        if let ty::RePlaceholder(placeholder) = r.kind() {
            self.constraints.placeholder_region(self.infer, placeholder).as_var()
        } else {
            self.universal.to_region_vid(r)
        }
    }

    fn normalize_and_add_type_outlives_constraints(
        &self,
        ty: Ty<'tcx>,
        next_outlives_predicates: &mut Vec<ty::ArgOutlivesPredicate<'tcx>>,
    ) -> Ty<'tcx> {
        match self.infer.perform(self.infer.param_env.and(DeeplyNormalize { value: ty }), self.span)
        {
            Ok((ty, constraints)) => {
                if let Some(QueryRegionConstraints { constraints, assumptions: _ }) = constraints {
                    next_outlives_predicates.extend(
                        constraints.iter().flat_map(|(constraint, _)| constraint.iter_outlives()),
                    );
                }
                ty
            }
            Err(()) => ty,
        }
    }
}

impl<'tcx> TypeOutlivesDelegate<'tcx> for &mut Conversion<'_, 'tcx> {
    fn push_sub_region_constraint(
        &mut self,
        _origin: SubregionOrigin<'tcx>,
        a: ty::Region<'tcx>,
        b: ty::Region<'tcx>,
        _constraint_category: ConstraintCategory<'tcx>,
    ) {
        let b: RegionVid = self.region_vid(b);
        let a: RegionVid = self.region_vid(a);
        self.constraints.push(b, a);
    }

    fn push_verify(
        &mut self,
        _origin: SubregionOrigin<'tcx>,
        kind: GenericKind<'tcx>,
        a: ty::Region<'tcx>,
        bound: VerifyBound<'tcx>,
    ) {
        let kind: GenericKind<'tcx> = self.replace_placeholders_with_nll(kind);
        let bound: VerifyBound<'tcx> = self.replace_placeholders_with_nll(bound);
        let lower_bound: RegionVid = self.region_vid(a);
        self.constraints.type_tests.push(TypeTest {
            generic_kind: kind,
            lower_bound,
            span: self.span,
            verify_bound: bound,
        });
    }
}
