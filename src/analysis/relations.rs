use preborrowck_mir::RecordedMir;
use rustc_data_structures::transitive_relation::{TransitiveRelation, TransitiveRelationBuilder};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::canonical::QueryRegionConstraints;
use rustc_infer::infer::outlives;
use rustc_infer::infer::outlives::env::RegionBoundPairs;
use rustc_infer::infer::region_constraints::GenericKind;
use rustc_infer::traits::query::type_op::DeeplyNormalize;
use rustc_middle::traits::query::OutlivesBound;
use rustc_middle::ty::{self, RegionVid, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::Span;
use rustc_trait_selection::traits::query::type_op::ImpliedOutlivesBounds;

use super::constraints::Constraints;
use super::convert::Conversion;
use super::infer::{Infer, assert_instantiated};
use super::universal::Universal;

// The universal regions of a body with the outlives relations between them that are
// known from where clauses and implied bounds.
pub(crate) struct Relations<'tcx> {
    pub(crate) universal: Universal<'tcx>,
    outlives: TransitiveRelation<RegionVid>,
    inverse_outlives: TransitiveRelation<RegionVid>,
    pub(crate) region_bound_pairs: RegionBoundPairs<'tcx>,
    pub(crate) known_type_outlives: Vec<ty::PolyTypeOutlivesPredicate<'tcx>>,
    pub(crate) normalized_inputs_and_output: Vec<Ty<'tcx>>,
}

impl Relations<'_> {
    // The smallest known regions that outlive `fr` and are not local to this body.
    pub(crate) fn non_local_upper_bounds(&self, fr: RegionVid) -> Vec<RegionVid> {
        let res: Vec<RegionVid> = self.non_local_bounds(&self.inverse_outlives, fr);
        assert!(!res.is_empty(), "can't find an upper bound!?");
        res
    }

    // The largest known regions that `fr` outlives and are not local to this body.
    pub(crate) fn non_local_lower_bounds(&self, fr: RegionVid) -> Vec<RegionVid> {
        self.non_local_bounds(&self.outlives, fr)
    }

    fn non_local_bounds(
        &self,
        relation: &TransitiveRelation<RegionVid>,
        fr0: RegionVid,
    ) -> Vec<RegionVid> {
        assert!(self.universal.is_universal_region(fr0));
        let mut external_parents: Vec<RegionVid> = vec![];
        let mut queue: Vec<RegionVid> = vec![relation.minimal_scc_representative(fr0)];
        while let Some(fr) = queue.pop() {
            if !self.universal.is_local_free_region(fr) {
                external_parents.push(fr);
                continue;
            }
            queue.extend(relation.parents(fr));
        }
        external_parents
    }

    pub(crate) fn outlives(&self, fr1: RegionVid, fr2: RegionVid) -> bool {
        self.outlives.contains(fr1, fr2)
    }

    pub(crate) fn equal(&self, fr1: RegionVid, fr2: RegionVid) -> bool {
        self.outlives.contains(fr1, fr2) && self.outlives.contains(fr2, fr1)
    }
}

struct RelationsBuilder<'a, 'tcx> {
    infer: &'a Infer<'tcx>,
    universal: Universal<'tcx>,
    constraints: &'a mut Constraints<'tcx>,
    outlives: TransitiveRelationBuilder<RegionVid>,
    inverse_outlives: TransitiveRelationBuilder<RegionVid>,
    region_bound_pairs: RegionBoundPairs<'tcx>,
}

pub(crate) fn create<'tcx>(
    infer: &Infer<'tcx>,
    universal: Universal<'tcx>,
    constraints: &mut Constraints<'tcx>,
    set: &RecordedMir<'tcx>,
) -> Relations<'tcx> {
    RelationsBuilder {
        infer,
        universal,
        constraints,
        outlives: TransitiveRelationBuilder::default(),
        inverse_outlives: TransitiveRelationBuilder::default(),
        region_bound_pairs: RegionBoundPairs::default(),
    }
    .create(set)
}

impl<'tcx> RelationsBuilder<'_, 'tcx> {
    fn relate_universal_regions(&mut self, fr_a: RegionVid, fr_b: RegionVid) {
        self.outlives.add(fr_a, fr_b);
        self.inverse_outlives.add(fr_b, fr_a);
    }

    fn create(mut self, set: &RecordedMir<'tcx>) -> Relations<'tcx> {
        let tcx: TyCtxt<'tcx> = self.infer.tcx;
        let defining_ty_def_id: DefId = self.universal.defining_ty.def_id();
        let span: Span = tcx.def_span(defining_ty_def_id);
        let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
        self.add_outlives_bounds(outlives::explicit_outlives_bounds(param_env));
        let fr_static: RegionVid = self.universal.fr_static;
        let fr_fn_body: RegionVid = self.universal.fr_fn_body;
        for fr in self.universal.universal_regions_iter() {
            self.relate_universal_regions(fr, fr);
            self.relate_universal_regions(fr_static, fr);
            self.relate_universal_regions(fr, fr_fn_body);
        }
        let mut constraints: Vec<&'tcx QueryRegionConstraints<'tcx>> = vec![];
        let mut known_type_outlives: Vec<ty::PolyTypeOutlivesPredicate<'tcx>> = vec![];
        for bound in param_env.caller_bounds() {
            if let Some(outlives) = bound.as_type_outlives_clause() {
                self.normalize_and_push_type_outlives_obligation(
                    outlives,
                    span,
                    &mut known_type_outlives,
                    &mut constraints,
                );
            }
        }
        let unnormalized_input_output_tys: Vec<Ty<'tcx>> = self
            .universal
            .unnormalized_input_tys
            .iter()
            .copied()
            .chain(Some(self.universal.unnormalized_output_ty))
            .collect();
        let mut normalized_inputs_and_output: Vec<Ty<'tcx>> =
            Vec::with_capacity(unnormalized_input_output_tys.len());
        for ty in unnormalized_input_output_tys {
            if let Some(c) = self.add_implied_bounds(ty, span) {
                constraints.push(c);
            }
            assert_instantiated(&ty);
            let (norm_ty, constraints_normalize) = self
                .infer
                .perform(param_env.and(DeeplyNormalize { value: ty }), span)
                .unwrap_or((ty, None));
            if let Some(c) = constraints_normalize {
                constraints.push(c);
            }
            if ty != norm_ty
                && let Some(c) = self.add_implied_bounds(norm_ty, span)
            {
                constraints.push(c);
            }
            normalized_inputs_and_output.push(norm_ty);
        }
        if matches!(tcx.def_kind(defining_ty_def_id), DefKind::AssocFn | DefKind::AssocConst { .. })
        {
            let assumptions: Vec<Ty<'tcx>> = set.typeck[&defining_ty_def_id]
                .assumed_wf_types
                .iter()
                .map(|&(ty, _)| self.universal.instantiate(tcx, ty::EarlyBinder::bind(ty)))
                .collect();
            for ty in assumptions {
                assert_instantiated(&ty);
                let Ok((norm_ty, normalization)) =
                    self.infer.perform(param_env.and(DeeplyNormalize { value: ty }), span)
                else {
                    continue;
                };
                constraints.extend(normalization);
                let implied: Option<&'tcx QueryRegionConstraints<'tcx>> =
                    self.add_implied_bounds(norm_ty, span);
                constraints.extend(implied);
            }
        }
        for c in constraints {
            Conversion::new(
                self.infer,
                &self.universal,
                &self.region_bound_pairs,
                &known_type_outlives,
                span,
                self.constraints,
            )
            .convert_all(c);
        }
        Relations {
            universal: self.universal,
            outlives: self.outlives.freeze(),
            inverse_outlives: self.inverse_outlives.freeze(),
            region_bound_pairs: self.region_bound_pairs,
            known_type_outlives,
            normalized_inputs_and_output,
        }
    }

    fn normalize_and_push_type_outlives_obligation(
        &self,
        mut outlives: ty::PolyTypeOutlivesPredicate<'tcx>,
        span: Span,
        known_type_outlives: &mut Vec<ty::PolyTypeOutlivesPredicate<'tcx>>,
        constraints: &mut Vec<&'tcx QueryRegionConstraints<'tcx>>,
    ) {
        if self.infer.next_trait_solver() {
            let Ok((normalized_outlives, constraints_normalize)) = self
                .infer
                .perform(self.infer.param_env.and(DeeplyNormalize { value: outlives }), span)
            else {
                return;
            };
            outlives = normalized_outlives;
            if let Some(c) = constraints_normalize {
                constraints.push(c);
            }
        }
        known_type_outlives.push(outlives);
    }

    fn add_implied_bounds(
        &mut self,
        ty: Ty<'tcx>,
        span: Span,
    ) -> Option<&'tcx QueryRegionConstraints<'tcx>> {
        assert_instantiated(&ty);
        let (bounds, constraints) = self
            .infer
            .perform(self.infer.param_env.and(ImpliedOutlivesBounds { ty }), span)
            .ok()?;
        let bounds = bounds.into_iter().filter(|bound| !bound.has_placeholders());
        self.add_outlives_bounds(bounds);
        constraints
    }

    fn add_outlives_bounds(
        &mut self,
        outlives_bounds: impl IntoIterator<Item = OutlivesBound<'tcx>>,
    ) {
        for outlives_bound in outlives_bounds {
            match outlives_bound {
                OutlivesBound::RegionSubRegion(r1, r2) => {
                    let r1: RegionVid = self.universal.to_region_vid(r1);
                    let r2: RegionVid = self.universal.to_region_vid(r2);
                    self.relate_universal_regions(r2, r1);
                }
                OutlivesBound::RegionSubParam(r_a, param_b) => {
                    self.region_bound_pairs
                        .insert(ty::OutlivesPredicate(GenericKind::Param(param_b), r_a));
                }
                OutlivesBound::RegionSubAlias(r_a, alias_b) => {
                    self.region_bound_pairs
                        .insert(ty::OutlivesPredicate(GenericKind::Alias(alias_b), r_a));
                }
            }
        }
    }
}
