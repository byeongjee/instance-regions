use rustc_index::IndexVec;
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_infer::infer::outlives::test_type_match;
use rustc_infer::infer::region_constraints::{VerifyBound, VerifyIfEq};
use rustc_middle::ty::{self, RegionVid, Ty, TyCtxt, TypeFoldable, fold_regions};
use rustc_span::{DUMMY_SP, Span};

use super::constraints::{Outlives, TypeTest};
use super::graph::{RegionDefinition, SccIndex};
use super::relations::Relations;
use super::values::RegionValues;
use crate::Error;

// The outlives requirements between the free regions of a closure body that the
// body cannot prove itself. The regions are numbered as in the closure body:
// `'static`, then the free regions of the closure type in order of appearance,
// then the late-bound regions of the enclosing bodies.
#[derive(Clone, Debug)]
pub(crate) struct ClosureRequirements<'tcx> {
    pub(crate) num_external_vids: usize,
    pub(crate) outlives: Vec<ClosureOutlives<'tcx>>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ClosureOutlives<'tcx> {
    pub(crate) subject: ClosureSubject<'tcx>,
    pub(crate) outlived_free_region: RegionVid,
    pub(crate) blame_span: Span,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum ClosureSubject<'tcx> {
    Region(RegionVid),
    // A type whose regions are the external region variables of the closure body.
    Ty(Ty<'tcx>),
}

// What a requirement the body can neither prove nor propagate means. rustc discards
// the error before the opaque types are handled, as their hidden types may still
// resolve the regions, and reports it afterwards.
#[derive(Clone, Copy)]
pub(crate) enum RegionErrors {
    Discard,
    Reject,
}

struct Solver<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    relations: &'a Relations<'tcx>,
    values: RegionValues,
    errors: RegionErrors,
    propagated: Vec<ClosureOutlives<'tcx>>,
}

pub(crate) fn closure_requirements<'tcx>(
    tcx: TyCtxt<'tcx>,
    relations: &Relations<'tcx>,
    definitions: &IndexVec<RegionVid, RegionDefinition<'tcx>>,
    outlives: &[Outlives],
    type_tests: &[TypeTest<'tcx>],
    errors: RegionErrors,
) -> Result<Option<ClosureRequirements<'tcx>>, Error> {
    let mut values: RegionValues = RegionValues::new(outlives, definitions, &relations.universal);
    values.propagate();
    let mut solver = Solver { tcx, relations, values, errors, propagated: Vec::new() };
    for type_test in type_tests {
        solver.check_type_test(type_test)?;
    }
    for (fr, definition) in definitions.iter_enumerated() {
        if let NllRegionVariableOrigin::FreeRegion = definition.origin {
            solver.check_universal_region(fr)?;
        }
    }
    if solver.propagated.is_empty() {
        return Ok(None);
    }
    Ok(Some(ClosureRequirements {
        num_external_vids: relations.universal.num_global_and_external_regions(),
        outlives: solver.propagated,
    }))
}

impl<'tcx> Solver<'_, 'tcx> {
    fn region_error(&self, reason: &str) -> Result<(), Error> {
        match self.errors {
            RegionErrors::Discard => Ok(()),
            RegionErrors::Reject => Err(Error::new(reason)),
        }
    }

    // A type test the closure body cannot prove is promoted to a requirement on the
    // external regions. One that rustc could not promote either is a region error.
    fn check_type_test(&mut self, type_test: &TypeTest<'tcx>) -> Result<(), Error> {
        let generic_ty: Ty<'tcx> = type_test.generic_kind.to_ty(self.tcx);
        if self.eval_verify_bound(generic_ty, type_test.lower_bound, &type_test.verify_bound)? {
            return Ok(());
        }
        let Some(subject) = self.try_promote_type_test_subject(generic_ty)? else {
            return self.region_error("a type test of a closure cannot be promoted");
        };
        let r_scc: SccIndex = self.values.scc(type_test.lower_bound);
        if self.values.contains_placeholder(r_scc) {
            self.propagated.push(ClosureOutlives {
                subject,
                outlived_free_region: self.relations.universal.fr_static,
                blame_span: type_test.span,
            });
            return Ok(());
        }
        let outlived: Vec<RegionVid> = self.values.universal_regions_outlived_by(r_scc).collect();
        assert!(!outlived.is_empty(), "a promoted type test has a universal lower bound");
        for ur in outlived {
            for upper_bound in self.relations.non_local_upper_bounds(ur) {
                self.propagated.push(ClosureOutlives {
                    subject,
                    outlived_free_region: upper_bound,
                    blame_span: type_test.span,
                });
            }
        }
        Ok(())
    }

    // The type of a type test with every region replaced by an equal external region.
    fn try_promote_type_test_subject(
        &self,
        ty: Ty<'tcx>,
    ) -> Result<Option<ClosureSubject<'tcx>>, Error> {
        let tcx: TyCtxt<'tcx> = self.tcx;
        let mut failed: bool = false;
        let mut error: Option<Error> = None;
        let ty: Ty<'tcx> = fold_regions(tcx, ty, |r, _| {
            let r_vid: RegionVid = self.relations.universal.to_region_vid(r);
            let r_scc: SccIndex = self.values.scc(r_vid);
            let candidates: Vec<RegionVid> = self
                .values
                .universal_regions_outlived_by(r_scc)
                .filter(|&u_r| !self.relations.universal.is_local_free_region(u_r))
                .collect();
            for u_r in candidates {
                match self.eval_equal(u_r, r_vid) {
                    Ok(true) => return ty::Region::new_var(tcx, u_r),
                    Ok(false) => {}
                    Err(failure) => {
                        error = Some(failure);
                        return r;
                    }
                }
            }
            failed = true;
            r
        });
        if let Some(error) = error {
            return Err(error);
        }
        if failed {
            return Ok(None);
        }
        Ok(Some(ClosureSubject::Ty(ty)))
    }

    fn eval_verify_bound(
        &self,
        generic_ty: Ty<'tcx>,
        lower_bound: RegionVid,
        verify_bound: &VerifyBound<'tcx>,
    ) -> Result<bool, Error> {
        match verify_bound {
            VerifyBound::IfEq(verify_if_eq_b) => {
                self.eval_if_eq(generic_ty, lower_bound, *verify_if_eq_b)
            }
            VerifyBound::IsEmpty => {
                let lower_bound_scc: SccIndex = self.values.scc(lower_bound);
                if self.values.universal_regions_outlived_by(lower_bound_scc).next().is_some()
                    || self.values.contains_placeholder(lower_bound_scc)
                {
                    return Ok(false);
                }
                Err(Error::new("the emptiness of an existential region is not evaluated"))
            }
            VerifyBound::OutlivedBy(r) => {
                let r_vid: RegionVid = self.relations.universal.to_region_vid(*r);
                self.eval_outlives(r_vid, lower_bound)
            }
            VerifyBound::AnyBound(verify_bounds) => {
                for verify_bound in verify_bounds {
                    if self.eval_verify_bound(generic_ty, lower_bound, verify_bound)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            VerifyBound::AllBounds(verify_bounds) => {
                for verify_bound in verify_bounds {
                    if !self.eval_verify_bound(generic_ty, lower_bound, verify_bound)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
    }

    fn eval_if_eq(
        &self,
        generic_ty: Ty<'tcx>,
        lower_bound: RegionVid,
        verify_if_eq_b: ty::Binder<'tcx, VerifyIfEq<'tcx>>,
    ) -> Result<bool, Error> {
        let generic_ty: Ty<'tcx> = self.normalize_to_scc_representatives(generic_ty);
        let verify_if_eq_b: ty::Binder<'tcx, VerifyIfEq<'tcx>> =
            self.normalize_to_scc_representatives(verify_if_eq_b);
        match test_type_match::extract_verify_if_eq(self.tcx, &verify_if_eq_b, generic_ty) {
            Some(r) => {
                let r_vid: RegionVid = self.relations.universal.to_region_vid(r);
                self.eval_outlives(r_vid, lower_bound)
            }
            None => Ok(false),
        }
    }

    // Replaces every region with the representative of its component, so that equal
    // regions compare equal.
    fn normalize_to_scc_representatives<T: TypeFoldable<TyCtxt<'tcx>>>(&self, value: T) -> T {
        fold_regions(self.tcx, value, |r, _| {
            let vid: RegionVid = self.relations.universal.to_region_vid(r);
            let representative: RegionVid = self.values.representative(vid).rvid();
            ty::Region::new_var(self.tcx, representative)
        })
    }

    fn check_universal_region(&mut self, longer_fr: RegionVid) -> Result<(), Error> {
        let longer_fr_scc: SccIndex = self.values.scc(longer_fr);
        assert!(self.values.max_nameable_universe(longer_fr_scc).is_root());
        let representative: RegionVid = self.values.representative(longer_fr).rvid();
        if representative != longer_fr {
            self.check_universal_region_relation(longer_fr, representative)?;
            return Ok(());
        }
        let outlived: Vec<RegionVid> =
            self.values.universal_regions_outlived_by(longer_fr_scc).collect();
        for shorter_fr in outlived {
            self.check_universal_region_relation(longer_fr, shorter_fr)?;
        }
        Ok(())
    }

    fn check_universal_region_relation(
        &mut self,
        longer_fr: RegionVid,
        shorter_fr: RegionVid,
    ) -> Result<(), Error> {
        if self.relations.outlives(longer_fr, shorter_fr) {
            return Ok(());
        }
        self.try_propagate_universal_region_error(longer_fr, shorter_fr)
    }

    fn try_propagate_universal_region_error(
        &mut self,
        longer_fr: RegionVid,
        shorter_fr: RegionVid,
    ) -> Result<(), Error> {
        let longer_fr_minus: Vec<RegionVid> = self.relations.non_local_lower_bounds(longer_fr);
        if longer_fr_minus.is_empty() {
            return self.region_error("a region error of a closure cannot be propagated");
        }
        let shorter_fr_plus: Vec<RegionVid> = self.relations.non_local_upper_bounds(shorter_fr);
        let mut constraints: Vec<(RegionVid, RegionVid)> = vec![];
        for fr_minus in longer_fr_minus {
            for shorter_fr_plus in &shorter_fr_plus {
                constraints.push((fr_minus, *shorter_fr_plus));
            }
        }
        let mut subset: Vec<(RegionVid, RegionVid)> = vec![];
        for &(fr_minus, fr_plus) in &constraints {
            if self.eval_outlives(fr_minus, fr_plus)? {
                subset.push((fr_minus, fr_plus));
            }
        }
        let propagated_constraints: Vec<(RegionVid, RegionVid)> =
            if subset.is_empty() { constraints } else { subset };
        assert!(
            !propagated_constraints.is_empty(),
            "Expected at least one constraint to propagate here"
        );
        for (fr_minus, fr_plus) in propagated_constraints {
            self.propagated.push(ClosureOutlives {
                subject: ClosureSubject::Region(fr_minus),
                outlived_free_region: fr_plus,
                blame_span: DUMMY_SP,
            });
        }
        Ok(())
    }

    fn eval_equal(&self, r1: RegionVid, r2: RegionVid) -> Result<bool, Error> {
        Ok(self.eval_outlives(r1, r2)? && self.eval_outlives(r2, r1)?)
    }

    // Whether `sup_region: sub_region` holds in the values. The points of an
    // existential region are not computed, so a relation that depends on them is
    // not evaluated.
    fn eval_outlives(&self, longer: RegionVid, shorter: RegionVid) -> Result<bool, Error> {
        let shorter_scc: SccIndex = self.values.scc(shorter);
        let longer_scc: SccIndex = self.values.scc(longer);
        if shorter_scc == longer_scc {
            return Ok(true);
        }
        let fr_static: RegionVid = self.relations.universal.fr_static;
        if shorter != fr_static && !self.values.can_name_all_placeholders(longer_scc, shorter_scc) {
            return self.eval_outlives(longer, fr_static);
        }
        let universal_outlives: bool =
            self.values.universal_regions_outlived_by(shorter_scc).all(|outlived| {
                self.values
                    .universal_regions_outlived_by(longer_scc)
                    .any(|outliving| self.relations.outlives(outliving, outlived))
            });
        if !universal_outlives {
            return Ok(false);
        }
        if self.relations.universal.is_universal_region(longer) {
            return Ok(true);
        }
        Err(Error::new("the outlives relation of an existential region is not evaluated"))
    }
}
