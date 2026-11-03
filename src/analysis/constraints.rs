use rustc_data_structures::fx::FxIndexMap;
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_infer::infer::region_constraints::{GenericKind, VerifyBound};
use rustc_middle::ty::{self, RegionVid};
use rustc_span::Span;

use super::infer::Infer;

// `sup: sub`, the region `sup` outlives the region `sub`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Outlives {
    pub(crate) sup: RegionVid,
    pub(crate) sub: RegionVid,
}

// `generic_kind: lower_bound`, provable through `verify_bound`.
#[derive(Clone, Debug)]
pub(crate) struct TypeTest<'tcx> {
    pub(crate) generic_kind: GenericKind<'tcx>,
    pub(crate) lower_bound: RegionVid,
    pub(crate) span: Span,
    pub(crate) verify_bound: VerifyBound<'tcx>,
}

#[derive(Default)]
pub(crate) struct Constraints<'tcx> {
    pub(crate) outlives: Vec<Outlives>,
    pub(crate) type_tests: Vec<TypeTest<'tcx>>,
    placeholders: FxIndexMap<ty::PlaceholderRegion<'tcx>, RegionVid>,
}

impl<'tcx> Constraints<'tcx> {
    pub(crate) fn push(&mut self, sup: RegionVid, sub: RegionVid) {
        self.outlives.push(Outlives { sup, sub });
    }

    // The region variable standing for a placeholder region, created in the
    // placeholder's universe on first use.
    pub(crate) fn placeholder_region(
        &mut self,
        infer: &Infer<'tcx>,
        placeholder: ty::PlaceholderRegion<'tcx>,
    ) -> ty::Region<'tcx> {
        let vid: RegionVid = *self.placeholders.entry(placeholder).or_insert_with(|| {
            infer
                .next_nll_region_var_in_universe(
                    NllRegionVariableOrigin::Placeholder(placeholder),
                    placeholder.universe,
                )
                .as_var()
        });
        ty::Region::new_var(infer.tcx, vid)
    }
}
