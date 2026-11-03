use rustc_index::IndexSlice;
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_middle::mir::visit::{MutVisitor, TyContext};
use rustc_middle::mir::{Body, ConstOperand, Location, Promoted};
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt, TypeFoldable, fold_regions};

use super::infer::Infer;

// Replaces every region in the MIR with a fresh existential region variable.
pub(crate) fn renumber_mir<'tcx>(
    infer: &Infer<'tcx>,
    body: &mut Body<'tcx>,
    promoted: &mut IndexSlice<Promoted, Body<'tcx>>,
) {
    let mut renumberer = RegionRenumberer { infer };
    for body in promoted.iter_mut() {
        renumberer.visit_body_preserves_cfg(body);
    }
    renumberer.visit_body_preserves_cfg(body);
}

struct RegionRenumberer<'a, 'tcx> {
    infer: &'a Infer<'tcx>,
}

impl<'tcx> RegionRenumberer<'_, 'tcx> {
    fn renumber_regions<T: TypeFoldable<TyCtxt<'tcx>>>(&mut self, value: T) -> T {
        fold_regions(self.infer.tcx, value, |_, _| {
            self.infer.next_nll_region_var(NllRegionVariableOrigin::Existential { name: None })
        })
    }
}

impl<'tcx> MutVisitor<'tcx> for RegionRenumberer<'_, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.infer.tcx
    }

    fn visit_ty(&mut self, ty: &mut Ty<'tcx>, ty_context: TyContext) {
        if matches!(ty_context, TyContext::ReturnTy(_)) {
            return;
        }
        *ty = self.renumber_regions(*ty);
    }

    fn visit_args(&mut self, args: &mut GenericArgsRef<'tcx>, _: Location) {
        *args = self.renumber_regions(*args);
    }

    fn visit_region(&mut self, region: &mut ty::Region<'tcx>, _: Location) {
        *region = self.renumber_regions(*region);
    }

    fn visit_ty_const(&mut self, ct: &mut ty::Const<'tcx>, _: Location) {
        *ct = self.renumber_regions(*ct);
    }

    fn visit_const_operand(&mut self, constant: &mut ConstOperand<'tcx>, _: Location) {
        constant.const_ = self.renumber_regions(constant.const_);
    }
}
