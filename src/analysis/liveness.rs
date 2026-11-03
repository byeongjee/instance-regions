use rustc_data_structures::fx::{FxHashSet, FxIndexMap};
use rustc_index::IndexVec;
use rustc_index::bit_set::MixedBitSet;
use rustc_infer::infer::canonical::QueryRegionConstraints;
use rustc_middle::mir::visit::{MutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{BasicBlock, Body, Local, Location};
use rustc_middle::ty::{ParamEnvAnd, RegionVid, Ty, TyCtxt};
use rustc_mir_dataflow::impls::MaybeInitializedPlaces;
use rustc_mir_dataflow::move_paths::{HasMoveData, MoveData, MovePath, MovePathIndex};
use rustc_mir_dataflow::{Analysis, MaybeReachable, ResultsCursor};
use rustc_span::DUMMY_SP;
use rustc_trait_selection::traits::query::type_op::DropckOutlives;

use super::constraints::Outlives;
use super::typeck::TypeChecker;
use super::universal::Universal;

impl<'a, 'tcx> TypeChecker<'a, 'tcx> {
    // Adds the constraints of the destructors that may run on the locals whose
    // types mention a region that is not known to outlive a free region. Such a
    // local is dropped where it may be initialized at a drop of it.
    pub(super) fn generate_liveness_constraints(&mut self) {
        let tcx: TyCtxt<'tcx> = self.infer.tcx;
        let body: &'a Body<'tcx> = self.body;
        let free_regions: FxHashSet<RegionVid> = regions_that_outlive_free_regions(
            self.infer.num_region_vars(),
            self.universal(),
            &self.constraints.outlives,
        );
        let (relevant_live_locals, boring_locals): (Vec<Local>, Vec<Local>) =
            body.local_decls.iter_enumerated().map(|(local, _)| local).partition(|&local| {
                !tcx.all_free_regions_meet(&body.local_decls[local].ty, |r| {
                    free_regions.contains(&r.as_var())
                })
            });
        let move_data: MoveData<'tcx> = MoveData::gather_moves(body, tcx, |_| true);
        let drops: Drops = Drops::collect(body, &relevant_live_locals);
        let mut flow_inits: Option<ResultsCursor<'_, 'tcx, MaybeInitializedPlaces<'_, 'tcx>>> =
            None;
        let mut drop_data: FxIndexMap<Ty<'tcx>, Option<&'tcx QueryRegionConstraints<'tcx>>> =
            FxIndexMap::default();
        for local in relevant_live_locals {
            let Some(mpi) = move_data.rev_lookup.find_local(local) else { continue };
            let mut dropped: bool = false;
            for &block in &drops.blocks[local] {
                let flow_inits = flow_inits.get_or_insert_with(|| {
                    MaybeInitializedPlaces::new(tcx, body, &move_data)
                        .iterate_to_fixpoint(tcx, body, Some("instance-regions"))
                        .into_results_cursor(body)
                });
                if initialized_at_terminator(body, flow_inits, block, mpi) {
                    dropped = true;
                }
            }
            if !dropped {
                continue;
            }
            let local_ty: Ty<'tcx> = body.local_decls[local].ty;
            let data: Option<&'tcx QueryRegionConstraints<'tcx>> =
                if let Some(&data) = drop_data.get(&local_ty) {
                    data
                } else {
                    let data: Option<&'tcx QueryRegionConstraints<'tcx>> =
                        self.compute_drop_data(local_ty);
                    drop_data.insert(local_ty, data);
                    data
                };
            if let Some(data) = data {
                self.push_region_constraints(DUMMY_SP, data);
            }
        }
        for local in boring_locals {
            let local_ty: Ty<'tcx> = body.local_decls[local].ty;
            if !drop_data.contains_key(&local_ty) {
                let data: Option<&'tcx QueryRegionConstraints<'tcx>> =
                    self.compute_drop_data(local_ty);
                drop_data.insert(local_ty, data);
            }
        }
    }

    fn compute_drop_data(
        &mut self,
        dropped_ty: Ty<'tcx>,
    ) -> Option<&'tcx QueryRegionConstraints<'tcx>> {
        let op: ParamEnvAnd<'tcx, DropckOutlives<'tcx>> =
            self.infer.param_env.and(DropckOutlives { dropped_ty });
        match self.infer.perform(op, DUMMY_SP) {
            Ok((_, constraints)) => constraints,
            Err(()) => None,
        }
    }
}

// The blocks whose terminator drops each relevant local.
struct Drops {
    blocks: IndexVec<Local, Vec<BasicBlock>>,
}

impl Drops {
    fn collect(body: &Body<'_>, relevant: &[Local]) -> Self {
        let mut drops = Drops { blocks: IndexVec::from_elem(Vec::new(), &body.local_decls) };
        let mut relevant_flags: IndexVec<Local, bool> =
            IndexVec::from_elem(false, &body.local_decls);
        for &local in relevant {
            relevant_flags[local] = true;
        }
        let mut collector = DropCollector { drops: &mut drops, relevant: relevant_flags };
        collector.visit_body(body);
        drops
    }
}

struct DropCollector<'a> {
    drops: &'a mut Drops,
    relevant: IndexVec<Local, bool>,
}

impl Visitor<'_> for DropCollector<'_> {
    fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
        if self.relevant[local]
            && let PlaceContext::MutatingUse(MutatingUseContext::Drop) = context
            && !self.drops.blocks[local].contains(&location.block)
        {
            self.drops.blocks[local].push(location.block);
        }
    }
}

fn initialized_at_terminator<'tcx>(
    body: &Body<'tcx>,
    flow_inits: &mut ResultsCursor<'_, 'tcx, MaybeInitializedPlaces<'_, 'tcx>>,
    block: BasicBlock,
    mpi: MovePathIndex,
) -> bool {
    flow_inits.seek_before_primary_effect(body.terminator_loc(block));
    let state: &MaybeReachable<MixedBitSet<MovePathIndex>> = flow_inits.get();
    if state.contains(mpi) {
        return true;
    }
    let move_paths: &IndexVec<MovePathIndex, MovePath<'tcx>> =
        &flow_inits.analysis().move_data().move_paths;
    move_paths[mpi].find_descendant(move_paths, |mpi| state.contains(mpi)).is_some()
}

// The regions that outlive a universal region through the constraints so far.
fn regions_that_outlive_free_regions(
    num_region_vars: usize,
    universal: &Universal<'_>,
    outlives: &[Outlives],
) -> FxHashSet<RegionVid> {
    let mut outlived_by: IndexVec<RegionVid, Vec<RegionVid>> =
        IndexVec::from_elem_n(Vec::new(), num_region_vars);
    for constraint in outlives {
        outlived_by[constraint.sub].push(constraint.sup);
    }
    let mut stack: Vec<RegionVid> = universal.universal_regions_iter().collect();
    let mut outlives_free_region: FxHashSet<RegionVid> = stack.iter().copied().collect();
    while let Some(sub_region) = stack.pop() {
        stack.extend(
            outlived_by[sub_region].iter().copied().filter(|&r| outlives_free_region.insert(r)),
        );
    }
    outlives_free_region
}
