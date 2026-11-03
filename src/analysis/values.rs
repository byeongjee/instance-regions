use std::ops::Range;

use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};
use rustc_data_structures::graph;
use rustc_data_structures::graph::vec_graph::VecGraph;
use rustc_index::IndexVec;
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_middle::ty::{RegionVid, UniverseIndex};

use super::constraints::Outlives;
use super::graph::{ConstraintSccs, RegionDefinition, Representative, SccIndex};
use super::universal::Universal;

// The universal regions that each component of the constraint graph outlives.
// Liveness and placeholders are ignored, as the closure requirements and the
// opaque types of a body depend only on the universal regions.
pub(crate) struct RegionValues {
    pub(crate) sccs: ConstraintSccs,
    free_regions: IndexVec<SccIndex, FxIndexSet<RegionVid>>,
    placeholders: IndexVec<SccIndex, bool>,
    reverse: VecGraph<SccIndex>,
    scc_regions: FxIndexMap<SccIndex, Range<usize>>,
    universal_regions: Vec<RegionVid>,
}

impl RegionValues {
    // The values before propagation: each universal region is in its own component.
    pub(crate) fn new<'tcx>(
        outlives: &[Outlives],
        definitions: &IndexVec<RegionVid, RegionDefinition<'tcx>>,
        universal: &Universal<'tcx>,
    ) -> Self {
        let sccs: ConstraintSccs =
            ConstraintSccs::compute(outlives, definitions, universal.fr_static);
        let mut free_regions: IndexVec<SccIndex, FxIndexSet<RegionVid>> =
            IndexVec::from_elem_n(FxIndexSet::default(), sccs.sccs.num_sccs());
        let mut placeholders: IndexVec<SccIndex, bool> =
            IndexVec::from_elem_n(false, sccs.sccs.num_sccs());
        for (variable, definition) in definitions.iter_enumerated() {
            match definition.origin {
                NllRegionVariableOrigin::FreeRegion => {
                    free_regions[sccs.scc(variable)].insert(variable);
                }
                NllRegionVariableOrigin::Placeholder(_) => placeholders[sccs.scc(variable)] = true,
                NllRegionVariableOrigin::Existential { .. } => {}
            }
        }
        let reverse: VecGraph<SccIndex> = sccs.sccs.reverse();
        let mut paired_scc_regions: Vec<(SccIndex, RegionVid)> =
            universal.universal_regions_iter().map(|region| (sccs.scc(region), region)).collect();
        paired_scc_regions.sort();
        let universal_regions: Vec<RegionVid> =
            paired_scc_regions.iter().map(|&(_, region)| region).collect();
        let mut scc_regions: FxIndexMap<SccIndex, Range<usize>> = FxIndexMap::default();
        let mut start: usize = 0;
        for chunk in paired_scc_regions.chunk_by(|&(scc1, _), &(scc2, _)| scc1 == scc2) {
            let (scc, _) = chunk[0];
            scc_regions.insert(scc, start..start + chunk.len());
            start += chunk.len();
        }
        RegionValues { sccs, free_regions, placeholders, reverse, scc_regions, universal_regions }
    }

    // Grows every component by the values of the components it outlives.
    pub(crate) fn propagate(&mut self) {
        for scc_a in self.sccs.sccs.all_sccs() {
            let successors: Vec<SccIndex> = self.sccs.sccs.successors(scc_a).to_vec();
            for scc_b in successors {
                self.add_region(scc_a, scc_b);
            }
        }
    }

    pub(crate) fn add_region(&mut self, scc_a: SccIndex, scc_b: SccIndex) {
        let outlived: Vec<RegionVid> = self.free_regions[scc_b].iter().copied().collect();
        self.free_regions[scc_a].extend(outlived);
        self.placeholders[scc_a] |= self.placeholders[scc_b];
    }

    pub(crate) fn contains_placeholder(&self, scc: SccIndex) -> bool {
        self.placeholders[scc]
    }

    pub(crate) fn scc(&self, r: RegionVid) -> SccIndex {
        self.sccs.scc(r)
    }

    pub(crate) fn representative(&self, r: RegionVid) -> Representative {
        self.sccs.annotations[self.sccs.scc(r)].representative
    }

    pub(crate) fn max_nameable_universe(&self, scc: SccIndex) -> UniverseIndex {
        self.sccs.annotations[scc].max_nameable_universe()
    }

    pub(crate) fn max_placeholder_universe_reached(&self, scc: SccIndex) -> UniverseIndex {
        self.sccs.annotations[scc].max_placeholder_universe_reached()
    }

    pub(crate) fn can_name_all_placeholders(&self, scc_a: SccIndex, scc_b: SccIndex) -> bool {
        self.sccs.annotations[scc_a].can_name_all_placeholders(self.sccs.annotations[scc_b])
    }

    pub(crate) fn universal_regions_outlived_by(
        &self,
        scc: SccIndex,
    ) -> impl Iterator<Item = RegionVid> + '_ {
        self.free_regions[scc].iter().copied()
    }

    // The universal regions that must outlive a component.
    pub(crate) fn upper_bounds(&self, scc0: SccIndex) -> impl Iterator<Item = RegionVid> + '_ {
        let mut duplicates: FxIndexSet<RegionVid> = FxIndexSet::default();
        graph::depth_first_search(&self.reverse, scc0)
            .flat_map(move |scc1| {
                self.scc_regions
                    .get(&scc1)
                    .map_or(&[][..], |range| &self.universal_regions[range.clone()])
            })
            .copied()
            .filter(move |r| duplicates.insert(*r))
    }
}
