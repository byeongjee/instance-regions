use rustc_data_structures::graph::scc::{self, Sccs};
use rustc_data_structures::graph::{DirectedGraph, Successors};
use rustc_index::IndexVec;
use rustc_infer::infer::{NllRegionVariableOrigin, RegionVariableOrigin};
use rustc_middle::ty::{RegionVid, UniverseIndex};

use super::constraints::Outlives;
use super::infer::Infer;

rustc_index::newtype_index! {
    #[orderable]
    pub(crate) struct SccIndex {}
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct RegionDefinition<'tcx> {
    pub(crate) origin: NllRegionVariableOrigin<'tcx>,
    pub(crate) universe: UniverseIndex,
}

pub(crate) fn region_definitions<'tcx>(
    infer: &Infer<'tcx>,
) -> IndexVec<RegionVid, RegionDefinition<'tcx>> {
    infer
        .get_region_var_infos()
        .iter()
        .map(|info| {
            let origin: NllRegionVariableOrigin<'tcx> = match info.origin {
                RegionVariableOrigin::Nll(origin) => origin,
                _ => NllRegionVariableOrigin::Existential { name: None },
            };
            RegionDefinition { origin, universe: info.universe }
        })
        .collect()
}

// The constraint graph with an edge `sup -> sub` for each `sup: sub`, where `'static`
// outlives every region.
pub(crate) struct RegionGraph {
    successors: IndexVec<RegionVid, Vec<RegionVid>>,
    fr_static: RegionVid,
}

impl RegionGraph {
    pub(crate) fn new(outlives: &[Outlives], num_regions: usize, fr_static: RegionVid) -> Self {
        let mut successors: IndexVec<RegionVid, Vec<RegionVid>> =
            IndexVec::from_elem_n(Vec::new(), num_regions);
        for constraint in outlives {
            successors[constraint.sup].push(constraint.sub);
        }
        RegionGraph { successors, fr_static }
    }
}

enum RegionSuccessors<'a> {
    All(std::ops::Range<usize>),
    Listed(std::slice::Iter<'a, RegionVid>),
}

impl Iterator for RegionSuccessors<'_> {
    type Item = RegionVid;

    fn next(&mut self) -> Option<RegionVid> {
        match self {
            RegionSuccessors::All(range) => range.next().map(RegionVid::from_usize),
            RegionSuccessors::Listed(iter) => iter.next().copied(),
        }
    }
}

impl DirectedGraph for RegionGraph {
    type Node = RegionVid;

    fn num_nodes(&self) -> usize {
        self.successors.len()
    }
}

impl Successors for RegionGraph {
    fn successors(&self, node: RegionVid) -> impl Iterator<Item = RegionVid> {
        if node == self.fr_static {
            RegionSuccessors::All(0..self.successors.len())
        } else {
            RegionSuccessors::Listed(self.successors[node].iter())
        }
    }
}

// The representative of a strongly connected component: a universal region if
// there is one, else a placeholder, else the existential with the smallest index.
#[derive(Copy, Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub(crate) enum Representative {
    FreeRegion(RegionVid),
    Placeholder(RegionVid),
    Existential(RegionVid),
}

impl Representative {
    pub(crate) fn rvid(self) -> RegionVid {
        match self {
            Representative::FreeRegion(vid)
            | Representative::Placeholder(vid)
            | Representative::Existential(vid) => vid,
        }
    }

    fn new(r: RegionVid, definition: &RegionDefinition<'_>) -> Self {
        match definition.origin {
            NllRegionVariableOrigin::FreeRegion => Representative::FreeRegion(r),
            NllRegionVariableOrigin::Placeholder(_) => Representative::Placeholder(r),
            NllRegionVariableOrigin::Existential { .. } => Representative::Existential(r),
        }
    }
}

// The universes reachable from a strongly connected component.
#[derive(Copy, Debug, Clone)]
pub(crate) struct RegionTracker {
    // The highest universe of a reachable placeholder, with that placeholder.
    reachable_placeholders: Option<(UniverseIndex, RegionVid)>,
    max_nameable_universe: (UniverseIndex, RegionVid),
    pub(crate) representative: Representative,
}

impl RegionTracker {
    fn new(rvid: RegionVid, definition: &RegionDefinition<'_>) -> Self {
        let reachable_placeholders: Option<(UniverseIndex, RegionVid)> =
            matches!(definition.origin, NllRegionVariableOrigin::Placeholder(_))
                .then_some((definition.universe, rvid));
        Self {
            reachable_placeholders,
            max_nameable_universe: (definition.universe, rvid),
            representative: Representative::new(rvid, definition),
        }
    }

    pub(crate) fn max_nameable_universe(self) -> UniverseIndex {
        self.max_nameable_universe.0
    }

    fn placeholders_can_be_named_by(&self, from: UniverseIndex) -> bool {
        self.reachable_placeholders.is_none_or(|(universe, _)| from.can_name(universe))
    }

    pub(crate) fn can_name_all_placeholders(&self, other: Self) -> bool {
        self.max_nameable_universe().can_name(other.max_nameable_universe())
            || other.placeholders_can_be_named_by(self.max_nameable_universe.0)
    }

    pub(crate) fn unnameable_placeholder(&self) -> Option<(UniverseIndex, RegionVid)> {
        self.reachable_placeholders
            .filter(|&(universe, _)| !self.max_nameable_universe().can_name(universe))
    }

    pub(crate) fn max_placeholder_universe_reached(self) -> UniverseIndex {
        self.reachable_placeholders.map_or(UniverseIndex::ROOT, |(universe, _)| universe)
    }
}

impl scc::Annotation for RegionTracker {
    fn update_scc(&mut self, other: &Self) {
        self.representative = self.representative.min(other.representative);
        self.update_reachable(other);
    }

    fn update_reachable(&mut self, other: &Self) {
        self.max_nameable_universe = self.max_nameable_universe.min(other.max_nameable_universe);
        self.reachable_placeholders = self.reachable_placeholders.max(other.reachable_placeholders);
    }
}

struct SccAnnotations<'d, 'tcx> {
    scc_to_annotation: IndexVec<SccIndex, RegionTracker>,
    definitions: &'d IndexVec<RegionVid, RegionDefinition<'tcx>>,
}

impl scc::Annotations<RegionVid> for SccAnnotations<'_, '_> {
    type Ann = RegionTracker;
    type SccIdx = SccIndex;

    fn new(&self, element: RegionVid) -> RegionTracker {
        RegionTracker::new(element, &self.definitions[element])
    }

    fn annotate_scc(&mut self, scc: SccIndex, annotation: RegionTracker) {
        let idx: SccIndex = self.scc_to_annotation.push(annotation);
        assert!(idx == scc);
    }
}

pub(crate) struct ConstraintSccs {
    pub(crate) sccs: Sccs<RegionVid, SccIndex>,
    pub(crate) annotations: IndexVec<SccIndex, RegionTracker>,
}

impl ConstraintSccs {
    pub(crate) fn compute(
        outlives: &[Outlives],
        definitions: &IndexVec<RegionVid, RegionDefinition<'_>>,
        fr_static: RegionVid,
    ) -> Self {
        let graph: RegionGraph = RegionGraph::new(outlives, definitions.len(), fr_static);
        let mut annotations = SccAnnotations { scc_to_annotation: IndexVec::new(), definitions };
        let sccs: Sccs<RegionVid, SccIndex> = Sccs::new_with_annotation(&graph, &mut annotations);
        ConstraintSccs { sccs, annotations: annotations.scc_to_annotation }
    }

    pub(crate) fn scc(&self, r: RegionVid) -> SccIndex {
        self.sccs.scc(r)
    }
}
