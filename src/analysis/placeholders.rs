use rustc_index::IndexVec;
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_middle::ty::RegionVid;

use super::constraints::Outlives;
use super::graph::{ConstraintSccs, RegionDefinition, RegionTracker, SccIndex};

// Lowers the higher-ranked constraints: a component of the constraint graph that
// reaches a placeholder whose universe it cannot name must outlive `'static`.
pub(crate) fn lower(
    outlives: &mut Vec<Outlives>,
    definitions: &IndexVec<RegionVid, RegionDefinition<'_>>,
    fr_static: RegionVid,
) {
    let has_placeholders: bool = definitions
        .iter()
        .any(|definition| matches!(definition.origin, NllRegionVariableOrigin::Placeholder(_)));
    if !has_placeholders {
        return;
    }
    let sccs: ConstraintSccs = ConstraintSccs::compute(outlives, definitions, fr_static);
    let static_scc: SccIndex = sccs.scc(fr_static);
    for scc in sccs.sccs.all_sccs() {
        if scc == static_scc {
            continue;
        }
        let annotation: RegionTracker = sccs.annotations[scc];
        if annotation.unnameable_placeholder().is_none() {
            continue;
        }
        outlives.push(Outlives { sup: annotation.representative.rvid(), sub: fr_static });
    }
}
