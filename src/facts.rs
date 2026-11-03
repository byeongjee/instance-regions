use std::mem::transmute;

use preborrowck_mir::{RecordedMir, recorded_mir};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::mir::{Body, Promoted};
use rustc_middle::ty::{GenericArgsRef, Instance, RegionVid, TyCtxt};
use rustc_utils::cache::Cache;

use crate::{Error, analysis};

// The MIR of a body of an instance with every region replaced by a region variable,
// and the constraints `sup: sub` between the region variables.
pub struct InstanceFacts<'tcx> {
    pub body: Body<'tcx>,
    pub promoted: IndexVec<Promoted, Body<'tcx>>,
    pub outlives: Vec<(RegionVid, RegionVid)>,
}

type RootFacts<'tcx> = FxHashMap<DefId, InstanceFacts<'tcx>>;
thread_local! {
    static INSTANCE_FACTS: Cache<Instance<'static>, Result<RootFacts<'static>, Error>> = Cache::default();
}

pub fn instance_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> Result<&'tcx InstanceFacts<'tcx>, Error> {
    let set: &RecordedMir<'tcx> = recorded_mir(tcx, instance.def_id())?;
    let root: DefId = set.root;
    let args: GenericArgsRef<'tcx> = instance.args.truncate_to(tcx, tcx.generics_of(root));
    let root_instance: Instance<'tcx> = Instance::new_raw(root, args);
    // SAFETY: rustc starts a fresh compiler thread for each session, so this
    // thread-local key is never compared against another session's interned types.
    let key: Instance<'static> =
        unsafe { transmute::<Instance<'tcx>, Instance<'static>>(root_instance) };
    INSTANCE_FACTS.with(|cache| {
        let facts: &Result<RootFacts<'static>, Error> = cache.get(&key, |_| {
            let result: Result<RootFacts<'tcx>, Error> = analysis::analyze(tcx, root, args, set);
            // SAFETY: only this compiler thread's current session can access the
            // cached facts; their arena references are never exposed across sessions.
            unsafe {
                transmute::<Result<RootFacts<'tcx>, Error>, Result<RootFacts<'static>, Error>>(
                    result,
                )
            }
        });
        match facts {
            Ok(facts) => {
                let facts: &InstanceFacts<'static> =
                    facts.get(&instance.def_id()).ok_or_else(|| {
                        Error::new("the instance is not a captured function or closure")
                    })?;
                // SAFETY: the cache pins the completed map and it is never mutated.
                // Its entry and arena references remain valid throughout this session.
                Ok(unsafe {
                    transmute::<&InstanceFacts<'static>, &'tcx InstanceFacts<'tcx>>(facts)
                })
            }
            Err(error) => Err(error.clone()),
        }
    })
}
