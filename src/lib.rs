#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(never_type)]

extern crate rustc_abi;
#[cfg(test)]
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
#[cfg(test)]
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_trait_selection;

mod analysis;
mod error;
mod facts;
mod instantiate;
#[cfg(test)]
mod tests;

pub use error::{Error, ErrorKind};
pub use facts::{InstanceFacts, instance_facts};
