# Tests of instance-regions

The oracle is the borrow checker of rustc: a body analyzed by instance-regions must have the
transitive closure of the `subset_base` facts rustc computes for it, with the regions matched
in the order they occur. rustc checks a generic body once with its params in place, while
instance-regions analyzes a monomorphized instance, so a body whose typeck root has no type or
const params is compared directly, and an instance of a generic function is compared with its
twin, the same function written by hand with the type args in place of the params, on the
regions of its user variables and return place only, because rustc builds different MIR for a
type param and for a reference. The analysis proves every obligation about the type args
through impls, never through the where clauses of the generic function, so a twin leaves those
where clauses out and writes `'_` where the generic function takes a lifetime from one of them.
`corpus.rs` holds a small program per case (a generic function, a `main` that creates one
instance of it, and the twin), `mod.rs` holds targeted programs, and `crates.rs` compiles the 66
crates its `crates/Cargo.toml` locks from the local cargo registry. Run them with
`cargo test -p instance-regions`.
