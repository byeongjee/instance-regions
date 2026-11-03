# instance-regions

This crate computes the region constraints of a monomorphized function. They are the
constraints the borrow checker of rustc computes, but for the function with concrete type
args instead of its params.

## Usage

Compile every crate with a driver that installs the hooks of preborrowck-mir. Then ask for
the facts of an instance.

```rust
let facts = instance_regions::instance_facts(tcx, instance)?;
```

`facts.body` is the MIR of the instance with every region replaced by a region variable.
`facts.promoted` holds its promoted constants in the same numbering. `facts.outlives` lists
the constraints between the variables as pairs `(sup, sub)` meaning `sup: sub`.
