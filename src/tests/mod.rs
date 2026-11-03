use oracle::{
    Comparison, body_owner, compare_created_instance_with_twin, compare_instance_with_twin,
    compare_local_bodies,
};
use preborrowck_mir::driver;
use preborrowck_mir::test_utils::Compile;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{GenericArgs, Instance, Ty, TyCtxt};

use crate::facts::instance_facts;

mod corpus;
mod crates;
mod oracle;

// Every function-like body whose typeck root is not generic has the facts rustc computes.
fn assert_same_facts(source: &str) {
    Compile::source(source).run(check_all_bodies);
}

fn check_all_bodies(tcx: TyCtxt<'_>) {
    let comparison: Comparison = compare_local_bodies(tcx);
    assert!(comparison.checked > 0, "the source has a body to check");
    assert!(comparison.report.is_empty(), "\n{}", comparison.report);
}

// Every function-like body whose typeck root is not generic has the facts rustc computes,
// and the one instance of each generic function that the source creates has the facts
// rustc computes for its twin: the same function written with the type args in place of
// the params.
fn assert_same_facts_and_twins(source: &str, twins: &[(&str, &str)]) {
    let twins: Vec<(String, String)> =
        twins.iter().map(|&(generic, twin)| (generic.to_owned(), twin.to_owned())).collect();
    Compile::source(source).run(move |tcx| {
        check_all_bodies(tcx);
        let mut report: String = String::new();
        for (generic, twin) in &twins {
            report.push_str(&compare_created_instance_with_twin(tcx, generic, twin));
        }
        assert!(report.is_empty(), "\n{report}");
    });
}

// The instance of a generic function has the facts rustc computes for its twin: the
// same function written with the type args in place of the params.
fn assert_same_facts_as_twin(
    source: &str,
    generic: &str,
    type_args: for<'tcx> fn(TyCtxt<'tcx>) -> Vec<Ty<'tcx>>,
    twin: &str,
) {
    Compile::source(source).run(move |tcx| {
        let report: String = compare_instance_with_twin(tcx, generic, &type_args(tcx), twin);
        assert!(report.is_empty(), "\n{report}");
    });
}

#[test]
fn a_reference_returned_from_an_argument() {
    assert_same_facts(
        r"
        fn f(x: &u32) -> &u32 {
            x
        }
        ",
    );
}

#[test]
fn a_generic_reference_returned_from_an_argument() {
    assert_same_facts_as_twin(
        "fn f<T>(x: &T) -> &T { x }
         fn f_u32(x: &u32) -> &u32 { x }",
        "f",
        |tcx| vec![tcx.types.u32],
        "f_u32",
    );
}

#[test]
fn a_generic_field_borrowed_through_a_reference() {
    assert_same_facts_as_twin(
        "struct W<T>(T, u32);
         fn f<'a, T>(w: &'a mut W<T>, y: &u32) -> &'a mut T { w.1 = *y; &mut w.0 }
         fn f_ref<'a, 'b>(w: &'a mut W<&'b u32>, y: &u32) -> &'a mut &'b u32 {
             w.1 = *y;
             &mut w.0
         }",
        "f",
        |tcx| vec![Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, tcx.types.u32)],
        "f_ref",
    );
}

#[test]
fn a_generic_drop_guard_holding_a_reference() {
    assert_same_facts_as_twin(
        "struct Guard<T>(T);
         impl<T> Drop for Guard<T> { fn drop(&mut self) {} }
         fn f<'y, T>(x: T, y: &'y u32) -> &'y u32 { let _g = Guard(x); y }
         fn f_ref<'y>(x: &u32, y: &'y u32) -> &'y u32 { let _g = Guard(x); y }",
        "f",
        |tcx| vec![Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, tcx.types.u32)],
        "f_ref",
    );
}

#[test]
fn a_generic_type_param_outlives_bound_against_its_twin() {
    assert_same_facts_as_twin(
        "fn f<'a, T: 'a>(x: T, y: &'a u32) -> &'a u32 { let _x = x; y }
         fn f_ref<'a, 'b>(x: &'b u32, y: &'a u32) -> &'a u32 { let _x = x; y }",
        "f",
        |tcx| vec![Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, tcx.types.u32)],
        "f_ref",
    );
}

#[test]
fn a_generic_async_function_instance_against_its_twin() {
    assert_same_facts_as_twin(
        "async fn f<T: Copy>(x: &T) -> T { *x }
         async fn f_u32(x: &u32) -> u32 { *x }",
        "f",
        |tcx| vec![tcx.types.u32],
        "f_u32",
    );
}

#[test]
fn a_generic_opaque_return_type_without_a_bound_against_its_twin() {
    assert_same_facts_as_twin(
        "fn f<T>(x: &T) -> impl Sized { x }
         fn f_u32(x: &u32) -> impl Sized { x }",
        "f",
        |tcx| vec![tcx.types.u32],
        "f_u32",
    );
}

#[test]
fn a_generic_opaque_return_type_against_its_twin() {
    assert_same_facts_as_twin(
        "fn f<T>(x: &T) -> impl Sized + '_ { x }
         fn f_u32(x: &u32) -> impl Sized + '_ { x }",
        "f",
        |tcx| vec![tcx.types.u32],
        "f_u32",
    );
}

#[test]
fn a_reborrow_through_a_local() {
    assert_same_facts(
        r"
        fn f(x: &mut Vec<u32>) -> &mut u32 {
            let y = &mut *x;
            let z = &mut y[0];
            z
        }
        ",
    );
}

#[test]
fn a_call_with_a_region_bound() {
    assert_same_facts(
        r"
        fn g<'a, T: 'a>(x: &'a T) -> &'a T { x }
        fn f(x: &u32, y: &u32) -> u32 {
            let a = g(x);
            let b = g(y);
            *a + *b
        }
        ",
    );
}

#[test]
fn a_closure_capturing_a_reference() {
    assert_same_facts(
        r"
        fn f(x: &u32) -> u32 {
            let c = || *x + 1;
            c()
        }
        ",
    );
}

#[test]
fn a_struct_with_a_drop_impl() {
    assert_same_facts(
        r"
        struct Guard<'a>(&'a u32);
        impl<'a> Drop for Guard<'a> {
            fn drop(&mut self) {}
        }
        fn f(x: &u32) -> u32 {
            let g = Guard(x);
            let r = &g;
            *r.0
        }
        ",
    );
}

#[test]
fn an_async_function() {
    assert_same_facts(
        "async fn f<'a>(x: &'a u32, y: &u32) -> &'a u32 { let _z = *y; x }
         fn g(x: &u32) { let _ = f(x, x); }",
    );
}

#[test]
fn a_generic_async_function_instance() {
    assert_same_facts(
        "async fn f<T: Copy>(x: &T) -> T { *x }
         fn g() { let _ = f(&1u32); }",
    );
}

#[test]
fn an_async_block_capturing_a_reference() {
    assert_same_facts("fn g(x: &u32) -> impl Future<Output = u32> { async move { *x } }");
}

#[test]
fn an_async_closure() {
    assert_same_facts("fn g(x: &u32) { let c = async |y: &u32| *y + *x; let _ = c(x); }");
}

#[test]
fn a_closure_in_a_static_initializer() {
    assert_same_facts("static F: fn(&u32) -> &u32 = |x| x;");
}

#[test]
fn a_closure_in_a_constant() {
    assert_same_facts("const F: fn(&u32) -> &u32 = |x| x;\n fn g(x: &u32) -> &u32 { F(x) }");
}

// rustc skips the borrow check of injected MIR, so the analysis has no constraints for it.
#[test]
fn injected_mir_is_unavailable() {
    Compile {
        overrides: |_, providers| driver::record_mir(providers),
        ..Compile::source(
            "#![feature(custom_mir, core_intrinsics)]
             use core::intrinsics::mir::*;
             #[custom_mir(dialect = \"runtime\")]
             fn f() { mir! { { Return() } } }",
        )
    }
    .run(|tcx| {
        let def: LocalDefId = body_owner(tcx, "f");
        let instance: Instance<'_> = Instance::new_raw(
            def.to_def_id(),
            GenericArgs::identity_for_item(tcx, def.to_def_id()),
        );
        let Err(error) = instance_facts(tcx, instance) else {
            panic!("rustc skips the borrow check of injected MIR");
        };
        assert!(error.is_unavailable(), "{error}");
    });
}
