use super::{assert_same_facts, assert_same_facts_and_twins};

#[test]
fn adts_a_field_of_a_generic_struct() {
    assert_same_facts_and_twins(
        r"
        struct W<T> {
            t: T,
            n: u32,
        }
        fn f<T>(w: W<T>) -> T {
            w.t
        }
        fn main() {
            let mut m: u32 = 0;
            f(W { t: &mut m, n: 1 });
        }
        fn f_twin(w: W<&mut u32>) -> &mut u32 {
            w.t
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn adts_a_mutable_reference_to_a_field_of_a_generic_struct() {
    assert_same_facts_and_twins(
        r"
        struct W<T> {
            t: T,
        }
        fn f<T>(w: &mut W<T>, t: T) {
            let r: &mut T = &mut w.t;
            *r = t;
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            let mut w: W<&u32> = W { t: &m };
            f(&mut w, &n);
        }
        fn f_twin<'a>(w: &mut W<&'a u32>, t: &'a u32) {
            let r: &mut &'a u32 = &mut w.t;
            *r = t;
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn adts_a_generic_tuple_struct() {
    assert_same_facts_and_twins(
        r"
        struct P<T, U>(T, U);
        fn f<T, U>(p: P<T, U>) -> P<U, T> {
            P(p.1, p.0)
        }
        fn main() {
            let m: u32 = 0;
            let mut n: u32 = 0;
            f(P(&m, &mut n));
        }
        fn f_twin<'a, 'b>(p: P<&'a u32, &'b mut u32>) -> P<&'b mut u32, &'a u32> {
            P(p.1, p.0)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn adts_a_match_on_a_generic_enum() {
    assert_same_facts_and_twins(
        r"
        enum E<T> {
            A(T),
            B(T, T),
            C,
        }
        fn f<T>(e: E<T>) -> Option<T> {
            match e {
                E::A(a) => Some(a),
                E::B(_, b) => Some(b),
                E::C => None,
            }
        }
        fn main() {
            let m: u32 = 0;
            f(E::A(&m));
        }
        fn f_twin(e: E<&u32>) -> Option<&u32> {
            match e {
                E::A(a) => Some(a),
                E::B(_, b) => Some(b),
                E::C => None,
            }
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn adts_a_match_by_reference_on_a_generic_enum() {
    assert_same_facts_and_twins(
        r"
        enum E<T> {
            A(T),
            B,
        }
        fn f<T>(e: &E<T>) -> Option<&T> {
            match e {
                E::A(a) => Some(a),
                E::B => None,
            }
        }
        fn main() {
            let m: u32 = 0;
            let e: E<&u32> = E::A(&m);
            f(&e);
        }
        fn f_twin<'a, 'b>(e: &'a E<&'b u32>) -> Option<&'a &'b u32> {
            match e {
                E::A(a) => Some(a),
                E::B => None,
            }
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn adts_a_struct_with_a_lifetime_and_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        struct R<'a, T> {
            r: &'a T,
        }
        fn f<'a, T>(r: R<'a, T>) -> &'a T {
            r.r
        }
        fn main() {
            let m: u32 = 0;
            let x: &u32 = &m;
            f(R { r: &x });
        }
        fn f_twin<'a, 'b>(r: R<'a, &'b u32>) -> &'a &'b u32 {
            r.r
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn adts_a_method_of_a_generic_struct_taking_self_by_value() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        impl<T> W<T> {
            fn into_inner(self) -> T {
                self.0
            }
        }
        fn main() {
            let mut m: u32 = 0;
            W(&mut m).into_inner();
        }
        fn into_inner_twin(this: W<&mut u32>) -> &mut u32 {
            this.0
        }
        ",
        &[("W::<T>::into_inner", "into_inner_twin")],
    );
}

#[test]
fn adts_a_method_of_a_generic_struct_taking_self_by_mutable_reference() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        impl<T> W<T> {
            fn replace(&mut self, t: T) -> T {
                std::mem::replace(&mut self.0, t)
            }
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            W(&m).replace(&n);
        }
        fn replace_twin<'a>(this: &mut W<&'a u32>, t: &'a u32) -> &'a u32 {
            std::mem::replace(&mut this.0, t)
        }
        ",
        &[("W::<T>::replace", "replace_twin")],
    );
}

#[test]
fn adts_a_generic_method_of_a_generic_struct() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        impl<T> W<T> {
            fn pair<U>(self, u: U) -> (T, U) {
                (self.0, u)
            }
        }
        fn main() {
            let m: u32 = 0;
            let mut n: u32 = 0;
            W(&m).pair(&mut n);
        }
        fn pair_twin<'a, 'b>(this: W<&'a u32>, u: &'b mut u32) -> (&'a u32, &'b mut u32) {
            (this.0, u)
        }
        ",
        &[("W::<T>::pair", "pair_twin")],
    );
}

#[test]
fn adts_a_nested_generic_struct() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        fn f<T>(w: W<W<T>>) -> T {
            (w.0).0
        }
        fn main() {
            let m: u32 = 0;
            f(W(W(&m)));
        }
        fn f_twin(w: W<W<&u32>>) -> &u32 {
            (w.0).0
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn adts_a_drop_impl_of_a_generic_struct() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        impl<T> Drop for W<T> {
            fn drop(&mut self) {}
        }
        fn f<T>(x: T) {
            let w: W<T> = W(x);
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) {
            let w: W<&'a u32> = W(x);
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn adts_a_union_field_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        union U<T: Copy> {
            t: T,
            n: u64,
        }
        fn f<T: Copy>(x: T) -> T {
            let u: U<T> = U { t: x };
            unsafe { u.t }
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let u: U<&'a u32> = U { t: x };
            unsafe { u.t }
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_let_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> T {
            let y: T = x;
            y
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin<'a>(x: &'a mut u32) -> &'a mut u32 {
            let y: &'a mut u32 = x;
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_let_of_a_reference_to_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) {
            let y: &T = &x;
            let z: &&T = &y;
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) {
            let y: &&'a u32 = &x;
            let z: &&&'a u32 = &y;
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_let_with_a_named_lifetime_and_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<'a, T>(x: &'a T) -> &'a T {
            let y: &'a T = x;
            y
        }
        fn main() {
            let m: u32 = 0;
            let r: &u32 = &m;
            f(&r);
        }
        fn f_twin<'a, 'b>(x: &'a &'b u32) -> &'a &'b u32 {
            let y: &'a &'b u32 = x;
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_let_with_an_inferred_part() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> Vec<T> {
            let v: Vec<_> = vec![x];
            v
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> Vec<&u32> {
            let v: Vec<_> = vec![x];
            v
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_let_with_an_inferred_lifetime() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) {
            let y: (T, &'_ u32) = (x, &0);
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) {
            let y: (&'a u32, &'_ u32) = (x, &0);
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_let_of_a_static_reference_next_to_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> (T, &'static u32) {
            let y: (T, &'static u32) = (x, &0);
            y
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> (&'a u32, &'static u32) {
            let y: (&'a u32, &'static u32) = (x, &0);
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_tuple_pattern_with_a_type() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T, y: T) -> T {
            let (a, b): (T, T) = (x, y);
            b
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(&m, &n);
        }
        fn f_twin<'a>(x: &'a u32, y: &'a u32) -> &'a u32 {
            let (a, b): (&'a u32, &'a u32) = (x, y);
            b
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_struct_pattern_with_a_type() {
    assert_same_facts_and_twins(
        r"
        struct W<T> {
            t: T,
            n: u32,
        }
        fn f<T>(w: W<T>) -> T {
            let W { t, n }: W<T> = w;
            t
        }
        fn main() {
            let m: u32 = 0;
            f(W { t: &m, n: 1 });
        }
        fn f_twin<'a>(w: W<&'a u32>) -> &'a u32 {
            let W { t, n }: W<&'a u32> = w;
            t
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_type_ascription_in_a_let_else() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: Option<T>) -> Option<T> {
            let Some(y): Option<T> = x else {
                return None;
            };
            Some(y)
        }
        fn main() {
            let m: u32 = 0;
            f(Some(&m));
        }
        fn f_twin<'a>(x: Option<&'a u32>) -> Option<&'a u32> {
            let Some(y): Option<&'a u32> = x else {
                return None;
            };
            Some(y)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_closure_parameter_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> T {
            let c = |a: T| a;
            c(x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let c = |a: &'a u32| a;
            c(x)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_closure_return_type_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> T {
            let c = || -> T { x };
            c()
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let c = || -> &'a u32 { x };
            c()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_closure_parameter_of_a_reference_to_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> T {
            let c = |a: &T| *a;
            c(&x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let c = |a: &&'a u32| *a;
            c(&x)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_closure_parameter_with_an_inferred_part() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> Vec<T> {
            let c = |a: Vec<_>| a;
            c(vec![x])
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> Vec<&u32> {
            let c = |a: Vec<_>| a;
            c(vec![x])
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_turbofish_on_a_generic_function() {
    assert_same_facts_and_twins(
        r"
        fn g<U>(u: U) -> U {
            u
        }
        fn f<T>(x: T) -> T {
            g::<T>(x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            g::<&'a u32>(x)
        }
        fn g_twin(u: &u32) -> &u32 {
            u
        }
        ",
        &[("f", "f_twin"), ("g", "g_twin")],
    );
}

#[test]
fn annotations_a_turbofish_on_a_generic_method() {
    assert_same_facts_and_twins(
        r"
        struct S;
        impl S {
            fn g<U>(&self, u: U) -> U {
                u
            }
        }
        fn f<T>(x: T) -> T {
            S.g::<T>(x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            S.g::<&'a u32>(x)
        }
        fn g_twin<'a>(this: &S, u: &'a u32) -> &'a u32 {
            u
        }
        ",
        &[("f", "f_twin"), ("S::g", "g_twin")],
    );
}

#[test]
fn annotations_a_turbofish_on_a_generic_type() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> Vec<T> {
            let mut v = Vec::<T>::new();
            v.push(x);
            v
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> Vec<&'a u32> {
            let mut v = Vec::<&'a u32>::new();
            v.push(x);
            v
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_qualified_path_to_a_trait_method() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            fn get(self) -> u32;
        }
        impl Get for &u32 {
            fn get(self) -> u32 {
                *self
            }
        }
        fn f<T: Get>(x: T) -> u32 {
            <T as Get>::get(x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> u32 {
            <&'a u32 as Get>::get(x)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_struct_expression_with_a_type_argument() {
    assert_same_facts_and_twins(
        r"
        struct W<T> {
            t: T,
        }
        fn f<T>(x: T) -> W<T> {
            W::<T> { t: x }
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> W<&'a u32> {
            W::<&'a u32> { t: x }
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_an_enum_variant_with_a_type_argument() {
    assert_same_facts_and_twins(
        r"
        enum E<T> {
            A(T),
            B,
        }
        fn f<T>(x: T) -> E<T> {
            E::<T>::A(x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> E<&'a u32> {
            E::<&'a u32>::A(x)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_tuple_struct_constructor_with_a_type_argument() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        fn f<T>(x: T) -> W<T> {
            let c = W::<T>;
            c(x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> W<&'a u32> {
            let c = W::<&'a u32>;
            c(x)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_an_associated_constant_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        trait C {
            const N: u32;
        }
        impl C for &u32 {
            const N: u32 = 1;
        }
        fn f<T: C>(x: T) -> (T, u32) {
            (x, T::N)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> (&'a u32, u32) {
            (x, <&'a u32>::N)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_an_associated_function_through_the_type_parameter() {
    assert_same_facts_and_twins(
        r"
        trait Make {
            fn make() -> Self;
        }
        impl Make for Option<&u32> {
            fn make() -> Self {
                None
            }
        }
        fn f<T: Make>() -> T {
            T::make()
        }
        fn main() {
            let v: Option<&u32> = f();
        }
        fn f_twin<'a>() -> Option<&'a u32> {
            <Option<&'a u32>>::make()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_let_of_an_associated_type_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            type Out;
            fn get(self) -> Self::Out;
        }
        impl<'a> Get for &'a mut u32 {
            type Out = &'a u32;
            fn get(self) -> Self::Out {
                self
            }
        }
        fn f<T: Get>(x: T) {
            let y: <T as Get>::Out = x.get();
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin<'a>(x: &'a mut u32) {
            let y: <&'a mut u32 as Get>::Out = x.get();
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_cast_to_a_type_parameter_pointer() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: &T) -> *const T {
            x as *const T
        }
        fn main() {
            let m: u32 = 0;
            let r: &u32 = &m;
            f(&r);
        }
        fn f_twin<'a>(x: &&'a u32) -> *const &'a u32 {
            x as *const &'a u32
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_function_pointer_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn id<U>(u: U) -> U {
            u
        }
        fn f<T>(x: T) -> T {
            let g: fn(T) -> T = id::<T>;
            g(x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let g: fn(&'a u32) -> &'a u32 = id::<&'a u32>;
            g(x)
        }
        fn id_twin(u: &u32) -> &u32 {
            u
        }
        ",
        &[("f", "f_twin"), ("id", "id_twin")],
    );
}

#[test]
fn annotations_a_type_alias_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        type Pair<T> = (T, T);
        fn f<T: Copy>(x: T) -> Pair<T> {
            let p: Pair<T> = (x, x);
            p
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> Pair<&'a u32> {
            let p: Pair<&'a u32> = (x, x);
            p
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn annotations_a_self_type_in_an_impl_of_a_generic_type() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        impl<T> W<T> {
            fn new(t: T) -> Self {
                let w: Self = Self(t);
                w
            }
        }
        fn main() {
            let m: u32 = 0;
            W::new(&m);
        }
        fn new_twin(t: &u32) -> W<&u32> {
            let w: W<&u32> = W(t);
            w
        }
        ",
        &[("W::<T>::new", "new_twin")],
    );
}

#[test]
fn closures_a_closure_capturing_a_type_parameter_by_reference() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> T {
            let c = || {
                let r: &T = &x;
            };
            c();
            x
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let c = || {
                let r: &&'a u32 = &x;
            };
            c();
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn closures_a_closure_capturing_a_type_parameter_by_mutable_reference() {
    assert_same_facts(
        r"
        fn f<T>(mut x: T, y: T) -> T {
            let mut c = || x = y;
            c();
            x
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(&m, &n);
        }
        ",
    );
}

#[test]
fn closures_a_closure_capturing_a_type_parameter_by_value() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> T {
            let c = move || x;
            c()
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin(x: &mut u32) -> &mut u32 {
            let c = move || x;
            c()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn closures_a_closure_writing_through_a_captured_type_parameter() {
    assert_same_facts_and_twins(
        r"
        trait Set {
            fn set(&mut self, v: u32);
        }
        impl Set for &mut u32 {
            fn set(&mut self, v: u32) {
                **self = v;
            }
        }
        fn f<T: Set>(mut x: T) {
            let mut c = |v: u32| x.set(v);
            c(1);
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin(mut x: &mut u32) {
            let mut c = |v: u32| x.set(v);
            c(1);
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn closures_a_closure_inside_a_closure() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> T {
            let c = || {
                let d = || x;
                d()
            };
            c()
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let c = || {
                let d = || x;
                d()
            };
            c()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn closures_a_closure_returned_as_an_opaque_type() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> impl Fn() -> T {
            move || x
        }
        fn main() {
            let m: u32 = 0;
            let c = f(&m);
            c();
        }
        fn f_twin<'a>(x: &'a u32) -> impl Fn() -> &'a u32 {
            move || x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn closures_a_closure_passed_to_a_generic_function() {
    assert_same_facts(
        r"
        fn apply<F: Fn(u32) -> u32>(g: F, v: u32) -> u32 {
            g(v)
        }
        fn main() {
            let k: u32 = 1;
            apply(|v| v + k, 2);
        }
        ",
    );
}

#[test]
fn closures_a_closure_mutating_a_capture_passed_to_a_generic_function() {
    assert_same_facts(
        r"
        fn apply<F: FnMut(u32)>(mut g: F) {
            g(1);
            g(2);
        }
        fn main() {
            let mut m: u32 = 0;
            apply(|v| m += v);
        }
        ",
    );
}

#[test]
fn closures_a_closure_consumed_by_a_generic_function() {
    assert_same_facts(
        r"
        fn apply<F: FnOnce() -> R, R>(g: F) -> R {
            g()
        }
        fn main() {
            let mut m: u32 = 0;
            let r: &mut u32 = apply(|| &mut m);
        }
        ",
    );
}

#[test]
fn closures_a_closure_in_a_generic_function_passed_to_another_generic_function() {
    assert_same_facts_and_twins(
        r"
        fn apply<F: Fn() -> R, R>(g: F) -> R {
            g()
        }
        fn f<T: Copy>(x: T) -> T {
            apply(|| x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            apply(|| x)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn closures_a_closure_taking_a_reference_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> T {
            let c = |r: &u32| *r;
            c(&1);
            x
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> &u32 {
            let c = |r: &u32| *r;
            c(&1);
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn closures_a_closure_capturing_a_field_of_a_type_parameter_tuple() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: (T, u32)) -> T {
            let c = || x.0;
            c()
        }
        fn main() {
            let m: u32 = 0;
            f((&m, 1));
        }
        fn f_twin<'a>(x: (&'a u32, u32)) -> &'a u32 {
            let c = || x.0;
            c()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn closures_a_closure_stored_in_a_variable_with_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> (T, T) {
            let c = || (x, x);
            let p: (T, T) = c();
            p
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> (&'a u32, &'a u32) {
            let c = || (x, x);
            let p: (&'a u32, &'a u32) = c();
            p
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn closures_a_closure_calling_a_method_of_the_type_parameter() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            fn get(&self) -> u32;
        }
        impl Get for &u32 {
            fn get(&self) -> u32 {
                **self
            }
        }
        fn f<T: Get>(x: T) -> u32 {
            let c = || x.get();
            c()
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> u32 {
            let c = || x.get();
            c()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn closures_a_closure_in_a_method_of_a_generic_impl() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        impl<T: Copy> W<T> {
            fn get(&self) -> T {
                let c = || self.0;
                c()
            }
        }
        fn main() {
            let m: u32 = 0;
            W(&m).get();
        }
        fn get_twin<'a>(this: &W<&'a u32>) -> &'a u32 {
            let c = || this.0;
            c()
        }
        ",
        &[("W::<T>::get", "get_twin")],
    );
}

#[test]
fn closures_a_closure_with_region_requirements_returning_an_associated_type_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        trait Access<'de> {
            type Error;
            fn custom() -> Self::Error;
        }
        struct Reader<'a, 'b>(&'a u32, &'b u32);
        impl<'de, 'a, 'b> Access<'de> for Reader<'a, 'b> {
            type Error = String;
            fn custom() -> String {
                String::new()
            }
        }
        fn f<'de, 'a: 'de, V: Access<'de>>(r: &'a u32) -> (V::Error, &'de u32) {
            let c = || -> (V::Error, &'de u32) { (V::custom(), r) };
            c()
        }
        fn main() {
            let x: u32 = 0;
            let _ = f::<Reader<'_, '_>>(&x);
        }
        fn f_twin<'de, 'a: 'de, 'x, 'y>(r: &'a u32) -> (<Reader<'x, 'y> as Access<'de>>::Error, &'de u32) {
            let c = || -> (<Reader<'x, 'y> as Access<'de>>::Error, &'de u32) {
                (<Reader<'x, 'y> as Access<'de>>::custom(), r)
            };
            c()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn const_generics_a_const_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<const N: usize>() -> usize {
            N
        }
        fn main() {
            f::<3>();
        }
        fn f_twin() -> usize {
            3
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn const_generics_an_array_of_a_type_parameter_and_a_const_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy, const N: usize>(x: [T; N]) -> T {
            x[N - 1]
        }
        fn main() {
            let m: u32 = 0;
            f([&m, &m]);
        }
        fn f_twin(x: [&u32; 2]) -> &u32 {
            x[2 - 1]
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn const_generics_a_let_of_an_array_with_a_const_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy, const N: usize>(x: T) -> [T; N] {
            let a: [T; N] = [x; N];
            a
        }
        fn main() {
            let m: u32 = 0;
            let a: [&u32; 4] = f(&m);
        }
        fn f_twin(x: &u32) -> [&u32; 4] {
            let a: [&u32; 4] = [x; 4];
            a
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn const_generics_a_generic_struct_with_a_const_parameter() {
    assert_same_facts_and_twins(
        r"
        struct A<T, const N: usize>([T; N]);
        impl<T: Copy, const N: usize> A<T, N> {
            fn first(&self) -> T {
                self.0[0]
            }
        }
        fn main() {
            let m: u32 = 0;
            A([&m; 3]).first();
        }
        fn first_twin<'a>(this: &A<&'a u32, 3>) -> &'a u32 {
            this.0[0]
        }
        ",
        &[("A::<T, N>::first", "first_twin")],
    );
}

#[test]
fn const_generics_an_inline_const_with_a_const_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T, const N: usize>(x: T) -> (T, usize) {
            (x, const { N * 2 })
        }
        fn main() {
            let m: u32 = 0;
            f::<_, 5>(&m);
        }
        fn f_twin(x: &u32) -> (&u32, usize) {
            (x, const { 5 * 2 })
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn const_generics_a_const_parameter_passed_on() {
    assert_same_facts_and_twins(
        r"
        fn g<T, const N: usize>(x: T) -> T {
            x
        }
        fn f<T, const N: usize>(x: T) -> T {
            g::<T, N>(x)
        }
        fn main() {
            let m: u32 = 0;
            f::<_, 7>(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            g::<&'a u32, 7>(x)
        }
        fn g_twin(x: &u32) -> &u32 {
            x
        }
        ",
        &[("f", "f_twin"), ("g", "g_twin")],
    );
}

#[test]
fn control_flow_a_branch_choosing_between_two_values() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T, y: T, c: bool) -> T {
            let z: T = if c { x } else { y };
            z
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(&m, &n, true);
        }
        fn f_twin<'a>(x: &'a u32, y: &'a u32, c: bool) -> &'a u32 {
            let z: &'a u32 = if c { x } else { y };
            z
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn control_flow_a_loop_moving_a_value() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T, n: u32) -> T {
            let mut y: T = x;
            let mut i: u32 = 0;
            while i < n {
                y = x;
                i += 1;
            }
            y
        }
        fn main() {
            let m: u32 = 0;
            f(&m, 3);
        }
        fn f_twin<'a>(x: &'a u32, n: u32) -> &'a u32 {
            let mut y: &'a u32 = x;
            let mut i: u32 = 0;
            while i < n {
                y = x;
                i += 1;
            }
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn control_flow_a_loop_with_a_break_value() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> T {
            let y: T = loop {
                break x;
            };
            y
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let y: &'a u32 = loop {
                break x;
            };
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn control_flow_an_early_return() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T, y: T, c: bool) -> T {
            if c {
                return x;
            }
            y
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(&m, &n, false);
        }
        fn f_twin<'a>(x: &'a u32, y: &'a u32, c: bool) -> &'a u32 {
            if c {
                return x;
            }
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn control_flow_a_panic_in_a_branch() {
    assert_same_facts_and_twins(
        r#"
        fn f<T>(x: Option<T>) -> T {
            match x {
                Some(t) => t,
                None => panic!("none"),
            }
        }
        fn main() {
            let m: u32 = 0;
            f(Some(&m));
        }
        fn f_twin(x: Option<&u32>) -> &u32 {
            match x {
                Some(t) => t,
                None => panic!("none"),
            }
        }
        "#,
        &[("f", "f_twin")],
    );
}

#[test]
fn control_flow_an_if_let_chain() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: Option<T>, y: Option<T>) -> Option<T> {
            if let Some(a) = x
                && let Some(b) = y
            {
                return Some(b);
            }
            x
        }
        fn main() {
            let m: u32 = 0;
            f(Some(&m), None);
        }
        fn f_twin<'a>(x: Option<&'a u32>, y: Option<&'a u32>) -> Option<&'a u32> {
            if let Some(a) = x
                && let Some(b) = y
            {
                return Some(b);
            }
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn control_flow_a_match_guard() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: (T, u32)) -> Option<T> {
            match x {
                (t, n) if n > 0 => Some(t),
                _ => None,
            }
        }
        fn main() {
            let m: u32 = 0;
            f((&m, 1));
        }
        fn f_twin(x: (&u32, u32)) -> Option<&u32> {
            match x {
                (t, n) if n > 0 => Some(t),
                _ => None,
            }
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn control_flow_a_labeled_block() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T, c: bool) -> Option<T> {
            let r: Option<T> = 'b: {
                if c {
                    break 'b None;
                }
                Some(x)
            };
            r
        }
        fn main() {
            let m: u32 = 0;
            f(&m, true);
        }
        fn f_twin<'a>(x: &'a u32, c: bool) -> Option<&'a u32> {
            let r: Option<&'a u32> = 'b: {
                if c {
                    break 'b None;
                }
                Some(x)
            };
            r
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn control_flow_a_two_phase_borrow_of_a_vec_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(v: &mut Vec<T>) {
            v.push(v[0]);
        }
        fn main() {
            let m: u32 = 0;
            let mut v: Vec<&u32> = vec![&m];
            f(&mut v);
        }
        fn f_twin(v: &mut Vec<&u32>) {
            v.push(v[0]);
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn control_flow_a_nested_block_shadowing_a_value() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> T {
            let y: T = x;
            {
                let y: T = y;
                let z: T = y;
            }
            y
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let y: &'a u32 = x;
            {
                let y: &'a u32 = y;
                let z: &'a u32 = y;
            }
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_parameter_of_a_type_parameter_flows_into_the_local_it_is_moved_into() {
    assert_same_facts_and_twins(
        r"
        trait Set {
            fn set(self, v: u32);
        }

        impl Set for &mut u32 {
            fn set(self, v: u32) {
                *self = v
            }
        }

        fn f<T: Set>(x: T, v: u32) {
            let y: (T, u32) = (x, 0);
            y.0.set(v);
        }

        fn main() {
            let mut m: u32 = 0;
            f(&mut m, 1);
        }
        fn f_twin<'a>(x: &'a mut u32, v: u32) {
            let y: (&'a mut u32, u32) = (x, 0);
            y.0.set(v);
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_value_of_a_type_parameter_returned_by_an_impl_flows_from_the_argument() {
    assert_same_facts_and_twins(
        r"
        trait Make<'a> {
            fn make(r: &'a mut u32) -> Self;
        }

        impl<'b> Make<'b> for &'b mut u32 {
            fn make(r: &'b mut u32) -> Self {
                r
            }
        }

        fn g<'a, 'b, T: Make<'a>>(p: &'a mut u32, q: &'b mut u32) {
            let t: T = T::make(p);
        }

        fn main() {
            let mut m: u32 = 0;
            let mut n: u32 = 0;
            g::<&mut u32>(&mut m, &mut n);
        }
        fn g_twin<'a, 'b, 'r>(p: &'a mut u32, q: &'b mut u32)
        where
            'a: 'r,
        {
            let t: &'r mut u32 = <&'r mut u32 as Make<'_>>::make(p);
        }
    ",
        &[("g", "g_twin")],
    );
}

#[test]
fn flows_the_instance_of_a_non_generic_function_has_the_facts_of_the_function() {
    assert_same_facts(
        r"
        fn h(p: &mut (u32, u32), x: u32) -> u32 {
            let q: &mut u32 = &mut p.0;
            *q = x;
            p.1
        }
    ",
    );
}

#[test]
fn flows_a_closure_capturing_a_parameter_of_a_type_parameter_is_checked_with_the_instance() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> T {
            let c = || x;
            let y: T = c();
            y
        }

        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let c = || x;
            let y: &'a u32 = c();
            y
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_an_inline_const_using_a_type_parameter_is_checked_with_the_instance() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> T {
            let n: usize = const { std::mem::size_of::<T>() };
            let y: T = x;
            y
        }

        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let n: usize = const { std::mem::size_of::<&u32>() };
            let y: &'a u32 = x;
            y
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_an_associated_type_of_a_type_parameter_is_normalized_with_the_impl() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            type Out;
            fn get(self) -> Self::Out;
        }

        impl<'a> Get for &'a mut u32 {
            type Out = &'a mut u32;
            fn get(self) -> Self::Out {
                self
            }
        }

        fn f<T: Get>(x: T) {
            let y: T::Out = x.get();
        }

        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin<'a>(x: &'a mut u32) {
            let y: <&'a mut u32 as Get>::Out = x.get();
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_function_returning_an_opaque_type_is_checked_with_the_instance() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> impl Copy {
            let y: T = x;
            y
        }

        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> impl Copy {
            let y: &'a u32 = x;
            y
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_value_stored_through_an_impl_flows_into_the_container() {
    assert_same_facts_and_twins(
        r"
        trait Store<V> {
            fn store(&mut self, v: V);
        }
        impl<'a> Store<&'a u32> for Vec<&'a u32> {
            fn store(&mut self, v: &'a u32) {
                self.push(v);
            }
        }
        fn f<C: Store<V>, V>(c: &mut C, v: V, z: &u32) {
            c.store(v);
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            let mut c: Vec<&u32> = Vec::new();
            f(&mut c, &m, &n);
        }
        fn f_twin<'a, 'b: 'a>(c: &mut Vec<&'a u32>, v: &'b u32, z: &u32) {
            c.store(v);
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_reference_linked_by_a_lifetime_bound_flows_into_the_type_parameter() {
    assert_same_facts_and_twins(
        r"
        trait Link<'a> {
            fn link(&mut self, r: &'a u32);
        }
        impl<'a> Link<'a> for Vec<&'a u32> {
            fn link(&mut self, r: &'a u32) {
                self.push(r);
            }
        }
        fn f<'a, T: Link<'a>>(t: &mut T, r: &'a u32, s: &u32) {
            t.link(r);
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            let mut t: Vec<&u32> = Vec::new();
            f(&mut t, &m, &n);
        }
        fn f_twin<'a: 'x, 'x>(t: &mut Vec<&'x u32>, r: &'a u32, s: &u32) {
            t.link(r);
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_value_passed_through_a_generic_callee_flows_into_the_result() {
    assert_same_facts_and_twins(
        r"
        fn g<U>(u: U) -> U {
            u
        }
        fn f<T>(x: T) -> T {
            let y: T = g(x);
            y
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin<'a>(x: &'a mut u32) -> &'a mut u32 {
            let y: &'a mut u32 = g(x);
            y
        }
        fn g_twin(u: &mut u32) -> &mut u32 {
            u
        }
    ",
        &[("f", "f_twin"), ("g", "g_twin")],
    );
}

#[test]
fn flows_only_the_first_type_parameter_flows_into_the_first_field() {
    assert_same_facts_and_twins(
        r"
        fn f<T, U>(x: T, y: U) -> (T, U) {
            let p: (T, U) = (x, y);
            p
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(&m, &n);
        }
        fn f_twin<'a, 'b>(x: &'a u32, y: &'b u32) -> (&'a u32, &'b u32) {
            let p: (&'a u32, &'b u32) = (x, y);
            p
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_part_returned_by_an_associated_type_flows_from_the_whole() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            type Out;
            fn get(self) -> Self::Out;
        }
        impl<'a> Get for &'a (u32, u32) {
            type Out = &'a u32;
            fn get(self) -> Self::Out {
                &self.1
            }
        }
        fn f<T: Get, U>(x: T, u: U) -> (T::Out, U) {
            let y: T::Out = x.get();
            (y, u)
        }
        fn main() {
            let p: (u32, u32) = (0, 1);
            let n: u32 = 0;
            f(&p, &n);
        }
        fn f_twin<'a, 'b>(x: &'a (u32, u32), u: &'b u32) -> (<&'a (u32, u32) as Get>::Out, &'b u32) {
            let y: <&'a (u32, u32) as Get>::Out = x.get();
            (y, u)
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_value_written_through_a_mutable_reference_to_a_type_parameter_flows_into_its_target() {
    assert_same_facts_and_twins(
        r"
        trait Put<V> {
            fn put(&mut self, v: V);
        }
        impl<'a> Put<&'a u32> for Option<&'a u32> {
            fn put(&mut self, v: &'a u32) {
                *self = Some(v);
            }
        }
        fn f<T: Put<V>, V>(t: &mut T, v: V) {
            t.put(v);
        }
        fn main() {
            let m: u32 = 0;
            let mut t: Option<&u32> = None;
            f(&mut t, &m);
        }
        fn f_twin<'a, 'b: 'a>(t: &mut Option<&'a u32>, v: &'b u32) {
            t.put(v);
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_value_moved_into_a_closure_flows_into_its_result() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> T {
            let c = move || x;
            let y: T = c();
            y
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin<'a>(x: &'a mut u32) -> &'a mut u32 {
            let c = move || x;
            let y: &'a mut u32 = c();
            y
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_value_pushed_into_a_vec_of_a_type_parameter_flows_into_the_vec() {
    assert_same_facts_and_twins(
        r"
        fn f<T, U>(x: T, u: U) -> (Vec<T>, U) {
            let mut v: Vec<T> = Vec::new();
            v.push(x);
            (v, u)
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(&m, &n);
        }
        fn f_twin<'a, 'b>(x: &'a u32, u: &'b u32) -> (Vec<&'a u32>, &'b u32) {
            let mut v: Vec<&'a u32> = Vec::new();
            v.push(x);
            (v, u)
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_value_stored_by_a_default_method_flows_into_self() {
    assert_same_facts_and_twins(
        r"
        trait Store<'a> {
            fn slot(&mut self) -> &mut Option<&'a u32>;
            fn store(&mut self, r: &'a u32) {
                *self.slot() = Some(r);
            }
        }
        struct S<'a>(Option<&'a u32>);
        impl<'a> Store<'a> for S<'a> {
            fn slot(&mut self) -> &mut Option<&'a u32> {
                &mut self.0
            }
        }
        fn f<'a, T: Store<'a>>(t: &mut T, r: &'a u32, s: &u32) {
            t.store(r);
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            let mut t: S<'_> = S(None);
            f(&mut t, &m, &n);
        }
        fn f_twin<'a: 'x, 'x>(t: &mut S<'x>, r: &'a u32, s: &u32) {
            t.store(r);
        }
        fn store_twin<'l: 'x, 'x>(this: &mut S<'x>, r: &'l u32) {
            *this.slot() = Some(r);
        }
    ",
        &[("f", "f_twin"), ("Store::store", "store_twin")],
    );
}

#[test]
fn flows_a_parameter_of_a_closure_flows_into_the_local_it_is_moved_into() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> T {
            let c = |a: T| {
                let b: T = a;
                b
            };
            c(x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let c = |a: &'a u32| {
                let b: &'a u32 = a;
                b
            };
            c(x)
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_another_parameter_of_a_closure_does_not_flow_into_the_returned_local() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy, U: Copy>(x: T, y: U) -> T {
            let c = |a: T, q: U| {
                let b: T = a;
                b
            };
            c(x, y)
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(&m, &n);
        }
        fn f_twin<'a, 'b>(x: &'a u32, y: &'b u32) -> &'a u32 {
            let c = |a: &'a u32, q: &'b u32| {
                let b: &'a u32 = a;
                b
            };
            c(x, y)
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_value_made_by_an_impl_in_a_closure_flows_from_the_argument() {
    assert_same_facts_and_twins(
        r"
        trait Make<'a> {
            fn make(r: &'a mut u32) -> Self;
        }
        impl<'b> Make<'b> for &'b mut u32 {
            fn make(r: &'b mut u32) -> Self {
                r
            }
        }
        fn g<'a, T: Make<'a>>(p: &'a mut u32, q: &mut u32) -> T {
            let c = |p: &'a mut u32, q: &mut u32| {
                let t: T = T::make(p);
                t
            };
            c(p, q)
        }
        fn main() {
            let mut m: u32 = 0;
            let mut n: u32 = 0;
            let _: &mut u32 = g(&mut m, &mut n);
        }
        fn g_twin<'a, 'r>(p: &'a mut u32, q: &mut u32) -> &'r mut u32
        where
            'a: 'r,
        {
            let c = |p: &'a mut u32, q: &mut u32| {
                let t: &'r mut u32 = <&'r mut u32 as Make<'_>>::make(p);
                t
            };
            c(p, q)
        }
    ",
        &[("g", "g_twin")],
    );
}

#[test]
fn flows_a_parameter_of_a_nested_closure_flows_into_the_local_it_is_moved_into() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> T {
            let c = |a: T| {
                let d = |e: T| {
                    let h: T = e;
                    h
                };
                d(a)
            };
            c(x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let c = |a: &'a u32| {
                let d = |e: &'a u32| {
                    let h: &'a u32 = e;
                    h
                };
                d(a)
            };
            c(x)
        }
    ",
        &[("f", "f_twin")],
    );
}

#[test]
fn flows_a_parameter_of_a_closure_in_a_method_of_a_generic_impl_flows_into_the_local_it_is_moved_into()
 {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        impl<T: Copy> W<T> {
            fn get(&self) -> T {
                let c = |a: T| {
                    let b: T = a;
                    b
                };
                c(self.0)
            }
        }
        fn main() {
            let m: u32 = 0;
            W(&m).get();
        }
        fn get_twin<'a>(this: &W<&'a u32>) -> &'a u32 {
            let c = |a: &'a u32| {
                let b: &'a u32 = a;
                b
            };
            c(this.0)
        }
    ",
        &[("W::<T>::get", "get_twin")],
    );
}

#[test]
fn lifetimes_a_late_bound_lifetime_next_to_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<'a, T>(x: &'a T, y: T) -> (&'a T, T) {
            (x, y)
        }
        fn main() {
            let m: u32 = 0;
            let r: &u32 = &m;
            f(&r, &m);
        }
        fn f_twin<'a, 'b>(x: &'a &'b u32, y: &'b u32) -> (&'a &'b u32, &'b u32) {
            (x, y)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn lifetimes_an_early_bound_lifetime_in_a_bound() {
    assert_same_facts_and_twins(
        r"
        fn f<'a, T: Into<&'a u32>>(x: T) -> &'a u32 {
            x.into()
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a, 'r: 'a>(x: &'r u32) -> &'a u32 {
            x.into()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn lifetimes_two_lifetimes_with_an_outlives_relation() {
    assert_same_facts_and_twins(
        r"
        fn f<'a: 'b, 'b, T: 'a>(x: &'a T) -> &'b T {
            x
        }
        fn main() {
            let m: u32 = 0;
            let r: &u32 = &m;
            f(&r);
        }
        fn f_twin<'a: 'b, 'b, 'c>(x: &'a &'c u32) -> &'b &'c u32 {
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn lifetimes_a_reference_to_a_reference_type_argument() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: &T) -> &T {
            let y: &T = x;
            y
        }
        fn main() {
            let m: u32 = 0;
            let r: &&u32 = &&m;
            f(r);
        }
        fn f_twin<'a, 'b>(x: &'a &'b u32) -> &'a &'b u32 {
            let y: &'a &'b u32 = x;
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn lifetimes_a_static_type_argument() {
    assert_same_facts_and_twins(
        r#"
        fn f<T>(x: T) -> T {
            x
        }
        fn main() {
            f("static");
        }
        fn f_twin(x: &str) -> &str {
            x
        }
        "#,
        &[("f", "f_twin")],
    );
}

#[test]
fn lifetimes_a_struct_type_argument_with_a_lifetime() {
    assert_same_facts_and_twins(
        r"
        struct R<'a>(&'a mut u32);
        fn f<T>(x: T) -> T {
            let y: T = x;
            y
        }
        fn main() {
            let mut m: u32 = 0;
            f(R(&mut m));
        }
        fn f_twin<'a>(x: R<'a>) -> R<'a> {
            let y: R<'a> = x;
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn lifetimes_a_type_argument_with_two_lifetimes() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> T {
            x
        }
        fn main() {
            let m: u32 = 0;
            let mut n: u32 = 0;
            f((&m, &mut n));
        }
        fn f_twin<'a, 'b>(x: (&'a u32, &'b mut u32)) -> (&'a u32, &'b mut u32) {
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn lifetimes_a_higher_ranked_function_pointer_type_argument() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> T {
            x
        }
        fn id(r: &u32) -> &u32 {
            r
        }
        fn main() {
            let g: for<'a> fn(&'a u32) -> &'a u32 = id;
            f(g);
        }
        fn f_twin(x: for<'a> fn(&'a u32) -> &'a u32) -> for<'a> fn(&'a u32) -> &'a u32 {
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn lifetimes_a_reborrow_of_a_type_argument() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: &mut T) -> &mut T {
            let y: &mut T = &mut *x;
            y
        }
        fn main() {
            let mut m: u32 = 0;
            let mut r: &mut u32 = &mut m;
            f(&mut r);
        }
        fn f_twin<'a, 'b>(x: &'a mut &'b mut u32) -> &'a mut &'b mut u32 {
            let y: &'a mut &'b mut u32 = &mut *x;
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn lifetimes_a_lifetime_only_function() {
    assert_same_facts_and_twins(
        r"
        fn f<'a>(x: &'a u32) -> &'a u32 {
            x
        }
        fn g<T>(x: T) -> T {
            x
        }
        fn main() {
            let m: u32 = 0;
            g(f(&m));
        }
        fn g_twin(x: &u32) -> &u32 {
            x
        }
        ",
        &[("g", "g_twin")],
    );
}

#[test]
fn nested_calls_a_generic_function_calling_a_generic_function() {
    assert_same_facts_and_twins(
        r"
        fn g<U>(u: U) -> U {
            u
        }
        fn f<T>(x: T) -> T {
            g(x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> &u32 {
            g(x)
        }
        fn g_twin(u: &u32) -> &u32 {
            u
        }
        ",
        &[("f", "f_twin"), ("g", "g_twin")],
    );
}

#[test]
fn nested_calls_a_chain_of_three_generic_functions() {
    assert_same_facts_and_twins(
        r"
        fn h<V>(v: V) -> V {
            v
        }
        fn g<U>(u: U) -> U {
            h(u)
        }
        fn f<T>(x: T) -> T {
            g(x)
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin(x: &mut u32) -> &mut u32 {
            g(x)
        }
        fn g_twin(u: &mut u32) -> &mut u32 {
            h(u)
        }
        fn h_twin(v: &mut u32) -> &mut u32 {
            v
        }
        ",
        &[("f", "f_twin"), ("g", "g_twin"), ("h", "h_twin")],
    );
}

#[test]
fn nested_calls_a_generic_function_calling_another_with_a_wrapped_argument() {
    assert_same_facts_and_twins(
        r"
        fn g<U>(u: U) -> U {
            u
        }
        fn f<T>(x: T) -> Option<T> {
            g(Some(x))
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> Option<&u32> {
            g(Some(x))
        }
        fn g_twin(u: Option<&u32>) -> Option<&u32> {
            u
        }
        ",
        &[("f", "f_twin"), ("g", "g_twin")],
    );
}

#[test]
fn nested_calls_a_generic_function_instantiated_twice() {
    assert_same_facts(
        r"
        fn f<T>(x: T) -> T {
            x
        }
        fn main() {
            let m: u32 = 0;
            let mut n: u32 = 0;
            f(&m);
            f(&mut n);
            f(1u8);
        }
        ",
    );
}

#[test]
fn nested_calls_a_recursive_generic_function() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T, n: u32) -> T {
            if n == 0 { x } else { f(x, n - 1) }
        }
        fn main() {
            let m: u32 = 0;
            f(&m, 3);
        }
        fn f_twin<'a>(x: &'a u32, n: u32) -> &'a u32 {
            if n == 0 { x } else { f(x, n - 1) }
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn nested_calls_mutually_recursive_generic_functions() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T, n: u32) -> T {
            if n == 0 { x } else { g(x, n - 1) }
        }
        fn g<T: Copy>(x: T, n: u32) -> T {
            if n == 0 { x } else { f(x, n - 1) }
        }
        fn main() {
            let m: u32 = 0;
            f(&m, 3);
        }
        fn f_twin<'a>(x: &'a u32, n: u32) -> &'a u32 {
            if n == 0 { x } else { g(x, n - 1) }
        }
        fn g_twin<'a>(x: &'a u32, n: u32) -> &'a u32 {
            if n == 0 { x } else { f(x, n - 1) }
        }
        ",
        &[("f", "f_twin"), ("g", "g_twin")],
    );
}

#[test]
fn nested_calls_a_generic_function_calling_a_trait_method_of_its_parameter() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            fn get<U>(&self, u: U) -> U;
        }
        struct S;
        impl Get for S {
            fn get<U>(&self, u: U) -> U {
                u
            }
        }
        fn f<T: Get, V>(t: T, v: V) -> V {
            t.get(v)
        }
        fn main() {
            let m: u32 = 0;
            f(S, &m);
        }
        fn f_twin(t: S, v: &u32) -> &u32 {
            t.get(v)
        }
        fn get_twin<'a>(this: &S, u: &'a u32) -> &'a u32 {
            u
        }
        ",
        &[("f", "f_twin"), ("<S as Get>::get", "get_twin")],
    );
}

#[test]
fn nested_calls_a_generic_method_calling_a_generic_function() {
    assert_same_facts_and_twins(
        r"
        fn g<U>(u: U) -> U {
            u
        }
        struct W<T>(T);
        impl<T> W<T> {
            fn get(self) -> T {
                g(self.0)
            }
        }
        fn main() {
            let m: u32 = 0;
            W(&m).get();
        }
        fn get_twin(this: W<&u32>) -> &u32 {
            g(this.0)
        }
        fn g_twin(u: &u32) -> &u32 {
            u
        }
        ",
        &[("W::<T>::get", "get_twin"), ("g", "g_twin")],
    );
}

#[test]
fn nested_calls_a_non_generic_function_called_from_an_instance() {
    assert_same_facts_and_twins(
        r"
        fn h(r: &u32) -> &u32 {
            r
        }
        fn f<T: Copy>(x: T, r: &u32) -> T {
            h(r);
            x
        }
        fn main() {
            let m: u32 = 0;
            f(&m, &m);
        }
        fn f_twin<'a>(x: &'a u32, r: &u32) -> &'a u32 {
            h(r);
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn nested_calls_a_generic_function_called_from_a_closure_in_a_non_generic_function() {
    assert_same_facts_and_twins(
        r"
        fn g<U>(u: U) -> U {
            u
        }
        fn main() {
            let m: u32 = 0;
            let c = || g(&m);
            c();
        }
        fn g_twin(u: &u32) -> &u32 {
            u
        }
        ",
        &[("g", "g_twin")],
    );
}

#[test]
fn nested_calls_a_generic_function_called_from_a_closure_in_a_generic_function() {
    assert_same_facts_and_twins(
        r"
        fn g<U>(u: U) -> U {
            u
        }
        fn f<T>(x: T) -> T {
            let c = || g(x);
            c()
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> &u32 {
            let c = move || g(x);
            c()
        }
        fn g_twin(u: &u32) -> &u32 {
            u
        }
        ",
        &[("f", "f_twin"), ("g", "g_twin")],
    );
}

#[test]
fn nested_calls_a_generic_function_called_from_a_nested_closure_in_a_generic_function() {
    assert_same_facts_and_twins(
        r"
        fn g<U>(u: U) -> U {
            u
        }
        fn f<T: Copy>(x: T) -> T {
            let c = || {
                let d = || g(x);
                d()
            };
            c()
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let c = || {
                let d = || g(x);
                d()
            };
            c()
        }
        fn g_twin(u: &u32) -> &u32 {
            u
        }
        ",
        &[("f", "f_twin"), ("g", "g_twin")],
    );
}

#[test]
fn nested_calls_a_generic_function_called_from_a_closure_with_a_tuple_of_the_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn g<U>(u: U) -> U {
            u
        }
        fn f<T>(x: T) -> (T, u32) {
            let c = move || g((x, 0));
            c()
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin(x: &mut u32) -> (&mut u32, u32) {
            let c = move || g((x, 0));
            c()
        }
        fn g_twin(u: (&mut u32, u32)) -> (&mut u32, u32) {
            u
        }
        ",
        &[("f", "f_twin"), ("g", "g_twin")],
    );
}

#[test]
fn nested_calls_a_method_of_a_generic_impl_called_from_a_closure_in_a_method_of_a_generic_impl() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        impl<T: Copy> W<T> {
            fn get(&self) -> T {
                self.0
            }
            fn get_in_closure(&self) -> T {
                let c = || self.get();
                c()
            }
        }
        fn main() {
            let m: u32 = 0;
            W(&m).get_in_closure();
        }
        fn get_twin<'a>(this: &W<&'a u32>) -> &'a u32 {
            this.0
        }
        fn get_in_closure_twin<'a>(this: &W<&'a u32>) -> &'a u32 {
            let c = || this.get();
            c()
        }
        ",
        &[("W::<T>::get", "get_twin"), ("W::<T>::get_in_closure", "get_in_closure_twin")],
    );
}

#[test]
fn nested_calls_a_trait_method_called_from_a_closure_in_a_generic_function() {
    assert_same_facts_and_twins(
        r"
        trait Set {
            fn set(self, v: u32);
        }
        impl Set for &mut u32 {
            fn set(self, v: u32) {
                *self = v;
            }
        }
        fn h<S: Set>(s: S) {
            s.set(1);
        }
        fn f<T: Set>(x: T) {
            let c = move || h(x);
            c();
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin(x: &mut u32) {
            let c = move || h(x);
            c();
        }
        fn h_twin(s: &mut u32) {
            s.set(1);
        }
        ",
        &[("f", "f_twin"), ("h", "h_twin")],
    );
}

#[test]
fn promoted_a_closure_with_a_promoted_constant_in_a_non_generic_function() {
    assert_same_facts(
        r"
        fn f() -> &'static u32 {
            let c = || &1;
            c()
        }
        ",
    );
}

#[test]
fn promoted_a_closure_formatting_a_capture_in_a_non_generic_function() {
    assert_same_facts(
        r#"
        fn f(s: &str) -> String {
            let c = || format!("{s} is not a number");
            c()
        }
        "#,
    );
}

#[test]
fn promoted_a_closure_with_a_promoted_constant_in_a_generic_function() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> (T, &'static u32) {
            let c = || &1;
            (x, c())
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> (&u32, &'static u32) {
            let c = || &1;
            (x, c())
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn promoted_a_closure_with_a_promoted_constant_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: 'static>(x: T) -> (T, &'static [T]) {
            let c = || -> &'static [T] { &[] };
            (x, c())
        }
        fn main() {
            f(0u32);
        }
        fn f_twin(x: u32) -> (u32, &'static [u32]) {
            let c = || -> &'static [u32] { &[] };
            (x, c())
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn promoted_a_closure_with_a_promoted_constant_capturing_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> (T, &'static u32) {
            let c = || {
                let r: &T = &x;
                &1
            };
            let p: &'static u32 = c();
            (x, p)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> (&'a u32, &'static u32) {
            let c = || {
                let r: &&'a u32 = &x;
                &1
            };
            let p: &'static u32 = c();
            (x, p)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn promoted_a_closure_inside_a_closure_with_a_promoted_constant() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> T {
            let c = || {
                let d = || &1;
                d();
            };
            c();
            x
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> &u32 {
            let c = || {
                let d = || &1;
                d();
            };
            c();
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn promoted_a_closure_with_a_promoted_constant_in_a_method_of_a_generic_impl() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        impl<T> W<T> {
            fn get(self) -> (T, &'static u32) {
                let c = || &1;
                (self.0, c())
            }
        }
        fn main() {
            let m: u32 = 0;
            W(&m).get();
        }
        fn get_twin(this: W<&u32>) -> (&u32, &'static u32) {
            let c = || &1;
            (this.0, c())
        }
        ",
        &[("W::<T>::get", "get_twin")],
    );
}

#[test]
fn promoted_an_inline_const_with_a_promoted_constant_in_a_non_generic_function() {
    assert_same_facts(
        r"
        fn f() -> u32 {
            const {
                let r: &'static u32 = &1;
                *r
            }
        }
        ",
    );
}

#[test]
fn promoted_an_inline_const_with_a_promoted_constant_in_a_generic_function() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> (T, u32) {
            (
                x,
                const {
                    let r: &'static u32 = &1;
                    *r
                },
            )
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> (&u32, u32) {
            (
                x,
                const {
                    let r: &'static u32 = &1;
                    *r
                },
            )
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn promoted_an_inline_const_with_a_promoted_constant_inside_a_closure() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> (T, u32) {
            let c = || const {
                let r: &'static u32 = &1;
                *r
            };
            (x, c())
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> (&u32, u32) {
            let c = || const {
                let r: &'static u32 = &1;
                *r
            };
            (x, c())
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_parameter_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) {}
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin(x: &mut u32) {}
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_return_value_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> T {
            x
        }
        fn main() {
            let m: u32 = 0;
            let r: &u32 = f(&m);
        }
        fn f_twin(x: &u32) -> &u32 {
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_two_parameters_of_one_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T, y: T) -> (T, T) {
            (y, x)
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(&m, &n);
        }
        fn f_twin<'a>(x: &'a u32, y: &'a u32) -> (&'a u32, &'a u32) {
            (y, x)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_two_type_parameters() {
    assert_same_facts_and_twins(
        r"
        fn f<T, U>(x: T, y: U) -> (U, T) {
            (y, x)
        }
        fn main() {
            let mut m: u32 = 0;
            let n: u32 = 0;
            f(&mut m, &n);
        }
        fn f_twin<'a, 'b>(x: &'a mut u32, y: &'b u32) -> (&'b u32, &'a mut u32) {
            (y, x)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_reference_to_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: &T) -> &T {
            x
        }
        fn main() {
            let m: u32 = 0;
            let r: &u32 = &m;
            f(&r);
        }
        fn f_twin<'a, 'b>(x: &'a &'b u32) -> &'a &'b u32 {
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_mutable_reference_to_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: &mut T, y: T) {
            *x = y;
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            let mut r: &u32 = &m;
            f(&mut r, &n);
        }
        fn f_twin<'a>(x: &mut &'a u32, y: &'a u32) {
            *x = y;
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_tuple_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: (T, u32)) -> T {
            x.0
        }
        fn main() {
            let m: u32 = 0;
            f((&m, 1));
        }
        fn f_twin(x: (&u32, u32)) -> &u32 {
            x.0
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_an_array_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: [T; 2]) -> T {
            x[1]
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f([&m, &n]);
        }
        fn f_twin(x: [&u32; 2]) -> &u32 {
            x[1]
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_slice_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: &[T]) -> Option<T> {
            x.first().copied()
        }
        fn main() {
            let m: u32 = 0;
            let v: [&u32; 1] = [&m];
            f(&v);
        }
        fn f_twin<'a>(x: &[&'a u32]) -> Option<&'a u32> {
            x.first().copied()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_box_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: Box<T>) -> T {
            *x
        }
        fn main() {
            let mut m: u32 = 0;
            f(Box::new(&mut m));
        }
        fn f_twin(x: Box<&mut u32>) -> &mut u32 {
            *x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_where_clause_on_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> T
        where
            T: Copy,
        {
            let y: T = x;
            x
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> &'a u32 {
            let y: &'a u32 = x;
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_an_outlives_bound_on_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<'a, T: 'a>(x: T, r: &'a u32) -> (T, &'a u32) {
            (x, r)
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(&m, &n);
        }
        fn f_twin<'a, 'b>(x: &'b u32, r: &'a u32) -> (&'b u32, &'a u32) {
            (x, r)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_static_bound_on_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: 'static>(x: T) -> T {
            x
        }
        fn main() {
            static M: u32 = 0;
            f(&M);
        }
        fn f_twin(x: &u32) -> &u32 {
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_an_argument_position_impl_trait() {
    assert_same_facts_and_twins(
        r"
        fn f(x: impl Copy) -> impl Copy {
            x
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> impl Copy {
            x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_return_position_impl_trait_capturing_a_reference() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: T) -> impl Copy {
            (x, 1)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> impl Copy {
            (x, 1)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_higher_ranked_bound() {
    assert_same_facts_and_twins(
        r"
        fn f<F>(g: F) -> u32
        where
            F: for<'a> Fn(&'a u32) -> &'a u32,
        {
            let m: u32 = 0;
            *g(&m)
        }
        fn id(x: &u32) -> &u32 {
            x
        }
        fn main() {
            f(id as for<'a> fn(&'a u32) -> &'a u32);
        }
        fn f_twin(g: for<'a> fn(&'a u32) -> &'a u32) -> u32 {
            let m: u32 = 0;
            *g(&m)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_a_type_parameter_with_a_default_in_a_struct() {
    assert_same_facts_and_twins(
        r"
        struct S<T = u32>(T);
        fn f<T>(s: S<T>) -> T {
            s.0
        }
        fn main() {
            let m: u32 = 0;
            f(S(&m));
        }
        fn f_twin(s: S<&u32>) -> &u32 {
            s.0
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn signatures_an_explicit_type_argument() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Default>() -> T {
            T::default()
        }
        fn main() {
            let v: Option<&u32> = f::<Option<&u32>>();
        }
        fn f_twin<'a>() -> Option<&'a u32> {
            <Option<&'a u32>>::default()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_an_option_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: Option<T>, y: T) -> T {
            x.unwrap_or(y)
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(Some(&m), &n);
        }
        fn f_twin<'a>(x: Option<&'a u32>, y: &'a u32) -> &'a u32 {
            x.unwrap_or(y)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_a_result_of_a_type_parameter_with_the_question_mark() {
    assert_same_facts_and_twins(
        r"
        fn f<T, E>(x: Result<T, E>) -> Result<T, E> {
            let y: T = x?;
            Ok(y)
        }
        fn main() {
            let m: u32 = 0;
            let r: Result<&u32, &str> = Ok(&m);
            f(r);
        }
        fn f_twin<'a, 'b>(x: Result<&'a u32, &'b str>) -> Result<&'a u32, &'b str> {
            let y: &'a u32 = x?;
            Ok(y)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_a_vec_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(mut v: Vec<T>, x: T) -> Option<T> {
            v.push(x);
            v.pop()
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            f(vec![&m], &n);
        }
        fn f_twin<'a>(mut v: Vec<&'a u32>, x: &'a u32) -> Option<&'a u32> {
            v.push(x);
            v.pop()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_an_iterator_chain_over_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(v: &[T]) -> Vec<(T, T)> {
            v.iter().map(|x| (*x, *x)).collect()
        }
        fn main() {
            let m: u32 = 0;
            let v: Vec<&u32> = vec![&m];
            f(&v);
        }
        fn f_twin<'a>(v: &[&'a u32]) -> Vec<(&'a u32, &'a u32)> {
            v.iter().map(|x| (*x, *x)).collect()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_a_for_loop_over_a_vec_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(v: Vec<T>) -> Option<T> {
            let mut last: Option<T> = None;
            for x in v {
                last = Some(x);
            }
            last
        }
        fn main() {
            let mut m: u32 = 0;
            f(vec![&mut m]);
        }
        fn f_twin<'a>(v: Vec<&'a mut u32>) -> Option<&'a mut u32> {
            let mut last: Option<&'a mut u32> = None;
            for x in v {
                last = Some(x);
            }
            last
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_mem_swap_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(a: &mut T, b: &mut T) {
            std::mem::swap(a, b);
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            let mut a: &u32 = &m;
            let mut b: &u32 = &n;
            f(&mut a, &mut b);
        }
        fn f_twin<'a>(a: &mut &'a u32, b: &mut &'a u32) {
            std::mem::swap(a, b);
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_a_hash_map_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        use std::collections::HashMap;
        fn f<V>(map: &mut HashMap<u32, V>, v: V) -> Option<V> {
            map.insert(0, v)
        }
        fn main() {
            let m: u32 = 0;
            let mut map: HashMap<u32, &u32> = HashMap::new();
            f(&mut map, &m);
        }
        fn f_twin<'a>(map: &mut HashMap<u32, &'a u32>, v: &'a u32) -> Option<&'a u32> {
            map.insert(0, v)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_a_ref_cell_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        use std::cell::RefCell;
        fn f<T>(c: &RefCell<T>, t: T) -> T {
            c.replace(t)
        }
        fn main() {
            let m: u32 = 0;
            let n: u32 = 0;
            let c: RefCell<&u32> = RefCell::new(&m);
            f(&c, &n);
        }
        fn f_twin<'a>(c: &RefCell<&'a u32>, t: &'a u32) -> &'a u32 {
            c.replace(t)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_a_raw_pointer_read_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Copy>(x: &T) -> T {
            unsafe { std::ptr::read(x as *const T) }
        }
        fn main() {
            let m: u32 = 0;
            let r: &u32 = &m;
            f(&r);
        }
        fn f_twin<'a>(x: &&'a u32) -> &'a u32 {
            unsafe { std::ptr::read(x as *const &'a u32) }
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_size_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        fn f<T>(x: T) -> (T, usize) {
            (x, std::mem::size_of::<T>())
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin<'a>(x: &'a u32) -> (&'a u32, usize) {
            (x, std::mem::size_of::<&'a u32>())
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn std_types_a_string_formatted_with_a_type_parameter() {
    assert_same_facts_and_twins(
        r#"
        fn f<T: std::fmt::Debug>(x: T) -> String {
            format!("{:?}", x)
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> String {
            format!("{:?}", x)
        }
        "#,
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_a_method_of_the_bound_of_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        trait Set {
            fn set(self, v: u32);
        }
        impl Set for &mut u32 {
            fn set(self, v: u32) {
                *self = v;
            }
        }
        fn f<T: Set>(x: T) {
            x.set(1);
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin(x: &mut u32) {
            x.set(1);
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_a_default_method_of_a_trait() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            fn get(&self) -> u32;
            fn twice(&self) -> u32 {
                let a: u32 = self.get();
                a + self.get()
            }
        }
        struct S<'a>(&'a u32);
        impl Get for S<'_> {
            fn get(&self) -> u32 {
                *self.0
            }
        }
        fn main() {
            let m: u32 = 0;
            S(&m).twice();
        }
        fn twice_twin(this: &S<'_>) -> u32 {
            let a: u32 = this.get();
            a + this.get()
        }
        ",
        &[("Get::twice", "twice_twin")],
    );
}

#[test]
fn traits_a_default_method_returning_self() {
    assert_same_facts_and_twins(
        r"
        trait Same: Sized {
            fn same(self) -> Self {
                let s: Self = self;
                s
            }
        }
        impl Same for &mut u32 {}
        fn main() {
            let mut m: u32 = 0;
            (&mut m).same();
        }
        fn same_twin<'a>(this: &'a mut u32) -> &'a mut u32 {
            let s: &'a mut u32 = this;
            s
        }
        ",
        &[("Same::same", "same_twin")],
    );
}

#[test]
fn traits_a_method_of_a_generic_impl() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            fn get(self) -> u32;
        }
        struct W<T>(T);
        impl<T: Copy> Get for W<T> {
            fn get(self) -> u32 {
                let t: T = self.0;
                0
            }
        }
        fn main() {
            let m: u32 = 0;
            W(&m).get();
        }
        fn get_twin<'a>(this: W<&'a u32>) -> u32 {
            let t: &'a u32 = this.0;
            0
        }
        ",
        &[("<W<T> as Get>::get", "get_twin")],
    );
}

#[test]
fn traits_a_generic_method_of_a_trait() {
    assert_same_facts_and_twins(
        r"
        trait Put {
            fn put<U>(&self, u: U) -> U;
        }
        struct S;
        impl Put for S {
            fn put<U>(&self, u: U) -> U {
                u
            }
        }
        fn main() {
            let m: u32 = 0;
            S.put(&m);
        }
        fn put_twin<'a>(this: &S, u: &'a u32) -> &'a u32 {
            u
        }
        ",
        &[("<S as Put>::put", "put_twin")],
    );
}

#[test]
fn traits_a_blanket_impl() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            fn get(&self) -> u32;
        }
        impl<T: Copy + Into<u32>> Get for T {
            fn get(&self) -> u32 {
                let t: T = *self;
                t.into()
            }
        }
        fn main() {
            let m: u8 = 0;
            m.get();
        }
        fn get_twin(this: &u8) -> u32 {
            let t: u8 = *this;
            t.into()
        }
        ",
        &[("<T as Get>::get", "get_twin")],
    );
}

#[test]
fn traits_a_supertrait_method() {
    assert_same_facts_and_twins(
        r"
        trait Base {
            fn base(&self) -> u32;
        }
        trait Derived: Base {
            fn derived(&self) -> u32;
        }
        impl Base for &u32 {
            fn base(&self) -> u32 {
                **self
            }
        }
        impl Derived for &u32 {
            fn derived(&self) -> u32 {
                self.base()
            }
        }
        fn f<T: Derived>(x: T) -> u32 {
            x.base() + x.derived()
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> u32 {
            x.base() + x.derived()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_a_trait_with_a_type_parameter() {
    assert_same_facts_and_twins(
        r"
        trait Put<U> {
            fn put(&mut self, u: U);
        }
        impl<'a> Put<&'a u32> for Vec<&'a u32> {
            fn put(&mut self, u: &'a u32) {
                self.push(u);
            }
        }
        fn f<C: Put<U>, U>(c: &mut C, u: U) {
            c.put(u);
        }
        fn main() {
            let m: u32 = 0;
            let mut v: Vec<&u32> = Vec::new();
            f(&mut v, &m);
        }
        fn f_twin<'a, 'b: 'a>(c: &mut Vec<&'a u32>, u: &'b u32) {
            c.put(u);
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_a_trait_with_a_lifetime_parameter() {
    assert_same_facts_and_twins(
        r"
        trait Make<'a> {
            fn make(r: &'a mut u32) -> Self;
        }
        impl<'b> Make<'b> for &'b mut u32 {
            fn make(r: &'b mut u32) -> Self {
                r
            }
        }
        fn f<'a, T: Make<'a>>(r: &'a mut u32) -> T {
            T::make(r)
        }
        fn main() {
            let mut m: u32 = 0;
            let r: &mut u32 = f(&mut m);
        }
        fn f_twin<'a, 'r>(r: &'a mut u32) -> &'r mut u32
        where
            'a: 'r,
        {
            <&'r mut u32 as Make<'_>>::make(r)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_an_associated_type_with_a_lifetime() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            type Out;
            fn get(self) -> Self::Out;
        }
        impl<'a> Get for &'a (u32, u32) {
            type Out = &'a u32;
            fn get(self) -> Self::Out {
                &self.1
            }
        }
        fn f<T: Get>(x: T) -> T::Out {
            let y: T::Out = x.get();
            y
        }
        fn main() {
            let p: (u32, u32) = (0, 1);
            f(&p);
        }
        fn f_twin<'a>(x: &'a (u32, u32)) -> <&'a (u32, u32) as Get>::Out {
            let y: <&'a (u32, u32) as Get>::Out = x.get();
            y
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_an_associated_type_bound_in_a_where_clause() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            type Out;
            fn get(self) -> Self::Out;
        }
        impl<'a> Get for &'a mut u32 {
            type Out = &'a mut u32;
            fn get(self) -> Self::Out {
                self
            }
        }
        fn f<'a, T>(x: T) -> &'a mut u32
        where
            T: Get<Out = &'a mut u32>,
        {
            x.get()
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin<'a, 'r: 'a>(x: &'r mut u32) -> &'a mut u32 {
            x.get()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_a_projection_of_a_projection() {
    assert_same_facts_and_twins(
        r"
        trait Get {
            type Out: Get;
            fn get(self) -> Self::Out;
        }
        impl<'a> Get for &'a mut u32 {
            type Out = &'a mut u32;
            fn get(self) -> Self::Out {
                self
            }
        }
        fn f<T: Get>(x: T) -> <T::Out as Get>::Out {
            let y: T::Out = x.get();
            y.get()
        }
        fn main() {
            let mut m: u32 = 0;
            f(&mut m);
        }
        fn f_twin<'a>(x: &'a mut u32) -> <<&'a mut u32 as Get>::Out as Get>::Out {
            let y: <&'a mut u32 as Get>::Out = x.get();
            y.get()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_an_iterator_bound() {
    assert_same_facts_and_twins(
        r"
        fn f<I: Iterator>(it: I) -> Option<I::Item> {
            let mut last: Option<I::Item> = None;
            for x in it {
                last = Some(x);
            }
            last
        }
        fn main() {
            let v: Vec<u32> = vec![1, 2];
            f(v.iter());
        }
        fn f_twin<'a>(it: std::slice::Iter<'a, u32>) -> Option<<std::slice::Iter<'a, u32> as Iterator>::Item> {
            let mut last: Option<<std::slice::Iter<'a, u32> as Iterator>::Item> = None;
            for x in it {
                last = Some(x);
            }
            last
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_an_into_iterator_bound() {
    assert_same_facts_and_twins(
        r"
        fn f<I: IntoIterator>(it: I) -> usize {
            it.into_iter().count()
        }
        fn main() {
            let v: Vec<u32> = vec![1, 2];
            f(&v);
        }
        fn f_twin(it: &Vec<u32>) -> usize {
            it.into_iter().count()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_a_clone_bound() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Clone>(x: &T) -> T {
            x.clone()
        }
        fn main() {
            let m: u32 = 0;
            let r: &u32 = &m;
            f(&r);
        }
        fn f_twin<'a>(x: &&'a u32) -> &'a u32 {
            x.clone()
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_a_default_bound() {
    assert_same_facts_and_twins(
        r"
        fn f<T: Default>(x: &mut T) -> T {
            std::mem::take(x)
        }
        fn main() {
            let mut v: Option<&u32> = None;
            f(&mut v);
        }
        fn f_twin<'a>(x: &mut Option<&'a u32>) -> Option<&'a u32> {
            std::mem::take(x)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_an_operator_through_a_bound() {
    assert_same_facts_and_twins(
        r"
        fn f<T: std::ops::Add<Output = T> + Copy>(x: T) -> T {
            x + x
        }
        fn main() {
            f(1u32);
        }
        fn f_twin(x: u32) -> u32 {
            x + x
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_a_deref_bound() {
    assert_same_facts_and_twins(
        r"
        fn f<T: std::ops::Deref<Target = u32>>(x: T) -> u32 {
            *x
        }
        fn main() {
            let m: u32 = 0;
            f(&m);
        }
        fn f_twin(x: &u32) -> u32 {
            *std::ops::Deref::deref(&x)
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_an_index_bound() {
    assert_same_facts_and_twins(
        r"
        fn f<C: std::ops::Index<usize, Output = u32>>(c: &C) -> &u32 {
            &c[0]
        }
        fn main() {
            let v: Vec<u32> = vec![1];
            f(&v);
        }
        fn f_twin(c: &Vec<u32>) -> &u32 {
            &c[0]
        }
        ",
        &[("f", "f_twin")],
    );
}

#[test]
fn traits_a_where_clause_on_a_method_of_a_generic_impl() {
    assert_same_facts_and_twins(
        r"
        struct W<T>(T);
        impl<T> W<T> {
            fn get(&self) -> T
            where
                T: Copy,
            {
                self.0
            }
        }
        fn main() {
            let m: u32 = 0;
            W(&m).get();
        }
        fn get_twin<'a>(this: &W<&'a u32>) -> &'a u32 {
            this.0
        }
        ",
        &[("W::<T>::get", "get_twin")],
    );
}

#[test]
fn opaque_types_a_closure_capturing_opaque_values_of_other_functions() {
    assert_same_facts(
        r#"
        fn mk(b: bool) -> impl Fn(&[u8]) -> Result<&[u8], &str> {
            move |i| if b { Ok(i) } else { Err("e") }
        }
        fn suffixed<F>(f: F) -> impl Fn(&[u8]) -> Result<&[u8], &str>
        where
            F: Fn(&[u8]) -> Result<&[u8], &str>,
        {
            move |i| f(i)
        }
        fn f(b: bool) -> impl FnMut(&[u8]) -> Result<&[u8], &str> {
            move |input| {
                let g = mk(b);
                let k = mk(!b);
                suffixed(move |i| g(i).or_else(|_| k(i)))(input)
            }
        }
        "#,
    );
}
