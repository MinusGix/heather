//! `assuming` is an item-group telescope, not an elaborator mode. The parser
//! prepends ordinary `:= infer` parameters to each enclosed declaration, so
//! all filling and explicit-override behavior below is the existing layer-2
//! solver path.

use heather_elab::Elaborator;

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

#[test]
fn a_group_assumption_is_local_and_threads_between_declarations() {
    ok(r#"
assuming h: Nat {
    theorem from_assumption(): Nat {
        h
    }

    theorem through_call(): Nat {
        from_assumption()
    }
}

theorem constructive_caller(n: Nat): Nat {
    through_call()
}

theorem explicit_caller(n: Nat): Nat {
    @through_call(n)
}
"#);
}

#[test]
fn an_anonymous_assumption_is_hygienic_and_still_resolves_by_type() {
    ok(r#"
assuming Nat {
    fn keep(n: Nat) -> Nat {
        n
    }
}

fn use_keep(n: Nat) -> Nat {
    keep(n)
}
"#);
}

#[test]
fn nested_groups_prepend_both_solver_worlds() {
    ok(r#"
assuming outer: Nat {
    assuming inner: 0 = 0 {
        theorem nested(): Nat {
            outer
        }
    }
}

theorem caller(n: Nat, p: 0 = 0): Nat {
    nested()
}
"#);
}

#[test]
fn an_anonymous_requires_parameter_is_inferred_like_a_named_one() {
    ok(r#"
class Has<A> { value: A }

fn needs_has requires Has<Nat> (n: Nat) -> Nat {
    n
}

fn supplies_has requires h: Has<Nat> (n: Nat) -> Nat {
    needs_has(n)
}
"#);
}
