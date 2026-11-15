//! `match` on an `IWf`-route family at a **specific** index
//! (`docs/kernel/iwf-former-design.md` §8.3): tier 1, inversion at a
//! constructor-headed index, and tier 2, abstraction of a computed one.
//!
//! The families here are `IWf`-route because a child sits at a non-variable
//! index, which route 1 has no `rec` for. The axes are
//! `docs/testing-generated-terms.md`'s: β is pinned by `refl` on **open**
//! data (axis 2) in a theorem (axis 3) and on a **literal** scrutinee
//! (axis 1); the negatives (axis 4) are what each tier does not do.

use heather_elab::{ElabError, Elaborator, IndexedRoute};

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
        Ok(()) => panic!("expected an error, but this elaborated:\n{src}"),
    }
}

/// A list whose every cell also carries an empty one: `l` at the literal
/// index `0` is what puts it on the `IWf` route.
const T: &str = r#"
inductive T<A> : (n: Nat) -> Type {
    TL                                        : T<A>(0),
    TN(n: Nat, x: A, l: T<A>(0), r: T<A>(n))  : T<A>(Succ(n)),
}
"#;

const ADD: &str = r#"
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
"#;

// ---------------------------------------------------------------------------
// Tier 1 — inversion
// ---------------------------------------------------------------------------

// `vhead`/`vtail`: at `T(Succ(n))` the `TL` arm cannot occur and is left
// out, and the `TN` arm's goal is at its own index `Succ(k)`, so `r : T(k)`
// is the tail. β is definitional on open data at an open element type.
#[test]
fn head_and_tail_at_a_successor_index_leave_out_the_empty_arm() {
    let e = elab(&format!(
        "{T}
         fn head<A>(n: Nat, t: T<A>(Succ(n))) -> A {{ match t {{ TN(k, x, l, r) => x }} }}
         fn tail<A>(n: Nat, t: T<A>(Succ(n))) -> T<A>(n) {{ match t {{ TN(k, x, l, r) => r }} }}
         theorem head_beta<A>(n: Nat, x: A, l: T<A>(0), r: T<A>(n)):
             head(n, TN(n, x, l, r)) = x {{ refl }}
         theorem tail_beta<A>(n: Nat, x: A, l: T<A>(0), r: T<A>(n)):
             tail(n, TN(n, x, l, r)) = r {{ refl }}"
    ));
    assert_eq!(e.indexed_route("T"), Some(IndexedRoute::Iwf));
}

// A literal index is constructor-headed too, and a literal scrutinee
// computes through the inverted motive.
#[test]
fn a_literal_index_inverts_and_computes() {
    elab(&format!(
        "{T}
         fn first(t: T<Nat>(2)) -> Nat {{ match t {{ TN(k, x, l, r) => x }} }}
         theorem first_two(): first(TN(1, 7, TL, TN(0, 8, TL, TL))) = 7 {{ refl }}"
    ));
}

// The impossible arm may still be written; its goal is `Unit` and it is
// dropped, which is what a `_` arm expanding over it relies on.
#[test]
fn a_written_impossible_arm_is_dropped() {
    elab(&format!(
        "{T}
         fn head0(n: Nat, t: T<Nat>(Succ(n))) -> Nat {{ match t {{ TL => 0, TN(k, x, l, r) => x }} }}
         fn head1(n: Nat, t: T<Nat>(Succ(n))) -> Nat {{ match t {{ TN(k, x, l, r) => x, _ => 0 }} }}
         theorem head0_beta(n: Nat, x: Nat, l: T<Nat>(0), r: T<Nat>(n)):
             head0(n, TN(n, x, l, r)) = x {{ refl }}"
    ));
}

// At a declared enum index, inversion goes through the index type's own
// `Case` tree.
#[test]
fn a_declared_index_inverts() {
    elab(
        "inductive Col { Red, Blue }
         inductive P : (c: Col) -> Type {
             PR(x: Nat, q: P(Blue)) : P(Red),
             PB                     : P(Blue),
         }
         fn inner(p: P(Red)) -> P(Blue) { match p { PR(x, q) => q } }
         fn payload(p: P(Red)) -> Nat { match p { PR(x, q) => x } }
         theorem inner_beta(x: Nat, q: P(Blue)): inner(PR(x, q)) = q { refl }",
    );
}

// Negative controls. At a variable index nothing is inverted, so every arm
// is still owed; and inversion refines the goal by the constructor's index,
// so a child at another index does not fit it.
#[test]
fn what_inversion_does_not_do() {
    let m = elab_err(&format!(
        "{T} fn bad<A>(n: Nat, t: T<A>(n)) -> Nat {{ match t {{ TN(k, x, l, r) => 0 }} }}"
    ));
    assert!(m.contains("missing an arm for `TL`"), "{m}");
    elab_err(&format!(
        "{T} fn bad<A>(n: Nat, t: T<A>(Succ(n))) -> T<A>(n) {{ match t {{ TN(k, x, l, r) => l }} }}"
    ));
}

// ---------------------------------------------------------------------------
// Tier 2 — abstraction
// ---------------------------------------------------------------------------

// `add(m, m)` is stuck, so nothing inverts; abstracting it out of the goal
// types each arm at its own index, where the constant motive would type the
// `B2Z` arm at `B2(add(m, m))` and reject it.
#[test]
fn a_computed_index_is_abstracted_out_of_the_goal() {
    elab(&format!(
        "{ADD}
         inductive B2 : (n: Nat) -> Type {{
             B2Z                          : B2(1),
             B2N(n: Nat, l: B2(n), r: B2(n)) : B2(add(n, n)),
         }}
         fn keep(m: Nat, t: B2(add(m, m))) -> B2(add(m, m)) {{
             match t {{ B2Z => B2Z, B2N(n, l, r) => B2N(n, l, r) }}
         }}
         theorem keep_beta(m: Nat, l: B2(m), r: B2(m)): keep(m, B2N(m, l, r)) = B2N(m, l, r) {{ refl }}"
    ));
}
