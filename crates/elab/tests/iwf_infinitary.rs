//! Acceptance for indexed families with a recursive **function** field: the
//! `IWf` route lowered on `W` (`docs/iwf-infinitary-design.md`, §11's
//! checklist), against the four axes of `docs/testing-generated-terms.md`.
//!
//! Every declaration below is lowered to `Σ(t : W₀). El(ok t m)` and every
//! term re-checked by the real kernel, so a wrong encoding is a rejection;
//! the propositional tests are what catch a *well-typed* wrong one:
//!
//! - **axis 1** — a literal scrutinee computes (a `refl` theorem against the
//!   written reduct), and so does a constructor with open payload and
//!   children;
//! - **axis 2** — open payloads and children, and an open element type;
//! - **axis 3** — checking positions: every claim is a `theorem`, and
//!   induction proves a dependent motive at a neutral derivation;
//! - **axis 4** — negative controls, one per encoding decision.

use heather_elab::{ElabError, Elaborator, IndexedRoute};

use crate::support::{assert_refused, Refusal};

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

const ADD: &str = r#"
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
"#;

/// Every child kind §3 distinguishes: a leaf (`Lf`, the children equation
/// at `n = 0`), one plain child (`One`), one function child whose index
/// reads its argument (`Br`), and two children, a function one and a plain
/// one (`Two`, the stored `k̄`).
const TR: &str = r#"
inductive Tr : (n: Nat) -> Type {
    Lf                                          : Tr(0),
    One(n: Nat, t: Tr(n))                       : Tr(Succ(n)),
    Br(n: Nat, k: (y: Nat) -> Tr(add(y, n)))    : Tr(Succ(n)),
    Two(n: Nat, k: (y: Nat) -> Tr(n), l: Tr(0)) : Tr(n),
}
fn size(n: Nat, t: Tr(n)) -> Nat {
    match t {
        Lf => 1,
        One(m, s) => Succ(size(m, s)),
        Br(m, k) => Succ(size(add(2, m), k(2))),
        Two(m, k, l) => add(size(m, k(1)), size(0, l)),
    }
}
fn chain(n: Nat) -> Tr(n) { match n { Zero => Lf, Succ(m) => One(m, chain(m)) } }
"#;

// §11.1 — the declaration lowers on `W` and every constructor builds, at
// open payloads and open children.
#[test]
fn every_child_kind_declares_and_builds() {
    let e = elab(&format!(
        "{ADD}{TR}
         fn lf() -> Tr(0) {{ Lf }}
         fn one(n: Nat, t: Tr(n)) -> Tr(Succ(n)) {{ One(n, t) }}
         fn br(n: Nat, k: (y: Nat) -> Tr(add(y, n))) -> Tr(Succ(n)) {{ Br(n, k) }}
         fn two(n: Nat, k: (y: Nat) -> Tr(n), l: Tr(0)) -> Tr(n) {{ Two(n, k, l) }}
         fn fan() -> Tr(1) {{ Br(0, λ y => Two(add(y, 0), λ z => chain(y), Lf)) }}"
    ));
    assert_eq!(e.indexed_route("Tr"), Some(IndexedRoute::IwfW));
}

// §11.2 — closed computation through every kind, by `refl`.
#[test]
fn closed_computation_through_every_kind() {
    elab(&format!(
        "{ADD}{TR}
         theorem s_lf(): size(0, Lf) = 1 {{ refl }}
         theorem s_one(): size(1, One(0, Lf)) = 2 {{ refl }}
         theorem s_two(): size(0, Two(0, λ y => Lf, Lf)) = 2 {{ refl }}
         theorem s_br(): size(1, Br(0, chain)) = 4 {{ refl }}
         theorem s_fan(): size(1, Br(0, λ y => Two(y, λ z => chain(y), Lf))) = 5 {{ refl }}"
    ));
}

// §11.3 — β on open data: a constructor with open payload and children
// reduces to its arm, the equations' `J`s computing at their `refl`s.
#[test]
fn beta_fires_on_open_children() {
    elab(&format!(
        "{ADD}{TR}
         theorem o_one(n: Nat, t: Tr(n)): size(Succ(n), One(n, t)) = Succ(size(n, t)) {{ refl }}
         theorem o_br(n: Nat, k: (y: Nat) -> Tr(add(y, n))):
             size(Succ(n), Br(n, k)) = Succ(size(add(2, n), k(2))) {{ refl }}
         theorem o_two(n: Nat, k: (y: Nat) -> Tr(n), l: Tr(0)):
             size(n, Two(n, k, l)) = add(size(n, k(1)), size(0, l)) {{ refl }}"
    ));
}

/// A copy that rebuilds every node: its `Br` arm recurses **under a written
/// λ**, at the index `add(y, m)` that mentions the λ's own variable — the
/// function child's rebound index, read under `y` and instantiated at it.
const CP: &str = r#"
fn cp(n: Nat, t: Tr(n)) -> Tr(n) {
    match t {
        Lf => Lf,
        One(m, s) => One(m, cp(m, s)),
        Br(m, k) => Br(m, λ y => cp(add(y, m), k(y))),
        Two(m, k, l) => Two(m, λ y => cp(m, k(y)), cp(0, l)),
    }
}
"#;

// §11.4 — induction at a neutral derivation, with a motive that depends on
// it, through both function children (`Br`'s at the rebound index, `Two`'s
// at a fixed one) and the plain ones: every arm closes by its children's
// hypotheses, so the `J`s over the stored equations compute on open data.
#[test]
fn induction_through_function_children_at_the_rebound_index() {
    elab(&format!(
        "{ADD}{TR}{CP}
         theorem add_eq(a: Nat, b: Nat, c: Nat, d: Nat, p: a = c, q: b = d): add(a, b) = add(c, d) {{ rewrite(p, q, refl) }}
         theorem cp_size(n: Nat, t: Tr(n)): size(n, cp(n, t)) = size(n, t) {{
             match t {{
                 Lf => refl,
                 One(m, s) => cong(cp_size(m, s)),
                 Br(m, k) => cong(cp_size(add(2, m), k(2))),
                 // Two holes, so not one `cong`; and `rewrite` looks for an
                 // occurrence by `size`'s head, which the reduct does not
                 // have (issues/cong-inference-through-iwf-w-children.md).
                 Two(m, k, l) => add_eq(size(m, cp(m, k(1))), size(0, cp(0, l)), size(m, k(1)), size(0, l),
                                        cp_size(m, k(1)), cp_size(0, l)),
             }}
         }}
         theorem cp_lit(): cp(1, Br(0, chain)) = Br(0, λ y => cp(add(y, 0), chain(y))) {{ refl }}"
    ));
}

// §11.5 — a neutral scrutinee does not compute: `size` at an open `t` is
// stuck, so a claim only a reduction could prove is a mismatch.
#[test]
fn a_neutral_scrutinee_does_not_compute() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    assert_refused(
        &mut e,
        "stuck",
        &format!("{ADD}{TR}\ntheorem stuck(n: Nat, t: Tr(n)): size(n, t) = 1 {{ refl }}"),
        Refusal::Says("`size(n, t)` and `1` are not"),
    );
}

// §11.6 — negative controls, one per encoding decision.
#[test]
fn a_function_child_at_the_wrong_index_is_refused() {
    // `t : Tr(n)` where `Br` needs `(y: Nat) -> Tr(add(y, n))`: the children
    // equation is not a convenience the constructor can skip.
    let mut e = Elaborator::with_prelude().expect("prelude");
    assert_refused(
        &mut e,
        "wrong_child",
        &format!("{ADD}{TR}\nfn bad(n: Nat, t: Tr(n)) -> Tr(Succ(n)) {{ Br(n, λ y => t) }}"),
        Refusal::Mismatch,
    );
}

#[test]
fn a_self_call_at_a_non_subtree_is_refused() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let m = assert_refused(
        &mut e,
        "non_subtree",
        &format!(
            "{ADD}{TR}
             fn bad(n: Nat, t: Tr(n)) -> Nat {{
                 match t {{ Lf => 0, One(m, s) => 0, Br(m, k) => 0, Two(m, k, l) => bad(m, Two(m, k, l)) }}
             }}"
        ),
        Refusal::Says("must descend"),
    );
    assert!(m.contains("`bad`"), "{m}");
}

#[test]
fn a_self_call_at_the_wrong_index_is_refused() {
    // `k(3) : Tr(add(3, m))`, called at `add(2, m)`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    assert_refused(
        &mut e,
        "wrong_index",
        &format!(
            "{ADD}{TR}
             fn bad(n: Nat, t: Tr(n)) -> Nat {{
                 match t {{ Lf => 0, One(m, s) => 0, Br(m, k) => bad(add(2, m), k(3)), Two(m, k, l) => 0 }}
             }}"
        ),
        Refusal::Says("must pass `n` unchanged"),
    );
}

#[test]
fn a_curried_function_field_is_refused() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    assert_refused(
        &mut e,
        "curried",
        "inductive Cu : (n: Nat) -> Type { CL : Cu(0), CC(k: (y: Nat) -> (z: Nat) -> Cu(y)) : Cu(1) }",
        Refusal::Says("is a curried function into `Cu`"),
    );
}

// §11.7 — index inversion: at a constructor-headed index, the arms whose
// constructors cannot reach it are omitted (`VL` is at `0`, never at a
// `Succ`), and the match still computes — through one function child (`VB`)
// and through two children (`VC`, the stored `k̄`).
#[test]
fn index_inversion_omits_unreachable_arms() {
    elab(
        r#"
        inductive Tv : (n: Nat) -> Type {
            VL                                          : Tv(0),
            VB(n: Nat, k: (y: Nat) -> Tv(n))            : Tv(Succ(n)),
            VC(n: Nat, k: (y: Nat) -> Tv(n), l: Tv(n))  : Tv(Succ(n)),
        }
        fn pre(n: Nat, t: Tv(Succ(n))) -> Nat { match t { VB(m, k) => m, VC(m, k, l) => Succ(m) } }
        theorem pre_vb(n: Nat, k: (y: Nat) -> Tv(n)): pre(n, VB(n, k)) = n { refl }
        theorem pre_vc(n: Nat, k: (y: Nat) -> Tv(n), l: Tv(n)): pre(n, VC(n, k, l)) = Succ(n) { refl }
        fn sub(n: Nat, t: Tv(Succ(n))) -> Tv(n) { match t { VB(m, k) => k(0), VC(m, k, l) => l } }
        theorem sub_vb(): sub(0, VB(0, λ y => VL)) = VL { refl }
        "#,
    );
}

// §11.8 — the logical-relation miniature the port needs (PR #158): a
// relation indexed by a type, whose arrow case quantifies its premise over
// every argument, and a lemma proved by induction over the relation.
#[test]
fn a_logical_relation_with_a_quantified_arrow_premise() {
    elab(
        r#"
        inductive Ty { Base, Arr(a: Ty, b: Ty) }
        fn depth(t: Ty) -> Nat { match t { Base => 0, Arr(a, b) => Succ(depth(b)) } }
        inductive Red : (t: Ty) -> Type {
            RB(v: Nat)                                  : Red(Base),
            RA(a: Ty, b: Ty, f: (x: Nat) -> Red(b))     : Red(Arr(a, b)),
        }
        fn val(t: Ty, r: Red(t)) -> Nat {
            match r { RB(v) => v, RA(a, b, f) => val(b, f(0)) }
        }
        fn shift(t: Ty, r: Red(t)) -> Red(t) {
            match r { RB(v) => RB(Succ(v)), RA(a, b, f) => RA(a, b, λ x => shift(b, f(x))) }
        }
        theorem val_shift(t: Ty, r: Red(t)): val(t, shift(t, r)) = Succ(val(t, r)) {
            match r { RB(v) => refl, RA(a, b, f) => val_shift(b, f(0)) }
        }
        theorem val_lit(): val(Arr(Base, Base), RA(Base, Base, λ x => RB(x))) = 0 { refl }
        "#,
    );
}

// Axis 2's open element type: the family's parameter `A` is a payload *and*
// a function field's domain (its code is `A` itself), and both compute.
#[test]
fn an_open_element_type_as_payload_and_domain() {
    elab(&format!(
        "{ADD}
         inductive Ro<A> : (n: Nat) -> Type {{
             RL(x: A)                              : Ro<A>(0),
             RN(n: Nat, a: A, k: (y: A) -> Ro<A>(n)) : Ro<A>(Succ(n)),
         }}
         fn first<A>(n: Nat, t: Ro<A>(n)) -> A {{ match t {{ RL(x) => x, RN(m, a, k) => first(m, k(a)) }} }}
         theorem first_rn<A>(n: Nat, a: A, k: (y: A) -> Ro<A>(n)): first(Succ(n), RN(n, a, k)) = first(n, k(a)) {{ refl }}
         theorem first_lit(): first(1, RN(0, 4, λ y => RL(add(y, 1)))) = 5 {{ refl }}"
    ));
}

// A mutual group with a function field: the group's one family is indexed
// by the member sum, and the member's function child recurses at its own
// index (docs/mutual-inductive-design.md §5's rebind, under `y`).
#[test]
fn a_mutual_group_with_a_function_field() {
    elab(
        r#"
        inductive Ev { EZ, ES(o: Od) }
        inductive Od { OS(e: Ev), OL(k: (y: Nat) -> Ev) }
        fn ecount(e: Ev) -> Nat { match e { EZ => 0, ES(o) => Succ(ocount(o)) } }
        fn ocount(o: Od) -> Nat { match o { OS(e) => Succ(ecount(e)), OL(k) => ecount(k(3)) } }
        theorem oc(): ocount(OL(λ y => ES(OS(EZ)))) = 2 { refl }
        "#,
    );
    // An indexed member whose function child varies the member's index
    // under `y`: the guard rebinds it through `#member`.
    elab(&format!(
        "{ADD}
         inductive Sy {{ SB, SA(t: Tm(0)) }}
         inductive Tm : (n: Nat) -> Type {{
             TV(n: Nat)                               : Tm(Succ(n)),
             TL(n: Nat, b: (y: Nat) -> Tm(add(y, n)))  : Tm(n),
             TS(n: Nat, s: Sy)                        : Tm(n),
         }}
         fn tsize(n: Nat, t: Tm(n)) -> Nat {{
             match t {{ TV(m) => 1, TL(m, b) => Succ(tsize(add(1, m), b(1))), TS(m, s) => ssize(s) }}
         }}
         fn ssize(s: Sy) -> Nat {{ match s {{ SB => 0, SA(t) => tsize(0, t) }} }}
         theorem ts(): tsize(0, TL(0, λ y => TS(add(y, 0), SA(TS(0, SB))))) = 1 {{ refl }}"
    ));
}
