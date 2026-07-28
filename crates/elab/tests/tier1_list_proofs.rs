//! Proof content over a *generated* tier-1 `List` — `issues/stress-proof-suite.md`
//! item 2's remainder.
//!
//! `crates/elab/tests/inductive_tier1.rs` shows that a linear declaration lowers
//! onto `Wf` and that its recursor computes. What it does not show is that the
//! result is usable for *proofs*: that a recursive `theorem` over a generated
//! `List` can carry a dependent motive through a self-call the way
//! `mirror_of_mirror` does for the branching side. That is what this file is.
//!
//! The reference is `crates/elab/tests/tier1_fording.rs`, which proved exactly
//! these lemmas by hand against the (now superseded) exact-height encoding.
//! Everything below is elaborated from surface syntax and re-checked by the
//! real kernel.

use heather_elab::{ElabError, Elaborator};

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

/// The declaration, `append`, and the two Id lemmas every proof below leans on.
/// `cong_cons` and `trans_list` are the `List` instances of what
/// `inductive_tier1.rs` writes as `cong_node_*`/`trans_tree`: the surface has no
/// function values yet, so a congruence is written per-constructor by hand.
const LIST: &str = r#"
inductive List { Nil, Cons(head: Nat, tail: List) }

fn append(xs: List, ys: List) -> List {
    match xs {
        Nil => ys,
        Cons(h, t) => Cons(h, append(t, ys)),
    }
}

theorem cong_cons(h: Nat, {t1: List}, {t2: List}, p: t1 = t2):
    Cons(h, t1) = Cons(h, t2)
{ j(p, λ y q => Cons(h, t1) = Cons(h, y), refl) }

theorem trans_list({a: List}, {b: List}, {c: List}, p: a = b, q: b = c): a = c
{ j(q, λ y r => a = y, p) }

theorem sym_list({a: List}, {b: List}, p: a = b): b = a
{ j(p, λ y q => y = a, refl) }
"#;

// Closed evaluation: `append` computes, so `refl` proves it.
#[test]
fn append_computes() {
    elab(&format!(
        "{LIST}
         theorem a_nil(): append(Nil, Cons(3, Nil)) = Cons(3, Nil) {{ refl }}
         theorem a_one(): append(Cons(1, Nil), Cons(2, Nil))
                        = Cons(1, Cons(2, Nil)) {{ refl }}
         theorem a_two(): append(Cons(1, Cons(2, Nil)), Cons(3, Nil))
                        = Cons(1, Cons(2, Cons(3, Nil))) {{ refl }}"
    ));
}

// The property the branching design was chosen for, at the linear tier and now
// from a *generated* declaration: β fires on a constructor form whatever its
// children are, so the `Cons` equation holds with all three variables open.
// (`tier1_fording.rs` pinned the same statement against the height encoding.)
#[test]
fn the_cons_equation_holds_with_open_arguments() {
    elab(&format!(
        "{LIST}
         theorem step(h: Nat, t: List, ys: List):
             append(Cons(h, t), ys) = Cons(h, append(t, ys)) {{ refl }}
         theorem nil_step(ys: List): append(Nil, ys) = ys {{ refl }}"
    ));
}

// **The acceptance.** `append xs nil = xs` is *not* `refl` — with `xs` open the
// left side is neutral — so this is a genuine induction: the motive varies with
// the scrutinee and the ih arrives as the guarded self-call.
#[test]
fn append_nil_by_induction() {
    elab(&format!(
        "{LIST}
         theorem append_nil(xs: List): append(xs, Nil) = xs {{
             match xs {{
                 Nil => refl,
                 Cons(h, t) => cong_cons(h, append_nil(t)),
             }}
         }}"
    ));
}

// Associativity: recursion on `xs` with two constant parameters carried along,
// which is the shape a self-call has to support beyond `mirror`'s single
// argument.
#[test]
fn append_assoc_by_induction() {
    elab(&format!(
        "{LIST}
         theorem append_assoc(xs: List, ys: List, zs: List):
             append(append(xs, ys), zs) = append(xs, append(ys, zs))
         {{
             match xs {{
                 Nil => refl,
                 Cons(h, t) => cong_cons(h, append_assoc(t, ys, zs)),
             }}
         }}"
    ));
}

// A proof that *uses* an earlier inductive proof rather than only `refl` and a
// congruence: `rev` is defined by `append`, and `rev (xs ++ ys) = rev ys ++ rev xs`
// needs `append_nil` and `append_assoc` as lemmas plus `trans_list` to chain
// them. This is the first place the suite composes two inductive results.
#[test]
fn rev_append_composes_the_earlier_lemmas() {
    elab(&format!(
        "{LIST}
         theorem append_nil(xs: List): append(xs, Nil) = xs {{
             match xs {{
                 Nil => refl,
                 Cons(h, t) => cong_cons(h, append_nil(t)),
             }}
         }}

         theorem append_assoc(xs: List, ys: List, zs: List):
             append(append(xs, ys), zs) = append(xs, append(ys, zs))
         {{
             match xs {{
                 Nil => refl,
                 Cons(h, t) => cong_cons(h, append_assoc(t, ys, zs)),
             }}
         }}

         fn rev(xs: List) -> List {{
             match xs {{
                 Nil => Nil,
                 Cons(h, t) => append(rev(t), Cons(h, Nil)),
             }}
         }}

         theorem rev_two(): rev(Cons(1, Cons(2, Nil))) = Cons(2, Cons(1, Nil))
         {{ refl }}

         theorem cong_append_l({{a: List}}, {{b: List}}, p: a = b, zs: List):
             append(a, zs) = append(b, zs)
         {{ j(p, λ y q => append(a, zs) = append(y, zs), refl) }}

         theorem rev_append(xs: List, ys: List):
             rev(append(xs, ys)) = append(rev(ys), rev(xs))
         {{
             match xs {{
                 Nil => sym_list(append_nil(rev(ys))),
                 Cons(h, t) => trans_list(
                     @cong_append_l(rev(append(t, ys)), append(rev(ys), rev(t)),
                                    rev_append(t, ys), Cons(h, Nil)),
                     @append_assoc(rev(ys), rev(t), Cons(h, Nil))),
             }}
         }}"
    ));
}

// Negative controls, so none of the above is vacuous. Each is a statement the
// kernel must *reject*; if the encoding were degenerate — every `List` term
// convertible with every other, say — these would go through too.
#[test]
fn the_gate_rejects_the_near_misses() {
    // `append xs nil` is genuinely neutral: without the induction, no `refl`.
    let m1 = elab_err(&format!(
        "{LIST}
         theorem not_refl(xs: List): append(xs, Nil) = xs {{ refl }}"
    ));

    // A false closed equation.
    let m2 = elab_err(&format!(
        "{LIST}
         theorem wrong(): append(Cons(1, Nil), Cons(2, Nil))
                        = Cons(2, Cons(1, Nil)) {{ refl }}"
    ));

    // Distinct constructors are not equal — the encoding is not collapsed.
    let m3 = elab_err(&format!(
        "{LIST}
         theorem collapsed(h: Nat, t: List): Cons(h, t) = Nil {{ refl }}"
    ));

    // Associativity is not commutativity: the same proof skeleton must fail on
    // the statement that is actually false.
    let m4 = elab_err(&format!(
        "{LIST}
         theorem not_comm(xs: List, ys: List): append(xs, ys) = append(ys, xs) {{
             match xs {{
                 Nil => refl,
                 Cons(h, t) => cong_cons(h, not_comm(t, ys)),
             }}
         }}"
    ));

    // Each is a *conversion* failure in the kernel, not a parse or scoping
    // slip — i.e. the gate that rejected them is the one that matters.
    for m in [&m1, &m2, &m3, &m4] {
        assert!(m.contains("the kernel rejected"), "{m}");
        assert!(m.contains("NotConvertible"), "{m}");
    }
}
