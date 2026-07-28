//! Container fields phase 3 (`docs/container-proofs.md`): **proofs** by
//! induction over a container, which phases 1 and 2 rejected with a message.
//!
//! Phase 2 made `Rose` programmable; the ih it hands an arm is pointwise, so a
//! *dependent* motive had nowhere to go — a vector of results needs one element
//! type. Phase 3 keeps the ih pointwise and closes the goal instead: when the
//! motive is an equation, the self-call over a container proves the two
//! children **vectors** equal (`vec::tab_cong`), and the rest of the proof is
//! ordinary `j`.

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

/// `Rose`, two container recursions that agree at every node, and the one
/// hand-written congruence the proof leans on.
///
/// `size_plus` differs from `size` only in writing `add(_, 1)` where `size`
/// writes `Succ` — and `add(x, 1) ⇝ Succ x` *definitionally*, since `add`
/// recurses on its second argument. So the node-local step needs no arithmetic
/// lemma, and the only gap between the two sides is the two vectors of
/// children results: exactly the gap phase 3 exists to close
/// (`docs/container-proofs.md` §2).
const ROSE: &str = r#"
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }

inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }

fn size(r: Rose) -> Nat {
    match r {
        Node(l, n, kids) => Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
    }
}

fn size_plus(r: Rose) -> Nat {
    match r {
        Node(l, n, kids) =>
            add(kids.map(size_plus).fold(0, λ (a: Nat) (b: Nat) => add(a, b)), 1),
    }
}

// `xs = ys` at a vector implies their folds are equal. Written by hand and
// monomorphically, exactly as tier1_list_proofs.rs writes `cong_cons`: there is
// no polymorphism below layer m, and phase 3 does not try to remove that tax.
theorem cong_fold(n: Nat, {xs: [Nat; n]}, {ys: [Nat; n]}, p: xs = ys):
    xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
        = ys.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
{
    j(p, λ y q => xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
                       = y.fold(0, λ (a: Nat) (b: Nat) => add(a, b)), refl)
}
"#;

/// **The acceptance.** The first theorem in this codebase proved by induction
/// over a container field.
#[test]
fn size_agrees_with_size_plus_over_rose() {
    elab(&format!(
        "{ROSE}
         theorem same(r: Rose): size(r) = size_plus(r) {{
             match r {{
                 Node(l, n, kids) => cong_succ(cong_fold(n, kids.cong(same))),
             }}
         }}"
    ));
}

/// The negative control, and the one that matters: §9.1's lesson is that a
/// positive test cannot distinguish a type from a quotient of it, and the same
/// goes for a proof rule from a *wrong* proof rule. A false theorem of exactly
/// the same shape, discharged exactly the same way, must be rejected.
#[test]
fn a_false_theorem_of_the_same_shape_is_rejected() {
    let m = elab_err(&format!(
        "{ROSE}
         theorem wrong(r: Rose): size(r) = Succ(size_plus(r)) {{
             match r {{
                 Node(l, n, kids) => cong_succ(cong_fold(n, kids.cong(wrong))),
             }}
         }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");
}

/// The mixed case: a plain recursive child *and* a container in one
/// constructor. The ih is indexed by `Fin (Succ len)`, so the container's
/// indices are offset by one, and the tree is **asymmetric** so that an
/// off-by-one in that offset cannot pass (`docs/container-fields.md` §10.3).
#[test]
fn a_plain_child_and_a_container_prove_together() {
    elab(
        r#"
        fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }

        inductive T {
            Tip(Nat),
            Both(first: T, len: Nat, rest: [T; len]),
        }

        fn total(t: T) -> Nat {
            match t {
                Tip(n) => n,
                Both(first, len, rest) =>
                    add(total(first), rest.map(total).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
            }
        }

        fn total_plus(t: T) -> Nat {
            match t {
                Tip(n) => add(n, 0),
                Both(first, len, rest) =>
                    add(total_plus(first),
                        rest.map(total_plus).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
            }
        }

        theorem cong_add({a: Nat}, {b: Nat}, {c: Nat}, {d: Nat}, p: a = b, q: c = d):
            add(a, c) = add(b, d)
        {
            j(p, λ y _ => add(a, c) = add(y, d),
              j(q, λ y _ => add(a, c) = add(a, y), refl))
        }

        theorem cong_fold(n: Nat, {xs: [Nat; n]}, {ys: [Nat; n]}, p: xs = ys):
            xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
                = ys.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
        {
            j(p, λ y q => xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
                               = y.fold(0, λ (a: Nat) (b: Nat) => add(a, b)), refl)
        }

        // `add(n, 0) ⇝ n`, so the `Tip` arm is `refl`; the `Both` arm needs the
        // plain child's ih *and* the container's, which is the point.
        theorem same(t: T): total(t) = total_plus(t) {
            match t {
                Tip(n) => refl,
                Both(first, len, rest) =>
                    cong_add(same(first), cong_fold(len, rest.cong(same))),
            }
        }
        "#,
    );
}

#[test]
fn rejections() {
    // `.cong` where the motive is *not* dependent: that is `.map`'s job.
    let m = elab_err(&format!(
        "{ROSE}
         fn wrong(r: Rose) -> Nat {{
             match r {{
                 Node(l, n, kids) =>
                     kids.cong(wrong).fold(0, λ (a: Nat) (b: Nat) => add(a, b)),
             }}
         }}"
    ));
    assert!(m.contains("write `.map(wrong)`"), "{m}");

    // …and `.map` where it *is* an equation: that is `.cong`'s job. The old
    // §4.3 message is gone from this case, because the case now works.
    let m = elab_err(&format!(
        "{ROSE}
         theorem same(r: Rose): size(r) = size_plus(r) {{
             match r {{
                 Node(l, n, kids) => cong_succ(cong_fold(n, kids.map(same))),
             }}
         }}"
    ));
    assert!(m.contains("write `.cong(same)`"), "{m}");

    // The **heterogeneous** motive: an `Id` whose *type* mentions the
    // scrutinee, here through `[Nat; size(r)]`. Out of scope by §7 — it is the
    // same transport question as issues/dependent-field-injectivity.md — and
    // diagnosed rather than mis-elaborated.
    let m = elab_err(&format!(
        "{ROSE}
         theorem het(r: Rose, xs: [Nat; size(r)]): xs = xs {{
             match r {{
                 Node(l, n, kids) => kids.cong(het),
             }}
         }}"
    ));
    assert!(m.contains("docs/container-proofs.md"), "{m}");

    // Where the boundary actually falls: `r = r` is an equation at `Rose`,
    // whose type does *not* mention the scrutinee, so the lifting is built —
    // it proves the two children vectors equal, which is simply not this goal,
    // and the kernel says so. The rule is about the equation's type, not about
    // whether the proof happens to close the goal.
    let m = elab_err(&format!(
        "{ROSE}
         theorem rr(r: Rose): r = r {{
             match r {{ Node(l, n, kids) => kids.cong(rr) }}
         }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");

    // `.cong` on something that is not the container binder.
    let m = elab_err(&format!(
        "{ROSE}
         theorem elsewhere(r: Rose, other: [Rose; 1]): size(r) = size_plus(r) {{
             match r {{
                 Node(l, n, kids) => cong_succ(cong_fold(n, other.cong(elsewhere))),
             }}
         }}"
    ));
    assert!(m.contains("container field bound by the enclosing"), "{m}");
}
