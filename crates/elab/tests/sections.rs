//! `section<…>(…) { … }` writes a head once for a run of declarations
//! (docs/sections-design.md). The parser splices the head into each member's
//! own, so what is pinned here is that the result is the declaration a reader
//! would have written by hand, and that the splice refuses what it cannot make
//! into one.

use heather_elab::Elaborator;

use crate::support::{Refusal, assert_refused};

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn refused(src: &str, says: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    assert_refused(&mut e, "sections_probe", src, Refusal::Says(says))
}

const PT: &str = r#"
class Pt<A> { pt: A }
inductive Two<A> { Mk(a: A, b: A) }
fn Two::fst<A>(self p: Two<A>) -> A { match p { Mk(a, _) => a } }
instance Pt<Nat> { pt := 0 }
"#;

/// A constrained type parameter in the head: the member is the hand-written
/// declaration, by `refl`, at an open carrier and at `Nat`, and a sibling's
/// statement uses the member with the carrier inferred.
#[test]
fn a_spliced_member_is_its_hand_written_twin() {
    ok(&format!(
        "{PT}
section<A: Pt> {{
fn pair(x: A) -> Two<A> {{ Mk(x, A.pt) }}
theorem pair_fst(x: A): pair(x).fst() = x {{ refl }}
}}

fn pair_by_hand<A: Pt>(x: A) -> Two<A> {{ Mk(x, A.pt) }}
theorem twins_open<A: Pt>(x: A): pair(x) = pair_by_hand(x) {{ refl }}
theorem twins_nat(): pair(3) = pair_by_hand(3) {{ refl }}
theorem pair_nat(): pair(3) = Mk(3, 0) {{ refl }}
"
    ));
}

/// Value binders: an implicit determined by a later binder's type, a `self`
/// receiver, a dependent hypothesis, and a nested section whose head follows
/// the outer one. Callers pass the head's explicit binders, inside the
/// section and out.
#[test]
fn value_binders_and_nested_sections_concatenate_outermost_first() {
    ok(&format!(
        "{PT}
section<A>({{x: A}}, self p: Two<A>, h: p.fst() = x) {{
theorem Two::fst_is(): p.fst() = x {{ h }}
section(y: A) {{
fn Two::with_snd() -> Two<A> {{ Mk(x, y) }}
theorem Two::with_snd_fst(): p.with_snd(h, y).fst() = p.fst() {{ sym(h) }}
}}
}}

theorem outside(q: Two<Nat>, e: q.fst() = 1): q.with_snd(e, 7) = Mk(1, 7) {{ refl }}
theorem receiver(q: Two<Nat>, e: q.fst() = 1): q.fst() = 1 {{ q.fst_is(e) }}
"
    ));
}

/// A section binder no member's head mentions is refused at that member, not
/// at its first call: neither a type parameter nor a `{}` implicit could be
/// inferred there.
#[test]
fn a_binder_the_member_does_not_determine_is_refused_at_the_member() {
    refused(
        "section<A> {\nfn constant() -> Nat { 0 }\n}\n",
        "parse error: `constant` does not determine the section's `A`",
    );
    refused(
        "section({k: Nat}, n: Nat) {\nfn first() -> Nat { n }\n}\n",
        "parse error: `first` does not determine the section's `k`",
    );
}

/// A determined implicit is found through another implicit's type: `k` is
/// written only in `v`'s type, and `v` only in the explicit `w`'s.
#[test]
fn determination_follows_implicit_types() {
    ok(r#"
section({k: Nat}, {v: [Nat; k]}, w: v = v) {
fn length() -> Nat { k }
}
theorem length_three(v3: [Nat; 3], e: v3 = v3): length(e) = 3 { refl }
"#);
}

/// Rebinding a head's name would shadow it silently (a repeated parameter
/// name does today), so it is refused, as is a second receiver, a section
/// with nothing in its head, and an item with no head to splice into.
#[test]
fn the_splice_refuses_what_a_head_cannot_say() {
    refused(
        "section(x: Nat) {\nfn f(x: Nat) -> Nat { x }\n}\n",
        "parse error: `x` is already bound by the enclosing section's head",
    );
    refused(
        "section<A> {\nfn g<A>(x: A) -> A { x }\n}\n",
        "parse error: `A` is already bound by the enclosing section's head",
    );
    refused(
        "section(n: Nat) {\nsection(n: Nat) {\nfn h() -> Nat { n }\n}\n}\n",
        "parse error: `n` is already bound by an enclosing section's head",
    );
    refused(
        "section(self x: Nat) {\nfn Nat::f(self y: Nat) -> Nat { y }\n}\n",
        "parse error: a declaration has at most one `self`, and the enclosing section's `x`",
    );
    refused("section {\nfn f() -> Nat { 0 }\n}\n", "parse error: a section's head is what it writes once");
    refused(
        "section(n: Nat) {\ninductive D { C }\n}\n",
        "parse error: an `inductive` or `record` cannot be in a section",
    );
    refused(
        "section(n: Nat) {\naxiom a(): n = n;\n}\n",
        "parse error: an `axiom` cannot be in a section",
    );
}
