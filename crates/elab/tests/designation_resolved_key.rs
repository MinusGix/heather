//! The designation table's key is a **resolved carrier**, never a spelling
//! (`issues/designation-key-collides-across-modules.md`, applying
//! `docs/instance-resolved-key-design.md` §3's rule one table over).
//!
//! `designation ++ at Box := join` used to key `("++", "Box")`, so two modules
//! each declaring a `Box` and each designating `++` at their own were one
//! entry and the second was refused. The registration side is one `carrier_key`
//! call; what this file is really about is the **lookup** side, which the
//! instance registry barely had and the operator path has four of: a
//! designation is looked up from an *operand's* carrier — a lowered type's
//! declaration — and that lookup has to land on the string the declaration
//! registered under.
//!
//! Four claims, each with the negative that tells it apart from the scheme it
//! replaces:
//!
//!  1. two modules declaring a type of the same name, each designating one
//!     symbol at its own, both register (the issue's repro);
//!  2. a use at each carrier gets *its own* operation — pinned by `refl`
//!     against the operation's written name, at **neutral** operands (the
//!     registry's answer, not the evaluator's) and at ones that **compute**;
//!  3. a carrier with no designation is not covered by its namesake next door
//!     — the control without which claim 2 would pass over a table that
//!     answered every `++` with whichever entry sorted first;
//!  4. a genuine duplicate — one module, one resolved carrier — is still
//!     refused, naming both parties qualified.
//!
//! `++` is the symbol throughout because it has **no fallback name**
//! (issues/bool-operator-designations.md): a lookup that misses the table
//! cannot be quietly rescued by rung 3, so every miss here is loud.
//!
//! Synthetic modules rather than `lib/std`: the collision is latent in the
//! library — today's colliding heads (`nat::Nat::Le`, `int::Int::Le`, `bool::Bool::Le`) are
//! designated at carriers whose *names* do not collide — so the tests are this
//! table's only customer, and two declarations say it in ten lines.

use heather_elab::{ElabError, Elaborator};

fn run(mods: &[(&str, &str)]) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in mods {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
        }
    }
    Ok(e)
}

fn ok(mods: &[(&str, &str)]) {
    if let Err(e) = run(mods) {
        panic!("expected these modules to check, got: {e}");
    }
}

fn bad(mods: &[(&str, &str)]) -> String {
    match run(mods) {
        Err(e) => e,
        Ok(_) => panic!("expected a refusal, but the modules checked"),
    }
}

/// Two modules, each with its own `Box`, each designating `++` at it — and the
/// two operations are **different functions of their arguments**, so a lookup
/// that picked the wrong entry is visible as a wrong term and not merely as a
/// type error.
const LEFT: &str = r#"
inductive Box { B0, B1 }
fn pick(a: Box, b: Box) -> Box { a }
fn b0() -> Box { B0 }
fn b1() -> Box { B1 }
designation ++ at Box := pick
"#;

const RIGHT: &str = r#"
inductive Box { C0, C1 }
fn pick(a: Box, b: Box) -> Box { b }
fn c0() -> Box { C0 }
fn c1() -> Box { C1 }
designation ++ at Box := pick
"#;

// ---------------------------------------------------------------------------
// 1: coexistence.

/// The issue's repro, verbatim in shape: one written head, two designations.
/// Under the head-spelling key the second declaration was refused as a
/// duplicate of the first.
#[test]
fn two_modules_same_head_both_designate() {
    ok(&[("left", LEFT), ("right", RIGHT)]);
}

// ---------------------------------------------------------------------------
// 2: each use gets its own operation.

/// One downstream file, both designations visible, `++` written unqualified at
/// both carriers. Each use resolves through the *operand's* declaration, so
/// each gets its own `pick` — pinned by `refl` against the qualified name,
/// which is the assertion that would fail if the lookup answered from the
/// other module's entry.
///
/// Both axes of `docs/testing-generated-terms.md` that apply to a table
/// lookup: **neutral** operands (parameters — nothing computes, so the answer
/// is the registry's) and operands that **compute** (a `fn` call reducible to
/// a constructor, so the equation is decided by evaluation too).
#[test]
fn a_use_at_each_carrier_gets_its_own_operation() {
    ok(&[
        ("left", LEFT),
        ("right", RIGHT),
        (
            "use",
            r#"
import left;
import right;

// Neutral on both sides: the operands are binders and cannot compute.
theorem at_left(x: left::Box, y: left::Box): x ++ y = left::pick(x, y) { refl }
theorem at_right(x: right::Box, y: right::Box): x ++ y = right::pick(x, y) { refl }

// And computing: `left`'s `++` keeps the first argument, `right`'s the second,
// so the two answers differ at the same written expression shape.
theorem lit_left(): left::b0() ++ left::b1() = left::b0() { refl }
theorem lit_right(): right::c0() ++ right::c1() = right::c1() { refl }
"#,
        ),
    ]);
}

/// The negative control for the pair above: `left`'s `++` is not `right`'s.
/// If the table had one entry for the written `Box`, one of these two would be
/// the other's operation and this equation would hold.
#[test]
fn the_two_operations_are_not_interchangeable() {
    let e = bad(&[
        ("left", LEFT),
        ("right", RIGHT),
        (
            "use",
            r#"
import left;
import right;
theorem wrong(x: left::Box, y: left::Box): x ++ y = y { refl }
"#,
        ),
    ]);
    // The kernel's refusal, and not a resolution one: `++` *did* resolve, to
    // `left::pick`, and `pick(x, y)` is `x`.
    assert!(e.contains("NotConvertible"), "{e}");
}

// ---------------------------------------------------------------------------
// 3: a namesake carrier is not covered.

/// A third `Box`, declared where it is used and designating nothing. `++` at
/// it has no meaning — its carrier is a different declaration and `++` has no
/// fallback name — and the refusal says so, listing the carriers that *are*
/// covered by their **written** names, which is what a reader can type.
///
/// Without this, `a_use_at_each_carrier_gets_its_own_operation` would pass
/// over a table that answered any `++` with whichever entry it found first.
#[test]
fn a_carrier_with_no_designation_is_not_covered_by_its_namesake() {
    let e = bad(&[
        ("left", LEFT),
        (
            "use",
            r#"
import left;
inductive Box { M0 }
theorem mine(x: Box, y: Box): x ++ y = x { refl }
"#,
        ),
    ]);
    assert!(e.contains("`++` has no meaning here"), "{e}");
    // The carrier it tried, as the writer spells it — not `use::Box`.
    assert!(e.contains("nothing designates `++` at `Box`"), "{e}");
    // And the row that exists, also written rather than keyed.
    assert!(e.contains("`Box` (`left::pick`)"), "{e}");
}

// ---------------------------------------------------------------------------
// 4: the duplicate that is still a duplicate.

/// One module, one resolved carrier, two designations of one symbol. Still
/// refused — the key got finer, not permissive — and the message names both
/// parties qualified, because "`++` already designates something at `Box`" is
/// exactly the sentence that used to be a lie about two modules.
#[test]
fn a_genuine_duplicate_is_refused_and_qualifies_both_parties() {
    let e = bad(&[(
        "dup",
        r#"
inductive Box { B0, B1 }
fn pick(a: Box, b: Box) -> Box { a }
fn pick2(a: Box, b: Box) -> Box { b }
designation ++ at Box := pick
designation ++ at Box := pick2
"#,
    )]);
    // The carrier, qualified: which `Box` is occupied.
    assert!(e.contains("at `dup::Box`"), "{e}");
    // The occupant, qualified: which operation is in the way.
    assert!(e.contains("`dup::pick`"), "{e}");
    assert!(e.contains("resolved"), "{e}");
}

/// And two modules' carriers are still two: the same symbol at the same
/// written head from *both* files, then a third designation in one of them at
/// the carrier it already covers, is the only thing refused.
#[test]
fn coexistence_does_not_disable_the_duplicate_check() {
    let e = bad(&[
        ("left", LEFT),
        ("right", RIGHT),
        (
            "third",
            r#"
import left;
fn also(a: left::Box, b: left::Box) -> left::Box { b }
designation ++ at left::Box := also
"#,
        ),
    ]);
    assert!(e.contains("at `left::Box`"), "{e}");
    assert!(e.contains("`left::pick`"), "{e}");
}
