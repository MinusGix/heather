//! Inside a member of `T`, a bare name may name `T`'s other members
//! (docs/sections-design.md §6). The member joins the candidate set with the
//! same rank as every other reading, so what is pinned beside each positive is
//! the negative a precedence would pass: a bare name that also resolves on its
//! own is ambiguous, whichever module either reading comes from.

use heather_elab::Elaborator;

use crate::support::{Refusal, assert_refused};

fn run(mods: &[(&str, &str)]) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in mods {
        e.elab_module_source(name, src).map_err(|err| err.render(src))?;
    }
    Ok(e)
}

fn ok(mods: &[(&str, &str)]) {
    if let Err(e) = run(mods) {
        panic!("expected these modules to check, got: {e}");
    }
}

/// Every module but the last checks; the last is refused for `says`.
fn refused(mods: &[(&str, &str)], says: &str) {
    let (last, before) = mods.split_last().expect("a module");
    let mut e = run(before).unwrap_or_else(|e| panic!("the prefix must check, got: {e}"));
    assert_refused(&mut e, last.0, last.1, Refusal::Says(says));
}

const BOX: &str = "inductive Box { Mk(v: Nat) }
fn Box::get(self b: Box) -> Nat { match b { Mk(v) => v } }
fn Box::get_succ(self b: Box) -> Nat { Succ(get(b)) }";

/// A sibling is reached bare as a call and as a value, inside a type's member
/// and inside a function's; a member's statement may name one too.
#[test]
fn a_member_names_its_siblings_bare() {
    ok(&[(
        "user",
        &format!(
            "{BOX}
fn Box::reader(self b: Box) -> Box -> Nat {{ get }}
theorem Box::get_succ_mk(n: Nat): get_succ(Mk(n)) = Succ(n) {{ refl }}
fn ten() -> Nat {{ 10 }}
theorem ten::value(): ten() = 10 {{ refl }}
theorem ten::again(): ten() = 10 {{ value() }}"
        ),
    )]);
}

/// The owner's members from another module count as siblings too: the owner
/// is `Box`, wherever `Box::get` was declared.
#[test]
fn an_imported_member_of_the_owner_is_a_sibling() {
    ok(&[
        ("boxes", BOX),
        (
            "user",
            "import boxes;\nfn Box::again(self b: Box) -> Nat { get_succ(Mk(get(b))) }",
        ),
    ]);
}

/// A bare name that resolves on its own as well is ambiguous, whichever side
/// is local: neither the sibling nor the ambient declaration wins.
#[test]
fn a_sibling_and_an_ambient_name_are_ambiguous() {
    refused(
        &[("user", &format!("{BOX}\nfn get(n: Nat) -> Nat {{ n }}\nfn Box::clash(self b: Box) -> Nat {{ get(b) }}"))],
        "`get` is ambiguous here: inside a member of `Box` it can name `Box::get`",
    );
    refused(
        &[
            ("other", "fn get(n: Nat) -> Nat { n }"),
            ("user", &format!("import other;\n{BOX}\nfn Box::clash(self b: Box) -> Nat {{ get(b) }}")),
        ],
        "`get` is ambiguous here: inside a member of `Box` it can name `Box::get`",
    );
}

/// Outside a member of `Box`, `Box`'s members are not bare names, and a
/// local binder still shadows a sibling inside one.
#[test]
fn siblings_are_only_a_members_and_binders_shadow_them() {
    refused(&[("user", &format!("{BOX}\nfn outside(b: Box) -> Nat {{ get(b) }}"))], "unbound name `get`");
    ok(&[(
        "user",
        &format!("{BOX}\nfn Box::shadow(self b: Box, get: Nat) -> Nat {{ get }}\ntheorem Box::shadowed(): Mk(1).shadow(5) = 5 {{ refl }}"),
    )]);
}

/// A constructor qualified by its type (`Box::Mk`) is not a member: a bare
/// constructor inside a member is the constructor, never an ambiguity with
/// itself.
#[test]
fn a_constructor_is_not_a_sibling() {
    ok(&[("user", &format!("{BOX}\nfn Box::fresh(self b: Box) -> Box {{ Mk(get(b)) }}"))]);
}
