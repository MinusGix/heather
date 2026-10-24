//! The instance registry's key is a **resolved carrier**, never a spelling
//! (`docs/instance-resolved-key-design.md`,
//! `issues/instance-key-collides-across-modules.md`).
//!
//! Five claims, and each one has the negative that tells it apart from the
//! scheme it replaced:
//!
//!  1. two modules declaring a relation of the same *name* register two
//!     instances, and both are found (the collision repro, now passing);
//!  2. resolution picks the one whose carrier the goal actually has — so
//!     coexistence is not "both are there and either might answer";
//!  3. a genuine duplicate — one module, one resolved carrier — is still
//!     refused, and the message module-qualifies both parties;
//!  4. the canonical name is a declaration of the declaring module, so
//!     `m::Head::Class` is a reference that resolves;
//!  5. the lexer joins a `::` chain, and the import-list form is the boundary
//!     that must not have moved.
//!
//! Synthetic modules rather than `lib/std`: the library carries the same three
//! `Le`s and is probed by `lib/_tests/std/num/int_tests.hthr`, but the *key* is what is under
//! test here and a two-declaration program says it in ten lines.

use heather_elab::{ElabError, Elaborator};
use heather_syntax::lexer::{lex, TokKind};

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

fn ok(mods: &[(&str, &str)]) -> Elaborator {
    run(mods).unwrap_or_else(|e| panic!("expected these modules to check, got: {e}"))
}

fn bad(mods: &[(&str, &str)]) -> String {
    match run(mods) {
        Err(e) => e,
        Ok(_) => panic!("expected a refusal, but the modules checked"),
    }
}

/// The class every test below registers at: `Decide`'s shape, stated locally so
/// that nothing here depends on `lib/std/core/logic.hthr`.
const CLASSES: &str = r#"
inductive Verdict<P> { Yes(proof: P), No }
class Judge<P> { verdict: Verdict<P> }
"#;

/// Two modules, each with its own `Le` — a `fn` into `Type`, so the carrier is
/// an applied **type former** and its head is `Le` in both.
const LEFT: &str = r#"
inductive L { L0 }
fn Le(x, y: L) -> Type { True }
instance(x, y: L) Judge<Le(x, y)> { verdict := Yes(trivial) }
"#;

const RIGHT: &str = r#"
inductive R { R0 }
fn Le(x, y: R) -> Type { True }
instance(x, y: R) Judge<Le(x, y)> { verdict := Yes(trivial) }
"#;

// ---------------------------------------------------------------------------
// 1–2: coexistence, and that it is coexistence and not a coin flip.

/// The repro from `issues/instance-key-collides-across-modules.md`, verbatim in
/// shape: two modules, one written head, two instances. Under the head-spelling
/// key the second declaration was refused.
#[test]
fn two_modules_same_head_both_register() {
    ok(&[
        ("cls", CLASSES),
        ("left", &format!("import cls;\n{LEFT}")),
        ("right", &format!("import cls;\n{RIGHT}")),
    ]);
}

/// Coexistence is worth nothing if the resolver then cannot tell them apart.
/// One downstream file, both instances visible, and each goal is answered by
/// the instance at *its* carrier — checked by the kernel at the goal type, as
/// every proposal is.
#[test]
fn resolution_picks_the_instance_at_the_goals_carrier() {
    ok(&[
        ("cls", CLASSES),
        ("left", &format!("import cls;\n{LEFT}")),
        ("right", &format!("import cls;\n{RIGHT}")),
        (
            "use",
            r#"
import cls;
import left;
import right;

fn judged<P> requires j: Judge<P> () -> Verdict<P> { j.verdict }

// An OPEN carrier on both sides: neither goal is closed by computation, so
// the answer is the registry's and not the evaluator's.
fn at_left(x, y: left::L) -> Verdict<left::Le(x, y)> { judged() }
fn at_right(x, y: right::R) -> Verdict<right::Le(x, y)> { judged() }
"#,
        ),
    ]);
}

/// The negative control for the pair above: a goal whose carrier has **no**
/// instance is not answered by the same-named one next door. Without it,
/// `resolution_picks_the_instance_at_the_goals_carrier` would pass over a
/// registry that answered every `Judge` goal with whichever entry sorted first.
#[test]
fn a_carrier_with_no_instance_is_not_answered_by_its_namesake() {
    let e = bad(&[
        ("cls", CLASSES),
        ("left", &format!("import cls;\n{LEFT}")),
        (
            "use",
            r#"
import cls;
import left;

inductive M { M0 }
fn Le(x, y: M) -> Type { True }

fn judged<P> requires j: Judge<P> () -> Verdict<P> { j.verdict }
fn at_mine(x, y: M) -> Verdict<Le(x, y)> { judged() }
"#,
        ),
    ]);
    assert!(e.contains("no instance for"), "{e}");
}

// ---------------------------------------------------------------------------
// 3: the duplicate that is still a duplicate.

/// One module, one resolved carrier, two instances of one class. Still refused
/// — the key got finer, not permissive — and the message now names both parties
/// by their qualified forms, because "`Le` already has an instance" is exactly
/// the sentence that used to be a lie.
#[test]
fn a_genuine_duplicate_is_refused_and_qualifies_both_parties() {
    let e = bad(&[
        ("cls", CLASSES),
        (
            "dup",
            r#"
import cls;
inductive L { L0 }
fn Le(x, y: L) -> Type { True }
instance(x, y: L) Judge<Le(x, y)> { verdict := Yes(trivial) }
instance(x, y: L) Judge<Le(x, y)> { verdict := No }
"#,
        ),
    ]);
    // The carrier, qualified: which `Le` is occupied.
    assert!(e.contains("`dup::Le` already has an instance"), "{e}");
    // The class, qualified: which `Judge`.
    assert!(e.contains("`cls::Judge`"), "{e}");
    // The occupant, qualified: which declaration is in the way.
    assert!(e.contains("`dup::Le::Judge`"), "{e}");
    assert!(e.contains("resolved"), "{e}");
}

// ---------------------------------------------------------------------------
// 4: the canonical name as a reference.

/// `left::Le::Judge` — the module, the carrier, the class. The canonical name
/// is an ordinary declaration of the declaring module, so the external face is
/// the module-qualified path and it is *writable*: three segments, joined by
/// the lexer, split at the first `::` by `names::split_qual`.
///
/// Its members and the projection spelling are checked in the same file,
/// because layer 1 §4.2 promised the two reach the same value and until this
/// round only one of them could be written.
#[test]
fn a_three_segment_canonical_name_resolves() {
    ok(&[
        ("cls", CLASSES),
        (
            "left",
            r#"
import cls;
inductive L { L0 }
fn Le(x, y: L) -> Type { True }
instance(x, y: L) Judge<Le(x, y)> {
    fn verdict() -> Verdict<Le(x, y)> { Yes(trivial) }
}
"#,
        ),
        (
            "use",
            r#"
import cls;
import left;

// The instance value, by its qualified canonical name. Its value binders are
// instance-implicit, so the expected type is what fills them.
fn dict(x, y: left::L) -> Judge<left::Le(x, y)> { left::Le::Judge() }

// A MEMBER, by its four-segment name — registered since layer 1 and unwritable
// until the lexer joined a chain.
fn by_name(x, y: left::L) -> Verdict<left::Le(x, y)> { left::Le::Judge::verdict() }

// The projection spelling §4.2 offered instead, all these months. Through
// `dict`, because a projection's receiver is an *inference* position and this
// instance's binders are recovered from the expected type.
fn by_proj(x, y: left::L) -> Verdict<left::Le(x, y)> { dict(x, y).verdict }

// And they are the same value, which is what §4.2 always claimed.
theorem the_two_spellings_agree(x, y: left::L): by_name(x, y) = by_proj(x, y) { refl }
"#,
        ),
    ]);
}

/// The negative: a three-segment path whose last segment names nothing is a
/// miss, not a silent success. Without it the test above could be passing on a
/// name that resolved by some other route.
#[test]
fn a_three_segment_name_with_no_declaration_is_a_miss() {
    let e = bad(&[
        ("cls", CLASSES),
        ("left", &format!("import cls;\n{LEFT}")),
        (
            "use",
            r#"
import cls;
import left;
fn nope(x, y: left::L) -> Verdict<left::Le(x, y)> { left::Le::Judge::nosuch() }
"#,
        ),
    ]);
    assert!(e.contains("left::Le::Judge::nosuch"), "{e}");
}

// ---------------------------------------------------------------------------
// 5: the lexer's boundary.

/// The join is a **chain** now, and the two neighbours it must not have eaten
/// are the import-list form (`m::{a, b}`, where `::` is followed by `{`) and
/// the applied-owner path (`Impl(add, R)::refines`, where `::` follows a `)`
/// and so never reaches the identifier scanner at all).
#[test]
fn the_lexer_joins_a_chain_and_stops_where_it_did() {
    let one = |s: &str| match &lex(s).expect("lexes")[0].kind {
        TokKind::Ident(n) => n.clone(),
        other => panic!("expected an identifier, got {other:?}"),
    };
    assert_eq!(one("nat"), "nat");
    assert_eq!(one("nat::Nat::sub"), "nat::Nat::sub");
    assert_eq!(one("int::Int::Le::Decide"), "int::Int::Le::Decide");
    assert_eq!(one("int::Int::Le::Decide::dec"), "int::Int::Le::Decide::dec");
    // `_` starts a segment; a digit does not.
    assert_eq!(one("a::_b::c9"), "a::_b::c9");
    // The import-list form: `::` followed by `{` does not join, at any depth.
    let toks = lex("import nat::{Le};").expect("lexes");
    assert!(
        matches!(&toks[1].kind, TokKind::Ident(n) if n == "nat"),
        "{:?}",
        toks[1].kind
    );
    assert!(matches!(&toks[2].kind, TokKind::ColonColon), "{:?}", toks[2].kind);
    // A trailing `::` with nothing to join to is still the standalone token.
    let toks = lex("a::").expect("lexes");
    assert!(matches!(&toks[0].kind, TokKind::Ident(n) if n == "a"), "{:?}", toks[0].kind);
    assert!(matches!(&toks[1].kind, TokKind::ColonColon), "{:?}", toks[1].kind);
}

/// The applied-owner path still parses and still resolves: it is the one
/// production that reads a standalone `::` after an expression, and the chain
/// join would have broken it if the owner had ever been a bare identifier.
#[test]
fn an_applied_owner_path_is_unaffected() {
    let toks = lex("Impl(add, BinNat)::refines").expect("lexes");
    assert!(
        matches!(&toks[0].kind, TokKind::Ident(n) if n == "Impl"),
        "{:?}",
        toks[0].kind
    );
    let cc = toks.iter().position(|t| matches!(t.kind, TokKind::ColonColon));
    // `Impl` `(` `add` `,` `BinNat` `)` `::` — the seventh token, after the
    // closing paren the identifier scanner never sees.
    assert_eq!(cc, Some(6), "the `::` after `)` stays a token of its own: {toks:?}");
}
