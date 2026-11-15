//! `lib/std/text/char.hthr` and `lib/std/text/string.hthr` — Unicode scalar
//! values and sequences of them as *specification* types
//! (docs/library/string-char-design.md): the refusals that need the checker. Every
//! law at a literal and at a neutral string, and the `¬` theorems for the
//! wrong values (a wrong character, split or length, a false equation, a code
//! outside `scalar`), are `lib/_tests/std/text/string_tests.hthr`, which the
//! whole-library gate checks (`crates/cli/tests/library.rs`;
//! docs/test-value-audit.md §3.4).

use crate::support::{self, Refusal};
use heather_elab::Elaborator;

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const CHAR: &str = include_str!("../../../lib/std/text/char.hthr");
const STRING: &str = include_str!("../../../lib/std/text/string.hthr");

const PREAMBLE: &str = "import logic;\nimport bool;\nimport nat;\nimport list;\nimport char;\nimport string;\n";

fn elaborated() -> Elaborator {
    support::library(&[
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("char", CHAR),
        ("string", STRING),
    ])
}

fn refused(body: &str, why: Refusal) {
    support::assert_refused(&mut elaborated(), "probe", &format!("{PREAMBLE}{body}"), why);
}

/// Out of range is unwritable rather than wrong: there is no third index
/// into a two-character string.
#[test]
fn an_index_past_the_end_is_unwritable() {
    refused("theorem bad(): \"ab\".nth(FS(FS(FZ))) = 'a' { refl }\n", Refusal::Says("`Fin(0)` is empty, so it has no index"));
}

/// `decide` builds no witness for a code outside `scalar`, and has no closed
/// decision for an equation at a neutral string. The refusal names the goal
/// with its literals as they were written, not the kernel encoding a
/// character's `scalar` witness and the list literal's vector used to leak
/// into it (issues/decide-refusal-spells-string-literal-encoding.md).
#[test]
fn decide_proves_only_closed_true_goals() {
    let why = Refusal::Says("whose decision here is not `Inl`");
    refused("theorem bad(): scalar(55296) { decide }\n", why);
    refused("theorem bad(): scalar(1114112) { decide }\n", why);
    refused("theorem bad(s: String): s = \"hi\" { decide }\n", Refusal::Says("resolved `Decide<s = \"hi\">`"));
    refused("theorem bad(c: Char): c = 'h' { decide }\n", Refusal::Says("resolved `Decide<c = 'h'>`"));
    refused("theorem bad(s: String): s = \"\" { decide }\n", Refusal::Says("resolved `Decide<s = \"\">`"));
    refused("theorem bad(xs: List<Char>): xs = ['a', 'b'] { decide }\n", Refusal::Says("resolved `Decide<xs = ['a', 'b']>`"));
}

/// A literal is spelled back with the lexer's escapes: the delimiter, the
/// backslash and the named control characters escaped, anything else as
/// itself.
#[test]
fn a_spelled_literal_keeps_its_escapes() {
    refused(
        "theorem bad(s: String): s = \"a\\nb\\\"c\\\\d'é\" { decide }\n",
        Refusal::Says(r#"resolved `Decide<s = "a\nb\"c\\d'é">`"#),
    );
    refused("theorem bad(c: Char): c = '\\'' { decide }\n", Refusal::Says(r"resolved `Decide<c = '\''>`"));
}
