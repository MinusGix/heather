//! `lib/std/text/char.hthr` and `lib/std/text/string.hthr` — Unicode scalar
//! values and sequences of them as *specification* types
//! (docs/string-char-design.md): the refusals that need the checker. Every
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
/// decision for an equation at a neutral string.
#[test]
fn decide_proves_only_closed_true_goals() {
    let why = Refusal::Says("whose decision here is not `Inl`");
    refused("theorem bad(): scalar(55296) { decide }\n", why);
    refused("theorem bad(): scalar(1114112) { decide }\n", why);
    refused("theorem bad(s: String): s = \"hi\" { decide }\n", why);
}
