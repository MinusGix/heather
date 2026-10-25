//! `lib/std/data/bounded_list.hthr` — capacity-bounded lists, their stack API,
//! and the first ordinary client of propositional truncation. The stack laws
//! are the module's own theorems, which the whole-library gate checks
//! (`crates/cli/tests/library.rs`); the closed computations are
//! `lib/_tests/std/data/bounded_list_tests.hthr` (docs/test-value-audit.md
//! §3.4). What is left is the refusal: a value over its capacity.

use crate::support::{self, Refusal};

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const BOUNDED_LIST: &str = include_str!("../../../lib/std/data/bounded_list.hthr");

/// The fit witness at capacity 0 and one element is a proof of `False`.
#[test]
fn an_invalid_fit_witness_is_rejected() {
    let mut e = support::library(&[
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("bounded_list", BOUNDED_LIST),
    ]);
    support::assert_refused(
        &mut e,
        "bad",
        "import bounded_list; import list;
        fn impossible() -> BoundedList<Nat> {
            BoundedList(capacity := 0, contents := Cons(1, Nil), fit := squash(trivial))
        }",
        Refusal::Says("`trivial` proves `True`, but `False` is expected here"),
    );
}
