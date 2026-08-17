//! `lib/list_algos.hthr` — the list-algorithm exercise file
//! (`issues/list-algorithms-exercise.md`), checked as a module closure.
//!
//! Written when the traits adoption round (2026-08-07) moved `cong_cons`,
//! `append_nil` and `append_assoc` out of it and into `lib/std/list.hthr`, and
//! found that nothing in the suite would have noticed if the move had broken
//! the file: `lib/std/list.hthr`, `lib/std/option.hthr` and `lib/list_algos.hthr`
//! had no Rust coverage at all — only `nat` and `bool` did, through
//! `tests/ir_v1.rs`. The CLI's fixture tests exercise the *loader*, not these
//! files.
//!
//! One test, deliberately: the claim is that the closure checks, and the
//! interesting content (`rev_involutive`, insertion sort's sortedness proof)
//! is proof content that either checks or does not. Cheap — under a second of
//! the suite's budget.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGOS: &str = include_str!("../../../lib/list_algos.hthr");

#[test]
fn the_list_algorithms_check() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in
        [("logic", LOGIC), ("bool", BOOL), ("nat", NAT), ("option", OPTION), ("list", LIST), ("list_algos", ALGOS)]
    {
        if let Err(err) = e.elab_module_source(name, src) {
            let msg = match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            };
            panic!("{name} did not check: {msg}");
        }
    }
}
