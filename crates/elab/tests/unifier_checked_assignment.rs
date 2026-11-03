//! The unifier's one write (issues/unifier-checked-assignment.md,
//! `crates/elab/src/solution_check.rs`): a solution is held to its slot's
//! type when it is written, and a slot already solved that a later argument's
//! type would make something else is said beside the mismatch it causes.

use heather_elab::{ElabError, Elaborator};

const APPLY: &str = "
    fn apply<A, B>(x: A, f: A → B) → B { f(x) }
    inductive Flag { On, Off }
    fn flip(b: Flag) → Flag { b }
";

fn refusal(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(src);
    let Err(ElabError::Elab { msg, .. }) = r else { panic!("expected a rejection, got {r:?}") };
    msg
}

/// `apply(n, flip)`: the first argument solves `A := Nat`; `flip`'s type
/// `Flag → Flag` meets `A → ?B` with `A` already solved, so the first write
/// wins and only the gate finds the mismatch. The message names the
/// implicit both arguments decided, and what each said.
#[test]
fn a_disagreement_about_a_solved_implicit_is_named() {
    let src = format!("{APPLY} fn g(n: Nat) → Flag {{ apply(n, flip) }}");
    let msg = refusal(&src);
    assert!(msg.contains("but `Nat -> Flag` is expected here"), "{msg}");
    assert!(
        msg.contains("`A` was inferred as `Nat` from an earlier argument, and this argument's type would make it `Flag`"),
        "{msg}"
    );
}

/// The positive control: the same call where both arguments agree.
#[test]
fn agreeing_arguments_elaborate() {
    let src = format!("{APPLY} fn g(b: Flag) → Flag {{ apply(b, flip) }}");
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(&src).expect("both arguments say `A = Flag`");
}
