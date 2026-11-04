//! The unifier's δ-lazy step at a rigid head mismatch
//! (issues/unifier-lazy-delta.md): a subject headed by a definition is
//! unfolded to its next head and compared again, as the kernel's conversion
//! does, instead of learning nothing and leaving the call to a whnf retry.

use heather_elab::{ElabError, Elaborator};

const FLAGS: &str = "
    inductive Flag { On, Off }
    fn both(a: Flag, b: Flag) → Flag { match a { On => b, Off => Off } }
    fn swapped(n: Flag, m: Flag) → Flag { both(m, n) }
    fn left({a, b: Flag}, h: both(a, b) = On) → Flag { a }
";

/// `both(?a, ?b)` against `swapped(n, m)`: the heads differ, `swapped`
/// unfolds to `both(m, n)`, and the implicits are read off that. Before,
/// the read learned nothing, and the whnf retry of an `Id` type is the same
/// `Id`, so `a` was not inferred
/// (issues/unifier-spine-across-distinct-heads.md, its second reading).
#[test]
fn a_definition_at_a_head_mismatch_is_unfolded_to_the_pattern_head() {
    let src = format!("{FLAGS} fn t(n, m: Flag, h: swapped(n, m) = On) → Flag {{ left(h) }}");
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(&src).expect("`swapped(n, m)` unfolds to `both(m, n)`");
}

/// The unfolding reads only what conversion would: a subject that never
/// reaches the pattern's head teaches nothing, and the call is refused for
/// the implicit it could not infer, not for a wrong solution.
#[test]
fn a_subject_that_never_meets_the_pattern_teaches_nothing() {
    let src = format!(
        "{FLAGS} fn other(n: Flag) → Flag {{ n }}
         fn t(n: Flag, h: other(n) = On) → Flag {{ left(h) }}"
    );
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(&src);
    let Err(ElabError::Elab { msg, .. }) = r else { panic!("expected a refusal, got {r:?}") };
    assert!(msg.contains("`a`") || msg.contains("`b`"), "{msg}");
}
