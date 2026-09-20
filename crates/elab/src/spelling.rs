//! Reading a pair, an injection or a projection **whichever spelling it is
//! written in** (`docs/intro-by-type-design.md` §4.2).
//!
//! Since stage 1 the kernel has five *checked spellings* —
//! `pair@`/`inl@`/`inr@`/`fst@`/`snd@` — that carry the type the term was
//! checked at in place of that type's components. They are the same terms:
//! the evaluator maps them onto the same values, β fires on either, and
//! conversion never reads either one's annotation. So every **shape-only**
//! reader in the elaborator — the ones that ask "is this an injection, and
//! into which summand" or "what are this tuple's fields" — must accept both,
//! and the three views here are how, rather than by a doubled `match` arm at
//! forty sites.
//!
//! A reader that genuinely needs the *components* (`lgg`'s anti-unification,
//! `matching`'s `field_rewrap`) is not served here: it has a decision to make
//! about the annotation and must make it in the open. The principle from
//! §4.2 stands for both kinds — the annotation is a spelling every reader
//! already accepts from a user-written type, so a broken reader is fixed in
//! the reader.

use std::sync::Arc as Rc;

use heather_kernel::term::Term;

/// The injected value of either injection spelling, with `true` for `inl`.
pub(crate) fn inj_of(t: &Term) -> Option<(bool, &Rc<Term>)> {
    match t {
        Term::Inl { val, .. } | Term::InlAt { val, .. } => Some((true, val)),
        Term::Inr { val, .. } | Term::InrAt { val, .. } => Some((false, val)),
        _ => None,
    }
}

/// The two components of either pair spelling.
pub(crate) fn pair_of(t: &Term) -> Option<(&Rc<Term>, &Rc<Term>)> {
    match t {
        Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => Some((fst, snd)),
        _ => None,
    }
}

/// Is this a pair, in either spelling?
pub(crate) fn is_pair(t: &Term) -> bool {
    matches!(t, Term::Pair { .. } | Term::PairAt { .. })
}

/// Is this an injection, in either spelling?
pub(crate) fn is_inj(t: &Term) -> bool {
    matches!(
        t,
        Term::Inl { .. } | Term::Inr { .. } | Term::InlAt { .. } | Term::InrAt { .. }
    )
}

/// The pair a projection projects, with `true` for `fst`.
pub(crate) fn proj_of(t: &Term) -> Option<(bool, &Rc<Term>)> {
    match t {
        Term::Fst { pair, .. } | Term::FstAt { pair, .. } => Some((true, pair)),
        Term::Snd { pair, .. } | Term::SndAt { pair, .. } => Some((false, pair)),
        _ => None,
    }
}
