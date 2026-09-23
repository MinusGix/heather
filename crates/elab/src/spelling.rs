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

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};

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

/// The head and argument of either application spelling — `app` with its
/// annotations or the checked `app@(f; a)`, whose Π is the one the head
/// infers (`docs/app-by-head-type-design.md` §6.2). A reader that needs the
/// Π itself has a decision to make and does not come here.
pub(crate) fn app_of(t: &Term) -> Option<(&Rc<Term>, &Rc<Term>)> {
    match t {
        Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => Some((fun, arg)),
        _ => None,
    }
}

/// Is this an application, in either spelling?
pub(crate) fn is_app(t: &Term) -> bool {
    matches!(t, Term::App { .. } | Term::AppAt { .. })
}

/// `f a₁ … aₙ` as its head and its arguments, outermost last, through
/// either spelling at every node.
pub(crate) fn app_spine(t: &Term) -> (&Term, Vec<&Rc<Term>>) {
    let mut args = Vec::new();
    let mut head = t;
    while let Some((fun, arg)) = app_of(head) {
        args.push(arg);
        head = fun;
    }
    args.reverse();
    (head, args)
}

/// An application the elaborator **constructs** from a Π it holds, outside
/// the surface-call path (`docs/app-by-head-type-design.md` §6.1, every
/// emitter switched): `app@(f; a)` unless the head is a λ, which infers only
/// if its body does and so keeps the annotated form. The annotations are
/// taken so a call site reads as the `app` it replaces and are dropped for
/// `app@`: its Π is the one the head infers.
///
/// Unconditional on the quotation state, because none of these builders
/// writes a `box` payload itself: a term pasted into a quotation goes through
/// the quote boundary's translator (`typing::spell_checked_in_code`), which
/// writes `app` back from the Π the checker read. Code that is *built* as a
/// payload (certgen's markers, the code recursor's branches) writes `app`.
pub(crate) fn checked_app(
    fun: Rc<Term>,
    dom_level: Level,
    cod_level: Level,
    dom: Rc<Type>,
    cod: Rc<Type>,
    arg: Rc<Term>,
) -> Term {
    if matches!(&*fun, Term::Lam { .. }) {
        Term::App { fun, dom_level, cod_level, dom, cod, arg }
    } else {
        Term::AppAt { fun, arg }
    }
}
