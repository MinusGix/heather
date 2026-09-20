//! **Deferred types**: what the checker passes between its rules
//! (`docs/intro-by-type-design.md` §3.2).
//!
//! An inferred or expected type is either syntax — what every rule but the
//! five checked spellings produces — or a *description* of a component of
//! something that reduces to a former, un-spelled. The description is the
//! "reduction provenance" of
//! `docs/conversion-query-traversal-design.md` §10.3 written down as a datum
//! instead of computed: `fst@(T; p)` infers *the first component of whatever
//! `T` reduces to* without ever spelling it, which is the exponential object
//! this round exists to stop constructing.
//!
//! Three properties are load-bearing and are why this is not a `Type`
//! variant and not a value:
//!
//! - **Arena-free.** A closure lives in a [`crate::value::ValueArena`], and
//!   an arena that outlives a conversion query costs +9.3 GB on
//!   `probes/str/p10.hthr` (the stage-1b measurement on the owning issue).
//!   An [`ITy`] is plain `Rc` and is freed when the rule that formed it
//!   returns.
//! - **Linear.** A `Sel` chain of length k over a `Syn` is k nodes,
//!   regardless of what the described type reduces to.
//! - **Not a kernel type.** `ITy` is `pub(crate)` and never reaches
//!   [`crate::term::Type`], so no walker, no image tag, no merkle hasher and
//!   no recursor branch gains an arm. Every rule that *builds* a type still
//!   builds syntax; a description that has to become one goes through
//!   `Tc::materialize` (§3.5), which is the current checker's answer and is
//!   counted.
//!
//! **Where a `Sel` arises, and only there** (§3.2, verified by construction
//! on this tree): the five `@` rules of `Tc::tm_infer_inner`, and the Π view
//! a *checking* λ takes of a `Sel` expected type. No other rule constructs
//! one — `app`'s result is `cod[arg/x]` from its own annotations, `fst`'s is
//! its annotation, the four λ inference arms materialize. So on a
//! declaration with no `@` form the checker's behaviour is byte-identical to
//! the one before this module existed, which is the stage-1b gate.

use std::sync::Arc as Rc;

use crate::level::Level;
use crate::term::{LocalCtx, LocalSubst, Term, Type};

/// Which component of a former a description selects.
///
/// `Snd` carries the *term* the Σ's codomain is instantiated at, not its
/// value: a value would need an arena, and the term is what the rule has.
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum Sel {
    /// `S` of `Σ(x:S). U`.
    Fst,
    /// `U[a/x]` of `Σ(x:S). U`.
    Snd(Rc<Term>),
    /// `A` of `A + B`.
    Lhs,
    /// `B` of `A + B`.
    Rhs,
    /// `S` of `Π(x:S). T`.
    Dom,
    /// `T` of `Π(x:S). T`, **under the binder** — the one selection whose
    /// result is scoped one deeper than its `of`.
    Cod,
}

impl Sel {
    /// The Γ-length `of` is scoped at, given the length the *selection* is
    /// scoped at. Only [`Sel::Cod`] moves the scope.
    pub(crate) fn of_depth(&self, at_depth: u32) -> u32 {
        match self {
            Sel::Cod => at_depth.saturating_sub(1),
            _ => at_depth,
        }
    }
}

/// An inferred or expected type: syntax, or an un-spelled selection.
///
/// Syntax comes in two shapes and the distinction is a **measured** one, not
/// a tidiness: `Tc::tm_infer` produces one of these per term node, and
/// boxing each in an `Rc` cost **4.1× on `nat/check-numeral`** — a benchmark
/// whose entire body is inference over a `Succ` chain, so one `malloc` per
/// node against almost no other work is the whole time. [`ITy::Owned`] is
/// the value the rule already had on its stack, moved; [`ITy::Syn`] is for
/// syntax that is genuinely shared (an `@` annotation, a component the
/// rewriter handed back behind an `Rc`). Nothing else distinguishes them —
/// `as_syn` and the equality below treat the two as one case.
#[derive(Clone)]
pub(crate) enum ITy {
    /// What every rule outside the checked spellings produces: the type it
    /// built, on the stack, allocation-free.
    Owned(Type),
    /// Shared syntax.
    Syn(Rc<Type>),
    /// *The component `sel` of whatever `of` reduces to*, where `of` denotes
    /// a type in a Γ of length `sel.of_depth(at_depth)` and the selection
    /// itself denotes one in a Γ of length `at_depth`. The lengths travel
    /// with the description because it is formed in one scope and may be
    /// evaluated in a longer one; variables are de Bruijn *levels* in the
    /// value domain, so the length is all that is needed and no weakening is
    /// ever paid.
    Sel { of: Rc<ITy>, sel: Sel, at_depth: u32 },
}

impl ITy {
    /// The syntax, when there is some. A rule that needs syntax and finds
    /// `None` goes through `Tc::materialize`.
    #[inline]
    pub(crate) fn as_syn(&self) -> Option<&Type> {
        match self {
            ITy::Owned(t) => Some(t),
            ITy::Syn(t) => Some(t),
            ITy::Sel { .. } => None,
        }
    }

    pub(crate) fn is_syn(&self) -> bool {
        !matches!(self, ITy::Sel { .. })
    }
}

/// Structural equality, which is [`crate::typing::Tc::conv_ty`]'s
/// reflexivity shortcut: on syntax it is the α-test the checker has always
/// run, and two equal selections are the same type by Determinacy. The
/// shape a value is *held* in — owned or shared — is not part of the
/// judgment, so the two mix.
impl PartialEq for ITy {
    #[inline]
    fn eq(&self, other: &ITy) -> bool {
        match (self, other) {
            (
                ITy::Sel { of: a, sel: s, at_depth: d },
                ITy::Sel { of: b, sel: t, at_depth: e },
            ) => d == e && s == t && (Rc::ptr_eq(a, b) || a == b),
            (ITy::Sel { .. }, _) | (_, ITy::Sel { .. }) => false,
            _ => match (self.as_syn(), other.as_syn()) {
                (Some(a), Some(b)) => std::ptr::eq(a, b) || a == b,
                _ => false,
            },
        }
    }
}

impl Eq for ITy {}

/// The head of a weak head normal type as the checker's rules need it: the
/// three formers whose components a rule descends into, with those
/// components as descriptions, and one catch-all.
///
/// Deliberately *not* a copy of [`crate::conv::dom::TyView`]: conversion
/// views every former because it compares them, while the checker only ever
/// asks "is this a Π / Σ / sum, and what are its parts". Everything else a
/// rule needs to match on comes back through `Tc::whnf` as ordinary syntax.
pub(crate) enum TyForm {
    Pi { dom_level: Level, cod_level: Level, dom: ITy, cod: ITy },
    Sigma { fst_level: Level, snd_level: Level, fst: ITy, snd: SndOf },
    Sum { lhs_level: Level, rhs_level: Level, lhs: ITy, rhs: ITy },
    /// Any other former, including the two neutral type forms. The rules
    /// that view a type answer [`crate::typing::TypeError::HeadMismatch`].
    Other,
}

/// A Σ's second component before the term it is instantiated at is known.
pub(crate) enum SndOf {
    /// `U` under the Σ's binder, as syntax: the rewriter's answer, and what
    /// the eager mode always produces.
    Syn(Rc<Type>),
    /// The description the selection will be taken of, and the Γ-length it
    /// is formed at.
    Sel(Rc<ITy>, u32),
}

impl SndOf {
    /// `U[a/x]`.
    pub(crate) fn at(&self, gamma: &LocalCtx, a: Rc<Term>) -> ITy {
        match self {
            SndOf::Syn(u) => {
                ITy::Owned(u.apply_local(&LocalSubst::id(gamma).extended(a)))
            }
            SndOf::Sel(of, at_depth) => {
                ITy::Sel { of: Rc::clone(of), sel: Sel::Snd(a), at_depth: *at_depth }
            }
        }
    }
}
