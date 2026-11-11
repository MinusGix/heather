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
//! on this tree): the six `@` rules of `Tc::tm_infer_at`, and the Π view
//! a *checking* λ takes of a `Sel` expected type. `app@` forms one only when
//! its head's type is not already a syntactic Π
//! (`docs/app-by-head-type-design.md` §3.1). No other rule constructs
//! one — `app`'s result is `cod[arg/x]` from its own annotations, `fst`'s is
//! its annotation, the four λ inference arms materialize. So on a
//! declaration with no `@` form the checker's behaviour is byte-identical to
//! the one before this module existed, which is the stage-1b gate.

use crate::rc::Rc;

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
    /// `T[a/x]` of `Π(x:S). T` — the result of a checked application
    /// `app@(f; a)` whose head's type needed reduction
    /// (`docs/app-by-head-type-design.md` §3.2). The Π analogue of
    /// [`Sel::Snd`], and scoped where its `of` is, unlike [`Sel::Cod`].
    App(Rc<Term>),
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
    /// Syntax scoped in a **prefix** of Γ, the one of length `depth`: a
    /// context entry's type as the entry holds it. Spelling it in the
    /// ambient scope is a shift of the whole type, and the value domain
    /// needs none (levels again), so the head of a projection spine that is
    /// a variable is described this way and never shifted
    /// (`issues/projection-description-quadratic.md`). Formed only as the
    /// `of` of a selection, by `Tc::projection_at_spine`.
    At { ty: Rc<Type>, depth: u32 },
}

impl ITy {
    /// The syntax, when there is some. A rule that needs syntax and finds
    /// `None` goes through `Tc::materialize`.
    #[inline]
    pub(crate) fn as_syn(&self) -> Option<&Type> {
        match self {
            ITy::Owned(t) => Some(t),
            ITy::Syn(t) => Some(t),
            ITy::Sel { .. } | ITy::At { .. } => None,
        }
    }

    pub(crate) fn is_syn(&self) -> bool {
        !matches!(self, ITy::Sel { .. } | ITy::At { .. })
    }

    /// This description, borrowed — the currency the *checking* direction
    /// takes. See [`ITyRef`].
    #[inline]
    pub(crate) fn as_ref(&self) -> ITyRef<'_> {
        ITyRef::Ity(self)
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
            (ITy::At { ty: a, depth: d }, ITy::At { ty: b, depth: e }) => {
                d == e && (Rc::ptr_eq(a, b) || a == b)
            }
            // A shortcut may say no: syntax in a prefix against syntax in
            // the ambient scope is left to conversion.
            (ITy::Sel { .. } | ITy::At { .. }, _) | (_, ITy::Sel { .. } | ITy::At { .. }) => false,
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

/// A **borrowed** expected type: what the *checking* direction passes.
///
/// `Tc::tm_check` never stores its expected type — it views it, whnfs it, or
/// hands it to `Tc::conv_ty` — so it does not need to own one, and stage 1b
/// made it pay for one anyway: each of the ~86 call sites of the two
/// `tm_check` wrappers constructed a 72-byte [`ITy`] temporary in the
/// *caller's* frame (they are `inline(always)`), and the `Rc<Type>` sites
/// paid an atomic refcount pair per term node on top. That is the whole of
/// the measured per-node constant
/// (`issues/ity-widens-the-checker-per-node-constant.md`): it moved
/// `tm_check_inner`'s frame from 296 to 712 bytes, which is the stack row,
/// and put an `Arc` increment and decrement on the hot path of every rule
/// that checks a subterm, which is the routine corpus's.
///
/// Two words, `Copy`, constructed by a tag write: the checking direction now
/// builds nothing at all in the common case. [`ITyRef::Syn`] is a spelling
/// the caller already holds — by far the common case, and never a selection;
/// [`ITyRef::Ity`] is a description the caller already holds, which may be
/// any [`ITy`] including a selection, and is what keeps the cold `@` path
/// from having to rebuild one.
#[derive(Clone, Copy)]
pub(crate) enum ITyRef<'a> {
    /// Syntax the caller holds.
    Syn(&'a Type),
    /// A description the caller holds.
    Ity(&'a ITy),
}

impl<'a> ITyRef<'a> {
    /// The syntax, when there is some — [`ITy::as_syn`] through the borrow.
    #[inline]
    pub(crate) fn as_syn(self) -> Option<&'a Type> {
        match self {
            ITyRef::Syn(t) => Some(t),
            ITyRef::Ity(t) => t.as_syn(),
        }
    }

    /// The description, when the caller had one. `None` means the borrow is
    /// a bare spelling, which is never a selection — so a caller that needs
    /// an [`ITy`] on the selection path may take this and `expect` it there.
    #[inline]
    pub(crate) fn as_ity(self) -> Option<&'a ITy> {
        match self {
            ITyRef::Syn(_) => None,
            ITyRef::Ity(t) => Some(t),
        }
    }
}

/// Exactly [`ITy`]'s equality, seen through the borrows: the reflexivity
/// shortcut of [`crate::typing::Tc::conv_ty`], unchanged to the counter.
impl PartialEq for ITyRef<'_> {
    #[inline]
    fn eq(&self, other: &ITyRef<'_>) -> bool {
        match (self.as_syn(), other.as_syn()) {
            (Some(a), Some(b)) => std::ptr::eq(a, b) || a == b,
            // At least one side is a selection, so both must be, and both
            // sides then have an `ITy` to compare.
            _ => match (self.as_ity(), other.as_ity()) {
                (Some(a), Some(b)) => a == b,
                _ => false,
            },
        }
    }
}

impl Eq for ITyRef<'_> {}
