//! Anti-unification — the least general generalization of two kernel terms,
//! constrained to abstract **one** given pair of witnesses
//! (issues/congruence-by-anti-unification.md §3).
//!
//! Given an expected equation `X = Y` and a proof `p : s = t`, the function
//! `f` with `f(s) = X` and `f(t) = Y` is recovered by walking `X` and `Y` in
//! parallel: agreeing nodes are kept, and a position where they *differ*
//! becomes the abstraction variable — but **only** if the two sides there are
//! exactly `s` and `t`. Anything else is a loud failure rather than a guess,
//! which is what keeps this a computation rather than a heuristic (§4: the
//! generalization is not *chosen* among candidates, it is *computed*).
//!
//! Deliberate properties, each of them a decision in the issue's interim
//! design section:
//!
//! - **"Exactly `s`" is `==`** — structural equality on de Bruijn kernel
//!   terms, which *is* α-equality here. No conversion call: that keeps the
//!   solver linear and terminating, keeps failure loud, and keeps an
//!   unbounded conversion out of every `cong` elaboration (decision 2).
//! - **Under binders: shift or fail** (decision 3). A hole under `k` binders
//!   matches only if the differing subterms are `s`/`t` weakened by `k`, and
//!   the abstraction variable lands at index `k`. Nothing is captured and
//!   nothing is strengthened by cleverness.
//! - **Zero holes is fine** (decision 5): `X ≡ Y` gives the constant
//!   function, which is a correct — if uninteresting — congruence.
//!
//! This module is deliberately standalone: it has no elaborator state, no
//! spans and no `Cx`. The elaborator hook that calls it is scheduled for
//! removal when the layer-m tactic surface arrives (§5), and that tactic
//! wants exactly this function and exactly these tests.
//!
//! ## Two deviations from a textbook LGG, both stated
//!
//! 1. **The witness pair is checked at the *outermost* position where it
//!    matches**, before descending. A textbook LGG of `Succ(0)` and `Succ(1)`
//!    is `Succ(□)`; if the proof happens to be `p : Succ(0) = Succ(1)` this
//!    module answers `λz. z` instead, because it tests the whole node against
//!    `(s, t)` first. Both are correct solutions of `f(s) = X`, `f(t) = Y`;
//!    testing outermost-first only ever *accepts more*, and the result stays
//!    a function of the inputs alone, which is the determinism property §4
//!    actually needs.
//! 2. **`s ≡ t` is handled up front**: the answer is the constant function
//!    and `X ≡ Y` is required. Abstracting occurrences would be equally
//!    correct but less specific, and the constant is what a textbook LGG of
//!    two identical terms gives.
//!
//! Unsupported heads (layer-m code formers: `box`, `letbox`, the code
//! recursors, universe abstraction) are a *failure*, never a silent
//! agreement — they can only be reached by terms that already differ, so
//! declining is the conservative answer.

use std::fmt;
use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalVar, Term, Type};

/// Where the walk stopped, as **data**.
///
/// The failure used to be a `String` built with `{:?}` on four kernel terms,
/// which at a lowered inductive is four multi-thousand-character walls with the
/// one useful fact — *which* subterm did not match — not recoverable from them
/// (issues/lgg-diagnostic-dumps-kernel-terms.md). Nothing here is a rendered
/// term: rendering wants `display.rs`'s speller and a `Cx`, and this module
/// deliberately has neither, so the elaborator does that half and this one
/// reports the position.
pub(crate) struct Mismatch {
    /// The head formers walked from the goal's root down to — but not
    /// including — the node the walk stopped at, outermost first.
    pub path: Vec<&'static str>,
    /// The head former of each side at that node. The whole of why it stopped:
    /// either they are different formers, or they are the same one with
    /// annotations that differ.
    pub sides: (&'static str, &'static str),
    /// The two subterms at that node, when it is a term position. `None` at a
    /// *type* position, where a caller that wants to spell them has a `Type`
    /// and not a `Term`.
    pub at: Option<(Term, Term)>,
    /// Binders between the goal's root and the stopping node — what
    /// [`crate::strengthen_tm`] must drop for [`Self::at`] (scoped in `Γ`
    /// plus those binders) to be readable in the goal's own context.
    pub depth: u32,
    /// The degenerate case: the proof's endpoints are the same term, so the
    /// only congruence is the constant one and the goal's sides had to agree
    /// outright (decision 5's second sentence). `path` is empty.
    pub endpoints_agree: bool,
}

impl fmt::Debug for Mismatch {
    /// [`fmt::Display`], deliberately: a derived `Debug` would print
    /// [`Mismatch::at`]'s two kernel terms, which is the wall this type
    /// exists to stop — and `.expect()` in a test is a user of `Debug`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Mismatch {
    /// The term-free half of the message: the position, and nothing that
    /// needs a context to read. [`crate::Elaborator`] appends the spelled
    /// expected type and endpoints.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.endpoints_agree {
            return write!(
                f,
                "cannot generalize: the proof's endpoints are the same term, so the only \
                 congruence is the constant one — but the goal's two sides differ, at \
                 `{}` against `{}`",
                self.sides.0, self.sides.1
            );
        }
        // `{:#}` is the *phrase* — just the position, for a caller that is
        // already mid-sentence (`crate::Elaborator::cong_invisible_difference`).
        if f.alternate() {
            if self.path.is_empty() {
                return write!(f, "at the root, `{}` against `{}`", self.sides.0, self.sides.1);
            }
            return write!(
                f,
                "under `{}` at `{}` against `{}`",
                self.path.join(" ▸ "),
                self.sides.0,
                self.sides.1
            );
        }
        write!(f, "cannot generalize: the goal's two sides agree ")?;
        if self.path.is_empty() {
            write!(f, "nowhere — they differ at the root, ")?;
        } else {
            write!(
                f,
                "down through `{}`, and differ under it ",
                self.path.join(" ▸ ")
            )?;
        }
        write!(f, "at `{}` against `{}`", self.sides.0, self.sides.1)
    }
}

/// The body of `f = λ z. body`, scoped in `Γ, z` — `Ok` exactly when every
/// position at which `x` and `y` differ is witnessed by `(s, t)`.
///
/// `x`, `y`, `s` and `t` are all scoped in `Γ`; `Err` locates the mismatching
/// position, for the caller to render and attach a span to.
pub(crate) fn lgg_body(x: &Term, y: &Term, s: &Term, t: &Term) -> Result<Term, Mismatch> {
    // `s ≡ t`: no position can be witnessed by a *difference*, so the only
    // generalization is the constant one — and it exists only if the goal's
    // two sides already agree (decision 5's second sentence).
    if s == t {
        if x != y {
            return Err(Mismatch {
                path: Vec::new(),
                sides: (former_tm(x), former_tm(y)),
                at: Some((x.clone(), y.clone())),
                depth: 0,
                endpoints_agree: true,
            });
        }
        return Ok(x.shift_local(1));
    }
    let mut lgg = Lgg {
        s: s.clone(),
        t: t.clone(),
        match_witness: true,
        conv: None,
        conv_fst: None,
        witness: Vec::new(),
        path: Vec::new(),
    };
    // The sides stay in `Γ` and only what the walk *keeps* is weakened into
    // `Γ, z`: a goal's reduct can be a large tree over a shared graph, and
    // weakening it whole up front cost more than the rest of `cong`
    // (issues/elab-whnf-family-transport-cost.md), where the walk itself
    // stops at the first difference.
    lgg.tm(x, y, 0)
}

/// [`lgg_body`] with the witness tested up to conversion: at a node where
/// the two sides differ and are not syntactically `(s, t)`, `conv` may still
/// make it the hole, if the node is under none of the walk's binders and the
/// sides convert to `(s, t)` there (in `Γ`, where the sides are scoped: they
/// are reducts that can be very large, and are never weakened or
/// strengthened to be compared). A difference anywhere else still stops the
/// walk.
///
/// What it is for: a goal reduced through two functions' eliminators has, in
/// place of the endpoints' calls, their reducts — and on a family a value
/// built by one function and taken apart by another carries annotations
/// spelled with the constructor's pieces as each function wrote them, so the
/// reducts are convertible to the endpoints and never syntactically equal to
/// them (`issues/cong-inference-through-iwf-w-children.md`). `conv` is asked
/// only at differing nodes, top-down, so in the common case once per side.
pub(crate) fn lgg_body_up_to_conversion(
    x: &Term,
    y: &Term,
    s: &Term,
    t: &Term,
    conv: &dyn Fn(&Term, &Term) -> bool,
    conv_fst: &dyn Fn(&Term, &Term, &Term, &Term, &Type, &Level) -> bool,
) -> Result<Term, Mismatch> {
    if s == t {
        return lgg_body(x, y, s, t);
    }
    let mut lgg = Lgg {
        s: s.clone(),
        t: t.clone(),
        match_witness: true,
        conv: Some(conv),
        conv_fst: Some(conv_fst),
        witness: Vec::new(),
        path: Vec::new(),
    };
    lgg.tm(x, y, 0)
}

/// The first position at which two terms differ **structurally** — implicit
/// arguments and type annotations included, which is the whole point of it.
///
/// This is [`lgg_body`]'s own walk with the witness test switched off, so
/// every difference is a stop: what comes back is the path to the first one
/// and the two formers there. `None` means the terms are `==`.
///
/// It exists for the diagnostic in [`crate::Elaborator::cong_mismatch`]. When
/// the position the LGG stopped at *spells* like the proof's endpoint and is
/// not it, the reason is invisible in surface syntax — a type spelled as a raw
/// code on one side and `El` of that code on the other, say — and the message
/// is a contradiction on its face without this
/// (issues/lgg-error-hides-the-implicit.md).
///
/// [`Mismatch::path`] and [`Mismatch::sides`] are what the `{:#}` rendering
/// reads; [`Mismatch::at`] and [`Mismatch::depth`] are scoped as for
/// [`lgg_body`], in `Γ` plus the binders walked.
pub(crate) fn first_difference(x: &Term, y: &Term) -> Option<Mismatch> {
    let mut lgg = Lgg {
        s: Term::Zero,
        t: Term::Zero,
        match_witness: false,
        conv: None,
        conv_fst: None,
        witness: Vec::new(),
        path: Vec::new(),
    };
    lgg.tm(x, y, 0).err()
}

struct Lgg<'c> {
    s: Term,
    t: Term,
    /// Whether [`Self::is_hole`] may answer `true`. Off in
    /// [`first_difference`], where there is no witness pair and every
    /// difference is meant to stop the walk.
    match_witness: bool,
    /// [`lgg_body_up_to_conversion`]'s witness test: given the two sides at
    /// a node under none of the walk's binders (scoped in `Γ`), whether they
    /// are `(s, t)` up to conversion there.
    conv: Option<&'c dyn Fn(&Term, &Term) -> bool>,
    /// The same test for a pair witness's first components (`a ≈ s₁`,
    /// `b ≈ t₁` at their type and level), for [`Self::projection_hole`].
    conv_fst: Option<&'c dyn Fn(&Term, &Term, &Term, &Term, &Type, &Level) -> bool>,
    /// `witness[k]` is `(s, t)` weakened past the `k` binders walked, the
    /// sides' scope there. Memoized because the walk asks for it at every
    /// node.
    witness: Vec<(Term, Term)>,
    /// The formers of the nodes currently being walked, outermost first —
    /// pushed on the way down and popped only on *success*, so at a failure it
    /// is exactly the path to the node that stopped
    /// (issues/lgg-diagnostic-dumps-kernel-terms.md).
    path: Vec<&'static str>,
}

/// The head former of a term, in the kernel's own vocabulary — one word, so a
/// path built from it stays readable at a lowered inductive, where the term
/// itself does not.
fn former_tm(t: &Term) -> &'static str {
    match t {
        Term::Var(_) => "variable",
        Term::Zero | Term::Succ(_) => "numeral",
        Term::Lam { .. } => "λ",
        Term::App { .. } | Term::AppAt { .. } => "application",
        Term::Pair { .. } => "pair",
        Term::Fst { .. } => "fst",
        Term::Snd { .. } => "snd",
        Term::Inl { .. } => "inl",
        Term::Inr { .. } => "inr",
        Term::PairAt { .. } => "pair@",
        Term::FstAt { .. } => "fst@",
        Term::SndAt { .. } => "snd@",
        Term::InlAt { .. } => "inl@",
        Term::InrAt { .. } => "inr@",
        Term::Case { .. } => "case",
        Term::Sup { .. } | Term::Supf { .. } => "constructor value",
        Term::ElimW { .. } | Term::ElimWf { .. } => "recursor",
        Term::ElimNat { .. } => "Nat eliminator",
        Term::ElimEmpty { .. } | Term::ElimSEmpty { .. } => "absurd",
        Term::ElimSquash { .. } => "squash eliminator",
        Term::Triv { .. } => "trivial",
        Term::Refl { .. } | Term::SRefl { .. } => "refl",
        Term::Squash { .. } => "squash",
        Term::J { .. } => "J",
        Term::GlobalTm { .. } => "global",
        Term::TmNat | Term::TmTy(_) | Term::TmUnit { .. } | Term::TmEmpty { .. } => "type code",
        Term::TmPi { .. }
        | Term::TmSigma { .. }
        | Term::TmSum { .. }
        | Term::TmW { .. }
        | Term::TmWf { .. }
        | Term::TmM { .. }
        | Term::TmDVec { .. }
        | Term::TmIWf { .. }
        | Term::TmVec { .. }
        | Term::TmFin { .. }
        | Term::TmSEmpty { .. } => "type code",
        Term::TmSquash { .. } => "type code",
        Term::TmId { .. } => "equation code",
        Term::TmSEq { .. } => "strict-equation code",
        // The layer-m formers, which the walk declines to enter at all.
        _ => "code former",
    }
}

/// [`former_tm`] at the type level.
fn former_ty(t: &Type) -> &'static str {
    match t {
        Type::Nat => "Nat",
        Type::Ty(_) => "universe",
        Type::El { .. } => "El",
        Type::Id { .. } => "equation",
        Type::SEq { .. } => "strict equation",
        Type::Pi { .. } => "function type",
        Type::Sigma { .. } => "pair type",
        Type::Sum { .. } => "sum type",
        Type::W { .. } | Type::Wf { .. } => "well-founded type",
        Type::Vec { .. } => "vector type",
        Type::Fin { .. } => "Fin",
        Type::Unit { .. } => "True",
        Type::Empty { .. } | Type::SEmpty { .. } => "False",
        Type::Squash { .. } => "squash type",
        Type::GlobalTy { .. } => "global type",
        _ => "type former",
    }
}

impl Lgg<'_> {
    fn is_hole(&mut self, x: &Term, y: &Term, k: u32) -> bool {
        if !self.match_witness {
            return false;
        }
        while self.witness.len() as u32 <= k {
            let i = self.witness.len() as u32;
            self.witness
                .push((self.s.shift_local(i), self.t.shift_local(i)));
        }
        let (sw, tw) = &self.witness[k as usize];
        x == sw && y == tw
    }

    /// A witness pair of two dependent pairs at one `Σ`, and a position whose
    /// sides are their first (or second) components: the hole is `fst(z)`
    /// (or `snd(z)`). This is how a packed equation `⟨i, s⟩ = ⟨j, t⟩` gives
    /// `i = j` by `cong` (docs/dependent-match-compiler-design.md §9).
    fn projection_hole(&mut self, x: &Term, y: &Term, k: u32) -> Option<Term> {
        if !self.match_witness {
            return None;
        }
        let (
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst: s1, snd: s2 },
            Term::Pair { fst_level: l2, snd_level: r2, fst_ty: f2, snd_ty: g2, fst: t1, snd: t2 },
        ) = (&self.s, &self.t)
        else {
            return None;
        };
        if fst_level != l2 || snd_level != r2 || fst_ty != f2 || snd_ty != g2 {
            return None;
        }
        let first = (*x == s1.shift_local(k) && *y == t1.shift_local(k))
            || (k == 0 && self.conv_fst.is_some_and(|conv| conv(x, y, s1, t1, fst_ty, fst_level)));
        let second = *x == s2.shift_local(k) && *y == t2.shift_local(k);
        let (fst_level, snd_level) = (fst_level.clone(), snd_level.clone());
        let fst_ty = Rc::new(fst_ty.shift_local(k + 1));
        let snd_ty = Rc::new(snd_ty.shift_local_above(k + 1, 1));
        let pair = Rc::new(Term::Var(LocalVar(k)));
        if first {
            Some(Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair })
        } else if second {
            Some(Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair })
        } else {
            None
        }
    }

    /// The path to the stopping node: everything pushed on the way down,
    /// *minus* the node itself, whose two formers are reported separately.
    fn ancestors(&self) -> Vec<&'static str> {
        let mut p = self.path.clone();
        p.pop();
        p
    }

    fn mismatch_tm<T>(&self, x: &Term, y: &Term, k: u32) -> Result<T, Mismatch> {
        Err(Mismatch {
            path: self.ancestors(),
            sides: (former_tm(x), former_tm(y)),
            at: Some((x.clone(), y.clone())),
            depth: k,
            endpoints_agree: false,
        })
    }

    fn mismatch_ty<T>(&self, x: &Type, y: &Type, k: u32) -> Result<T, Mismatch> {
        Err(Mismatch {
            path: self.ancestors(),
            sides: (former_ty(x), former_ty(y)),
            at: None,
            depth: k,
            endpoints_agree: false,
        })
    }

    /// One term node, with its former on the path for as long as the walk is
    /// inside it. [`Self::tm_at`] is the walk proper.
    fn tm(&mut self, x: &Term, y: &Term, k: u32) -> Result<Term, Mismatch> {
        self.path.push(former_tm(x));
        let r = self.tm_at(x, y, k);
        if r.is_ok() {
            self.path.pop();
        }
        r
    }

    /// One type node, likewise.
    /// Two checked spellings' annotations: anti-unified when both are
    /// present, the present one when only one is.
    fn opt_ty(
        &mut self,
        x: &Option<Rc<Type>>,
        y: &Option<Rc<Type>>,
        k: u32,
    ) -> Result<Option<Rc<Type>>, Mismatch> {
        match (x, y) {
            (Some(x), Some(y)) => Ok(Some(Rc::new(self.ty(x, y, k)?))),
            (Some(t), None) | (None, Some(t)) => Ok(Some(kept_ty(t, k))),
            (None, None) => Ok(None),
        }
    }

    fn ty(&mut self, x: &Type, y: &Type, k: u32) -> Result<Type, Mismatch> {
        self.path.push(former_ty(x));
        let r = self.ty_at(x, y, k);
        if r.is_ok() {
            self.path.pop();
        }
        r
    }

    /// One term node. `x`/`y` are scoped in `Γ` plus `k` binders; the
    /// result is in `Γ, z` plus the same `k`, with `Var(k)` wherever the
    /// abstraction variable was placed. Every piece kept from a side is
    /// weakened past `z` as it is kept (agreement, [`kept_ty`]).
    fn tm_at(&mut self, x: &Term, y: &Term, k: u32) -> Result<Term, Mismatch> {
        // Agreement: keep it whole. Nothing inside can need a hole — a hole
        // needs a *difference*, and these subtrees are identical.
        if x == y {
            return Ok(x.shift_local_above(1, k));
        }
        if self.is_hole(x, y, k) || (k == 0 && self.conv.is_some_and(|conv| conv(x, y))) {
            return Ok(Term::Var(LocalVar(k)));
        }
        if let Some(projected) = self.projection_hole(x, y, k) {
            return Ok(projected);
        }
        match (x, y) {
            (Term::Succ(a), Term::Succ(b)) => Ok(Term::Succ(Rc::new(self.tm(a, b, k)?))),
            (
                Term::TmPi {
                    dom_level: dl1,
                    cod_level: cl1,
                    dom: d1,
                    cod: c1,
                },
                Term::TmPi {
                    dom_level: dl2,
                    cod_level: cl2,
                    dom: d2,
                    cod: c2,
                },
            ) if dl1 == dl2 && cl1 == cl2 => Ok(Term::TmPi {
                dom_level: dl1.clone(),
                cod_level: cl1.clone(),
                dom: Rc::new(self.tm(d1, d2, k)?),
                cod: Rc::new(self.tm(c1, c2, k + 1)?),
            }),
            (
                Term::TmSigma {
                    fst_level: fl1,
                    snd_level: sl1,
                    fst: f1,
                    snd: s1,
                },
                Term::TmSigma {
                    fst_level: fl2,
                    snd_level: sl2,
                    fst: f2,
                    snd: s2,
                },
            ) if fl1 == fl2 && sl1 == sl2 => Ok(Term::TmSigma {
                fst_level: fl1.clone(),
                snd_level: sl1.clone(),
                fst: Rc::new(self.tm(f1, f2, k)?),
                snd: Rc::new(self.tm(s1, s2, k + 1)?),
            }),
            (
                Term::TmW {
                    shape_level: sl1,
                    pos_level: pl1,
                    shape: s1,
                    pos: p1,
                },
                Term::TmW {
                    shape_level: sl2,
                    pos_level: pl2,
                    shape: s2,
                    pos: p2,
                },
            ) if sl1 == sl2 && pl1 == pl2 => Ok(Term::TmW {
                shape_level: sl1.clone(),
                pos_level: pl1.clone(),
                shape: Rc::new(self.tm(s1, s2, k)?),
                pos: Rc::new(self.tm(p1, p2, k + 1)?),
            }),
            (
                Term::TmId {
                    level: l1,
                    ty: t1,
                    lhs: a1,
                    rhs: b1,
                },
                Term::TmId {
                    level: l2,
                    ty: t2,
                    lhs: a2,
                    rhs: b2,
                },
            ) if l1 == l2 => Ok(Term::TmId {
                level: l1.clone(),
                ty: Rc::new(self.tm(t1, t2, k)?),
                lhs: Rc::new(self.tm(a1, a2, k)?),
                rhs: Rc::new(self.tm(b1, b2, k)?),
            }),
            (
                Term::TmSEq {
                    level: l1,
                    ty: t1,
                    lhs: a1,
                    rhs: b1,
                },
                Term::TmSEq {
                    level: l2,
                    ty: t2,
                    lhs: a2,
                    rhs: b2,
                },
            ) if l1 == l2 => Ok(Term::TmSEq {
                level: l1.clone(),
                ty: Rc::new(self.tm(t1, t2, k)?),
                lhs: Rc::new(self.tm(a1, a2, k)?),
                rhs: Rc::new(self.tm(b1, b2, k)?),
            }),
            (
                Term::TmSum {
                    lhs_level: ll1,
                    rhs_level: rl1,
                    lhs: a1,
                    rhs: b1,
                },
                Term::TmSum {
                    lhs_level: ll2,
                    rhs_level: rl2,
                    lhs: a2,
                    rhs: b2,
                },
            ) if ll1 == ll2 && rl1 == rl2 => Ok(Term::TmSum {
                lhs_level: ll1.clone(),
                rhs_level: rl1.clone(),
                lhs: Rc::new(self.tm(a1, a2, k)?),
                rhs: Rc::new(self.tm(b1, b2, k)?),
            }),
            (
                Term::TmVec {
                    level: l1,
                    elem: e1,
                    len: n1,
                },
                Term::TmVec {
                    level: l2,
                    elem: e2,
                    len: n2,
                },
            ) if l1 == l2 => Ok(Term::TmVec {
                level: l1.clone(),
                elem: Rc::new(self.tm(e1, e2, k)?),
                len: Rc::new(self.tm(n1, n2, k)?),
            }),
            (Term::TmFin { len: n1 }, Term::TmFin { len: n2 }) => Ok(Term::TmFin {
                len: Rc::new(self.tm(n1, n2, k)?),
            }),
            (
                Term::TmWf {
                    level: l1,
                    shape: s1,
                    arity: a1,
                },
                Term::TmWf {
                    level: l2,
                    shape: s2,
                    arity: a2,
                },
            ) if l1 == l2 => Ok(Term::TmWf {
                level: l1.clone(),
                shape: Rc::new(self.tm(s1, s2, k)?),
                // The arity binds the shape.
                arity: Rc::new(self.tm(a1, a2, k + 1)?),
            }),
            (
                Term::TmDVec { level: l1, len: k1, fam: f1 },
                Term::TmDVec { level: l2, len: k2, fam: f2 },
            ) if l1 == l2 => Ok(Term::TmDVec {
                level: l1.clone(),
                len: Rc::new(self.tm(k1, k2, k)?),
                // The family binds the position.
                fam: Rc::new(self.tm(f1, f2, k + 1)?),
            }),
            (
                Term::TmIWf { level: l1, idx_level: i1, idx: x1, shape: s1, arity: a1, out: o1, child: c1, index: m1 },
                Term::TmIWf { level: l2, idx_level: i2, idx: x2, shape: s2, arity: a2, out: o2, child: c2, index: m2 },
            ) if l1 == l2 && i1 == i2 => Ok(Term::TmIWf {
                level: l1.clone(),
                idx_level: i1.clone(),
                idx: Rc::new(self.tm(x1, x2, k)?),
                shape: Rc::new(self.tm(s1, s2, k)?),
                // arity and out bind x, child x i.
                arity: Rc::new(self.tm(a1, a2, k + 1)?),
                out: Rc::new(self.tm(o1, o2, k + 1)?),
                child: Rc::new(self.tm(c1, c2, k + 2)?),
                index: Rc::new(self.tm(m1, m2, k)?),
            }),
            (
                Term::TmM { level: l1, pos_level: p1, idx_level: i1, idx: x1, shape: s1, pos: q1, next: n1, index: j1 },
                Term::TmM { level: l2, pos_level: p2, idx_level: i2, idx: x2, shape: s2, pos: q2, next: n2, index: j2 },
            ) if l1 == l2 && p1 == p2 && i1 == i2 => Ok(Term::TmM {
                level: l1.clone(),
                pos_level: p1.clone(),
                idx_level: i1.clone(),
                idx: Rc::new(self.tm(x1, x2, k)?),
                // shape binds i, pos i s, next i s p.
                shape: Rc::new(self.tm(s1, s2, k + 1)?),
                pos: Rc::new(self.tm(q1, q2, k + 2)?),
                next: Rc::new(self.tm(n1, n2, k + 3)?),
                index: Rc::new(self.tm(j1, j2, k)?),
            }),
            (
                Term::ElimNat {
                    level: l1,
                    motive: m1,
                    base: b1,
                    step: s1,
                    scrut: t1,
                },
                Term::ElimNat {
                    level: l2,
                    motive: m2,
                    base: b2,
                    step: s2,
                    scrut: t2,
                },
            ) if l1 == l2 => Ok(Term::ElimNat {
                level: l1.clone(),
                motive: Rc::new(self.ty(m1, m2, k + 1)?),
                base: Rc::new(self.tm(b1, b2, k)?),
                // The step binds the predecessor and the recursive result.
                step: Rc::new(self.tm(s1, s2, k + 2)?),
                scrut: Rc::new(self.tm(t1, t2, k)?),
            }),
            (
                Term::Refl {
                    level: l1,
                    ty: t1,
                    tm: a1,
                },
                Term::Refl {
                    level: l2,
                    ty: t2,
                    tm: a2,
                },
            ) if l1 == l2 => Ok(Term::Refl {
                level: l1.clone(),
                ty: Rc::new(self.ty(t1, t2, k)?),
                tm: Rc::new(self.tm(a1, a2, k)?),
            }),
            (
                Term::SRefl {
                    level: l1,
                    ty: t1,
                    tm: a1,
                },
                Term::SRefl {
                    level: l2,
                    ty: t2,
                    tm: a2,
                },
            ) if l1 == l2 => Ok(Term::SRefl {
                level: l1.clone(),
                ty: Rc::new(self.ty(t1, t2, k)?),
                tm: Rc::new(self.tm(a1, a2, k)?),
            }),
            (
                Term::J {
                    ty_level: tl1,
                    motive_level: ml1,
                    ty: t1,
                    lhs: a1,
                    motive: m1,
                    case: c1,
                    rhs: r1,
                    proof: p1,
                },
                Term::J {
                    ty_level: tl2,
                    motive_level: ml2,
                    ty: t2,
                    lhs: a2,
                    motive: m2,
                    case: c2,
                    rhs: r2,
                    proof: p2,
                },
            ) if tl1 == tl2 && ml1 == ml2 => Ok(Term::J {
                ty_level: tl1.clone(),
                motive_level: ml1.clone(),
                ty: Rc::new(self.ty(t1, t2, k)?),
                lhs: Rc::new(self.tm(a1, a2, k)?),
                // The motive binds the endpoint and the path.
                motive: Rc::new(self.ty(m1, m2, k + 2)?),
                case: Rc::new(self.tm(c1, c2, k)?),
                rhs: Rc::new(self.tm(r1, r2, k)?),
                proof: Rc::new(self.tm(p1, p2, k)?),
            }),
            (
                Term::ElimSEmpty {
                    level: l1,
                    scrut_level: sl1,
                    motive: m1,
                    scrut: t1,
                },
                Term::ElimSEmpty {
                    level: l2,
                    scrut_level: sl2,
                    motive: m2,
                    scrut: t2,
                },
            ) if l1 == l2 && sl1 == sl2 => Ok(Term::ElimSEmpty {
                level: l1.clone(),
                scrut_level: sl1.clone(),
                motive: Rc::new(self.ty(m1, m2, k + 1)?),
                scrut: Rc::new(self.tm(t1, t2, k)?),
            }),
            (
                Term::ElimEmpty {
                    level: l1,
                    scrut_level: sl1,
                    motive: m1,
                    scrut: t1,
                },
                Term::ElimEmpty {
                    level: l2,
                    scrut_level: sl2,
                    motive: m2,
                    scrut: t2,
                },
            ) if l1 == l2 && sl1 == sl2 => Ok(Term::ElimEmpty {
                level: l1.clone(),
                scrut_level: sl1.clone(),
                motive: Rc::new(self.ty(m1, m2, k + 1)?),
                scrut: Rc::new(self.tm(t1, t2, k)?),
            }),
            // The checked spellings (`docs/intro-by-type-design.md` §4.2):
            // one annotation to anti-unify instead of two components, and
            // no levels to require equal — structurally smaller, and more
            // often identical than two reducts. Mixed spellings fall to
            // `mismatch_tm` and generalize, which is what two different
            // spellings of one term have always done here.
            // A component form against a checked spelling of the same former
            // is **one** former written two ways — a reduct beside an emitted
            // value, the normal case since the emitters write checked
            // spellings (`docs/intro-by-type-design.md` §4.2). Anti-unify the
            // children and keep the component side's annotations, which are
            // valid in inference and checking position alike; the kernel
            // re-checks the generalization either way.
            (
                Term::Inl { lhs_level, rhs_level, lhs, rhs, val: v1 },
                Term::InlAt { val: v2, .. },
            ) => Ok(Term::Inl {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: kept_ty(lhs, k),
                rhs: kept_ty(rhs, k),
                val: Rc::new(self.tm(v1, v2, k)?),
            }),
            (
                Term::InlAt { val: v1, .. },
                Term::Inl { lhs_level, rhs_level, lhs, rhs, val: v2 },
            ) => Ok(Term::Inl {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: kept_ty(lhs, k),
                rhs: kept_ty(rhs, k),
                val: Rc::new(self.tm(v1, v2, k)?),
            }),
            (
                Term::Inr { lhs_level, rhs_level, lhs, rhs, val: v1 },
                Term::InrAt { val: v2, .. },
            ) => Ok(Term::Inr {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: kept_ty(lhs, k),
                rhs: kept_ty(rhs, k),
                val: Rc::new(self.tm(v1, v2, k)?),
            }),
            (
                Term::InrAt { val: v1, .. },
                Term::Inr { lhs_level, rhs_level, lhs, rhs, val: v2 },
            ) => Ok(Term::Inr {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: kept_ty(lhs, k),
                rhs: kept_ty(rhs, k),
                val: Rc::new(self.tm(v1, v2, k)?),
            }),
            (
                Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst: a1, snd: b1 },
                Term::PairAt { fst: a2, snd: b2, .. },
            ) => Ok(Term::Pair {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: kept_ty(fst_ty, k),
                snd_ty: kept_ty(snd_ty, k + 1),
                fst: Rc::new(self.tm(a1, a2, k)?),
                snd: Rc::new(self.tm(b1, b2, k)?),
            }),
            (
                Term::PairAt { fst: a1, snd: b1, .. },
                Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst: a2, snd: b2 },
            ) => Ok(Term::Pair {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: kept_ty(fst_ty, k),
                snd_ty: kept_ty(snd_ty, k + 1),
                fst: Rc::new(self.tm(a1, a2, k)?),
                snd: Rc::new(self.tm(b1, b2, k)?),
            }),
            (
                Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair: p1 },
                Term::FstAt { pair: p2 },
            )
            | (
                Term::FstAt { pair: p1 },
                Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair: p2 },
            ) => Ok(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: kept_ty(fst_ty, k),
                snd_ty: kept_ty(snd_ty, k + 1),
                pair: Rc::new(self.tm(p1, p2, k)?),
            }),
            (
                Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair: p1 },
                Term::SndAt { pair: p2 },
            )
            | (
                Term::SndAt { pair: p1 },
                Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair: p2 },
            ) => Ok(Term::Snd {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: kept_ty(fst_ty, k),
                snd_ty: kept_ty(snd_ty, k + 1),
                pair: Rc::new(self.tm(p1, p2, k)?),
            }),
            // An annotated intro against an unannotated one keeps the
            // annotation, so the generalization still infers where it must.
            (Term::PairAt { ty: t1, fst: a1, snd: b1 }, Term::PairAt { ty: t2, fst: a2, snd: b2 }) =>
            {
                Ok(Term::PairAt {
                    ty: self.opt_ty(t1, t2, k)?,
                    fst: Rc::new(self.tm(a1, a2, k)?),
                    snd: Rc::new(self.tm(b1, b2, k)?),
                })
            }
            (Term::InlAt { ty: t1, val: v1 }, Term::InlAt { ty: t2, val: v2 }) =>
            {
                Ok(Term::InlAt { ty: self.opt_ty(t1, t2, k)?, val: Rc::new(self.tm(v1, v2, k)?) })
            }
            (Term::InrAt { ty: t1, val: v1 }, Term::InrAt { ty: t2, val: v2 }) =>
            {
                Ok(Term::InrAt { ty: self.opt_ty(t1, t2, k)?, val: Rc::new(self.tm(v1, v2, k)?) })
            }
            (Term::FstAt { pair: p1 }, Term::FstAt { pair: p2 }) => {
                Ok(Term::FstAt { pair: Rc::new(self.tm(p1, p2, k)?) })
            }
            (Term::SndAt { pair: p1 }, Term::SndAt { pair: p2 }) => {
                Ok(Term::SndAt { pair: Rc::new(self.tm(p1, p2, k)?) })
            }
            (
                Term::Pair {
                    fst_level: fl1,
                    snd_level: sl1,
                    fst_ty: ft1,
                    snd_ty: st1,
                    fst: a1,
                    snd: b1,
                },
                Term::Pair {
                    fst_level: fl2,
                    snd_level: sl2,
                    fst_ty: ft2,
                    snd_ty: st2,
                    fst: a2,
                    snd: b2,
                },
            ) if fl1 == fl2 && sl1 == sl2 => Ok(Term::Pair {
                fst_level: fl1.clone(),
                snd_level: sl1.clone(),
                fst_ty: Rc::new(self.ty(ft1, ft2, k)?),
                snd_ty: Rc::new(self.ty(st1, st2, k + 1)?),
                fst: Rc::new(self.tm(a1, a2, k)?),
                snd: Rc::new(self.tm(b1, b2, k)?),
            }),
            (
                Term::Fst {
                    fst_level: fl1,
                    snd_level: sl1,
                    fst_ty: ft1,
                    snd_ty: st1,
                    pair: p1,
                },
                Term::Fst {
                    fst_level: fl2,
                    snd_level: sl2,
                    fst_ty: ft2,
                    snd_ty: st2,
                    pair: p2,
                },
            ) if fl1 == fl2 && sl1 == sl2 => Ok(Term::Fst {
                fst_level: fl1.clone(),
                snd_level: sl1.clone(),
                fst_ty: Rc::new(self.ty(ft1, ft2, k)?),
                snd_ty: Rc::new(self.ty(st1, st2, k + 1)?),
                pair: Rc::new(self.tm(p1, p2, k)?),
            }),
            (
                Term::Snd {
                    fst_level: fl1,
                    snd_level: sl1,
                    fst_ty: ft1,
                    snd_ty: st1,
                    pair: p1,
                },
                Term::Snd {
                    fst_level: fl2,
                    snd_level: sl2,
                    fst_ty: ft2,
                    snd_ty: st2,
                    pair: p2,
                },
            ) if fl1 == fl2 && sl1 == sl2 => Ok(Term::Snd {
                fst_level: fl1.clone(),
                snd_level: sl1.clone(),
                fst_ty: Rc::new(self.ty(ft1, ft2, k)?),
                snd_ty: Rc::new(self.ty(st1, st2, k + 1)?),
                pair: Rc::new(self.tm(p1, p2, k)?),
            }),
            (
                Term::Inl {
                    lhs_level: ll1,
                    rhs_level: rl1,
                    lhs: a1,
                    rhs: b1,
                    val: v1,
                },
                Term::Inl {
                    lhs_level: ll2,
                    rhs_level: rl2,
                    lhs: a2,
                    rhs: b2,
                    val: v2,
                },
            ) if ll1 == ll2 && rl1 == rl2 => Ok(Term::Inl {
                lhs_level: ll1.clone(),
                rhs_level: rl1.clone(),
                lhs: Rc::new(self.ty(a1, a2, k)?),
                rhs: Rc::new(self.ty(b1, b2, k)?),
                val: Rc::new(self.tm(v1, v2, k)?),
            }),
            (
                Term::Inr {
                    lhs_level: ll1,
                    rhs_level: rl1,
                    lhs: a1,
                    rhs: b1,
                    val: v1,
                },
                Term::Inr {
                    lhs_level: ll2,
                    rhs_level: rl2,
                    lhs: a2,
                    rhs: b2,
                    val: v2,
                },
            ) if ll1 == ll2 && rl1 == rl2 => Ok(Term::Inr {
                lhs_level: ll1.clone(),
                rhs_level: rl1.clone(),
                lhs: Rc::new(self.ty(a1, a2, k)?),
                rhs: Rc::new(self.ty(b1, b2, k)?),
                val: Rc::new(self.tm(v1, v2, k)?),
            }),
            (
                Term::Case {
                    lhs_level: ll1,
                    rhs_level: rl1,
                    motive_level: ml1,
                    lhs: a1,
                    rhs: b1,
                    motive: m1,
                    case_l: cl1,
                    case_r: cr1,
                    scrut: t1,
                },
                Term::Case {
                    lhs_level: ll2,
                    rhs_level: rl2,
                    motive_level: ml2,
                    lhs: a2,
                    rhs: b2,
                    motive: m2,
                    case_l: cl2,
                    case_r: cr2,
                    scrut: t2,
                },
            ) if ll1 == ll2 && rl1 == rl2 && ml1 == ml2 => Ok(Term::Case {
                lhs_level: ll1.clone(),
                rhs_level: rl1.clone(),
                motive_level: ml1.clone(),
                lhs: Rc::new(self.ty(a1, a2, k)?),
                rhs: Rc::new(self.ty(b1, b2, k)?),
                motive: Rc::new(self.ty(m1, m2, k + 1)?),
                case_l: Rc::new(self.tm(cl1, cl2, k + 1)?),
                case_r: Rc::new(self.tm(cr1, cr2, k + 1)?),
                scrut: Rc::new(self.tm(t1, t2, k)?),
            }),
            (
                Term::Sup {
                    shape_level: sl1,
                    pos_level: pl1,
                    shape_ty: s1,
                    pos_ty: p1,
                    label: a1,
                    children: c1,
                },
                Term::Sup {
                    shape_level: sl2,
                    pos_level: pl2,
                    shape_ty: s2,
                    pos_ty: p2,
                    label: a2,
                    children: c2,
                },
            ) if sl1 == sl2 && pl1 == pl2 => Ok(Term::Sup {
                shape_level: sl1.clone(),
                pos_level: pl1.clone(),
                shape_ty: Rc::new(self.ty(s1, s2, k)?),
                pos_ty: Rc::new(self.ty(p1, p2, k + 1)?),
                label: Rc::new(self.tm(a1, a2, k)?),
                children: Rc::new(self.tm(c1, c2, k)?),
            }),
            (
                Term::ElimW {
                    shape_level: sl1,
                    pos_level: pl1,
                    motive_level: ml1,
                    shape: s1,
                    pos: p1,
                    motive: m1,
                    step: st1,
                    scrut: t1,
                },
                Term::ElimW {
                    shape_level: sl2,
                    pos_level: pl2,
                    motive_level: ml2,
                    shape: s2,
                    pos: p2,
                    motive: m2,
                    step: st2,
                    scrut: t2,
                },
            ) if sl1 == sl2 && pl1 == pl2 && ml1 == ml2 => Ok(Term::ElimW {
                shape_level: sl1.clone(),
                pos_level: pl1.clone(),
                motive_level: ml1.clone(),
                shape: Rc::new(self.ty(s1, s2, k)?),
                pos: Rc::new(self.ty(p1, p2, k + 1)?),
                motive: Rc::new(self.ty(m1, m2, k + 1)?),
                // The step binds the label, the child function and the ih.
                step: Rc::new(self.tm(st1, st2, k + 3)?),
                scrut: Rc::new(self.tm(t1, t2, k)?),
            }),
            (
                Term::Supf {
                    level: l1,
                    shape: s1,
                    arity: n1,
                    label: a1,
                    children: c1,
                },
                Term::Supf {
                    level: l2,
                    shape: s2,
                    arity: n2,
                    label: a2,
                    children: c2,
                },
            ) if l1 == l2 => Ok(Term::Supf {
                level: l1.clone(),
                shape: Rc::new(self.ty(s1, s2, k)?),
                arity: Rc::new(self.tm(n1, n2, k + 1)?),
                label: Rc::new(self.tm(a1, a2, k)?),
                children: Rc::new(self.tm(c1, c2, k)?),
            }),
            (
                Term::ElimWf {
                    level: l1,
                    motive_level: ml1,
                    shape: s1,
                    arity: n1,
                    motive: m1,
                    step: st1,
                    scrut: t1,
                },
                Term::ElimWf {
                    level: l2,
                    motive_level: ml2,
                    shape: s2,
                    arity: n2,
                    motive: m2,
                    step: st2,
                    scrut: t2,
                },
            ) if l1 == l2 && ml1 == ml2 => Ok(Term::ElimWf {
                level: l1.clone(),
                motive_level: ml1.clone(),
                shape: Rc::new(self.ty(s1, s2, k)?),
                arity: Rc::new(self.tm(n1, n2, k + 1)?),
                motive: Rc::new(self.ty(m1, m2, k + 1)?),
                // The step binds the label, the children tuple and the ih.
                step: Rc::new(self.tm(st1, st2, k + 3)?),
                scrut: Rc::new(self.tm(t1, t2, k)?),
            }),
            (
                Term::Lam {
                    dom_level: dl1,
                    cod_level: cl1,
                    dom: d1,
                    body: b1,
                },
                Term::Lam {
                    dom_level: dl2,
                    cod_level: cl2,
                    dom: d2,
                    body: b2,
                },
            ) if dl1 == dl2 && cl1 == cl2 => Ok(Term::Lam {
                dom_level: dl1.clone(),
                cod_level: cl1.clone(),
                dom: Rc::new(self.ty(d1, d2, k)?),
                body: Rc::new(self.tm(b1, b2, k + 1)?),
            }),
            (
                Term::App {
                    fun: f1,
                    dom_level: dl1,
                    cod_level: cl1,
                    dom: d1,
                    cod: c1,
                    arg: a1,
                },
                Term::App {
                    fun: f2,
                    dom_level: dl2,
                    cod_level: cl2,
                    dom: d2,
                    cod: c2,
                    arg: a2,
                },
            ) if dl1 == dl2 && cl1 == cl2 => Ok(Term::App {
                fun: Rc::new(self.tm(f1, f2, k)?),
                dom_level: dl1.clone(),
                cod_level: cl1.clone(),
                dom: Rc::new(self.ty(d1, d2, k)?),
                cod: Rc::new(self.ty(c1, c2, k + 1)?),
                arg: Rc::new(self.tm(a1, a2, k)?),
            }),
            // `app@` (docs/app-by-head-type-design.md §6.2): no annotation to
            // relate, and against an `app` it is one former written two ways.
            // The generalization is `app@` — its head generalizes two heads
            // that infer, and it carries no annotation that could mention a
            // generalized position — except over a λ head, which does not
            // infer and keeps the annotated side's Π.
            (Term::AppAt { fun: f1, arg: a1 }, Term::AppAt { fun: f2, arg: a2 }) => {
                Ok(Term::AppAt {
                    fun: Rc::new(self.tm(f1, f2, k)?),
                    arg: Rc::new(self.tm(a1, a2, k)?),
                })
            }
            (Term::App { fun: f1, dom_level, cod_level, dom, cod, arg: a1 }, Term::AppAt { fun: f2, arg: a2 }) => {
                let fun = Rc::new(self.tm(f1, f2, k)?);
                let arg = Rc::new(self.tm(a1, a2, k)?);
                Ok(mixed_app(fun, dom_level, cod_level, dom, cod, arg, k))
            }
            (Term::AppAt { fun: f1, arg: a1 }, Term::App { fun: f2, dom_level, cod_level, dom, cod, arg: a2 }) => {
                let fun = Rc::new(self.tm(f1, f2, k)?);
                let arg = Rc::new(self.tm(a1, a2, k)?);
                Ok(mixed_app(fun, dom_level, cod_level, dom, cod, arg, k))
            }
            // Everything else — mismatched heads, differing level or context
            // annotations, and the layer-m code formers this module declines
            // to walk into.
            _ => self.mismatch_tm(x, y, k),
        }
    }

    /// One type node. There is no hole rule here: the abstraction variable is
    /// a *term*, so a difference between two types can only be repaired by a
    /// difference in a term it contains.
    fn ty_at(&mut self, x: &Type, y: &Type, k: u32) -> Result<Type, Mismatch> {
        if x == y {
            return Ok(x.shift_local_above(1, k));
        }
        match (x, y) {
            (
                Type::Pi {
                    dom_level: dl1,
                    cod_level: cl1,
                    dom: d1,
                    cod: c1,
                },
                Type::Pi {
                    dom_level: dl2,
                    cod_level: cl2,
                    dom: d2,
                    cod: c2,
                },
            ) if dl1 == dl2 && cl1 == cl2 => Ok(Type::Pi {
                dom_level: dl1.clone(),
                cod_level: cl1.clone(),
                dom: Rc::new(self.ty(d1, d2, k)?),
                cod: Rc::new(self.ty(c1, c2, k + 1)?),
            }),
            (
                Type::Sigma {
                    fst_level: fl1,
                    snd_level: sl1,
                    fst: f1,
                    snd: s1,
                },
                Type::Sigma {
                    fst_level: fl2,
                    snd_level: sl2,
                    fst: f2,
                    snd: s2,
                },
            ) if fl1 == fl2 && sl1 == sl2 => Ok(Type::Sigma {
                fst_level: fl1.clone(),
                snd_level: sl1.clone(),
                fst: Rc::new(self.ty(f1, f2, k)?),
                snd: Rc::new(self.ty(s1, s2, k + 1)?),
            }),
            (
                Type::W {
                    shape_level: sl1,
                    pos_level: pl1,
                    shape: s1,
                    pos: p1,
                },
                Type::W {
                    shape_level: sl2,
                    pos_level: pl2,
                    shape: s2,
                    pos: p2,
                },
            ) if sl1 == sl2 && pl1 == pl2 => Ok(Type::W {
                shape_level: sl1.clone(),
                pos_level: pl1.clone(),
                shape: Rc::new(self.ty(s1, s2, k)?),
                pos: Rc::new(self.ty(p1, p2, k + 1)?),
            }),
            (Type::El { level: l1, tm: t1 }, Type::El { level: l2, tm: t2 }) if l1 == l2 => {
                Ok(Type::El {
                    level: l1.clone(),
                    tm: Rc::new(self.tm(t1, t2, k)?),
                })
            }
            (
                Type::Id {
                    level: l1,
                    ty: t1,
                    lhs: a1,
                    rhs: b1,
                },
                Type::Id {
                    level: l2,
                    ty: t2,
                    lhs: a2,
                    rhs: b2,
                },
            ) if l1 == l2 => Ok(Type::Id {
                level: l1.clone(),
                ty: Rc::new(self.ty(t1, t2, k)?),
                lhs: Rc::new(self.tm(a1, a2, k)?),
                rhs: Rc::new(self.tm(b1, b2, k)?),
            }),
            (
                Type::SEq {
                    level: l1,
                    ty: t1,
                    lhs: a1,
                    rhs: b1,
                },
                Type::SEq {
                    level: l2,
                    ty: t2,
                    lhs: a2,
                    rhs: b2,
                },
            ) if l1 == l2 => Ok(Type::SEq {
                level: l1.clone(),
                ty: Rc::new(self.ty(t1, t2, k)?),
                lhs: Rc::new(self.tm(a1, a2, k)?),
                rhs: Rc::new(self.tm(b1, b2, k)?),
            }),
            (
                Type::Sum {
                    lhs_level: ll1,
                    rhs_level: rl1,
                    lhs: a1,
                    rhs: b1,
                },
                Type::Sum {
                    lhs_level: ll2,
                    rhs_level: rl2,
                    lhs: a2,
                    rhs: b2,
                },
            ) if ll1 == ll2 && rl1 == rl2 => Ok(Type::Sum {
                lhs_level: ll1.clone(),
                rhs_level: rl1.clone(),
                lhs: Rc::new(self.ty(a1, a2, k)?),
                rhs: Rc::new(self.ty(b1, b2, k)?),
            }),
            (
                Type::Vec {
                    level: l1,
                    elem: e1,
                    len: n1,
                },
                Type::Vec {
                    level: l2,
                    elem: e2,
                    len: n2,
                },
            ) if l1 == l2 => Ok(Type::Vec {
                level: l1.clone(),
                elem: Rc::new(self.ty(e1, e2, k)?),
                len: Rc::new(self.tm(n1, n2, k)?),
            }),
            (Type::Fin { len: n1 }, Type::Fin { len: n2 }) => Ok(Type::Fin {
                len: Rc::new(self.tm(n1, n2, k)?),
            }),
            (
                Type::Wf {
                    level: l1,
                    shape: s1,
                    arity: n1,
                },
                Type::Wf {
                    level: l2,
                    shape: s2,
                    arity: n2,
                },
            ) if l1 == l2 => Ok(Type::Wf {
                level: l1.clone(),
                shape: Rc::new(self.ty(s1, s2, k)?),
                arity: Rc::new(self.tm(n1, n2, k + 1)?),
            }),
            _ => self.mismatch_ty(x, y, k),
        }
    }
}

/// A side's annotation kept in the generalization: scoped in `Γ` plus `k`
/// binders, weakened past `z` under them.
fn kept_ty(t: &Rc<Type>, k: u32) -> Rc<Type> {
    Rc::new(t.shift_local_above(1, k))
}

/// The generalization of an `app` against an `app@`: `app@` unless the
/// generalized head is a λ, which would not infer. The annotation is the
/// `app` side's, at `k` binders.
fn mixed_app(
    fun: Rc<Term>,
    dom_level: &Level,
    cod_level: &Level,
    dom: &Rc<Type>,
    cod: &Rc<Type>,
    arg: Rc<Term>,
    k: u32,
) -> Term {
    if matches!(&*fun, Term::Lam { .. }) {
        Term::App {
            fun,
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: kept_ty(dom, k),
            cod: kept_ty(cod, k + 1),
            arg,
        }
    } else {
        Term::AppAt { fun, arg }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use heather_kernel::level::Level;

    fn nat(n: u32) -> Term {
        (0..n).fold(Term::Zero, |t, _| Term::Succ(Rc::new(t)))
    }

    fn var(i: u32) -> Term {
        Term::Var(LocalVar(i))
    }

    /// `f(a)` at `Nat -> Nat`, the shape a surface `f(a)` elaborates to.
    fn app(f: Term, a: Term) -> Term {
        Term::App {
            fun: Rc::new(f),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Nat),
            arg: Rc::new(a),
        }
    }

    #[test]
    fn succ_of_literals() {
        // `X = Succ(0)`, `Y = Succ(1)`, `p : 0 = 1` ⟹ `λz. Succ(z)`.
        let body = lgg_body(&nat(1), &nat(2), &nat(0), &nat(1)).expect("generalizes");
        assert_eq!(body, Term::Succ(Rc::new(var(0))));
    }

    #[test]
    fn succ_of_neutrals() {
        // The same with variable endpoints — the axis a literal-only test
        // misses (docs/testing-generated-terms.md).
        let body = lgg_body(
            &Term::Succ(Rc::new(var(1))),
            &Term::Succ(Rc::new(var(0))),
            &var(1),
            &var(0),
        )
        .expect("generalizes");
        // Both sides were weakened into `Γ, z`, so `Γ`'s vars moved up by one.
        assert_eq!(body, Term::Succ(Rc::new(var(0))));
    }

    #[test]
    fn multiple_occurrences_all_abstract() {
        // `add(a, a) = add(b, b)` from `p : a = b` — every differing position
        // is abstracted, which is §6's "a different theorem from congruence
        // in one argument" and correct all the same.
        let f = var(2); // some function in Γ
        let x = app(app(f.clone(), var(1)), var(1));
        let y = app(app(f.clone(), var(0)), var(0));
        let body = lgg_body(&x, &y, &var(1), &var(0)).expect("generalizes");
        let z = var(0);
        assert_eq!(body, app(app(var(3), z.clone()), z));
    }

    #[test]
    fn zero_holes_is_the_constant_function() {
        // `X ≡ Y` with distinct endpoints: no position differs, so the
        // congruence is constant (decision 5).
        let body = lgg_body(&nat(3), &nat(3), &nat(0), &nat(1)).expect("generalizes");
        assert_eq!(body, nat(3));
    }

    #[test]
    fn equal_endpoints_need_equal_sides() {
        // `s ≡ t`: the constant function is the only candidate, so `X ≢ Y`
        // is a failure and `X ≡ Y` is the constant.
        assert_eq!(
            lgg_body(&nat(3), &nat(3), &nat(1), &nat(1)).expect("constant"),
            nat(3)
        );
        let e = lgg_body(&nat(3), &nat(4), &nat(1), &nat(1)).expect_err("no congruence");
        assert!(e.to_string().contains("same term"), "{e}");
    }

    #[test]
    fn witness_mismatch_is_loud() {
        // `Succ(0) = Succ(1)` from `p : 0 = 2`: the differing position's
        // witness is `(0, 1)`, not the proof's `(0, 2)`.
        let e = lgg_body(&nat(1), &nat(2), &nat(0), &nat(2)).expect_err("must not guess");
        assert!(e.to_string().contains("cannot generalize"), "{e}");
    }

    #[test]
    fn mismatched_heads_are_loud() {
        let e = lgg_body(&nat(1), &var(0), &nat(0), &nat(1)).expect_err("must not guess");
        assert!(e.to_string().contains("cannot generalize"), "{e}");
    }

    #[test]
    fn hole_under_a_binder_shifts() {
        // `λ(w: Nat). Succ(a)` vs `λ(w: Nat). Succ(b)` from `p : a = b`:
        // the hole sits under one binder, so the witness is `a` weakened by
        // one and the abstraction variable lands at index 1 (decision 3).
        let lam = |b: Term| Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::Succ(Rc::new(b))),
        };
        // `a = Var(1)`, `b = Var(0)` in Γ; under the λ they are 2 and 1, and
        // once Γ is weakened by `z` they are 3 and 2.
        let body = lgg_body(&lam(var(2)), &lam(var(1)), &var(1), &var(0)).expect("generalizes");
        assert_eq!(body, lam(var(1)));
    }

    #[test]
    fn a_captured_witness_is_refused() {
        // The differing position is the λ's *own* variable, which no witness
        // from `Γ` can be: `Var(0)` under the binder is the bound `w`, not
        // the `a` of `p : a = b`. Refused rather than captured.
        let lam = |b: Term| Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::Succ(Rc::new(b))),
        };
        let e = lgg_body(&lam(var(0)), &lam(var(1)), &var(1), &var(0))
            .expect_err("the bound variable is not the proof's endpoint");
        assert!(e.to_string().contains("cannot generalize"), "{e}");
    }

    #[test]
    fn the_failure_carries_the_path_to_the_stopping_node() {
        // The same shape, read as *data*: the walk agreed through the λ and
        // the `Succ`, and stopped at the two variables under them. This is
        // what replaced four `{:?}`d kernel terms
        // (issues/lgg-diagnostic-dumps-kernel-terms.md), and it is asserted
        // here rather than through a rendered string because the rendering
        // belongs to the elaborator.
        let lam = |b: Term| Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::Succ(Rc::new(b))),
        };
        let e = lgg_body(&lam(var(0)), &lam(var(1)), &var(1), &var(0)).expect_err("no congruence");
        assert_eq!(e.path, vec!["λ", "numeral"]);
        assert_eq!(e.sides, ("variable", "variable"));
        // One binder between the goal's root and the stopping node, the λ's:
        // the sides are walked in `Γ`, and `z` exists only in the result.
        assert_eq!(e.depth, 1);
        assert!(e.at.is_some(), "a term position carries its two sides");
        assert!(e.to_string().contains("`λ ▸ numeral`"), "{e}");
    }

    #[test]
    fn is_deterministic() {
        // §4's property, mechanically: the same inputs give the same output,
        // because nothing here chooses.
        let a = lgg_body(&nat(2), &nat(3), &nat(1), &nat(2)).expect("generalizes");
        let b = lgg_body(&nat(2), &nat(3), &nat(1), &nat(2)).expect("generalizes");
        assert_eq!(a, b);
        assert_eq!(a, Term::Succ(Rc::new(var(0))));
    }

    #[test]
    fn generalizes_inside_a_type_annotation() {
        // The walk descends through *types* too — a `refl` carries the type
        // its endpoints live at, and a difference can hide there.
        let refl = |n: Term| Term::Refl {
            level: Level::Zero,
            ty: Rc::new(Type::Vec {
                level: Level::Zero,
                elem: Rc::new(Type::Nat),
                len: Rc::new(n),
            }),
            tm: Rc::new(Term::Triv { level: Level::Zero }),
        };
        let body = lgg_body(&refl(nat(1)), &refl(nat(2)), &nat(1), &nat(2)).expect("generalizes");
        assert_eq!(
            body,
            Term::Refl {
                level: Level::Zero,
                ty: Rc::new(Type::Vec {
                    level: Level::Zero,
                    elem: Rc::new(Type::Nat),
                    len: Rc::new(var(0)),
                }),
                tm: Rc::new(Term::Triv { level: Level::Zero }),
            }
        );
    }

    // -- first_difference ---------------------------------------------------
    //
    // The diagnostic half (issues/lgg-error-hides-the-implicit.md). What it
    // has to get right is the case the surface speller cannot show: two terms
    // that print the same and are not the same term.

    #[test]
    fn identical_terms_have_no_difference() {
        assert!(first_difference(&nat(3), &nat(3)).is_none());
        assert!(first_difference(&app(var(0), nat(1)), &app(var(0), nat(1))).is_none());
    }

    #[test]
    fn difference_at_the_root_has_an_empty_path() {
        let d = first_difference(&nat(1), &var(0)).expect("differs");
        assert!(d.path.is_empty());
        assert_eq!(d.sides, ("numeral", "variable"));
        assert_eq!(format!("{d:#}"), "at the root, `numeral` against `variable`");
    }

    #[test]
    fn difference_under_a_spine_names_the_path() {
        let d = first_difference(&app(var(0), nat(1)), &app(var(0), var(2))).expect("differs");
        assert_eq!(d.path, vec!["application"]);
        assert_eq!(d.sides, ("numeral", "variable"));
        assert_eq!(
            format!("{d:#}"),
            "under `application` at `numeral` against `variable`"
        );
    }

    /// **The case this exists for.** Two terms whose *surface* is identical —
    /// same head, same arguments — differing only in a type annotation the
    /// speller does not print. Anti-unification declines on it (the witness
    /// test is `==`, decision 2) and the message is a contradiction without
    /// this walk to name where they part.
    #[test]
    fn difference_inside_an_annotation_the_surface_drops() {
        // `refl` at `El(code)` against `refl` at the raw code's type: the two
        // print the same and are not `==`.
        let refl_at = |ty: Type| Term::Refl {
            level: Level::Zero,
            ty: Rc::new(ty),
            tm: Rc::new(Term::Triv { level: Level::Zero }),
        };
        let raw = Type::Unit { level: Level::Zero };
        let wrapped = Type::El {
            level: Level::Zero,
            tm: Rc::new(Term::TmUnit { level: Level::Zero }),
        };
        let d = first_difference(&refl_at(raw), &refl_at(wrapped)).expect("differs");
        assert_eq!(d.path, vec!["refl"]);
        assert_eq!(d.sides, ("True", "El"));
        // `at` is `None` at a type position — the formers are the whole of
        // what can be said, which is exactly why they are one word each.
        assert!(d.at.is_none());
    }

    #[test]
    fn the_path_accumulates_down_to_the_difference() {
        // Two levels of agreeing spine above the node that differs. The path
        // is what the reader navigates by, so it has to name every step.
        let d = first_difference(
            &app(app(var(0), nat(1)), nat(2)),
            &app(app(var(0), var(5)), nat(2)),
        )
        .expect("differs");
        assert_eq!(d.path, vec!["application", "application"]);
        assert_eq!(d.sides, ("numeral", "variable"));
        assert_eq!(
            format!("{d:#}"),
            "under `application ▸ application` at `numeral` against `variable`"
        );
    }

    #[test]
    fn a_difference_at_the_root_stops_there() {
        // The whole node differs, so nothing below it is reported: the path
        // never points past the first thing to fix.
        let d = first_difference(&app(nat(0), nat(1)), &var(3)).expect("differs");
        assert!(d.path.is_empty());
        assert_eq!(d.sides, ("application", "variable"));
    }
}
