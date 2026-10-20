//! Budget-bounded, syntax-flavored `Debug` for the recursive kernel types.
//!
//! Substitution produces terms whose printed tree can be enormous (and, with
//! sharing, astronomically larger than the memory they occupy). A derived
//! `Debug` will happily build that entire string in RAM — which has OOM'd a
//! machine before it OOM'd a process. These impls make *any* `{:?}` safe:
//! a thread-local node budget is armed at the outermost format call, every
//! node consumes one unit, and an exhausted node prints `…` without
//! recursing, so output size and traversal work are both hard-bounded.
//!
//! The output is compact surface-ish syntax (`λ`, `Π`, `□`, `x0`, `u1^δ`),
//! not derive-style records — meant for reading terms while debugging the
//! kernel, not for round-tripping.
//!
//! [`write_exact`] is the one deliberate way out of the budget: same impls,
//! elision disarmed, for callers that need the *whole* structure (a content
//! hash of elaborated output, say). It streams, and the caller owns the
//! stack-depth risk.
//!
//! # Totality
//!
//! Because `write_exact` reuses these impls as an *identity* for a term, an
//! impl that omits a field is not a rendering choice — it is a blind spot in
//! every hash taken over it (`Branches` printed 37 of its 52 fields, and the
//! Nat suite's golden hash inherited the gap: issues/branches-debug-partial.md).
//! The enum impls are total by construction, since a `match` arm binding every
//! field without `..` is checked by the compiler. The struct impls get the
//! same property the same way: destructure the whole struct, no `..`, under
//! `#[deny(unused_variables)]`, so a new field fails the build until this
//! module learns to print it.

use std::cell::Cell;
use std::fmt;

use crate::level::Level;
use crate::term::{
    Branches, CtxBase, CtxEntries, CtxEntry, IWfSig, LocalCtx, LocalSubst, Motives, SubstTail, Term, Type,
};

/// Maximum nodes printed per outermost format call (bounds output size and
/// total work).
const NODE_BUDGET: isize = 512;

/// Maximum nesting depth printed (bounds stack: debug-build formatter frames
/// are several KB each, and test threads get a 2 MB stack).
const DEPTH_BUDGET: u32 = 64;

thread_local! {
    /// Remaining node budget; negative means "no format call in progress".
    static REMAINING: Cell<isize> = const { Cell::new(-1) };
    /// Current nesting depth within the outermost format call.
    static DEPTH: Cell<u32> = const { Cell::new(0) };
    /// Set for the duration of [`write_exact`]: no elision at all.
    static EXACT: Cell<bool> = const { Cell::new(false) };
}

/// Wrap one node's formatting: arms the budget at the outermost call,
/// consumes one unit per node, and prints `…` instead of recursing when
/// either the node budget or the depth budget is spent.
pub(crate) fn node(
    f: &mut fmt::Formatter<'_>,
    body: impl FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    REMAINING.with(|r| {
        DEPTH.with(|d| {
            let exact = EXACT.with(Cell::get);
            let outermost = r.get() < 0;
            if outermost {
                // In exact mode the counter must never reach 0, or a nested
                // call would mistake `r < 0` for "outermost" and re-arm.
                r.set(if exact { isize::MAX } else { NODE_BUDGET });
                d.set(0);
            }
            let spent = !exact && (r.get() == 0 || d.get() >= DEPTH_BUDGET);
            let res = if spent {
                f.write_str("…")
            } else {
                r.set(r.get() - 1);
                d.set(d.get() + 1);
                let res = body(f);
                d.set(d.get() - 1);
                res
            };
            if outermost {
                r.set(-1);
            }
            res
        })
    })
}

/// Render `value` with **no elision at all**, streaming it into `sink`.
///
/// The `Debug` impls below are budget-bounded on purpose (see the module
/// docs); that makes them unusable as an identity for a term — two different
/// terms sharing a 512-node prefix print the same. This escape hatch reuses
/// exactly those impls with both budgets disarmed, so the result is a total,
/// deterministic, injective-enough-for-hashing rendering of the whole
/// structure. It is what a content hash of elaborated output must be taken
/// over (issues/elaboration-determinism.md,
/// issues/parallel-checking-and-caching.md).
///
/// Two costs the caller is accepting by choosing it, and the reason the
/// default stays bounded:
///
/// - **Unbounded output.** Stream it — into a hasher, a file, a
///   `LineWriter` — rather than into a `String`; substitution can make the
///   printed tree astronomically larger than the term in memory.
/// - **Unbounded recursion.** Formatter frames are several KB in a debug
///   build, so a deep term can overflow a small stack. Callers run on a
///   thread with a raised stack (`scripts/test` sets `RUST_MIN_STACK`).
///
/// Not for diagnostics, and never for a `{:?}` reached by accident: every
/// use should be a deliberate "I want the exact structure".
pub fn write_exact(sink: &mut impl fmt::Write, value: &impl fmt::Debug) -> fmt::Result {
    struct Guard(bool);
    impl Drop for Guard {
        fn drop(&mut self) {
            EXACT.with(|e| e.set(self.0));
        }
    }
    // A guard, not a plain reset: `write!` can return early on sink error,
    // and a leaked `EXACT` would silently unbound every later `{:?}`. It
    // restores the previous value so a nested call re-nests correctly.
    let _guard = Guard(EXACT.with(|e| e.replace(true)));
    write!(sink, "{value:?}")
}

impl fmt::Debug for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            // Collapse `1 + (1 + …)` prefixes into a numeral.
            let mut n = 0u64;
            let mut cur = self;
            while let Level::Succ(inner) = cur {
                n += 1;
                cur = inner;
            }
            if n > 0 && !matches!(cur, Level::Zero) {
                write!(f, "{n}+")?;
            }
            match cur {
                Level::Zero => write!(f, "{n}"),
                Level::Var(v) => write!(f, "ℓ{}", v.0),
                Level::Max(a, b) => write!(f, "({a:?} ⊔ {b:?})"),
                Level::Omega => f.write_str("ω"),
                Level::Succ(_) => unreachable!(),
            }
        })
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            Type::Nat => f.write_str("Nat"),
            Type::Pi { dom_level, cod_level, dom, cod } => {
                write!(f, "Π[{dom_level:?},{cod_level:?}]({dom:?}). {cod:?}")
            }
            Type::Ty(l) => write!(f, "Ty {l:?}"),
            Type::UPi { num_vars, level, body } => {
                write!(f, "ΠΠ[{num_vars}ℓ@{level:?}]. {body:?}")
            }
            Type::El { level, tm } => write!(f, "El[{level:?}]({tm:?})"),
            Type::Id { level, ty, lhs, rhs } => {
                write!(f, "Id[{level:?}]({ty:?}; {lhs:?}; {rhs:?})")
            }
            Type::SEq { level, ty, lhs, rhs } => {
                write!(f, "sEq[{level:?}]({ty:?}; {lhs:?}; {rhs:?})")
            }
            Type::SEmpty { level } => write!(f, "sEmpty {level:?}"),
            Type::Squash { level, ty } => write!(f, "Squash[{level:?}]({ty:?})"),
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                write!(f, "Σ[{fst_level:?},{snd_level:?}]({fst:?}). {snd:?}")
            }
            Type::Unit { level } => write!(f, "Unit {level:?}"),
            Type::Empty { level } => write!(f, "Empty {level:?}"),
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => {
                write!(f, "({lhs:?} +[{lhs_level:?},{rhs_level:?}] {rhs:?})")
            }
            Type::W { shape_level, pos_level, shape, pos } => {
                write!(f, "W[{shape_level:?},{pos_level:?}]({shape:?}). {pos:?}")
            }
            Type::Vec { level, elem, len } => write!(f, "Vec[{level:?}]({elem:?}; {len:?})"),
            Type::Fin { len } => write!(f, "Fin({len:?})"),
            Type::Wf { level, shape, arity } => {
                write!(f, "Wf[{level:?}]({shape:?}). {arity:?}")
            }
            Type::DVec { level, len, fam } => write!(f, "DVec[{level:?}]({len:?}; {fam:?})"),
            Type::IWf { sig, index } => {
                let IWfSig { level, idx_level, idx, shape, arity, out, child } = &**sig;
                write!(
                    f,
                    "IWf[{level:?},{idx_level:?}]({idx:?}; {shape:?}. {arity:?}; {out:?}; {child:?})({index:?})"
                )
            }
            Type::GlobalTy { var, subst } => write!(f, "U{}^{subst:?}", var.0),
            Type::CtxPi { level, body } => write!(f, "Π[g:Ctx@{level:?}]. {body:?}"),
            Type::TyPi { ctx, arg_level, body_level, body } => {
                write!(f, "Π[U:Typ({ctx:?},{arg_level:?})@{body_level:?}]. {body:?}")
            }
            Type::CodeTy { ctx, level } => write!(f, "□({ctx:?} ⊢ Ty {level:?})"),
            Type::CodeTm { ctx, ty, level } => {
                write!(f, "□({ctx:?} ⊢ {ty:?} @ {level:?})")
            }
        })
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            Term::Var(v) => write!(f, "x{}", v.0),
            Term::TmNat => f.write_str("«Nat»"),
            Term::TmPi { dom_level, cod_level, dom, cod } => {
                write!(f, "«Π[{dom_level:?},{cod_level:?}]({dom:?}). {cod:?}»")
            }
            Term::TmTy(l) => write!(f, "«Ty {l:?}»"),
            Term::TmId { level, ty, lhs, rhs } => {
                write!(f, "«Id[{level:?}]({ty:?}; {lhs:?}; {rhs:?})»")
            }
            Term::TmSigma { fst_level, snd_level, fst, snd } => {
                write!(f, "«Σ[{fst_level:?},{snd_level:?}]({fst:?}). {snd:?}»")
            }
            Term::TmUnit { level } => write!(f, "«Unit {level:?}»"),
            Term::TmEmpty { level } => write!(f, "«Empty {level:?}»"),
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => {
                write!(f, "«({lhs:?} +[{lhs_level:?},{rhs_level:?}] {rhs:?})»")
            }
            Term::TmW { shape_level, pos_level, shape, pos } => {
                write!(f, "«W[{shape_level:?},{pos_level:?}]({shape:?}). {pos:?}»")
            }
            Term::TmVec { level, elem, len } => {
                write!(f, "«Vec[{level:?}]({elem:?}; {len:?})»")
            }
            Term::TmFin { len } => write!(f, "«Fin({len:?})»"),
            Term::TmWf { level, shape, arity } => {
                write!(f, "«Wf[{level:?}]({shape:?}). {arity:?}»")
            }
            Term::Zero => f.write_str("0"),
            Term::NatLit(n) => write!(f, "{n}"),
            Term::Succ(t) => write!(f, "S({t:?})"),
            Term::ElimNat { level, motive, base, step, scrut } => write!(
                f,
                "elimN[{level:?}](M {motive:?}; z {base:?}; s {step:?}; {scrut:?})"
            ),
            Term::Refl { level, ty, tm } => write!(f, "refl[{level:?}]({ty:?}; {tm:?})"),
            Term::SRefl { level, ty, tm } => write!(f, "srefl[{level:?}]({ty:?}; {tm:?})"),
            Term::TmSEq { level, ty, lhs, rhs } => {
                write!(f, "«sEq»[{level:?}]({ty:?}; {lhs:?}; {rhs:?})")
            }
            Term::TmSEmpty { level } => write!(f, "«sEmpty» {level:?}"),
            Term::TmSquash { level, ty } => write!(f, "«Squash»[{level:?}]({ty:?})"),
            Term::Squash { level, ty, tm } => {
                write!(f, "squash[{level:?}]({ty:?}; {tm:?})")
            }
            Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => write!(
                f,
                "transp[{ty_level:?},{motive_level:?}]({ty:?}; x.{motive:?}; {lhs:?}; {rhs:?}; {proof:?}; {tm:?})"
            ),
            Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
                write!(f, "elim_sEmpty[{level:?},{scrut_level:?}](x. {motive:?}; {scrut:?})")
            }
            Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => write!(
                f,
                "elim_Squash[{src_level:?},{dst_level:?}]({src_ty:?}; z.{motive:?}; x.{case:?}; {scrut:?})"
            ),
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => write!(
                f,
                "J[{ty_level:?},{motive_level:?}]({ty:?}; a {lhs:?}; M {motive:?}; c {case:?}; {rhs:?}; {proof:?})"
            ),
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => write!(
                f,
                "pair[{fst_level:?},{snd_level:?}]({fst_ty:?}. {snd_ty:?}; {fst:?}; {snd:?})"
            ),
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => write!(
                f,
                "fst[{fst_level:?},{snd_level:?}]({fst_ty:?}. {snd_ty:?}; {pair:?})"
            ),
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => write!(
                f,
                "snd[{fst_level:?},{snd_level:?}]({fst_ty:?}. {snd_ty:?}; {pair:?})"
            ),
            // The checked spellings print with `@` and their one
            // annotation, so a `{:?}` says at a glance which spelling a term
            // carries. Budget-bounded like everything here.
            Term::PairAt { ty: Some(ty), fst, snd } => {
                write!(f, "pair@({ty:?}; {fst:?}; {snd:?})")
            }
            Term::PairAt { ty: None, fst, snd } => write!(f, "pair@({fst:?}; {snd:?})"),
            Term::InlAt { ty: Some(ty), val } => write!(f, "inl@({ty:?}; {val:?})"),
            Term::InlAt { ty: None, val } => write!(f, "inl@({val:?})"),
            Term::InrAt { ty: Some(ty), val } => write!(f, "inr@({ty:?}; {val:?})"),
            Term::InrAt { ty: None, val } => write!(f, "inr@({val:?})"),
            Term::FstAt { pair } => write!(f, "fst@({pair:?})"),
            Term::SndAt { pair } => write!(f, "snd@({pair:?})"),
            Term::AppAt { fun, arg } => write!(f, "app@({fun:?}; {arg:?})"),
            Term::Triv { level } => write!(f, "⟨⟩{level:?}"),
            Term::ElimEmpty { level, scrut_level, motive, scrut } => {
                write!(f, "elimE[{level:?},{scrut_level:?}](M {motive:?}; {scrut:?})")
            }
            Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => write!(
                f,
                "inl[{lhs_level:?},{rhs_level:?}]({lhs:?}; {rhs:?}; {val:?})"
            ),
            Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => write!(
                f,
                "inr[{lhs_level:?},{rhs_level:?}]({lhs:?}; {rhs:?}; {val:?})"
            ),
            Term::Case {
                lhs_level,
                rhs_level,
                motive_level,
                lhs,
                rhs,
                motive,
                case_l,
                case_r,
                scrut,
            } => write!(
                f,
                "case[{lhs_level:?},{rhs_level:?},{motive_level:?}](M {motive:?}; {lhs:?}; {rhs:?}; l {case_l:?}; r {case_r:?}; {scrut:?})"
            ),
            Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => write!(
                f,
                "sup[{shape_level:?},{pos_level:?}]({shape_ty:?}. {pos_ty:?}; {label:?}; {children:?})"
            ),
            Term::ElimW {
                shape_level,
                pos_level,
                motive_level,
                shape,
                pos,
                motive,
                step,
                scrut,
            } => write!(
                f,
                "elimW[{shape_level:?},{pos_level:?},{motive_level:?}]({shape:?}. {pos:?}; M {motive:?}; s {step:?}; {scrut:?})"
            ),
            Term::Supf { level, shape, arity, label, children } => write!(
                f,
                "supf[{level:?}]({shape:?}. {arity:?}; {label:?}; {children:?})"
            ),
            Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => write!(
                f,
                "elimWf[{level:?},{motive_level:?}]({shape:?}. {arity:?}; M {motive:?}; s {step:?}; {scrut:?})"
            ),
            Term::Supi { sig, label, children } => {
                let IWfSig { level, idx_level, idx, shape, arity, out, child } = &**sig;
                write!(
                    f,
                    "supi[{level:?},{idx_level:?}]({idx:?}; {shape:?}. {arity:?}; {out:?}; {child:?}; {label:?}; {children:?})"
                )
            }
            Term::ElimIWf { sig, motive_level, motive, step, index, scrut } => {
                let IWfSig { level, idx_level, idx, shape, arity, out, child } = &**sig;
                write!(
                    f,
                    "elimIWf[{level:?},{idx_level:?},{motive_level:?}]({idx:?}; {shape:?}. {arity:?}; {out:?}; {child:?}; M {motive:?}; s {step:?}; {index:?}; {scrut:?})"
                )
            }
            Term::Lam { dom_level, cod_level, dom, body } => {
                write!(f, "λ[{dom_level:?},{cod_level:?}]({dom:?}). {body:?}")
            }
            Term::App { fun, dom_level, cod_level, dom, cod, arg } => write!(
                f,
                "app({fun:?}; [{dom_level:?},{cod_level:?}] {dom:?} → {cod:?}; {arg:?})"
            ),
            Term::ULam { num_vars, level, body } => {
                write!(f, "Λ[{num_vars}ℓ@{level:?}]. {body:?}")
            }
            Term::UApp { fun, levels } => {
                write!(f, "({fun:?} $")?;
                for l in levels {
                    write!(f, " {l:?}")?;
                }
                f.write_str(")")
            }
            Term::GlobalTm { var, subst } => write!(f, "u{}^{subst:?}", var.0),
            Term::CtxLam { level, body } => write!(f, "Λ[g:Ctx@{level:?}]. {body:?}"),
            Term::CtxApp { fun, ctx } => write!(f, "capp({fun:?}, {ctx:?})"),
            Term::TyLam { ctx, arg_level, body_level, body } => {
                write!(f, "Λ[U:Typ({ctx:?},{arg_level:?})@{body_level:?}]. {body:?}")
            }
            Term::TyApp { fun, arg } => write!(f, "tapp({fun:?}, {arg:?})"),
            Term::BoxTy(t) => write!(f, "box({t:?})"),
            Term::BoxTm(t) => write!(f, "box({t:?})"),
            Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => write!(
                f,
                "letboxT[{motive_level:?},{code_level:?}]({ctx:?}; M {motive:?}; U. {body:?}; {scrut:?})"
            ),
            Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => write!(
                f,
                "letboxt[{motive_level:?},{code_level:?}]({ctx:?} ⊢ {ty:?}; M {motive:?}; u. {body:?}; {scrut:?})"
            ),
            Term::ElimCodeTy {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                scrut,
            } => write!(
                f,
                "elimTy[{ty_motive_level:?},{tm_motive_level:?}]({motives:?}; {branches:?}; @{code_level:?} {ctx:?}; {scrut:?})"
            ),
            Term::ElimCodeTm {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                ty,
                scrut,
            } => write!(
                f,
                "elimTm[{ty_motive_level:?},{tm_motive_level:?}]({motives:?}; {branches:?}; @{code_level:?} {ctx:?} ⊢ {ty:?}; {scrut:?})"
            ),
        })
    }
}

impl fmt::Debug for LocalCtx {
    #[deny(unused_variables)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let LocalCtx { base, entries } = self;
        node(f, |f| {
            f.write_str("(")?;
            match base {
                CtxBase::Nil => f.write_str("·")?,
                CtxBase::Var(g) => write!(f, "g{}", g.0)?,
            }
            for CtxEntry { ty, level } in entries {
                write!(f, ", {ty:?}@{level:?}")?;
            }
            f.write_str(")")
        })
    }
}

/// The entries alone, outermost-first, in [`LocalCtx`]'s own notation minus
/// the base. Manual and `node()`-gated like every other recursive kernel
/// type: a spine is still a tree of types, and an accidental `{:?}` on one
/// must stay bounded (see this module's docs).
impl fmt::Debug for CtxEntries {
    #[deny(unused_variables)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            let mut first = true;
            for CtxEntry { ty, level } in self {
                if !first {
                    f.write_str(", ")?;
                }
                first = false;
                write!(f, "{ty:?}@{level:?}")?;
            }
            Ok(())
        })
    }
}

impl fmt::Debug for LocalSubst {
    #[deny(unused_variables)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let LocalSubst { tail, terms } = self;
        node(f, |f| {
            f.write_str("{")?;
            match *tail {
                SubstTail::Empty { len, base: CtxBase::Nil } => write!(f, "·^{len}")?,
                SubstTail::Empty { len, base: CtxBase::Var(g) } => {
                    write!(f, "·^{len}_g{}", g.0)?
                }
                SubstTail::Wk { len, ctx_var } => write!(f, "wk^{len}_g{}", ctx_var.0)?,
            }
            for t in terms {
                write!(f, "; {t:?}")?;
            }
            f.write_str("}")
        })
    }
}

impl fmt::Debug for Motives {
    #[deny(unused_variables)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Motives { ty_motive, tm_motive } = self;
        node(f, |f| write!(f, "M⃗(Typ {ty_motive:?}; Trm {tm_motive:?})"))
    }
}

/// All 56 branches, labelled and in declaration order — the same order and
/// the same no-`..` destructuring as the cache's structural walker
/// (`heather_cache::merkle`), so the printed form and the content hash cannot
/// disagree about what a recursor *is*.
impl fmt::Debug for Branches {
    #[deny(unused_variables)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Branches {
            ty_nat,
            ty_pi,
            ty_ty,
            ty_el,
            ty_id,
            ty_sigma,
            ty_unit,
            ty_empty,
            tm_var,
            tm_nat,
            tm_pi,
            tm_ty,
            tm_zero,
            tm_succ,
            tm_elim_nat,
            tm_lam,
            tm_app,
            tm_id,
            tm_refl,
            tm_j,
            tm_sigma,
            tm_pair,
            tm_fst,
            tm_snd,
            tm_unit,
            tm_empty,
            tm_triv,
            tm_elim_empty,
            ty_sum,
            tm_sum,
            tm_inl,
            tm_inr,
            tm_case,
            ty_w,
            tm_w,
            tm_sup,
            tm_elim_w,
            ty_vec,
            tm_vec,
            ty_fin,
            tm_fin,
            ty_wf,
            tm_wf,
            tm_supf,
            tm_elim_wf,
            ty_seq,
            tm_seq,
            ty_sempty,
            tm_sempty,
            tm_srefl,
            tm_transp,
            tm_elim_sempty,
            ty_squash,
            tm_squash,
            tm_squash_in,
            tm_elim_squash,
        } = self;
        node(f, |f| {
            f.write_str("b⃗(")?;
            let mut first = true;
            for (label, branch) in [
                ("Nat", ty_nat),
                ("Π", ty_pi),
                ("Ty", ty_ty),
                ("El", ty_el),
                ("Id", ty_id),
                ("Σ", ty_sigma),
                ("Unit", ty_unit),
                ("Empty", ty_empty),
                ("x", tm_var),
                ("«Nat»", tm_nat),
                ("«Π»", tm_pi),
                ("«Ty»", tm_ty),
                ("0", tm_zero),
                ("S", tm_succ),
                ("elimN", tm_elim_nat),
                ("λ", tm_lam),
                ("app", tm_app),
                ("«Id»", tm_id),
                ("refl", tm_refl),
                ("J", tm_j),
                ("«Σ»", tm_sigma),
                ("pair", tm_pair),
                ("fst", tm_fst),
                ("snd", tm_snd),
                ("«Unit»", tm_unit),
                ("«Empty»", tm_empty),
                ("⟨⟩", tm_triv),
                ("elimE", tm_elim_empty),
                ("+", ty_sum),
                ("«+»", tm_sum),
                ("inl", tm_inl),
                ("inr", tm_inr),
                ("case", tm_case),
                ("W", ty_w),
                ("«W»", tm_w),
                ("sup", tm_sup),
                ("elimW", tm_elim_w),
                ("Vec", ty_vec),
                ("«Vec»", tm_vec),
                ("Fin", ty_fin),
                ("«Fin»", tm_fin),
                ("Wf", ty_wf),
                ("«Wf»", tm_wf),
                ("supf", tm_supf),
                ("elimWf", tm_elim_wf),
                ("sEq", ty_seq),
                ("«sEq»", tm_seq),
                ("sEmpty", ty_sempty),
                ("«sEmpty»", tm_sempty),
                ("srefl", tm_srefl),
                ("transp", tm_transp),
                ("elim_sEmpty", tm_elim_sempty),
                ("Squash", ty_squash),
                ("«Squash»", tm_squash),
                ("squash", tm_squash_in),
                ("elim_Squash", tm_elim_squash),
            ] {
                if !first {
                    f.write_str("; ")?;
                }
                first = false;
                write!(f, "{label} {branch:?}")?;
            }
            f.write_str(")")
        })
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc as Rc;

    use crate::level::Level;
    use crate::term::{Term, Type};

    /// A DAG whose tree-expansion is 2^64 nodes: formatting must stay
    /// bounded in both output size and time.
    #[test]
    fn debug_of_exponential_dag_is_bounded() {
        let mut t = Rc::new(Term::Zero);
        for _ in 0..64 {
            t = Rc::new(Term::App {
                fun: Rc::clone(&t),
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Nat),
                arg: Rc::clone(&t),
            });
        }
        let s = format!("{t:?}");
        assert!(s.len() < 128 * 1024, "unbounded debug output: {} bytes", s.len());
        assert!(s.contains('…'), "expected elision marker in bounded output");
    }

    /// The budget re-arms per outermost call: repeated formats of the same
    /// value agree (no leakage of a half-spent budget).
    #[test]
    fn budget_rearms_between_calls() {
        let mut t = Rc::new(Term::Zero);
        for _ in 0..2000 {
            t = Rc::new(Term::Succ(t));
        }
        let a = format!("{t:?}");
        let b = format!("{t:?}");
        assert_eq!(a, b);
        assert!(a.contains('…'));
    }

    #[test]
    fn small_terms_print_fully_and_readably() {
        let id = Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::Var(crate::term::LocalVar(0))),
        };
        assert_eq!(format!("{id:?}"), "λ[0,0](Nat). x0");
    }
}
