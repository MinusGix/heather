//! Gluing a withheld definition at a saturated closed call
//! (`docs/interface-definitions-design.md` §3).
//!
//! In a world with an interface boundary ([`crate::term::GlobalCtx::withheld`])
//! a withheld global evaluates to an *unglued* neutral, as a sealed theorem
//! does: it compares by head and spine and never unfolds. When an
//! application makes its spine reach the declaration's arity, and every
//! argument reads no free local variable, it is glued to its body exactly as
//! [`Eval::global_tm`] glues a definition, and from there it computes as one.
//! The syntax reducer's rule is `reduce::withheld_call`; the two agree on
//! every argument this walk can classify, and where it cannot (a budget
//! spent, a value form it does not open) it answers "open", so the value
//! machine is never the more permissive of the two.

use super::Eval;
use crate::value::{Elim, Head, Lookup, TmClo, VNeutral, Val};

/// Value nodes the closedness walk visits per call before it answers
/// "open". Generous next to the literals a verdict is stated over.
const CLOSED_NODES: u32 = 1 << 14;

impl<'a, 'v> Eval<'a, 'v> {
    /// `n` glued to its withheld body, when `n` is a call of a withheld
    /// global whose spine has just reached its arity at closed arguments.
    /// `None` in every other case, including a call already glued.
    pub(super) fn glue_withheld(&mut self, n: &'v VNeutral<'v>) -> Option<&'v Val<'v>> {
        if n.unfold.is_some() {
            return None;
        }
        let Head::Global { var, subst } = &n.head else { return None };
        let arity = self.defs.withheld(*var)? as usize;
        let mut elims: Vec<&'v Elim<'v>> = n.spine.iter_rev().collect();
        elims.reverse();
        if !elims.iter().all(|e| e.is_application()) {
            return None;
        }
        let args: Vec<&'v TmClo<'v>> = elims
            .iter()
            .filter_map(|e| match e {
                Elim::App { arg, .. } => Some(*arg),
                _ => None,
            })
            .collect();
        // Only at the application that saturates the call: past it the
        // arguments are what they were, so an open call stays open.
        if arity == 0 || args.len() != arity {
            return None;
        }
        let mut budget = CLOSED_NODES;
        if !subst.terms.iter().all(|v| closed_val(v, &mut budget))
            || !args.iter().all(|a| closed_clo(a, 0, &mut budget))
        {
            return None;
        }
        let body = std::sync::Arc::clone(self.defs.withheld_body_unshifted(*var)?);
        crate::withheld::note(self.defs, *var);
        let mut unfold = self.glue(*var, subst, body);
        for e in elims {
            unfold = self.arena.tm(TmClo::elim(unfold, e));
        }
        let glued = self.arena.neutral(VNeutral { head: n.head.clone(), spine: n.spine, unfold: Some(unfold) });
        Some(self.arena.val(Val::Neutral(glued)))
    }
}

/// Whether the closure `c`, under `pending` binders of its own, reads no
/// free local variable. A spent budget answers `false`.
fn closed_clo<'v>(c: &'v TmClo<'v>, pending: u32, budget: &mut u32) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    match c {
        TmClo::Syn { env, body } => {
            // Every `u^δ` carries a substitution tail, so `has_tail` is no
            // sign of a variable: an `·^k` tail reads none. A `wk_g` tail
            // reads a context variable's prefix, which an elaborator's Γ
            // (based at `·`) does not have.
            let used = crate::bounds::term_local_use(body);
            (pending..used.bound).all(|i| {
                if i < 64 && used.uses & (1u64 << i) == 0 {
                    return true;
                }
                match env.lookup(i - pending) {
                    Lookup::Bound(entry) => closed_clo(entry, 0, budget),
                    Lookup::Base(_) => false,
                }
            })
        }
        // A value under a binder ignores it: values are ambient.
        TmClo::Val(v) => closed_val(v, budget),
        TmClo::Elim { head, elim } => closed_clo(head, 0, budget) && closed_elim(elim, budget),
    }
}

fn closed_elim<'v>(e: &'v Elim<'v>, budget: &mut u32) -> bool {
    match e {
        Elim::App { arg, .. } => closed_clo(arg, 0, budget),
        Elim::UApp { .. } => true,
        // Motives, branches and type arguments are not opened: unknown is
        // open.
        _ => false,
    }
}

fn closed_val<'v>(v: &'v Val<'v>, budget: &mut u32) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    macro_rules! c {
        ($x:expr, $p:expr) => {
            closed_clo($x, $p, budget)
        };
    }
    match v {
        Val::TmNat
        | Val::TmTy(_)
        | Val::TmUnit { .. }
        | Val::TmEmpty { .. }
        | Val::TmSEmpty { .. }
        | Val::Zero
        | Val::Triv { .. }
        | Val::BoxTy(_)
        | Val::BoxTm(_) => true,
        Val::TmSquash { ty, .. } => c!(ty, 0),
        Val::TmPi { dom, cod, .. } => c!(dom, 0) && c!(cod, 1),
        Val::TmSigma { fst, snd, .. } => c!(fst, 0) && c!(snd, 1),
        Val::TmW { shape, pos, .. } => c!(shape, 0) && c!(pos, 1),
        Val::TmSum { lhs, rhs, .. } => c!(lhs, 0) && c!(rhs, 0),
        Val::TmVec { elem, len, .. } => c!(elem, 0) && c!(len, 0),
        Val::TmFin { len } => c!(len, 0),
        Val::TmId { ty, lhs, rhs, .. } | Val::TmSEq { ty, lhs, rhs, .. } => c!(ty, 0) && c!(lhs, 0) && c!(rhs, 0),
        Val::Succ(p) => c!(p, 0),
        Val::NatRun { tail, .. } => c!(tail, 0),
        Val::BitRun { tail, tail_len, .. } => c!(tail, 0) && c!(tail_len, 0),
        Val::Refl { tm, .. } | Val::SRefl { tm, .. } | Val::Squash { tm, .. } => c!(tm, 0),
        Val::Pair { fst, snd, .. } => c!(fst, 0) && c!(snd, 0),
        Val::Inl { val, .. } | Val::Inr { val, .. } => c!(val, 0),
        Val::Sup { label, children, .. } | Val::Supi { label, children, .. } => c!(label, 0) && c!(children, 0),
        Val::Supf { arity, label, children, .. } => c!(arity, 0) && c!(label, 0) && c!(children, 0),
        Val::Lam { body, .. } => c!(body, 1),
        // Universe and context binders bind no local variable.
        Val::ULam { body, .. } | Val::CtxLam { body, .. } | Val::TyLam { body, .. } => c!(body, 0),
        Val::Neutral(n) => match &n.head {
            Head::Var(_) | Head::BaseVar(_) | Head::Stuck(_) => false,
            Head::BoxedGlobalTy(_) | Head::BoxedGlobalTm(_) => true,
            Head::Global { subst, .. } => {
                subst.terms.iter().all(|t| closed_val(t, budget))
                    && n.spine.iter_rev().all(|e| closed_elim(e, budget))
            }
        },
        // Folds, induction hypotheses, codata and the rarer type codes are
        // not opened: unknown is open.
        _ => false,
    }
}
