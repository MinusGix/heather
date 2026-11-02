//! Gluing a withheld definition at a saturated closed call
//! (`docs/interface-definitions-design.md` §3).
//!
//! In a world with an interface boundary ([`crate::term::GlobalCtx::withheld`])
//! a withheld global evaluates to an *unglued* neutral, as a sealed theorem
//! does: it compares by head and spine and never unfolds. When an
//! application makes its spine reach the declaration's arity, and every
//! argument reads no free local variable, it is glued to its body exactly as
//! [`Eval::global_tm`] glues a definition, and from there it computes as one.
//!
//! Closedness is decided by **forcing**: an argument is forced to its weak
//! head and its parts are walked, forced in turn, from a work list under a
//! node budget. A lazy argument is usually a computation in flight (an
//! induction hypothesis, a call of another definition), which only forcing
//! can classify; a call at closed arguments computes once it reads them
//! anyway. A binder's body cannot be forced and is classified by its
//! syntax and environment instead ([`closed_clo`]). Anything the walk does
//! not open, a spent budget and an evaluation error all answer "open":
//! unknown means atom.
//!
//! The syntax reducer's rule is `reduce::withheld_call`, which asks only
//! that the argument terms be syntactically closed. The two can differ on an
//! argument that names a variable and does not read it (`K(0, x)`): the
//! value machine glues there and the reducer does not. Both only ever
//! unfold the body ordinary δ would, so either is sound.

use super::Eval;
use crate::value::{Elim, Head, Lookup, TmClo, VNeutral, Val};

/// Value nodes the closedness walk visits per call before it answers
/// "open". Generous next to the literals a verdict is stated over.
const CLOSED_NODES: u32 = 1 << 14;

/// One step of the closedness walk.
enum Item<'v> {
    Clo(&'v TmClo<'v>),
    Val(&'v Val<'v>),
}

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
        let mut work: Vec<Item<'v>> = subst.terms.iter().map(|v| Item::Val(*v)).collect();
        work.extend(args.iter().map(|a| Item::Clo(*a)));
        if !self.closed(work) {
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

    /// Whether every item reads no free local variable, forcing what it
    /// visits (module docs). Iterative, so a long closed list costs no
    /// native depth.
    fn closed(&mut self, mut work: Vec<Item<'v>>) -> bool {
        let mut budget = CLOSED_NODES;
        while let Some(item) = work.pop() {
            if budget == 0 {
                return false;
            }
            budget -= 1;
            let v = match item {
                Item::Val(v) => v,
                Item::Clo(c) => match self.force(c) {
                    Ok(v) => v,
                    Err(_) => return false,
                },
            };
            if !parts(v, &mut work, &mut budget) {
                return false;
            }
        }
        true
    }
}

/// Push `v`'s parts onto the walk; `false` when `v` is open or of a form the
/// walk does not open.
fn parts<'v>(v: &'v Val<'v>, work: &mut Vec<Item<'v>>, budget: &mut u32) -> bool {
    macro_rules! push {
        ($($c:expr),*) => {{ $(work.push(Item::Clo($c));)* }};
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
        | Val::BoxTm(_) => {}
        Val::TmSquash { ty, .. } => push!(ty),
        Val::TmSum { lhs, rhs, .. } => push!(lhs, rhs),
        Val::TmVec { elem, len, .. } => push!(elem, len),
        Val::TmFin { len } => push!(len),
        Val::TmId { ty, lhs, rhs, .. } | Val::TmSEq { ty, lhs, rhs, .. } => push!(ty, lhs, rhs),
        Val::Succ(p) => push!(p),
        Val::NatRun { tail, .. } => push!(tail),
        Val::BitRun { tail, tail_len, .. } => push!(tail, tail_len),
        Val::Refl { tm, .. } | Val::SRefl { tm, .. } | Val::Squash { tm, .. } => push!(tm),
        Val::Pair { fst, snd, .. } => push!(fst, snd),
        Val::Inl { val, .. } | Val::Inr { val, .. } => push!(val),
        Val::Sup { label, children, .. } | Val::Supi { label, children, .. } => push!(label, children),
        Val::Supf { arity, label, children, .. } => push!(arity, label, children),
        // Universe and context binders bind no local variable.
        Val::ULam { body, .. } | Val::CtxLam { body, .. } | Val::TyLam { body, .. } => push!(body),
        // A term binder's body cannot be forced: its syntax decides.
        Val::Lam { body, .. } => return closed_clo(body, 1, budget),
        Val::TmPi { dom, cod, .. } => return { push!(dom); closed_clo(cod, 1, budget) },
        Val::TmSigma { fst, snd, .. } => return { push!(fst); closed_clo(snd, 1, budget) },
        Val::TmW { shape, pos, .. } => return { push!(shape); closed_clo(pos, 1, budget) },
        Val::Neutral(n) => match &n.head {
            Head::Var(_) | Head::BaseVar(_) | Head::Stuck(_) => return false,
            Head::BoxedGlobalTy(_) | Head::BoxedGlobalTm(_) => {}
            // A global the force left neutral: opaque, sealed, or a
            // withheld call that stayed withheld. Closed when its universe
            // substitution and its arguments are.
            Head::Global { subst, .. } => {
                work.extend(subst.terms.iter().map(|t| Item::Val(*t)));
                for e in n.spine.iter_rev() {
                    match e {
                        Elim::App { arg, .. } => work.push(Item::Clo(*arg)),
                        Elim::UApp { .. } => {}
                        _ => return false,
                    }
                }
            }
        },
        // Folds, codata and the rarer type codes are not opened: unknown
        // is open.
        _ => return false,
    }
    true
}

/// Whether the closure `c`, under `pending` binders of its own, reads no
/// free local variable, by its syntax and environment, without forcing.
/// A spent budget answers `false`.
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
        TmClo::Val(v) => {
            // A value under a binder ignores it: values are ambient. Walk
            // it without forcing (there is no machine here).
            let mut work = Vec::new();
            if !parts(v, &mut work, budget) {
                return false;
            }
            work.into_iter().all(|item| match item {
                Item::Clo(c) => closed_clo(c, 0, budget),
                Item::Val(v) => closed_clo_val(v, budget),
            })
        }
        TmClo::Elim { head, elim } => {
            closed_clo(head, 0, budget)
                && match elim {
                    Elim::App { arg, .. } => closed_clo(arg, 0, budget),
                    Elim::UApp { .. } => true,
                    // Motives, branches and type arguments are not opened
                    // here: unknown is open.
                    _ => false,
                }
        }
    }
}

fn closed_clo_val<'v>(v: &'v Val<'v>, budget: &mut u32) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    let mut work = Vec::new();
    parts(v, &mut work, budget)
        && work.into_iter().all(|item| match item {
            Item::Clo(c) => closed_clo(c, 0, budget),
            Item::Val(v) => closed_clo_val(v, budget),
        })
}
