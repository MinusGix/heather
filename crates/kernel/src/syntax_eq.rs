//! Structural equality on syntax, in the shared size of the two sides.
//!
//! `==` on [`Type`] and [`Term`] is the α-test (de Bruijn syntax makes it
//! plain structural equality), and it sits on every conversion query's path:
//! `Tc::conv_ty`'s reflexivity shortcut is `expected == inferred`, and the
//! elaborator asks the same question before it records a `refl` note. A
//! derived `==` gets `Rc::ptr_eq` for free at each child (std's `Arc`
//! equality tries it first), so a DAG compared with *itself* is cheap. Two
//! equal DAGs built separately are not: the derived walk visits the pair of
//! a shared node once per path to it, 2^k for a k-link let chain stated
//! twice (`issues/kernel-equality-walks-dags-as-trees.md`).
//!
//! So equality here is written per variant over [`SharedEq`], which threads
//! one [`PairMemo`] through a whole comparison: a pair of nodes found equal
//! is recorded by both addresses, and a second path into the same pair is
//! answered from the record. Two properties make that safe without any
//! argument about the terms:
//!
//! - **Addresses cannot be reused while the memo lives.** The memo is local
//!   to one top-level `==` call, every node it records is reachable from the
//!   two roots that call borrows, and nothing under a shared `&` is freed.
//!   (`subst.rs`'s `NodeMemo` needs keep-alive clones because its traversal
//!   builds and drops nodes; this one only reads.)
//! - **The memo changes work, never the answer.** An entry is written only
//!   after its pair compared equal, and a comparison stops at its first
//!   inequality, so only equal pairs are ever looked up. It is consulted
//!   only when both nodes have `Rc::strong_count > 1`, since only those can
//!   be reached twice (the first node of any repeated region has two
//!   parents), and the count is a filter, never part of the answer: an
//!   `Arc` handle held elsewhere makes an unshared node look shared, which
//!   costs a table entry and nothing else.
//!
//! The memo is a [`FewMap`]: a comparison of unshared syntax (most of them)
//! costs the derived walk and no more, and one that meets a few shared pairs
//! (most of the rest) records them without allocating. Debug
//! builds compare one level again behind a sample of hits, as `subst.rs`
//! does for its own memo.
//!
//! Every enum match below is exhaustive on `self` and every struct is
//! destructured whole, so a new variant or field does not compile until it
//! is compared.

use crate::rc::Rc;

use crate::level::Level;
use crate::term::*;
use crate::few_map::FewMap;

/// Equality threading one comparison's [`PairMemo`].
pub(crate) trait SharedEq {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool;
}

/// The pairs of shared nodes one comparison has found equal, and what it
/// did, for [`crate::stats`].
#[derive(Default)]
pub(crate) struct PairMemo {
    equal: FewMap<(usize, usize), ()>,
    nodes: u64,
    hits: u64,
}

impl PairMemo {
    /// Compare `a` and `b` with a fresh memo, reporting its work once.
    fn run<T: SharedEq + ?Sized>(a: &T, b: &T) -> bool {
        let mut m = PairMemo::default();
        let eq = a.shared_eq(b, &mut m);
        if m.nodes > 0 {
            crate::stats::syntax_eq_nodes(m.nodes);
        }
        if m.hits > 0 {
            crate::stats::syntax_eq_memo_hits(m.hits);
        }
        eq
    }
}

impl<T: SharedEq> SharedEq for Rc<T> {
    #[inline]
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        if Rc::ptr_eq(self, other) {
            return true;
        }
        m.nodes += 1;
        if Rc::strong_count(self) == 1 || Rc::strong_count(other) == 1 {
            return (**self).shared_eq(other, m);
        }
        let key = (Rc::as_ptr(self) as usize, Rc::as_ptr(other) as usize);
        if m.equal.contains_key(&key) {
            m.hits += 1;
            #[cfg(debug_assertions)]
            if crate::checks::verify_this_skip() {
                // Compared again with no pair under it compared again in
                // turn, and with the walk's own counts put back.
                let counted = (m.nodes, m.hits);
                let again = crate::checks::rederive(crate::checks::Claim::Kept, || (**self).shared_eq(other, m));
                (m.nodes, m.hits) = counted;
                assert!(
                    again,
                    "syntax equality memoized a pair that comparing it again finds unequal \
                     (term output suppressed: see CLAUDE.md)"
                );
            }
            return true;
        }
        let eq = (**self).shared_eq(other, m);
        if eq {
            m.equal.insert(key, ());
        }
        eq
    }
}

impl<T: SharedEq> SharedEq for Vec<T> {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        self.len() == other.len() && self.iter().zip(other).all(|(a, b)| a.shared_eq(b, m))
    }
}

impl<T: SharedEq> SharedEq for Option<T> {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        match (self, other) {
            (Some(a), Some(b)) => a.shared_eq(b, m),
            (None, None) => true,
            _ => false,
        }
    }
}

/// Leaves: no syntax below them, so their own `==`.
macro_rules! leaf_eq {
    ($($t:ty),*) => {$(
        impl SharedEq for $t {
            #[inline]
            fn shared_eq(&self, other: &Self, _: &mut PairMemo) -> bool {
                self == other
            }
        }
    )*};
}

leaf_eq!(u32, Level, LocalVar, GlobalVar, Numeral, CtxBase, SubstTail);

/// `PartialEq` as one memoized comparison.
macro_rules! memo_partial_eq {
    ($($t:ty),*) => {$(
        impl PartialEq for $t {
            fn eq(&self, other: &Self) -> bool {
                PairMemo::run(self, other)
            }
        }
    )*};
}

memo_partial_eq!(Type, Term, Motives, Branches, IWfSig, MSig, LocalSubst, LocalCtx, CtxEntry, CtxEntries);

impl SharedEq for Type {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        match self {
            Type::Nat => matches!(other, Type::Nat),
            Type::Pi { dom_level, cod_level, dom, cod } => {
                let Type::Pi {
                    dom_level: o_dom_level, cod_level: o_cod_level, dom: o_dom, cod: o_cod,
                } = other else { return false };
                dom_level.shared_eq(o_dom_level, m) && cod_level.shared_eq(o_cod_level, m)
                    && dom.shared_eq(o_dom, m) && cod.shared_eq(o_cod, m)
            }
            Type::Ty(a0) => {
                let Type::Ty(b0) = other else { return false };
                a0.shared_eq(b0, m)
            }
            Type::UPi { num_vars, level, body } => {
                let Type::UPi {
                    num_vars: o_num_vars, level: o_level, body: o_body,
                } = other else { return false };
                num_vars.shared_eq(o_num_vars, m) && level.shared_eq(o_level, m)
                    && body.shared_eq(o_body, m)
            }
            Type::El { level, tm } => {
                let Type::El { level: o_level, tm: o_tm } = other else { return false };
                level.shared_eq(o_level, m) && tm.shared_eq(o_tm, m)
            }
            Type::Id { level, ty, lhs, rhs } => {
                let Type::Id {
                    level: o_level, ty: o_ty, lhs: o_lhs, rhs: o_rhs,
                } = other else { return false };
                level.shared_eq(o_level, m) && ty.shared_eq(o_ty, m) && lhs.shared_eq(o_lhs, m)
                    && rhs.shared_eq(o_rhs, m)
            }
            Type::SEq { level, ty, lhs, rhs } => {
                let Type::SEq {
                    level: o_level, ty: o_ty, lhs: o_lhs, rhs: o_rhs,
                } = other else { return false };
                level.shared_eq(o_level, m) && ty.shared_eq(o_ty, m) && lhs.shared_eq(o_lhs, m)
                    && rhs.shared_eq(o_rhs, m)
            }
            Type::SEmpty { level } => {
                let Type::SEmpty { level: o_level } = other else { return false };
                level.shared_eq(o_level, m)
            }
            Type::Squash { level, ty } => {
                let Type::Squash { level: o_level, ty: o_ty } = other else { return false };
                level.shared_eq(o_level, m) && ty.shared_eq(o_ty, m)
            }
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                let Type::Sigma {
                    fst_level: o_fst_level, snd_level: o_snd_level, fst: o_fst, snd: o_snd,
                } = other else { return false };
                fst_level.shared_eq(o_fst_level, m) && snd_level.shared_eq(o_snd_level, m)
                    && fst.shared_eq(o_fst, m) && snd.shared_eq(o_snd, m)
            }
            Type::Unit { level } => {
                let Type::Unit { level: o_level } = other else { return false };
                level.shared_eq(o_level, m)
            }
            Type::Empty { level } => {
                let Type::Empty { level: o_level } = other else { return false };
                level.shared_eq(o_level, m)
            }
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => {
                let Type::Sum {
                    lhs_level: o_lhs_level, rhs_level: o_rhs_level, lhs: o_lhs, rhs: o_rhs,
                } = other else { return false };
                lhs_level.shared_eq(o_lhs_level, m) && rhs_level.shared_eq(o_rhs_level, m)
                    && lhs.shared_eq(o_lhs, m) && rhs.shared_eq(o_rhs, m)
            }
            Type::W { shape_level, pos_level, shape, pos } => {
                let Type::W {
                    shape_level: o_shape_level, pos_level: o_pos_level, shape: o_shape, pos: o_pos,
                } = other else { return false };
                shape_level.shared_eq(o_shape_level, m) && pos_level.shared_eq(o_pos_level, m)
                    && shape.shared_eq(o_shape, m) && pos.shared_eq(o_pos, m)
            }
            Type::Vec { level, elem, len } => {
                let Type::Vec {
                    level: o_level, elem: o_elem, len: o_len,
                } = other else { return false };
                level.shared_eq(o_level, m) && elem.shared_eq(o_elem, m) && len.shared_eq(o_len, m)
            }
            Type::Fin { len } => {
                let Type::Fin { len: o_len } = other else { return false };
                len.shared_eq(o_len, m)
            }
            Type::Wf { level, shape, arity } => {
                let Type::Wf {
                    level: o_level, shape: o_shape, arity: o_arity,
                } = other else { return false };
                level.shared_eq(o_level, m) && shape.shared_eq(o_shape, m)
                    && arity.shared_eq(o_arity, m)
            }
            Type::DVec { level, len, fam } => {
                let Type::DVec {
                    level: o_level, len: o_len, fam: o_fam,
                } = other else { return false };
                level.shared_eq(o_level, m) && len.shared_eq(o_len, m) && fam.shared_eq(o_fam, m)
            }
            Type::IWf { sig, index } => {
                let Type::IWf { sig: o_sig, index: o_index } = other else { return false };
                sig.shared_eq(o_sig, m) && index.shared_eq(o_index, m)
            }
            Type::M { sig, index } => {
                let Type::M { sig: o_sig, index: o_index } = other else { return false };
                sig.shared_eq(o_sig, m) && index.shared_eq(o_index, m)
            }
            Type::GlobalTy { var, subst } => {
                let Type::GlobalTy { var: o_var, subst: o_subst } = other else { return false };
                var.shared_eq(o_var, m) && subst.shared_eq(o_subst, m)
            }
            Type::CtxPi { level, body } => {
                let Type::CtxPi { level: o_level, body: o_body } = other else { return false };
                level.shared_eq(o_level, m) && body.shared_eq(o_body, m)
            }
            Type::TyPi { ctx, arg_level, body_level, body } => {
                let Type::TyPi {
                    ctx: o_ctx, arg_level: o_arg_level, body_level: o_body_level, body: o_body,
                } = other else { return false };
                ctx.shared_eq(o_ctx, m) && arg_level.shared_eq(o_arg_level, m)
                    && body_level.shared_eq(o_body_level, m) && body.shared_eq(o_body, m)
            }
            Type::CodeTy { ctx, level } => {
                let Type::CodeTy { ctx: o_ctx, level: o_level } = other else { return false };
                ctx.shared_eq(o_ctx, m) && level.shared_eq(o_level, m)
            }
            Type::CodeTm { ctx, ty, level } => {
                let Type::CodeTm {
                    ctx: o_ctx, ty: o_ty, level: o_level,
                } = other else { return false };
                ctx.shared_eq(o_ctx, m) && ty.shared_eq(o_ty, m) && level.shared_eq(o_level, m)
            }
        }
    }
}

impl SharedEq for Term {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        match self {
            Term::Var(a0) => {
                let Term::Var(b0) = other else { return false };
                a0.shared_eq(b0, m)
            }
            Term::TmNat => matches!(other, Term::TmNat),
            Term::TmPi { dom_level, cod_level, dom, cod } => {
                let Term::TmPi {
                    dom_level: o_dom_level, cod_level: o_cod_level, dom: o_dom, cod: o_cod,
                } = other else { return false };
                dom_level.shared_eq(o_dom_level, m) && cod_level.shared_eq(o_cod_level, m)
                    && dom.shared_eq(o_dom, m) && cod.shared_eq(o_cod, m)
            }
            Term::TmTy(a0) => {
                let Term::TmTy(b0) = other else { return false };
                a0.shared_eq(b0, m)
            }
            Term::TmId { level, ty, lhs, rhs } => {
                let Term::TmId {
                    level: o_level, ty: o_ty, lhs: o_lhs, rhs: o_rhs,
                } = other else { return false };
                level.shared_eq(o_level, m) && ty.shared_eq(o_ty, m) && lhs.shared_eq(o_lhs, m)
                    && rhs.shared_eq(o_rhs, m)
            }
            Term::TmSEq { level, ty, lhs, rhs } => {
                let Term::TmSEq {
                    level: o_level, ty: o_ty, lhs: o_lhs, rhs: o_rhs,
                } = other else { return false };
                level.shared_eq(o_level, m) && ty.shared_eq(o_ty, m) && lhs.shared_eq(o_lhs, m)
                    && rhs.shared_eq(o_rhs, m)
            }
            Term::TmSEmpty { level } => {
                let Term::TmSEmpty { level: o_level } = other else { return false };
                level.shared_eq(o_level, m)
            }
            Term::TmSquash { level, ty } => {
                let Term::TmSquash { level: o_level, ty: o_ty } = other else { return false };
                level.shared_eq(o_level, m) && ty.shared_eq(o_ty, m)
            }
            Term::TmSigma { fst_level, snd_level, fst, snd } => {
                let Term::TmSigma {
                    fst_level: o_fst_level, snd_level: o_snd_level, fst: o_fst, snd: o_snd,
                } = other else { return false };
                fst_level.shared_eq(o_fst_level, m) && snd_level.shared_eq(o_snd_level, m)
                    && fst.shared_eq(o_fst, m) && snd.shared_eq(o_snd, m)
            }
            Term::TmUnit { level } => {
                let Term::TmUnit { level: o_level } = other else { return false };
                level.shared_eq(o_level, m)
            }
            Term::TmEmpty { level } => {
                let Term::TmEmpty { level: o_level } = other else { return false };
                level.shared_eq(o_level, m)
            }
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => {
                let Term::TmSum {
                    lhs_level: o_lhs_level, rhs_level: o_rhs_level, lhs: o_lhs, rhs: o_rhs,
                } = other else { return false };
                lhs_level.shared_eq(o_lhs_level, m) && rhs_level.shared_eq(o_rhs_level, m)
                    && lhs.shared_eq(o_lhs, m) && rhs.shared_eq(o_rhs, m)
            }
            Term::TmW { shape_level, pos_level, shape, pos } => {
                let Term::TmW {
                    shape_level: o_shape_level, pos_level: o_pos_level, shape: o_shape, pos: o_pos,
                } = other else { return false };
                shape_level.shared_eq(o_shape_level, m) && pos_level.shared_eq(o_pos_level, m)
                    && shape.shared_eq(o_shape, m) && pos.shared_eq(o_pos, m)
            }
            Term::TmVec { level, elem, len } => {
                let Term::TmVec {
                    level: o_level, elem: o_elem, len: o_len,
                } = other else { return false };
                level.shared_eq(o_level, m) && elem.shared_eq(o_elem, m) && len.shared_eq(o_len, m)
            }
            Term::TmFin { len } => {
                let Term::TmFin { len: o_len } = other else { return false };
                len.shared_eq(o_len, m)
            }
            Term::TmWf { level, shape, arity } => {
                let Term::TmWf {
                    level: o_level, shape: o_shape, arity: o_arity,
                } = other else { return false };
                level.shared_eq(o_level, m) && shape.shared_eq(o_shape, m)
                    && arity.shared_eq(o_arity, m)
            }
            Term::TmDVec { level, len, fam } => {
                let Term::TmDVec {
                    level: o_level, len: o_len, fam: o_fam,
                } = other else { return false };
                level.shared_eq(o_level, m) && len.shared_eq(o_len, m) && fam.shared_eq(o_fam, m)
            }
            Term::TmIWf { level, idx_level, idx, shape, arity, out, child, index } => {
                let Term::TmIWf {
                    level: o_level, idx_level: o_idx_level, idx: o_idx, shape: o_shape,
                    arity: o_arity, out: o_out, child: o_child, index: o_index,
                } = other else { return false };
                level.shared_eq(o_level, m) && idx_level.shared_eq(o_idx_level, m)
                    && idx.shared_eq(o_idx, m) && shape.shared_eq(o_shape, m)
                    && arity.shared_eq(o_arity, m) && out.shared_eq(o_out, m)
                    && child.shared_eq(o_child, m) && index.shared_eq(o_index, m)
            }
            Term::TmM { level, pos_level, idx_level, idx, shape, pos, next, index } => {
                let Term::TmM {
                    level: o_level, pos_level: o_pos_level, idx_level: o_idx_level, idx: o_idx,
                    shape: o_shape, pos: o_pos, next: o_next, index: o_index,
                } = other else { return false };
                level.shared_eq(o_level, m) && pos_level.shared_eq(o_pos_level, m)
                    && idx_level.shared_eq(o_idx_level, m) && idx.shared_eq(o_idx, m)
                    && shape.shared_eq(o_shape, m) && pos.shared_eq(o_pos, m)
                    && next.shared_eq(o_next, m) && index.shared_eq(o_index, m)
            }
            Term::Zero => matches!(other, Term::Zero),
            Term::NatLit(a0) => {
                let Term::NatLit(b0) = other else { return false };
                a0.shared_eq(b0, m)
            }
            Term::Succ(a0) => {
                let Term::Succ(b0) = other else { return false };
                a0.shared_eq(b0, m)
            }
            Term::ElimNat { level, motive, base, step, scrut } => {
                let Term::ElimNat {
                    level: o_level, motive: o_motive, base: o_base, step: o_step, scrut: o_scrut,
                } = other else { return false };
                level.shared_eq(o_level, m) && motive.shared_eq(o_motive, m)
                    && base.shared_eq(o_base, m) && step.shared_eq(o_step, m)
                    && scrut.shared_eq(o_scrut, m)
            }
            Term::Refl { level, ty, tm } => {
                let Term::Refl { level: o_level, ty: o_ty, tm: o_tm } = other else { return false };
                level.shared_eq(o_level, m) && ty.shared_eq(o_ty, m) && tm.shared_eq(o_tm, m)
            }
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => {
                let Term::J {
                    ty_level: o_ty_level, motive_level: o_motive_level, ty: o_ty, lhs: o_lhs,
                    motive: o_motive, case: o_case, rhs: o_rhs, proof: o_proof,
                } = other else { return false };
                ty_level.shared_eq(o_ty_level, m) && motive_level.shared_eq(o_motive_level, m)
                    && ty.shared_eq(o_ty, m) && lhs.shared_eq(o_lhs, m)
                    && motive.shared_eq(o_motive, m) && case.shared_eq(o_case, m)
                    && rhs.shared_eq(o_rhs, m) && proof.shared_eq(o_proof, m)
            }
            Term::SRefl { level, ty, tm } => {
                let Term::SRefl {
                    level: o_level, ty: o_ty, tm: o_tm,
                } = other else { return false };
                level.shared_eq(o_level, m) && ty.shared_eq(o_ty, m) && tm.shared_eq(o_tm, m)
            }
            Term::Squash { level, ty, tm } => {
                let Term::Squash {
                    level: o_level, ty: o_ty, tm: o_tm,
                } = other else { return false };
                level.shared_eq(o_level, m) && ty.shared_eq(o_ty, m) && tm.shared_eq(o_tm, m)
            }
            Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
                let Term::ElimSEmpty {
                    level: o_level, scrut_level: o_scrut_level, motive: o_motive, scrut: o_scrut,
                } = other else { return false };
                level.shared_eq(o_level, m) && scrut_level.shared_eq(o_scrut_level, m)
                    && motive.shared_eq(o_motive, m) && scrut.shared_eq(o_scrut, m)
            }
            Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => {
                let Term::ElimSquash {
                    src_level: o_src_level, dst_level: o_dst_level, src_ty: o_src_ty,
                    motive: o_motive, case: o_case, scrut: o_scrut,
                } = other else { return false };
                src_level.shared_eq(o_src_level, m) && dst_level.shared_eq(o_dst_level, m)
                    && src_ty.shared_eq(o_src_ty, m) && motive.shared_eq(o_motive, m)
                    && case.shared_eq(o_case, m) && scrut.shared_eq(o_scrut, m)
            }
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => {
                let Term::Pair {
                    fst_level: o_fst_level, snd_level: o_snd_level, fst_ty: o_fst_ty,
                    snd_ty: o_snd_ty, fst: o_fst, snd: o_snd,
                } = other else { return false };
                fst_level.shared_eq(o_fst_level, m) && snd_level.shared_eq(o_snd_level, m)
                    && fst_ty.shared_eq(o_fst_ty, m) && snd_ty.shared_eq(o_snd_ty, m)
                    && fst.shared_eq(o_fst, m) && snd.shared_eq(o_snd, m)
            }
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => {
                let Term::Fst {
                    fst_level: o_fst_level, snd_level: o_snd_level, fst_ty: o_fst_ty,
                    snd_ty: o_snd_ty, pair: o_pair,
                } = other else { return false };
                fst_level.shared_eq(o_fst_level, m) && snd_level.shared_eq(o_snd_level, m)
                    && fst_ty.shared_eq(o_fst_ty, m) && snd_ty.shared_eq(o_snd_ty, m)
                    && pair.shared_eq(o_pair, m)
            }
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => {
                let Term::Snd {
                    fst_level: o_fst_level, snd_level: o_snd_level, fst_ty: o_fst_ty,
                    snd_ty: o_snd_ty, pair: o_pair,
                } = other else { return false };
                fst_level.shared_eq(o_fst_level, m) && snd_level.shared_eq(o_snd_level, m)
                    && fst_ty.shared_eq(o_fst_ty, m) && snd_ty.shared_eq(o_snd_ty, m)
                    && pair.shared_eq(o_pair, m)
            }
            Term::VecLit { level, elem, zero, one, width, bits } => {
                let Term::VecLit {
                    level: o_level, elem: o_elem, zero: o_zero, one: o_one, width: o_width,
                    bits: o_bits,
                } = other else { return false };
                width == o_width && bits == o_bits && level.shared_eq(o_level, m)
                    && elem.shared_eq(o_elem, m) && zero.shared_eq(o_zero, m)
                    && one.shared_eq(o_one, m)
            }
            // The live elements, wherever each array starts.
            Term::VecItems { level, elem, items, from } => {
                let Term::VecItems { level: o_level, elem: o_elem, items: o_items, from: o_from } = other
                else {
                    return false;
                };
                let (a, b) = (items.get(*from as usize..), o_items.get(*o_from as usize..));
                let (Some(a), Some(b)) = (a, b) else { return false };
                a.len() == b.len() && level.shared_eq(o_level, m) && elem.shared_eq(o_elem, m)
                    && a.iter().zip(b).all(|(x, y)| x.shared_eq(y, m))
            }
            Term::PairAt { ty, fst, snd } => {
                let Term::PairAt { ty: o_ty, fst: o_fst, snd: o_snd } = other else { return false };
                ty.shared_eq(o_ty, m) && fst.shared_eq(o_fst, m) && snd.shared_eq(o_snd, m)
            }
            Term::InlAt { ty, val } => {
                let Term::InlAt { ty: o_ty, val: o_val } = other else { return false };
                ty.shared_eq(o_ty, m) && val.shared_eq(o_val, m)
            }
            Term::InrAt { ty, val } => {
                let Term::InrAt { ty: o_ty, val: o_val } = other else { return false };
                ty.shared_eq(o_ty, m) && val.shared_eq(o_val, m)
            }
            Term::FstAt { pair } => {
                let Term::FstAt { pair: o_pair } = other else { return false };
                pair.shared_eq(o_pair, m)
            }
            Term::SndAt { pair } => {
                let Term::SndAt { pair: o_pair } = other else { return false };
                pair.shared_eq(o_pair, m)
            }
            Term::AppAt { fun, arg } => {
                let Term::AppAt { fun: o_fun, arg: o_arg } = other else { return false };
                fun.shared_eq(o_fun, m) && arg.shared_eq(o_arg, m)
            }
            Term::Triv { level } => {
                let Term::Triv { level: o_level } = other else { return false };
                level.shared_eq(o_level, m)
            }
            Term::ElimEmpty { level, scrut_level, motive, scrut } => {
                let Term::ElimEmpty {
                    level: o_level, scrut_level: o_scrut_level, motive: o_motive, scrut: o_scrut,
                } = other else { return false };
                level.shared_eq(o_level, m) && scrut_level.shared_eq(o_scrut_level, m)
                    && motive.shared_eq(o_motive, m) && scrut.shared_eq(o_scrut, m)
            }
            Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => {
                let Term::Inl {
                    lhs_level: o_lhs_level, rhs_level: o_rhs_level, lhs: o_lhs, rhs: o_rhs,
                    val: o_val,
                } = other else { return false };
                lhs_level.shared_eq(o_lhs_level, m) && rhs_level.shared_eq(o_rhs_level, m)
                    && lhs.shared_eq(o_lhs, m) && rhs.shared_eq(o_rhs, m) && val.shared_eq(o_val, m)
            }
            Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => {
                let Term::Inr {
                    lhs_level: o_lhs_level, rhs_level: o_rhs_level, lhs: o_lhs, rhs: o_rhs,
                    val: o_val,
                } = other else { return false };
                lhs_level.shared_eq(o_lhs_level, m) && rhs_level.shared_eq(o_rhs_level, m)
                    && lhs.shared_eq(o_lhs, m) && rhs.shared_eq(o_rhs, m) && val.shared_eq(o_val, m)
            }
            Term::Case {
                lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r, scrut,
            } => {
                let Term::Case {
                    lhs_level: o_lhs_level, rhs_level: o_rhs_level, motive_level: o_motive_level,
                    lhs: o_lhs, rhs: o_rhs, motive: o_motive, case_l: o_case_l, case_r: o_case_r,
                    scrut: o_scrut,
                } = other else { return false };
                lhs_level.shared_eq(o_lhs_level, m) && rhs_level.shared_eq(o_rhs_level, m)
                    && motive_level.shared_eq(o_motive_level, m) && lhs.shared_eq(o_lhs, m)
                    && rhs.shared_eq(o_rhs, m) && motive.shared_eq(o_motive, m)
                    && case_l.shared_eq(o_case_l, m) && case_r.shared_eq(o_case_r, m)
                    && scrut.shared_eq(o_scrut, m)
            }
            Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => {
                let Term::Sup {
                    shape_level: o_shape_level, pos_level: o_pos_level, shape_ty: o_shape_ty,
                    pos_ty: o_pos_ty, label: o_label, children: o_children,
                } = other else { return false };
                shape_level.shared_eq(o_shape_level, m) && pos_level.shared_eq(o_pos_level, m)
                    && shape_ty.shared_eq(o_shape_ty, m) && pos_ty.shared_eq(o_pos_ty, m)
                    && label.shared_eq(o_label, m) && children.shared_eq(o_children, m)
            }
            Term::ElimW {
                shape_level, pos_level, motive_level, shape, pos, motive, step, scrut,
            } => {
                let Term::ElimW {
                    shape_level: o_shape_level, pos_level: o_pos_level,
                    motive_level: o_motive_level, shape: o_shape, pos: o_pos, motive: o_motive,
                    step: o_step, scrut: o_scrut,
                } = other else { return false };
                shape_level.shared_eq(o_shape_level, m) && pos_level.shared_eq(o_pos_level, m)
                    && motive_level.shared_eq(o_motive_level, m) && shape.shared_eq(o_shape, m)
                    && pos.shared_eq(o_pos, m) && motive.shared_eq(o_motive, m)
                    && step.shared_eq(o_step, m) && scrut.shared_eq(o_scrut, m)
            }
            Term::Supf { level, shape, arity, label, children } => {
                let Term::Supf {
                    level: o_level, shape: o_shape, arity: o_arity, label: o_label,
                    children: o_children,
                } = other else { return false };
                level.shared_eq(o_level, m) && shape.shared_eq(o_shape, m)
                    && arity.shared_eq(o_arity, m) && label.shared_eq(o_label, m)
                    && children.shared_eq(o_children, m)
            }
            Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => {
                let Term::ElimWf {
                    level: o_level, motive_level: o_motive_level, shape: o_shape, arity: o_arity,
                    motive: o_motive, step: o_step, scrut: o_scrut,
                } = other else { return false };
                level.shared_eq(o_level, m) && motive_level.shared_eq(o_motive_level, m)
                    && shape.shared_eq(o_shape, m) && arity.shared_eq(o_arity, m)
                    && motive.shared_eq(o_motive, m) && step.shared_eq(o_step, m)
                    && scrut.shared_eq(o_scrut, m)
            }
            Term::Supi { sig, label, children } => {
                let Term::Supi {
                    sig: o_sig, label: o_label, children: o_children,
                } = other else { return false };
                sig.shared_eq(o_sig, m) && label.shared_eq(o_label, m)
                    && children.shared_eq(o_children, m)
            }
            Term::ElimIWf { sig, motive_level, motive, step, index, scrut } => {
                let Term::ElimIWf {
                    sig: o_sig, motive_level: o_motive_level, motive: o_motive, step: o_step,
                    index: o_index, scrut: o_scrut,
                } = other else { return false };
                sig.shared_eq(o_sig, m) && motive_level.shared_eq(o_motive_level, m)
                    && motive.shared_eq(o_motive, m) && step.shared_eq(o_step, m)
                    && index.shared_eq(o_index, m) && scrut.shared_eq(o_scrut, m)
            }
            Term::Corec { sig, carrier_level, carrier, step, index, seed } => {
                let Term::Corec {
                    sig: o_sig, carrier_level: o_carrier_level, carrier: o_carrier, step: o_step,
                    index: o_index, seed: o_seed,
                } = other else { return false };
                sig.shared_eq(o_sig, m) && carrier_level.shared_eq(o_carrier_level, m)
                    && carrier.shared_eq(o_carrier, m) && step.shared_eq(o_step, m)
                    && index.shared_eq(o_index, m) && seed.shared_eq(o_seed, m)
            }
            Term::Out { sig, index, scrut } => {
                let Term::Out {
                    sig: o_sig, index: o_index, scrut: o_scrut,
                } = other else { return false };
                sig.shared_eq(o_sig, m) && index.shared_eq(o_index, m)
                    && scrut.shared_eq(o_scrut, m)
            }
            Term::Lam { dom_level, cod_level, dom, body } => {
                let Term::Lam {
                    dom_level: o_dom_level, cod_level: o_cod_level, dom: o_dom, body: o_body,
                } = other else { return false };
                dom_level.shared_eq(o_dom_level, m) && cod_level.shared_eq(o_cod_level, m)
                    && dom.shared_eq(o_dom, m) && body.shared_eq(o_body, m)
            }
            Term::App { fun, dom_level, cod_level, dom, cod, arg } => {
                let Term::App {
                    fun: o_fun, dom_level: o_dom_level, cod_level: o_cod_level, dom: o_dom,
                    cod: o_cod, arg: o_arg,
                } = other else { return false };
                fun.shared_eq(o_fun, m) && dom_level.shared_eq(o_dom_level, m)
                    && cod_level.shared_eq(o_cod_level, m) && dom.shared_eq(o_dom, m)
                    && cod.shared_eq(o_cod, m) && arg.shared_eq(o_arg, m)
            }
            Term::ULam { num_vars, level, body } => {
                let Term::ULam {
                    num_vars: o_num_vars, level: o_level, body: o_body,
                } = other else { return false };
                num_vars.shared_eq(o_num_vars, m) && level.shared_eq(o_level, m)
                    && body.shared_eq(o_body, m)
            }
            Term::UApp { fun, levels } => {
                let Term::UApp { fun: o_fun, levels: o_levels } = other else { return false };
                fun.shared_eq(o_fun, m) && levels.shared_eq(o_levels, m)
            }
            Term::GlobalTm { var, subst } => {
                let Term::GlobalTm { var: o_var, subst: o_subst } = other else { return false };
                var.shared_eq(o_var, m) && subst.shared_eq(o_subst, m)
            }
            Term::CtxLam { level, body } => {
                let Term::CtxLam { level: o_level, body: o_body } = other else { return false };
                level.shared_eq(o_level, m) && body.shared_eq(o_body, m)
            }
            Term::CtxApp { fun, ctx } => {
                let Term::CtxApp { fun: o_fun, ctx: o_ctx } = other else { return false };
                fun.shared_eq(o_fun, m) && ctx.shared_eq(o_ctx, m)
            }
            Term::TyLam { ctx, arg_level, body_level, body } => {
                let Term::TyLam {
                    ctx: o_ctx, arg_level: o_arg_level, body_level: o_body_level, body: o_body,
                } = other else { return false };
                ctx.shared_eq(o_ctx, m) && arg_level.shared_eq(o_arg_level, m)
                    && body_level.shared_eq(o_body_level, m) && body.shared_eq(o_body, m)
            }
            Term::TyApp { fun, arg } => {
                let Term::TyApp { fun: o_fun, arg: o_arg } = other else { return false };
                fun.shared_eq(o_fun, m) && arg.shared_eq(o_arg, m)
            }
            Term::BoxTy(a0) => {
                let Term::BoxTy(b0) = other else { return false };
                a0.shared_eq(b0, m)
            }
            Term::BoxTm(a0) => {
                let Term::BoxTm(b0) = other else { return false };
                a0.shared_eq(b0, m)
            }
            Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => {
                let Term::LetBoxTy {
                    motive_level: o_motive_level, code_level: o_code_level, ctx: o_ctx,
                    motive: o_motive, body: o_body, scrut: o_scrut,
                } = other else { return false };
                motive_level.shared_eq(o_motive_level, m) && code_level.shared_eq(o_code_level, m)
                    && ctx.shared_eq(o_ctx, m) && motive.shared_eq(o_motive, m)
                    && body.shared_eq(o_body, m) && scrut.shared_eq(o_scrut, m)
            }
            Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => {
                let Term::LetBoxTm {
                    motive_level: o_motive_level, code_level: o_code_level, ctx: o_ctx, ty: o_ty,
                    motive: o_motive, body: o_body, scrut: o_scrut,
                } = other else { return false };
                motive_level.shared_eq(o_motive_level, m) && code_level.shared_eq(o_code_level, m)
                    && ctx.shared_eq(o_ctx, m) && ty.shared_eq(o_ty, m)
                    && motive.shared_eq(o_motive, m) && body.shared_eq(o_body, m)
                    && scrut.shared_eq(o_scrut, m)
            }
            Term::ElimCodeTy {
                ty_motive_level, tm_motive_level, motives, branches, code_level, ctx, scrut,
            } => {
                let Term::ElimCodeTy {
                    ty_motive_level: o_ty_motive_level, tm_motive_level: o_tm_motive_level,
                    motives: o_motives, branches: o_branches, code_level: o_code_level, ctx: o_ctx,
                    scrut: o_scrut,
                } = other else { return false };
                ty_motive_level.shared_eq(o_ty_motive_level, m)
                    && tm_motive_level.shared_eq(o_tm_motive_level, m)
                    && motives.shared_eq(o_motives, m) && branches.shared_eq(o_branches, m)
                    && code_level.shared_eq(o_code_level, m) && ctx.shared_eq(o_ctx, m)
                    && scrut.shared_eq(o_scrut, m)
            }
            Term::ElimCodeTm {
                ty_motive_level, tm_motive_level, motives, branches, code_level, ctx, ty, scrut,
            } => {
                let Term::ElimCodeTm {
                    ty_motive_level: o_ty_motive_level, tm_motive_level: o_tm_motive_level,
                    motives: o_motives, branches: o_branches, code_level: o_code_level, ctx: o_ctx,
                    ty: o_ty, scrut: o_scrut,
                } = other else { return false };
                ty_motive_level.shared_eq(o_ty_motive_level, m)
                    && tm_motive_level.shared_eq(o_tm_motive_level, m)
                    && motives.shared_eq(o_motives, m) && branches.shared_eq(o_branches, m)
                    && code_level.shared_eq(o_code_level, m) && ctx.shared_eq(o_ctx, m)
                    && ty.shared_eq(o_ty, m) && scrut.shared_eq(o_scrut, m)
            }
        }
    }
}

impl SharedEq for Motives {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        let Motives { ty_motive, tm_motive } = self;
        let Motives { ty_motive: o_ty_motive, tm_motive: o_tm_motive } = other;
        ty_motive.shared_eq(o_ty_motive, m) && tm_motive.shared_eq(o_tm_motive, m)
    }
}

impl SharedEq for Branches {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        let Branches {
            ty_nat, ty_pi, ty_ty, ty_el, ty_id, ty_sigma, ty_unit, ty_empty, tm_var, tm_nat, tm_pi,
            tm_ty, tm_zero, tm_succ, tm_elim_nat, tm_lam, tm_app, tm_id, tm_refl, tm_j, tm_sigma,
            tm_pair, tm_fst, tm_snd, tm_unit, tm_empty, tm_triv, tm_elim_empty, ty_sum, tm_sum,
            tm_inl, tm_inr, tm_case, ty_w, tm_w, tm_sup, tm_elim_w, ty_vec, tm_vec, ty_fin, tm_fin,
            ty_wf, tm_wf, tm_supf, tm_elim_wf, ty_seq, tm_seq, ty_sempty, tm_sempty, tm_srefl,
            tm_elim_sempty, ty_squash, tm_squash, tm_squash_in, tm_elim_squash, ty_m, tm_m,
            tm_corec, tm_out, ty_dvec, tm_dvec, ty_iwf, tm_iwf, tm_sup_i, tm_elim_iwf,
        } = self;
        let Branches {
            ty_nat: o_ty_nat, ty_pi: o_ty_pi, ty_ty: o_ty_ty, ty_el: o_ty_el, ty_id: o_ty_id,
            ty_sigma: o_ty_sigma, ty_unit: o_ty_unit, ty_empty: o_ty_empty, tm_var: o_tm_var,
            tm_nat: o_tm_nat, tm_pi: o_tm_pi, tm_ty: o_tm_ty, tm_zero: o_tm_zero,
            tm_succ: o_tm_succ, tm_elim_nat: o_tm_elim_nat, tm_lam: o_tm_lam, tm_app: o_tm_app,
            tm_id: o_tm_id, tm_refl: o_tm_refl, tm_j: o_tm_j, tm_sigma: o_tm_sigma,
            tm_pair: o_tm_pair, tm_fst: o_tm_fst, tm_snd: o_tm_snd, tm_unit: o_tm_unit,
            tm_empty: o_tm_empty, tm_triv: o_tm_triv, tm_elim_empty: o_tm_elim_empty,
            ty_sum: o_ty_sum, tm_sum: o_tm_sum, tm_inl: o_tm_inl, tm_inr: o_tm_inr,
            tm_case: o_tm_case, ty_w: o_ty_w, tm_w: o_tm_w, tm_sup: o_tm_sup,
            tm_elim_w: o_tm_elim_w, ty_vec: o_ty_vec, tm_vec: o_tm_vec, ty_fin: o_ty_fin,
            tm_fin: o_tm_fin, ty_wf: o_ty_wf, tm_wf: o_tm_wf, tm_supf: o_tm_supf,
            tm_elim_wf: o_tm_elim_wf, ty_seq: o_ty_seq, tm_seq: o_tm_seq, ty_sempty: o_ty_sempty,
            tm_sempty: o_tm_sempty, tm_srefl: o_tm_srefl, tm_elim_sempty: o_tm_elim_sempty,
            ty_squash: o_ty_squash, tm_squash: o_tm_squash, tm_squash_in: o_tm_squash_in,
            tm_elim_squash: o_tm_elim_squash, ty_m: o_ty_m, tm_m: o_tm_m, tm_corec: o_tm_corec,
            tm_out: o_tm_out, ty_dvec: o_ty_dvec, tm_dvec: o_tm_dvec, ty_iwf: o_ty_iwf,
            tm_iwf: o_tm_iwf, tm_sup_i: o_tm_sup_i, tm_elim_iwf: o_tm_elim_iwf,
        } = other;
        ty_nat.shared_eq(o_ty_nat, m) && ty_pi.shared_eq(o_ty_pi, m) && ty_ty.shared_eq(o_ty_ty, m)
            && ty_el.shared_eq(o_ty_el, m) && ty_id.shared_eq(o_ty_id, m)
            && ty_sigma.shared_eq(o_ty_sigma, m) && ty_unit.shared_eq(o_ty_unit, m)
            && ty_empty.shared_eq(o_ty_empty, m) && tm_var.shared_eq(o_tm_var, m)
            && tm_nat.shared_eq(o_tm_nat, m) && tm_pi.shared_eq(o_tm_pi, m)
            && tm_ty.shared_eq(o_tm_ty, m) && tm_zero.shared_eq(o_tm_zero, m)
            && tm_succ.shared_eq(o_tm_succ, m) && tm_elim_nat.shared_eq(o_tm_elim_nat, m)
            && tm_lam.shared_eq(o_tm_lam, m) && tm_app.shared_eq(o_tm_app, m)
            && tm_id.shared_eq(o_tm_id, m) && tm_refl.shared_eq(o_tm_refl, m)
            && tm_j.shared_eq(o_tm_j, m) && tm_sigma.shared_eq(o_tm_sigma, m)
            && tm_pair.shared_eq(o_tm_pair, m) && tm_fst.shared_eq(o_tm_fst, m)
            && tm_snd.shared_eq(o_tm_snd, m) && tm_unit.shared_eq(o_tm_unit, m)
            && tm_empty.shared_eq(o_tm_empty, m) && tm_triv.shared_eq(o_tm_triv, m)
            && tm_elim_empty.shared_eq(o_tm_elim_empty, m) && ty_sum.shared_eq(o_ty_sum, m)
            && tm_sum.shared_eq(o_tm_sum, m) && tm_inl.shared_eq(o_tm_inl, m)
            && tm_inr.shared_eq(o_tm_inr, m) && tm_case.shared_eq(o_tm_case, m)
            && ty_w.shared_eq(o_ty_w, m) && tm_w.shared_eq(o_tm_w, m)
            && tm_sup.shared_eq(o_tm_sup, m) && tm_elim_w.shared_eq(o_tm_elim_w, m)
            && ty_vec.shared_eq(o_ty_vec, m) && tm_vec.shared_eq(o_tm_vec, m)
            && ty_fin.shared_eq(o_ty_fin, m) && tm_fin.shared_eq(o_tm_fin, m)
            && ty_wf.shared_eq(o_ty_wf, m) && tm_wf.shared_eq(o_tm_wf, m)
            && tm_supf.shared_eq(o_tm_supf, m) && tm_elim_wf.shared_eq(o_tm_elim_wf, m)
            && ty_seq.shared_eq(o_ty_seq, m) && tm_seq.shared_eq(o_tm_seq, m)
            && ty_sempty.shared_eq(o_ty_sempty, m) && tm_sempty.shared_eq(o_tm_sempty, m)
            && tm_srefl.shared_eq(o_tm_srefl, m) && tm_elim_sempty.shared_eq(o_tm_elim_sempty, m)
            && ty_squash.shared_eq(o_ty_squash, m) && tm_squash.shared_eq(o_tm_squash, m)
            && tm_squash_in.shared_eq(o_tm_squash_in, m)
            && tm_elim_squash.shared_eq(o_tm_elim_squash, m) && ty_m.shared_eq(o_ty_m, m)
            && tm_m.shared_eq(o_tm_m, m) && tm_corec.shared_eq(o_tm_corec, m)
            && tm_out.shared_eq(o_tm_out, m) && ty_dvec.shared_eq(o_ty_dvec, m)
            && tm_dvec.shared_eq(o_tm_dvec, m) && ty_iwf.shared_eq(o_ty_iwf, m)
            && tm_iwf.shared_eq(o_tm_iwf, m) && tm_sup_i.shared_eq(o_tm_sup_i, m)
            && tm_elim_iwf.shared_eq(o_tm_elim_iwf, m)
    }
}

impl SharedEq for IWfSig {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        let IWfSig { level, idx_level, idx, shape, arity, out, child } = self;
        let IWfSig {
            level: o_level, idx_level: o_idx_level, idx: o_idx, shape: o_shape, arity: o_arity,
            out: o_out, child: o_child,
        } = other;
        level.shared_eq(o_level, m) && idx_level.shared_eq(o_idx_level, m)
            && idx.shared_eq(o_idx, m) && shape.shared_eq(o_shape, m) && arity.shared_eq(o_arity, m)
            && out.shared_eq(o_out, m) && child.shared_eq(o_child, m)
    }
}

impl SharedEq for MSig {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        let MSig { level, pos_level, idx_level, idx, shape, pos, next } = self;
        let MSig {
            level: o_level, pos_level: o_pos_level, idx_level: o_idx_level, idx: o_idx,
            shape: o_shape, pos: o_pos, next: o_next,
        } = other;
        level.shared_eq(o_level, m) && pos_level.shared_eq(o_pos_level, m)
            && idx_level.shared_eq(o_idx_level, m) && idx.shared_eq(o_idx, m)
            && shape.shared_eq(o_shape, m) && pos.shared_eq(o_pos, m) && next.shared_eq(o_next, m)
    }
}

impl SharedEq for LocalSubst {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        let LocalSubst { tail, terms } = self;
        let LocalSubst { tail: o_tail, terms: o_terms } = other;
        tail.shared_eq(o_tail, m) && terms.shared_eq(o_terms, m)
    }
}

impl SharedEq for LocalCtx {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        let LocalCtx { base, entries } = self;
        let LocalCtx { base: o_base, entries: o_entries } = other;
        base.shared_eq(o_base, m) && entries.shared_eq(o_entries, m)
    }
}

impl SharedEq for CtxEntry {
    fn shared_eq(&self, other: &Self, m: &mut PairMemo) -> bool {
        let CtxEntry { ty, level } = self;
        let CtxEntry { ty: o_ty, level: o_level } = other;
        ty.shared_eq(o_ty, m) && level.shared_eq(o_level, m)
    }
}
