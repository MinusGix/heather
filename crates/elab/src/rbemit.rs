//! The readback of `docs/projected-tuple-tower-design.md` §5 E / §6, stage
//! one: the whnf **value** `oracle.rs` already produced, spelled back into
//! syntax by the elaborator, with **no naming yet**.
//!
//! Why the naming is a separate stage, and why this one is still worth
//! having: §5 E's own negative says a readback without a sharing memo writes
//! the normal form, which is exponential — the spike (`rbcount.rs`) measured
//! it at 0.67–0.85 of the rewriter's own reduct, on the same curve. What this
//! stage settles is the *other* half of the obligation, §9 item 3: whether a
//! spelling that comes out of the value machine is one the structural readers
//! at `build_ctor` (`tag_of`, `spine`, `unspell_here`,
//! `unspell_sum_components`, `build_fields_skel`) and the kernel accept at
//! all. The sharing memo keeps the *elaborator's* copy graph-sized (one
//! `Rc` per distinct sub-value); the tree is what the kernel then walks.
//!
//! Every arm that cannot be spelled faithfully declines — the whole readback
//! returns `None` and the site keeps the rewriter's reduct. Declining is the
//! only safe failure: a value shape with no faithful syntax (a compressed
//! `Nat`/bit run whose height is unbounded, a code recursor's elimination
//! whose motives are syntax in another environment) must never be guessed at.
//!
//! Instrument-gated (`HEATHER_RB=fire`) and inert otherwise.

use std::collections::HashMap;
use std::sync::Arc as Rc;
use std::sync::OnceLock;

use heather_kernel::eval::{self, Eval};
use heather_kernel::reduce::Defs;
use heather_kernel::term::{
    CtxBase, GlobalCtx, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type,
};
use heather_kernel::value::{
    CloId, Elim, Head, TmClo, TyClo, VNeTy, VSubst, VTail, VTy, Val, ValueArena,
};

pub(crate) fn firing() -> bool {
    static M: OnceLock<bool> = OnceLock::new();
    *M.get_or_init(|| std::env::var("HEATHER_RB").ok().as_deref() == Some("fire"))
}

/// Native recursion depth, as in `rbcount.rs`.
const DEPTH_CAP: u32 = 1_500;
/// The tallest `Succ` chain a compressed run is spelled as before the
/// readback declines. A literal over `Zero` is spelled as one `NatLit`, so
/// this bounds only the neutral-tailed case.
const RUN_CAP: u64 = 4_096;

type Key = (CloId, u32);

struct Emit<'a, 'v> {
    ev: Eval<'a, 'v>,
    arena: &'v ValueArena<'v>,
    /// The ambient Γ's abstract prefix, for a substitution tail's δ̌ (values
    /// drop it — `value.rs`'s `VTail` — and the scope the value lives in is
    /// what recovers it).
    base: CtxBase,
    tm: HashMap<Key, Rc<Term>>,
    ty: HashMap<Key, Rc<Type>>,
    depth: u32,
    declined: bool,
}

impl<'a, 'v> Emit<'a, 'v> {
    /// A placeholder the caller never keeps: `declined` is what the entry
    /// point reads, and it discards the whole readback.
    fn decline_tm(&mut self) -> Term {
        self.declined = true;
        Term::Zero
    }

    fn decline_ty(&mut self) -> Type {
        self.declined = true;
        Type::Nat
    }

    fn fresh(&self, lvl: u32) -> &'v TmClo<'v> {
        self.arena.tm(TmClo::val(Rc::new(Val::var(lvl))))
    }

    /// A concrete local at level `lvl`, read at depth `d`: variables are
    /// levels in the domain and indices in the syntax.
    fn var(&mut self, lvl: u32, d: u32) -> Term {
        match d.checked_sub(lvl + 1) {
            Some(i) => Term::Var(LocalVar(i)),
            None => self.decline_tm(),
        }
    }

    fn tm_at(&mut self, c: &'v TmClo<'v>, pending: u32, d: u32) -> Rc<Term> {
        let key = (c.ident(), d);
        if let Some(t) = self.tm.get(&key) {
            return Rc::clone(t);
        }
        if self.depth >= DEPTH_CAP || self.declined {
            return Rc::new(self.decline_tm());
        }
        self.depth += 1;
        let opened = if pending == 0 {
            self.ev.force(c)
        } else {
            let args: Vec<&'v TmClo<'v>> = (0..pending).map(|i| self.fresh(d + i)).collect();
            self.ev.apply(c, &args)
        };
        let out = match opened {
            Ok(v) => Rc::new(self.val(&v, d + pending)),
            Err(_) => Rc::new(self.decline_tm()),
        };
        self.depth -= 1;
        self.tm.insert(key, Rc::clone(&out));
        out
    }

    /// `El l ν` at a **glued** encoding, kept folded: forcing it would decode
    /// the definition the encoding names, and the registry's whole reason for
    /// naming a lowering is that `El (D#tycode^δ)` is the spelling every
    /// structural reader anchors on (`Elaborator::whnf`'s `unspell_here`).
    /// This is §6's preference (a) at the type level — the one place a
    /// readback would otherwise throw a name away.
    fn el_folded(&mut self, c: &'v TyClo<'v>, pending: u32, d: u32) -> Option<Type> {
        let (level, tm) = match c {
            TyClo::El { level, tm } if pending == 0 => {
                ((*level).clone(), self.ev.force(tm).ok()?)
            }
            TyClo::Syn { env, body } => match &**body {
                Type::El { level, tm } => {
                    let args: Vec<&'v TmClo<'v>> =
                        (0..pending).map(|i| self.fresh(d + i)).collect();
                    let env = env.extend(self.arena, &args);
                    (level.clone(), self.ev.eval_tm(tm, &env).ok()?)
                }
                _ => return None,
            },
            _ => return None,
        };
        match &*tm {
            Val::Neutral(n) if n.unfold.is_some() => {
                let d = d + pending;
                let tm = self.shared(&tm, d);
                Some(Type::El { level, tm })
            }
            _ => None,
        }
    }

    fn ty_at(&mut self, c: &'v TyClo<'v>, pending: u32, d: u32) -> Rc<Type> {
        let key = (c.ident(), d);
        if let Some(t) = self.ty.get(&key) {
            return Rc::clone(t);
        }
        if self.depth >= DEPTH_CAP || self.declined {
            return Rc::new(self.decline_ty());
        }
        if !std::env::var("HEATHER_RB_NOFOLD").is_ok()
            && let Some(folded) = self.el_folded(c, pending, d)
        {
            let out = Rc::new(folded);
            self.ty.insert(key, Rc::clone(&out));
            return out;
        }
        self.depth += 1;
        let opened = if pending == 0 {
            self.ev.force_ty(c)
        } else {
            let args: Vec<&'v TmClo<'v>> = (0..pending).map(|i| self.fresh(d + i)).collect();
            self.ev.apply_ty(c, &args)
        };
        let out = match opened {
            Ok(v) => Rc::new(self.vty(&v, d + pending)),
            Err(_) => Rc::new(self.decline_ty()),
        };
        self.depth -= 1;
        self.ty.insert(key, Rc::clone(&out));
        out
    }

    fn shared(&mut self, v: &Rc<Val<'v>>, d: u32) -> Rc<Term> {
        Rc::new(self.val(v, d))
    }

    fn subst(&mut self, s: &VSubst<'v>, d: u32) -> LocalSubst {
        let tail = match s.tail {
            // δ̂ is the *source* context's length, which is the depth the
            // occurrence is read at.
            VTail::Empty(_) => SubstTail::Empty { len: d, base: self.base },
            VTail::Wk(ctx_var) => SubstTail::Wk { len: d, ctx_var },
        };
        let terms = s.terms.clone();
        LocalSubst {
            tail,
            terms: terms.iter().map(|t| self.shared(t, d)).collect(),
        }
    }

    fn vty(&mut self, v: &Rc<VTy<'v>>, d: u32) -> Type {
        match &**v {
            VTy::Nat => Type::Nat,
            VTy::Ty(l) => Type::Ty(l.clone()),
            VTy::Unit { level } => Type::Unit { level: level.clone() },
            VTy::Empty { level } => Type::Empty { level: level.clone() },
            VTy::SEmpty { level } => Type::SEmpty { level: level.clone() },
            VTy::Squash { level, ty } => Type::Squash {
                level: level.clone(),
                ty: self.ty_at(ty, 0, d),
            },
            VTy::Pi { dom_level, cod_level, dom, cod } => Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: self.ty_at(dom, 0, d),
                cod: self.ty_at(cod, 1, d),
            },
            VTy::Sigma { fst_level, snd_level, fst, snd } => Type::Sigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: self.ty_at(fst, 0, d),
                snd: self.ty_at(snd, 1, d),
            },
            VTy::W { shape_level, pos_level, shape, pos } => Type::W {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: self.ty_at(shape, 0, d),
                pos: self.ty_at(pos, 1, d),
            },
            VTy::Wf { level, shape, arity } => Type::Wf {
                level: level.clone(),
                shape: self.ty_at(shape, 0, d),
                arity: self.tm_at(arity, 1, d),
            },
            VTy::Sum { lhs_level, rhs_level, lhs, rhs } => Type::Sum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: self.ty_at(lhs, 0, d),
                rhs: self.ty_at(rhs, 0, d),
            },
            VTy::Id { level, ty, lhs, rhs } => Type::Id {
                level: level.clone(),
                ty: self.ty_at(ty, 0, d),
                lhs: self.tm_at(lhs, 0, d),
                rhs: self.tm_at(rhs, 0, d),
            },
            VTy::SEq { level, ty, lhs, rhs } => Type::SEq {
                level: level.clone(),
                ty: self.ty_at(ty, 0, d),
                lhs: self.tm_at(lhs, 0, d),
                rhs: self.tm_at(rhs, 0, d),
            },
            VTy::Vec { level, elem, len } => {
                let len = Rc::clone(len);
                Type::Vec {
                    level: level.clone(),
                    elem: self.ty_at(elem, 0, d),
                    len: self.shared(&len, d),
                }
            }
            VTy::Fin { len } => {
                let len = Rc::clone(len);
                Type::Fin { len: self.shared(&len, d) }
            }
            VTy::UPi { num_vars, level, body } => Type::UPi {
                num_vars: *num_vars,
                level: level.clone(),
                body: self.ty_at(body, 0, d),
            },
            VTy::CtxPi { level, body } => Type::CtxPi {
                level: level.clone(),
                body: self.ty_at(body, 0, d),
            },
            VTy::TyPi { ctx, arg_level, body_level, body } => Type::TyPi {
                ctx: ctx.clone(),
                arg_level: arg_level.clone(),
                body_level: body_level.clone(),
                body: self.ty_at(body, 0, d),
            },
            VTy::CodeTy { ctx, level } => Type::CodeTy {
                ctx: ctx.clone(),
                level: level.clone(),
            },
            VTy::CodeTm { ctx, ty, level } => Type::CodeTm {
                ctx: ctx.clone(),
                ty: Rc::clone(ty),
                level: level.clone(),
            },
            VTy::Neutral(VNeTy::Global { var, subst }) => {
                let subst = subst.clone();
                Type::GlobalTy { var: *var, subst: self.subst(&subst, d) }
            }
            VTy::Neutral(VNeTy::El { level, tm }) => {
                let tm = Rc::clone(tm);
                Type::El {
                    level: level.clone(),
                    tm: self.shared(&tm, d),
                }
            }
        }
    }

    fn val(&mut self, v: &Rc<Val<'v>>, d: u32) -> Term {
        match &**v {
            Val::TmNat => Term::TmNat,
            Val::TmTy(l) => Term::TmTy(l.clone()),
            Val::TmUnit { level } => Term::TmUnit { level: level.clone() },
            Val::TmEmpty { level } => Term::TmEmpty { level: level.clone() },
            Val::TmSEmpty { level } => Term::TmSEmpty { level: level.clone() },
            Val::TmSquash { level, ty } => Term::TmSquash {
                level: level.clone(),
                ty: self.tm_at(ty, 0, d),
            },
            Val::TmPi { dom_level, cod_level, dom, cod } => Term::TmPi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: self.tm_at(dom, 0, d),
                cod: self.tm_at(cod, 1, d),
            },
            Val::TmSigma { fst_level, snd_level, fst, snd } => Term::TmSigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: self.tm_at(fst, 0, d),
                snd: self.tm_at(snd, 1, d),
            },
            Val::TmW { shape_level, pos_level, shape, pos } => Term::TmW {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: self.tm_at(shape, 0, d),
                pos: self.tm_at(pos, 1, d),
            },
            Val::TmWf { level, shape, arity } => Term::TmWf {
                level: level.clone(),
                shape: self.tm_at(shape, 0, d),
                arity: self.tm_at(arity, 1, d),
            },
            Val::TmId { level, ty, lhs, rhs } => Term::TmId {
                level: level.clone(),
                ty: self.tm_at(ty, 0, d),
                lhs: self.tm_at(lhs, 0, d),
                rhs: self.tm_at(rhs, 0, d),
            },
            Val::TmSEq { level, ty, lhs, rhs } => Term::TmSEq {
                level: level.clone(),
                ty: self.tm_at(ty, 0, d),
                lhs: self.tm_at(lhs, 0, d),
                rhs: self.tm_at(rhs, 0, d),
            },
            Val::TmSum { lhs_level, rhs_level, lhs, rhs } => Term::TmSum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: self.tm_at(lhs, 0, d),
                rhs: self.tm_at(rhs, 0, d),
            },
            Val::TmVec { level, elem, len } => Term::TmVec {
                level: level.clone(),
                elem: self.tm_at(elem, 0, d),
                len: self.tm_at(len, 0, d),
            },
            Val::TmFin { len } => Term::TmFin { len: self.tm_at(len, 0, d) },

            Val::Zero => Term::Zero,
            Val::Succ(t) => Term::Succ(self.tm_at(t, 0, d)),
            Val::NatRun { program, tail } => {
                let (program, tail) = (Rc::clone(program), *tail);
                self.nat_run(&program, tail, d)
            }
            Val::Refl { level, ty, tm } => Term::Refl {
                level: level.clone(),
                ty: self.ty_at(ty, 0, d),
                tm: self.tm_at(tm, 0, d),
            },
            Val::SRefl { level, ty, tm } => Term::SRefl {
                level: level.clone(),
                ty: self.ty_at(ty, 0, d),
                tm: self.tm_at(tm, 0, d),
            },
            Val::Squash { level, ty, tm } => Term::Squash {
                level: level.clone(),
                ty: self.ty_at(ty, 0, d),
                tm: self.tm_at(tm, 0, d),
            },
            Val::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => Term::Pair {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: self.ty_at(fst_ty, 0, d),
                snd_ty: self.ty_at(snd_ty, 1, d),
                fst: self.tm_at(fst, 0, d),
                snd: self.tm_at(snd, 0, d),
            },
            Val::Triv { level } => Term::Triv { level: level.clone() },
            Val::Inl { lhs_level, rhs_level, lhs, rhs, val } => Term::Inl {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: self.ty_at(lhs, 0, d),
                rhs: self.ty_at(rhs, 0, d),
                val: self.tm_at(val, 0, d),
            },
            Val::Inr { lhs_level, rhs_level, lhs, rhs, val } => Term::Inr {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: self.ty_at(lhs, 0, d),
                rhs: self.ty_at(rhs, 0, d),
                val: self.tm_at(val, 0, d),
            },
            Val::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => Term::Sup {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape_ty: self.ty_at(shape_ty, 0, d),
                pos_ty: self.ty_at(pos_ty, 1, d),
                label: self.tm_at(label, 0, d),
                children: self.tm_at(children, 0, d),
            },
            Val::Supf { level, shape, arity, label, children } => Term::Supf {
                level: level.clone(),
                shape: self.ty_at(shape, 0, d),
                arity: self.tm_at(arity, 1, d),
                label: self.tm_at(label, 0, d),
                children: self.tm_at(children, 0, d),
            },
            Val::Lam { dom_level, cod_level, dom, body } => Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: self.ty_at(dom, 0, d),
                body: self.tm_at(body, 1, d),
            },
            Val::ULam { num_vars, level, body } => Term::ULam {
                num_vars: *num_vars,
                level: level.clone(),
                body: self.tm_at(body, 0, d),
            },
            Val::CtxLam { level, body } => Term::CtxLam {
                level: level.clone(),
                body: self.tm_at(body, 0, d),
            },
            Val::TyLam { ctx, arg_level, body_level, body } => Term::TyLam {
                ctx: ctx.clone(),
                arg_level: arg_level.clone(),
                body_level: body_level.clone(),
                body: self.tm_at(body, 0, d),
            },
            Val::BoxTy(t) => Term::BoxTy(Rc::clone(t)),
            Val::BoxTm(t) => Term::BoxTm(Rc::clone(t)),
            // An evaluator representation with no bounded syntax of its own:
            // the readback declines rather than unpack a machine word or a
            // fold's pending algebra into a shape the emitters never saw.
            Val::BitRun { .. } | Val::NatSync { .. } | Val::BitFold { .. } => self.decline_tm(),
            Val::Neutral(n) => {
                let (head, spine) = (&n.head, n.spine);
                let mut t = match head {
                    Head::Var(lvl) => self.var(*lvl, d),
                    // Past the concrete entries: a variable of the abstract
                    // prefix, whose index counts from the inner end of `g`
                    // (`Env::lookup`).
                    Head::BaseVar(k) => Term::Var(LocalVar(d + k)),
                    Head::Global { var, subst } => {
                        let subst = subst.clone();
                        Term::GlobalTm { var: *var, subst: self.subst(&subst, d) }
                    }
                    Head::BoxedGlobalTy(t) => Term::BoxTy(Rc::clone(t)),
                    Head::BoxedGlobalTm(t) => Term::BoxTm(Rc::clone(t)),
                    Head::Stuck(_) => self.decline_tm(),
                };
                let mut elims: Vec<Elim<'v>> = spine.iter_rev().cloned().collect();
                elims.reverse();
                for e in &elims {
                    t = self.elim(e, t, d);
                }
                t
            }
        }
    }

    /// A compressed successor program, spelled as the chain it stands for: a
    /// literal when it bottoms out at `Zero`, `Succ`s over a neutral tail
    /// otherwise, and a decline past [`RUN_CAP`].
    fn nat_run(
        &mut self,
        program: &Rc<heather_kernel::value::program::ContextProgram<()>>,
        tail: &'v TmClo<'v>,
        d: u32,
    ) -> Term {
        let Some(height) =
            heather_kernel::value::program::ContextProgram::repetition_count_up_to(program, RUN_CAP)
        else {
            return self.decline_tm();
        };
        let tail = self.tm_at(tail, 0, d);
        if matches!(&*tail, Term::Zero) {
            return Term::NatLit(height);
        }
        let mut t = (*tail).clone();
        for _ in 0..height {
            t = Term::Succ(Rc::new(t));
        }
        t
    }

    fn elim(&mut self, e: &Elim<'v>, scrut: Term, d: u32) -> Term {
        let scrut = Rc::new(scrut);
        match e {
            Elim::App { dom_level, cod_level, dom, cod, arg } => Term::App {
                fun: scrut,
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: self.ty_at(dom, 0, d),
                cod: self.ty_at(cod, 1, d),
                arg: self.tm_at(arg, 0, d),
            },
            Elim::UApp { levels } => Term::UApp {
                fun: scrut,
                levels: levels.clone(),
            },
            Elim::CtxApp { ctx } => Term::CtxApp {
                fun: scrut,
                ctx: ctx.clone(),
            },
            Elim::TyApp { arg } => Term::TyApp {
                fun: scrut,
                arg: Rc::clone(arg),
            },
            Elim::Fst { fst_level, snd_level, fst_ty, snd_ty } => Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: self.ty_at(fst_ty, 0, d),
                snd_ty: self.ty_at(snd_ty, 1, d),
                pair: scrut,
            },
            Elim::Snd { fst_level, snd_level, fst_ty, snd_ty } => Term::Snd {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: self.ty_at(fst_ty, 0, d),
                snd_ty: self.ty_at(snd_ty, 1, d),
                pair: scrut,
            },
            Elim::ElimNat { level, motive, base, step } => Term::ElimNat {
                level: level.clone(),
                motive: self.ty_at(motive, 1, d),
                base: self.tm_at(base, 0, d),
                step: self.tm_at(step, 2, d),
                scrut,
            },
            Elim::ElimEmpty { level, scrut_level, motive } => Term::ElimEmpty {
                level: level.clone(),
                scrut_level: scrut_level.clone(),
                motive: self.ty_at(motive, 1, d),
                scrut,
            },
            Elim::ElimSEmpty { level, scrut_level, motive } => Term::ElimSEmpty {
                level: level.clone(),
                scrut_level: scrut_level.clone(),
                motive: self.ty_at(motive, 1, d),
                scrut,
            },
            Elim::ElimSquash { src_level, dst_level, src_ty, motive, case } => Term::ElimSquash {
                src_level: src_level.clone(),
                dst_level: dst_level.clone(),
                src_ty: self.ty_at(src_ty, 0, d),
                motive: self.ty_at(motive, 1, d),
                case: self.tm_at(case, 1, d),
                scrut,
            },
            Elim::Case { lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r } => {
                Term::Case {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    motive_level: motive_level.clone(),
                    lhs: self.ty_at(lhs, 0, d),
                    rhs: self.ty_at(rhs, 0, d),
                    motive: self.ty_at(motive, 1, d),
                    case_l: self.tm_at(case_l, 1, d),
                    case_r: self.tm_at(case_r, 1, d),
                    scrut,
                }
            }
            Elim::ElimW { shape_level, pos_level, motive_level, shape, pos, motive, step, .. } => {
                Term::ElimW {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    motive_level: motive_level.clone(),
                    shape: self.ty_at(shape, 0, d),
                    pos: self.ty_at(pos, 1, d),
                    motive: self.ty_at(motive, 1, d),
                    step: self.tm_at(step, 3, d),
                    scrut,
                }
            }
            Elim::ElimWf { level, motive_level, shape, arity, motive, step, .. } => Term::ElimWf {
                level: level.clone(),
                motive_level: motive_level.clone(),
                shape: self.ty_at(shape, 0, d),
                arity: self.tm_at(arity, 1, d),
                motive: self.ty_at(motive, 1, d),
                step: self.tm_at(step, 3, d),
                scrut,
            },
            Elim::J { ty_level, motive_level, ty, lhs, motive, case, rhs } => Term::J {
                ty_level: ty_level.clone(),
                motive_level: motive_level.clone(),
                ty: self.ty_at(ty, 0, d),
                lhs: self.tm_at(lhs, 0, d),
                motive: self.ty_at(motive, 2, d),
                case: self.tm_at(case, 0, d),
                rhs: self.tm_at(rhs, 0, d),
                proof: scrut,
            },
            Elim::Transp { ty_level, motive_level, ty, motive, lhs, rhs, tm } => Term::Transp {
                ty_level: ty_level.clone(),
                motive_level: motive_level.clone(),
                ty: self.ty_at(ty, 0, d),
                motive: self.ty_at(motive, 1, d),
                lhs: self.tm_at(lhs, 0, d),
                rhs: self.tm_at(rhs, 0, d),
                proof: scrut,
                tm: self.tm_at(tm, 0, d),
            },
            Elim::LetBoxTy { motive_level, code_level, ctx, motive, body } => Term::LetBoxTy {
                motive_level: motive_level.clone(),
                code_level: code_level.clone(),
                ctx: ctx.clone(),
                motive: self.ty_at(motive, 1, d),
                body: self.tm_at(body, 0, d),
                scrut,
            },
            Elim::LetBoxTm { motive_level, code_level, ctx, ty, motive, body } => Term::LetBoxTm {
                motive_level: motive_level.clone(),
                code_level: code_level.clone(),
                ctx: ctx.clone(),
                ty: Rc::clone(ty),
                motive: self.ty_at(motive, 1, d),
                body: self.tm_at(body, 0, d),
                scrut,
            },
            // The code recursors carry their motives and branches as syntax
            // in the environment they were built in; spelling them here would
            // mean substituting that environment, which is the tree this
            // round exists to stop writing. Declined.
            Elim::ElimCodeTy { .. } | Elim::ElimCodeTm { .. } => self.decline_tm(),
        }
    }
}

/// The δ-transparent weak head normal form of `ty`, **spelled from the
/// value** the machine produces rather than by the small-step rewriter.
/// `None` when any part of the value has no faithful syntax, in which case
/// the caller keeps the rewriter's answer.
pub(crate) fn whnf_type_from_value(
    world: &GlobalCtx,
    gamma: &LocalCtx,
    ty: &Type,
    fuel: u64,
) -> Option<Type> {
    let arena = ValueArena::new();
    let defs = Defs::transparent(world);
    let root = eval::whnf_value_ty(&arena, &Rc::new(ty.clone()), gamma, defs, fuel).ok()?;
    // A **stuck** head is the oracle's own decline (`oracle.rs`'s second
    // bullet): every reduct witnesses "no former" equally well, and the
    // cheapest witness is the spelling every consumer read before the probe.
    // Reading one back would respell a type no reader needed respelled.
    if matches!(&*root, VTy::Neutral(_)) {
        return None;
    }
    let mut e = Emit {
        ev: Eval::new(fuel, defs, gamma.base, &arena),
        arena: &arena,
        base: gamma.base,
        tm: HashMap::new(),
        ty: HashMap::new(),
        depth: 0,
        declined: false,
    };
    let d = gamma.entries.len() as u32;
    let out = e.vty(&root, d);
    if e.declined {
        return None;
    }
    Some(out)
}

/// The one call site, beside [`crate::rbcount::at_build_ctor`]: with
/// `HEATHER_RB=fire` the reduct `build_ctor` reads components out of is the
/// readback's, and the rewriter's is kept only when the readback declines.
pub(crate) fn at_build_ctor(
    world: &GlobalCtx,
    gamma: &LocalCtx,
    ty: &Type,
    fuel: u64,
    reduct: Type,
) -> Type {
    if !firing() {
        return reduct;
    }
    let _phase = crate::stats::guard(crate::stats::Timer::ElabWhnf);
    match whnf_type_from_value(world, gamma, ty, fuel) {
        Some(t) => {
            if std::env::var("HEATHER_RB_DIFF").is_ok() && t != reduct {
                eprintln!("rb diff\n  reduct   {reduct:?}\n  readback {t:?}");
            }
            t
        }
        // A decline is the parent's behaviour at that site, and the round
        // wants to know how often it happens.
        None => {
            let (m, i) = crate::stats::current_item().unwrap_or(("-".into(), "-".into()));
            eprintln!("rb decline item={m}::{i}");
            reduct
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc as Rc;

    use heather_kernel::layer::Layer;
    use heather_kernel::level::Level;
    use heather_kernel::reduce;
    use heather_kernel::term::{GlobalBinding, GlobalCtx, GlobalVar, LocalVar};

    use super::*;

    const FUEL: u64 = 1 << 20;

    /// The fixture `oracle.rs`'s tests use: one computing family at
    /// `GlobalVar(0)`, `P : Π(Nat). Ty 0 := λ n. elim_Nat(n; Nat; Unit)` —
    /// a `fn … → Type` whose head is a `match`, which is the shape every
    /// library type abbreviation this round cares about has.
    fn computing_world() -> GlobalCtx {
        let body = Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::constant(1),
            dom: Rc::new(Type::Nat),
            body: Rc::new(Term::ElimNat {
                level: Level::constant(1),
                motive: Rc::new(Type::Ty(Level::Zero)),
                base: Rc::new(Term::TmNat),
                step: Rc::new(Term::TmUnit { level: Level::Zero }),
                scrut: Rc::new(Term::Var(LocalVar(0))),
            }),
        };
        GlobalCtx::new(vec![GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::constant(1),
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Ty(Level::Zero)),
            }),
            level: Level::constant(1),
            body: Some(Rc::new(body)),
        }])
    }

    fn one_nat() -> LocalCtx {
        LocalCtx::nil().extended(Rc::new(Type::Nat), Level::Zero)
    }

    /// `El^0 (P arg)` in `Γ = x : Nat`.
    fn p_of(arg: Term) -> Type {
        Type::El {
            level: Level::Zero,
            tm: Rc::new(Term::App {
                fun: Rc::new(Term::GlobalTm {
                    var: GlobalVar(0),
                    subst: LocalSubst::id(&one_nat()),
                }),
                dom_level: Level::Zero,
                cod_level: Level::constant(1),
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Ty(Level::Zero)),
                arg: Rc::new(arg),
            }),
        }
    }

    fn readback(ty: &Type) -> Option<Type> {
        whnf_type_from_value(&computing_world(), &one_nat(), ty, FUEL)
    }

    fn reducer(ty: &Type) -> Type {
        reduce::whnf_type_delta(
            ty,
            &one_nat(),
            Defs::transparent(&computing_world()),
            FUEL,
        )
        .unwrap()
    }

    /// A **literal** scrutinee: the computation runs, and the readback lands
    /// on the former the rewriter lands on.
    #[test]
    fn a_literal_scrutinee_reads_back_as_the_reducers_former() {
        for (arg, want) in [
            (Term::Zero, Type::Nat),
            (Term::NatLit(1000), Type::Unit { level: Level::Zero }),
        ] {
            let ty = p_of(arg);
            assert_eq!(readback(&ty), Some(want.clone()));
            assert_eq!(reducer(&ty), want);
        }
    }

    /// A **neutral** scrutinee: nothing computes, and the readback keeps the
    /// definition's *name* rather than unfolding it — §6's preference (a),
    /// and what every structural reader at `build_ctor` anchors on.
    #[test]
    fn a_neutral_scrutinee_keeps_the_folded_global() {
        // At the head, a stuck type is declined outright — the oracle's own
        // rule, and the spelling the site already had.
        assert_eq!(readback(&p_of(Term::Var(LocalVar(0)))), None);
        // One level down it is spelled, and spelled **folded**: the
        // definition's name survives the readback (§6's preference (a)),
        // which is what every structural reader anchors on.
        let ty = Type::Sigma {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst: Rc::new(Type::Nat),
            snd: Rc::new(p_of(Term::Var(LocalVar(1)))),
        };
        let got = readback(&ty).expect("a Sigma is a former");
        let Type::Sigma { snd, .. } = &got else {
            panic!("expected a `Σ`, got {got:?}");
        };
        let Type::El { tm, .. } = &**snd else {
            panic!("expected an `El` under the binder, got {got:?}");
        };
        let mut head = &**tm;
        while let Term::App { fun, .. } = head {
            head = fun;
        }
        assert!(
            matches!(head, Term::GlobalTm { var, .. } if *var == GlobalVar(0)),
            "the readback unfolded the definition: {got:?}"
        );
    }

    /// An **open** element type, in a *checking*-shaped position (the
    /// codomain under the binder the former introduces), against the closed
    /// control: the readback goes under the binder and reads the variable
    /// back as an index, not as the level it is in the domain.
    #[test]
    fn an_open_codomain_reads_back_under_its_binder() {
        let open = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            // `Vec^0(Nat; y)` — the binder's own variable, which is index 0
            // under the binder and level 1 in the value domain.
            cod: Rc::new(Type::Vec {
                level: Level::Zero,
                elem: Rc::new(Type::Nat),
                len: Rc::new(Term::Var(LocalVar(0))),
            }),
        };
        let closed = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Vec {
                level: Level::Zero,
                elem: Rc::new(Type::Nat),
                len: Rc::new(Term::NatLit(0)),
            }),
        };
        assert_eq!(readback(&open), Some(open.clone()));
        // The closed control, and the one structural difference this stage
        // has from the rewriter: the readback's answer is a **deep** normal
        // form, so the `Vec` at a canonical length steps under the binder
        // where the small-step rewriter — weak head only — leaves it. That
        // is where the exponent of §2 lives, and also why the kernel then
        // hits where it missed.
        assert_eq!(
            readback(&closed),
            Some(Type::Pi {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Unit { level: Level::Zero }),
            })
        );
        assert_eq!(reducer(&closed), closed);
    }

    /// The negative control: a value shape with no bounded syntax — a
    /// compressed successor program over a neutral tail, past [`RUN_CAP`] —
    /// is **declined**, and the caller keeps the rewriter's answer. A
    /// readback that guessed here would write a spelling no emitter has seen.
    #[test]
    fn an_unbounded_run_declines_rather_than_guessing() {
        let mut len = Term::Var(LocalVar(0));
        for _ in 0..(4 * RUN_CAP) {
            len = Term::Succ(Rc::new(len));
        }
        let ty = Type::Vec {
            level: Level::Zero,
            elem: Rc::new(Type::Nat),
            len: Rc::new(len),
        };
        assert_eq!(readback(&ty), None);
    }
}
