//! The spike of `docs/projected-tuple-tower-design.md` §9 items 2–3: what a
//! readback of `build_ctor`'s whnf **value** would write down, counted before
//! anything is built.
//!
//! Two numbers per reduct, from one walk:
//!
//! - the **naive** count — the nodes a readback that expands every closure it
//!   meets would emit. §5 E predicts it is the normal form, i.e. §2's
//!   pre-firing count within the rewriter's annotation constant; if it came
//!   out linear the value domain would be doing something §3 did not account
//!   for and §6 would have no basis;
//! - the **graph** count — how many distinct closure identities that walk
//!   visits. §3 predicts ≈3 distinct components per combinator layer, i.e.
//!   linear in the nesting.
//!
//! One walk gives both because the count is memoized on closure identity:
//! `count(c) = 1 + Σ count(children)` over the *graph* is exactly the size of
//! the *tree* the naive readback would write, and the memo's population is
//! the graph's size. That is the round's whole claim in two columns.
//!
//! The walk is a readback's walk without the syntax: it forces a 0-binder
//! sub-structure and applies a `k`-binder one to `k` fresh neutrals, with the
//! binder counts of `crates/kernel/src/conv/dom/values.rs`'s views (the one
//! place the arities are already written down). A glued neutral is read at
//! its **folded** head — its `unfold` is not followed — which is both what a
//! readback does and §6's preference (a).
//!
//! Instrument only: `HEATHER_RB=count` prints one line per `build_ctor`
//! reduct and changes nothing. Unset, nothing is called.

use std::collections::HashMap;
use std::sync::Arc as Rc;
use std::sync::OnceLock;

use heather_kernel::eval::{self, Eval};
use heather_kernel::reduce::Defs;
use heather_kernel::term::{GlobalCtx, LocalCtx, Term, Type};
use heather_kernel::value::{
    CloId, Elim, Head, TmClo, TyClo, VNeTy, VTy, Val, ValueArena,
};

/// The exhaustive, **unbudgeted** node count of a piece of kernel syntax —
/// `docs/projected-tuple-tower-design.md` §1's counter, kept from the
/// previous round's instrument (`probes/tt_D.patch`) with its redex columns
/// dropped: this round needs the size and not the redexes. Unbudgeted is the
/// point — the bounded `Debug` (`crates/kernel/src/fmt.rs`) saturates at 512
/// nodes, and the clocks are proxies for size rather than size.
#[derive(Default, Clone, Copy)]
pub(crate) struct Counts {
    pub(crate) nodes: u64,
}

impl Counts {
    fn node(&mut self) {
        self.nodes += 1;
    }
}

pub(crate) fn count_ty(ty: &Type) -> Counts {
    let mut c = Counts::default();
    cty(ty, &mut c);
    c
}

/// [`count_ty`]'s term half — the same exhaustive count, for a minted body
/// (`rbname.rs`).
pub(crate) fn count_tm(t: &Term) -> Counts {
    let mut c = Counts::default();
    ctm(t, &mut c);
    c
}

fn ctms(ts: &[Rc<Term>], c: &mut Counts) {
    for t in ts {
        ctm(t, c);
    }
}

fn cty(ty: &Type, c: &mut Counts) {
    c.node();
    match ty {
        Type::Nat | Type::Ty(_) | Type::SEmpty { .. } | Type::Unit { .. } | Type::Empty { .. } => {}
        Type::Pi { dom, cod, .. } => {
            cty(dom, c);
            cty(cod, c);
        }
        Type::UPi { body, .. } | Type::CtxPi { body, .. } | Type::TyPi { body, .. } => cty(body, c),
        Type::El { tm, .. } => ctm(tm, c),
        Type::Id { ty, lhs, rhs, .. } | Type::SEq { ty, lhs, rhs, .. } => {
            cty(ty, c);
            ctm(lhs, c);
            ctm(rhs, c);
        }
        Type::Squash { ty, .. } => cty(ty, c),
        Type::Sigma { fst, snd, .. } => {
            cty(fst, c);
            cty(snd, c);
        }
        Type::Sum { lhs, rhs, .. } => {
            cty(lhs, c);
            cty(rhs, c);
        }
        Type::W { shape, pos, .. } => {
            cty(shape, c);
            cty(pos, c);
        }
        Type::Vec { elem, len, .. } => {
            cty(elem, c);
            ctm(len, c);
        }
        Type::Fin { len } => ctm(len, c),
        Type::Wf { shape, arity, .. } => {
            cty(shape, c);
            ctm(arity, c);
        }
        Type::GlobalTy { subst, .. } => ctms(&subst.terms, c),
        Type::CodeTy { .. } => {}
        Type::CodeTm { ty, .. } => cty(ty, c),
    }
}

fn ctm(t: &Term, c: &mut Counts) {
    c.node();
    match t {
        Term::Var(_)
        | Term::TmNat
        | Term::TmTy(_)
        | Term::Zero
        | Term::NatLit(_)
        | Term::TmSEmpty { .. }
        | Term::TmUnit { .. }
        | Term::TmEmpty { .. }
        | Term::Triv { .. } => {}
        Term::Succ(t) => ctm(t, c),
        Term::TmPi { dom, cod, .. } => {
            ctm(dom, c);
            ctm(cod, c);
        }
        Term::TmId { ty, lhs, rhs, .. } | Term::TmSEq { ty, lhs, rhs, .. } => {
            ctm(ty, c);
            ctm(lhs, c);
            ctm(rhs, c);
        }
        Term::TmSquash { ty, .. } => ctm(ty, c),
        Term::TmSigma { fst, snd, .. } => {
            ctm(fst, c);
            ctm(snd, c);
        }
        Term::TmSum { lhs, rhs, .. } => {
            ctm(lhs, c);
            ctm(rhs, c);
        }
        Term::TmW { shape, pos, .. } => {
            ctm(shape, c);
            ctm(pos, c);
        }
        Term::TmVec { elem, len, .. } => {
            ctm(elem, c);
            ctm(len, c);
        }
        Term::TmFin { len } => ctm(len, c),
        Term::TmWf { shape, arity, .. } => {
            ctm(shape, c);
            ctm(arity, c);
        }
        Term::ElimNat {
            motive,
            base,
            step,
            scrut,
            ..
        } => {
            cty(motive, c);
            ctm(base, c);
            ctm(step, c);
            ctm(scrut, c);
        }
        Term::Refl { ty, tm, .. } | Term::SRefl { ty, tm, .. } | Term::Squash { ty, tm, .. } => {
            cty(ty, c);
            ctm(tm, c);
        }
        Term::J {
            ty,
            lhs,
            motive,
            case,
            rhs,
            proof,
            ..
        } => {
            cty(ty, c);
            cty(motive, c);
            ctm(lhs, c);
            ctm(case, c);
            ctm(rhs, c);
            ctm(proof, c);
        }
        Term::Transp {
            ty,
            motive,
            lhs,
            rhs,
            proof,
            tm,
            ..
        } => {
            cty(ty, c);
            cty(motive, c);
            ctm(lhs, c);
            ctm(rhs, c);
            ctm(proof, c);
            ctm(tm, c);
        }
        Term::ElimSEmpty { motive, scrut, .. } | Term::ElimEmpty { motive, scrut, .. } => {
            cty(motive, c);
            ctm(scrut, c);
        }
        Term::ElimSquash {
            src_ty,
            motive,
            case,
            scrut,
            ..
        } => {
            cty(src_ty, c);
            cty(motive, c);
            ctm(case, c);
            ctm(scrut, c);
        }
        Term::Pair {
            fst_ty,
            snd_ty,
            fst,
            snd,
            ..
        } => {
            cty(fst_ty, c);
            cty(snd_ty, c);
            ctm(fst, c);
            ctm(snd, c);
        }
        Term::Fst {
            fst_ty,
            snd_ty,
            pair,
            ..
        }
        | Term::Snd {
            fst_ty,
            snd_ty,
            pair,
            ..
        } => {
            cty(fst_ty, c);
            cty(snd_ty, c);
            ctm(pair, c);
        }
        Term::Inl { lhs, rhs, val, .. } | Term::Inr { lhs, rhs, val, .. } => {
            cty(lhs, c);
            cty(rhs, c);
            ctm(val, c);
        }
        Term::Case {
            lhs,
            rhs,
            motive,
            case_l,
            case_r,
            scrut,
            ..
        } => {
            cty(lhs, c);
            cty(rhs, c);
            cty(motive, c);
            ctm(case_l, c);
            ctm(case_r, c);
            ctm(scrut, c);
        }
        Term::Sup {
            shape_ty,
            pos_ty,
            label,
            children,
            ..
        } => {
            cty(shape_ty, c);
            cty(pos_ty, c);
            ctm(label, c);
            ctm(children, c);
        }
        Term::ElimW {
            shape,
            pos,
            motive,
            step,
            scrut,
            ..
        } => {
            cty(shape, c);
            cty(pos, c);
            cty(motive, c);
            ctm(step, c);
            ctm(scrut, c);
        }
        Term::Supf {
            shape,
            arity,
            label,
            children,
            ..
        } => {
            cty(shape, c);
            ctm(arity, c);
            ctm(label, c);
            ctm(children, c);
        }
        Term::ElimWf {
            shape,
            arity,
            motive,
            step,
            scrut,
            ..
        } => {
            cty(shape, c);
            ctm(arity, c);
            cty(motive, c);
            ctm(step, c);
            ctm(scrut, c);
        }
        Term::Lam { dom, body, .. } => {
            cty(dom, c);
            ctm(body, c);
        }
        Term::App {
            fun,
            dom,
            cod,
            arg,
            ..
        } => {
            cty(dom, c);
            cty(cod, c);
            ctm(fun, c);
            ctm(arg, c);
        }
        Term::ULam { body, .. } => ctm(body, c),
        Term::UApp { fun, .. } => ctm(fun, c),
        Term::GlobalTm { subst, .. } => ctms(&subst.terms, c),
        Term::CtxLam { body, .. } => ctm(body, c),
        Term::CtxApp { fun, .. } => ctm(fun, c),
        Term::TyLam { body, .. } => ctm(body, c),
        Term::TyApp { fun, arg } => {
            cty(arg, c);
            ctm(fun, c);
        }
        Term::BoxTy(ty) => cty(ty, c),
        Term::BoxTm(tm) => ctm(tm, c),
        Term::LetBoxTy {
            motive,
            body,
            scrut,
            ..
        } => {
            cty(motive, c);
            ctm(body, c);
            ctm(scrut, c);
        }
        Term::LetBoxTm {
            ty,
            motive,
            body,
            scrut,
            ..
        } => {
            cty(ty, c);
            cty(motive, c);
            ctm(body, c);
            ctm(scrut, c);
        }
        Term::ElimCodeTy { scrut, .. } => ctm(scrut, c),
        Term::ElimCodeTm { ty, scrut, .. } => {
            cty(ty, c);
            ctm(scrut, c);
        }
    }
}

pub(crate) fn enabled() -> bool {
    static M: OnceLock<bool> = OnceLock::new();
    *M.get_or_init(|| std::env::var("HEATHER_RB").ok().as_deref() == Some("count"))
}

/// Distinct graph nodes one walk may visit. A guard against a malformed
/// input, not a policy: §3 predicts a few thousand.
const GRAPH_CAP: usize = 4_000_000;
/// Native recursion depth. The elaborator's worker stacks are the limit here,
/// not the value graph's.
const DEPTH_CAP: u32 = 1_500;

#[derive(Default)]
struct Report {
    /// Depth-capped sub-walks (counted as one node each).
    bails: u64,
    /// Closures the evaluator could not force under the oracle's fuel.
    stuck: u64,
    capped: bool,
}

/// A memo key: a closure's identity, plus the first fresh level it was opened
/// at when it has pending binders (a 0-binder closure carries its own
/// environment and its value does not depend on the ambient depth).
type Key = (CloId, u32);

/// The graph the walk discovers: one node per distinct sub-value, its
/// children in order, and the syntax mass the node itself writes (its head
/// node, its spine's elimination nodes, and any payload that is syntax
/// already).
#[derive(Default)]
struct Dag {
    kids: Vec<Vec<u32>>,
    own: Vec<u64>,
    /// Whether the node's value has a type this elaborator can write down
    /// without inferring one: a type (its code's statement is `Ty l`) or a
    /// type *encoding* (same). Only such a node can be minted as a code
    /// definition; everything else would need the type a value does not
    /// carry.
    typable: Vec<bool>,
    /// Completion order: every node's children finish before it does, so one
    /// forward pass over this is a bottom-up fold.
    finish: Vec<u32>,
}

impl Dag {
    fn new_node(&mut self) -> u32 {
        self.kids.push(Vec::new());
        self.own.push(1);
        self.typable.push(false);
        (self.kids.len() - 1) as u32
    }

    fn len(&self) -> usize {
        self.kids.len()
    }
}

struct Walk<'a, 'v> {
    ev: Eval<'a, 'v>,
    arena: &'v ValueArena<'v>,
    tm: HashMap<Key, u32>,
    ty: HashMap<Key, u32>,
    val: HashMap<usize, u32>,
    dag: Dag,
    /// The node under construction: its children so far, and its own mass.
    cur: (Vec<u32>, u64),
    /// Whether the node under construction is mintable as a code.
    cur_typable: bool,
    depth: u32,
    rep: Report,
}

impl<'a, 'v> Walk<'a, 'v> {
    fn fresh(&self, lvl: u32) -> &'v TmClo<'v> {
        self.arena.tm(TmClo::val(Rc::new(Val::var(lvl))))
    }

    fn budget(&mut self) -> bool {
        if self.dag.len() >= GRAPH_CAP {
            self.rep.capped = true;
            return false;
        }
        self.depth < DEPTH_CAP
    }

    /// A leaf node, for a sub-walk the budget or the fuel stopped.
    fn leaf(&mut self) -> u32 {
        let id = self.dag.new_node();
        self.dag.finish.push(id);
        id
    }

    /// Open `body` as a new graph node: the children it pushes become the
    /// node's, and the mass it returns is the node's own.
    fn node<F>(&mut self, body: F) -> u32
    where
        F: FnOnce(&mut Self) -> u64,
    {
        let id = self.dag.new_node();
        let saved = std::mem::take(&mut self.cur);
        let saved_t = std::mem::take(&mut self.cur_typable);
        self.depth += 1;
        let mass = body(self);
        self.depth -= 1;
        self.dag.typable[id as usize] = std::mem::replace(&mut self.cur_typable, saved_t);
        let (kids, own) = std::mem::replace(&mut self.cur, saved);
        self.dag.kids[id as usize] = kids;
        // `val`/`vty` already count the head node they wrote.
        self.dag.own[id as usize] = own + mass;
        self.dag.finish.push(id);
        id
    }

    /// A term sub-structure with `pending` of its own binders, opened at
    /// `lvl`; the graph node it is.
    fn tm_node(&mut self, c: &'v TmClo<'v>, pending: u32, lvl: u32) -> u32 {
        let key = (c.ident(), if pending == 0 { 0 } else { lvl });
        if let Some(id) = self.tm.get(&key) {
            return *id;
        }
        if !self.budget() {
            self.rep.bails += 1;
            return self.leaf();
        }
        // A sentinel breaks a cycle the way a readback's own memo would; the
        // value graph of a normalizing term has none.
        let placeholder = self.dag.len() as u32;
        self.tm.insert(key, placeholder);
        let opened = if pending == 0 {
            self.ev.force(c)
        } else {
            let args: Vec<&'v TmClo<'v>> = (0..pending).map(|i| self.fresh(lvl + i)).collect();
            self.ev.apply(c, &args)
        };
        let id = match opened {
            Ok(v) => self.node(|w| w.val(&v, lvl + pending)),
            Err(_) => {
                self.rep.stuck += 1;
                self.leaf()
            }
        };
        self.tm.insert(key, id);
        id
    }

    fn ty_node(&mut self, c: &'v TyClo<'v>, pending: u32, lvl: u32) -> u32 {
        let key = (c.ident(), if pending == 0 { 0 } else { lvl });
        if let Some(id) = self.ty.get(&key) {
            return *id;
        }
        if !self.budget() {
            self.rep.bails += 1;
            return self.leaf();
        }
        let placeholder = self.dag.len() as u32;
        self.ty.insert(key, placeholder);
        let opened = if pending == 0 {
            self.ev.force_ty(c)
        } else {
            let args: Vec<&'v TmClo<'v>> = (0..pending).map(|i| self.fresh(lvl + i)).collect();
            self.ev.apply_ty(c, &args)
        };
        let id = match opened {
            Ok(v) => self.node(|w| w.vty(&v, lvl + pending)),
            Err(_) => {
                self.rep.stuck += 1;
                self.leaf()
            }
        };
        self.ty.insert(key, id);
        id
    }

    /// An already-forced value reached out of line (a neutral's substitution,
    /// a `Vec`'s length), keyed on its `Rc`'s address.
    fn shared_node(&mut self, v: &Rc<Val<'v>>, lvl: u32) -> u32 {
        let key = Rc::as_ptr(v) as usize;
        if let Some(id) = self.val.get(&key) {
            return *id;
        }
        if !self.budget() {
            self.rep.bails += 1;
            return self.leaf();
        }
        let placeholder = self.dag.len() as u32;
        self.val.insert(key, placeholder);
        let v = Rc::clone(v);
        let id = self.node(|w| w.val(&v, lvl));
        self.val.insert(key, id);
        id
    }

    // The three the arms below call: a child is a *node*, so it contributes
    // an edge and no mass of its own.
    fn tm(&mut self, c: &'v TmClo<'v>, pending: u32, lvl: u32) -> u64 {
        let id = self.tm_node(c, pending, lvl);
        self.cur.0.push(id);
        0
    }

    fn ty(&mut self, c: &'v TyClo<'v>, pending: u32, lvl: u32) -> u64 {
        let id = self.ty_node(c, pending, lvl);
        self.cur.0.push(id);
        0
    }

    fn shared(&mut self, v: &Rc<Val<'v>>, lvl: u32) -> u64 {
        let id = self.shared_node(v, lvl);
        self.cur.0.push(id);
        0
    }

    fn val(&mut self, v: &Rc<Val<'v>>, lvl: u32) -> u64 {
        self.cur_typable = matches!(
            &**v,
            Val::TmNat
                | Val::TmTy(_)
                | Val::TmUnit { .. }
                | Val::TmEmpty { .. }
                | Val::TmSEmpty { .. }
                | Val::TmSquash { .. }
                | Val::TmPi { .. }
                | Val::TmSigma { .. }
                | Val::TmW { .. }
                | Val::TmWf { .. }
                | Val::TmId { .. }
                | Val::TmSEq { .. }
                | Val::TmSum { .. }
                | Val::TmVec { .. }
                | Val::TmFin { .. }
        );
        let kids: u64 = match &**v {
            Val::TmNat
            | Val::TmTy(_)
            | Val::TmUnit { .. }
            | Val::TmEmpty { .. }
            | Val::TmSEmpty { .. }
            | Val::Zero
            | Val::Triv { .. } => 0,
            Val::BoxTy(t) => count_ty(t).nodes,
            // A code payload's syntax is a leaf for this walk, as it is for
            // every emitter: it is scoped in another Δ.
            Val::BoxTm(_) => 1,
            Val::TmSquash { ty, .. } => self.tm(ty, 0, lvl),
            Val::TmPi { dom, cod, .. }
            | Val::TmSigma { fst: dom, snd: cod, .. }
            | Val::TmW { shape: dom, pos: cod, .. } => {
                self.tm(dom, 0, lvl) + self.tm(cod, 1, lvl)
            }
            Val::TmWf { shape, arity, .. } => self.tm(shape, 0, lvl) + self.tm(arity, 1, lvl),
            Val::TmId { ty, lhs, rhs, .. } | Val::TmSEq { ty, lhs, rhs, .. } => {
                self.tm(ty, 0, lvl) + self.tm(lhs, 0, lvl) + self.tm(rhs, 0, lvl)
            }
            Val::TmSum { lhs, rhs, .. } => self.tm(lhs, 0, lvl) + self.tm(rhs, 0, lvl),
            Val::TmVec { elem, len, .. } => self.tm(elem, 0, lvl) + self.tm(len, 0, lvl),
            Val::TmFin { len } => self.tm(len, 0, lvl),
            Val::Succ(t) => self.tm(t, 0, lvl),
            // A run's readback is the `Succ` chain it stands for; the program
            // is the evaluator's spelling of that chain's height.
            Val::NatRun { program, tail } => {
                // The chain's height, when it is a bounded repetition; the
                // readback of a wider program is at least one `Succ`.
                let h = heather_kernel::value::program::ContextProgram::repetition_count_up_to(
                    program, 1 << 20,
                )
                .unwrap_or(1);
                h.max(1) + self.tm(tail, 0, lvl)
            }
            // A bit run reads back as the Σ-chain `bit_run_unpack` produces:
            // one `Pair` with two type annotations per bit.
            Val::BitRun { width, tail_len, tail, .. } => {
                4 * u64::from(*width) + self.tm(tail_len, 0, lvl) + self.tm(tail, 0, lvl)
            }
            Val::NatSync { tail, elim, .. } => {
                let e = self.elim(elim, lvl);
                self.tm(tail, 0, lvl) + e
            }
            Val::BitFold { tail, elim, apps, .. } => {
                let mut n = self.elim(elim, lvl);
                for a in apps.iter() {
                    n += self.elim(a, lvl);
                }
                n + self.tm(tail, 0, lvl)
            }
            Val::Refl { ty, tm, .. } | Val::SRefl { ty, tm, .. } | Val::Squash { ty, tm, .. } => {
                self.ty(ty, 0, lvl) + self.tm(tm, 0, lvl)
            }
            Val::Pair { fst_ty, snd_ty, fst, snd, .. } => {
                self.ty(fst_ty, 0, lvl)
                    + self.ty(snd_ty, 1, lvl)
                    + self.tm(fst, 0, lvl)
                    + self.tm(snd, 0, lvl)
            }
            Val::Inl { lhs, rhs, val, .. } | Val::Inr { lhs, rhs, val, .. } => {
                self.ty(lhs, 0, lvl) + self.ty(rhs, 0, lvl) + self.tm(val, 0, lvl)
            }
            Val::Sup { shape_ty, pos_ty, label, children, .. } => {
                self.ty(shape_ty, 0, lvl)
                    + self.ty(pos_ty, 1, lvl)
                    + self.tm(label, 0, lvl)
                    + self.tm(children, 0, lvl)
            }
            Val::Supf { shape, arity, label, children, .. } => {
                self.ty(shape, 0, lvl)
                    + self.tm(arity, 1, lvl)
                    + self.tm(label, 0, lvl)
                    + self.tm(children, 0, lvl)
            }
            Val::Lam { dom, body, .. } => self.ty(dom, 0, lvl) + self.tm(body, 1, lvl),
            Val::ULam { body, .. } | Val::CtxLam { body, .. } | Val::TyLam { body, .. } => {
                self.tm(body, 0, lvl)
            }
            Val::Neutral(n) => {
                let mut k = match &n.head {
                    Head::Var(_) | Head::BaseVar(_) => 0,
                    Head::Global { subst, .. } => {
                        let terms = subst.terms.clone();
                        let mut s = 0;
                        for t in &terms {
                            s += self.shared(t, lvl);
                        }
                        s
                    }
                    Head::BoxedGlobalTy(t) => count_ty(t).nodes,
                    Head::BoxedGlobalTm(_) => 1,
                    Head::Stuck(v) => {
                        let v = Rc::clone(v);
                        self.shared(&v, lvl)
                    }
                };
                let spine: Vec<Rc<Elim<'v>>> =
                    n.spine.iter_rev().map(|e| Rc::new(e.clone())).collect();
                for e in &spine {
                    k += 1 + self.elim(e, lvl);
                }
                k
            }
        };
        1 + kids
    }

    fn vty(&mut self, v: &Rc<VTy<'v>>, lvl: u32) -> u64 {
        self.cur_typable = true;
        let kids: u64 = match &**v {
            VTy::Nat
            | VTy::Ty(_)
            | VTy::Unit { .. }
            | VTy::Empty { .. }
            | VTy::SEmpty { .. }
            | VTy::CodeTy { .. } => 0,
            VTy::CodeTm { ty, .. } => count_ty(ty).nodes,
            VTy::Squash { ty, .. } => self.ty(ty, 0, lvl),
            VTy::Pi { dom, cod, .. }
            | VTy::Sigma { fst: dom, snd: cod, .. }
            | VTy::W { shape: dom, pos: cod, .. } => self.ty(dom, 0, lvl) + self.ty(cod, 1, lvl),
            VTy::Wf { shape, arity, .. } => self.ty(shape, 0, lvl) + self.tm(arity, 1, lvl),
            VTy::Sum { lhs, rhs, .. } => self.ty(lhs, 0, lvl) + self.ty(rhs, 0, lvl),
            VTy::Id { ty, lhs, rhs, .. } | VTy::SEq { ty, lhs, rhs, .. } => {
                self.ty(ty, 0, lvl) + self.tm(lhs, 0, lvl) + self.tm(rhs, 0, lvl)
            }
            VTy::Vec { elem, len, .. } => {
                let len = Rc::clone(len);
                self.ty(elem, 0, lvl) + self.shared(&len, lvl)
            }
            VTy::Fin { len } => {
                let len = Rc::clone(len);
                self.shared(&len, lvl)
            }
            VTy::UPi { body, .. } | VTy::CtxPi { body, .. } | VTy::TyPi { body, .. } => {
                self.ty(body, 0, lvl)
            }
            VTy::Neutral(VNeTy::Global { subst, .. }) => {
                let terms = subst.terms.clone();
                let mut s = 0;
                for t in &terms {
                    s += self.shared(t, lvl);
                }
                s
            }
            VTy::Neutral(VNeTy::El { tm, .. }) => {
                let tm = Rc::clone(tm);
                self.shared(&tm, lvl)
            }
        };
        1 + kids
    }

    /// One elimination's annotations. Binder counts are
    /// `conv/dom/values.rs`'s `view_neutral`.
    fn elim(&mut self, e: &Elim<'v>, lvl: u32) -> u64 {
        match e {
            Elim::App { dom, cod, arg, .. } => {
                self.ty(dom, 0, lvl) + self.ty(cod, 1, lvl) + self.tm(arg, 0, lvl)
            }
            Elim::UApp { .. } | Elim::CtxApp { .. } => 0,
            Elim::TyApp { arg } => count_ty(arg).nodes,
            Elim::Fst { fst_ty, snd_ty, .. } | Elim::Snd { fst_ty, snd_ty, .. } => {
                self.ty(fst_ty, 0, lvl) + self.ty(snd_ty, 1, lvl)
            }
            Elim::ElimNat { motive, base, step, .. } => {
                self.ty(motive, 1, lvl) + self.tm(base, 0, lvl) + self.tm(step, 2, lvl)
            }
            Elim::ElimEmpty { motive, .. } | Elim::ElimSEmpty { motive, .. } => {
                self.ty(motive, 1, lvl)
            }
            Elim::ElimSquash { src_ty, motive, case, .. } => {
                self.ty(src_ty, 0, lvl) + self.ty(motive, 1, lvl) + self.tm(case, 1, lvl)
            }
            Elim::Case { lhs, rhs, motive, case_l, case_r, .. } => {
                self.ty(lhs, 0, lvl)
                    + self.ty(rhs, 0, lvl)
                    + self.ty(motive, 1, lvl)
                    + self.tm(case_l, 1, lvl)
                    + self.tm(case_r, 1, lvl)
            }
            Elim::ElimW { shape, pos, motive, step, .. } => {
                self.ty(shape, 0, lvl)
                    + self.ty(pos, 1, lvl)
                    + self.ty(motive, 1, lvl)
                    + self.tm(step, 3, lvl)
            }
            Elim::ElimWf { shape, arity, motive, step, .. } => {
                self.ty(shape, 0, lvl)
                    + self.tm(arity, 1, lvl)
                    + self.ty(motive, 1, lvl)
                    + self.tm(step, 3, lvl)
            }
            Elim::J { ty, lhs, motive, case, rhs, .. } => {
                self.ty(ty, 0, lvl)
                    + self.tm(lhs, 0, lvl)
                    + self.ty(motive, 2, lvl)
                    + self.tm(case, 0, lvl)
                    + self.tm(rhs, 0, lvl)
            }
            Elim::Transp { ty, motive, lhs, rhs, tm, .. } => {
                self.ty(ty, 0, lvl)
                    + self.ty(motive, 1, lvl)
                    + self.tm(lhs, 0, lvl)
                    + self.tm(rhs, 0, lvl)
                    + self.tm(tm, 0, lvl)
            }
            Elim::LetBoxTy { motive, body, .. } => self.ty(motive, 1, lvl) + self.tm(body, 0, lvl),
            Elim::LetBoxTm { ty, motive, body, .. } => {
                count_ty(ty).nodes + self.ty(motive, 1, lvl) + self.tm(body, 0, lvl)
            }
            // The code recursors' motives and branches are syntax in another
            // Δ, as they are for every emitter.
            Elim::ElimCodeTy { .. } | Elim::ElimCodeTm { .. } => 1,
        }
    }
}

/// What a reference to a minted name costs where the component used to be
/// spelled: `El (D#c^δ)` is the `El`, the `GlobalTm` and its (empty)
/// substitution.
const REF_COST: u64 = 3;

/// The thresholds §6's "unit of sharing" is chosen among: a node is named
/// when it is spelled more than once **and** naming it saves at least this
/// many nodes. `0` is "every node spelled twice", the design's first
/// reading; the rest buy most of the collapse with a fraction of the
/// declarations.
const THRESHOLDS: [u64; 5] = [0, 64, 1_024, 16_384, 262_144];

/// The tree each node expands to when nothing is named: the naive readback's
/// output, computed over the graph in the graph's own time.
fn tree_sizes(dag: &Dag) -> Vec<u64> {
    let mut size = vec![0u64; dag.len()];
    for &n in &dag.finish {
        let mut s = dag.own[n as usize];
        for &k in &dag.kids[n as usize] {
            s = s.saturating_add(size[k as usize]);
        }
        size[n as usize] = s;
    }
    size
}

/// One threshold's answer: how many nodes are named, and how many nodes the
/// emitted spelling then has (the root's term plus every minted body).
fn with_names(dag: &Dag, indeg: &[u32], threshold: u64, root: u32, codes_only: bool) -> (u64, u64) {
    let mut cost = vec![0u64; dag.len()];
    let mut named = vec![false; dag.len()];
    let mut mints = 0u64;
    let mut bodies = 0u64;
    for &n in &dag.finish {
        let mut c = dag.own[n as usize];
        for &k in &dag.kids[n as usize] {
            c = c.saturating_add(if named[k as usize] {
                REF_COST
            } else {
                cost[k as usize]
            });
        }
        cost[n as usize] = c;
        let shares = u64::from(indeg[n as usize]).saturating_sub(1);
        if shares > 0
            && shares.saturating_mul(c.saturating_sub(REF_COST)) >= threshold
            && n != root
            && (!codes_only || dag.typable[n as usize])
        {
            named[n as usize] = true;
            mints += 1;
            bodies = bodies.saturating_add(c);
        }
    }
    (mints, bodies.saturating_add(cost[root as usize]))
}

/// The one call site: `build_ctor`'s reduct, with the type the rewriter was
/// asked to reduce (`ty`) and the reduct it produced (`reduct`), so the
/// naive-readback column and §2's tree count are one line.
pub(crate) fn at_build_ctor(
    world: &GlobalCtx,
    gamma: &LocalCtx,
    ty: &Type,
    fuel: u64,
    reduct: &Type,
) {
    if !enabled() {
        return;
    }
    let syntax = count_ty(reduct).nodes;
    let t0 = std::time::Instant::now();
    let arena = ValueArena::new();
    let defs = Defs::transparent(world);
    let root = match eval::whnf_value_ty(&arena, &Rc::new(ty.clone()), gamma, defs, fuel) {
        Ok(v) => v,
        Err(_) => {
            eprintln!("rb count item=- OUTOFFUEL syntax={syntax}");
            return;
        }
    };
    let mut w = Walk {
        ev: Eval::new(fuel, defs, gamma.base, &arena),
        arena: &arena,
        tm: HashMap::new(),
        ty: HashMap::new(),
        val: HashMap::new(),
        dag: Dag::default(),
        cur: (Vec::new(), 0),
        cur_typable: false,
        depth: 0,
        rep: Report::default(),
    };
    let lvl = gamma.entries.len() as u32;
    let root_id = w.node(|x| x.vty(&root, lvl));
    let us = t0.elapsed().as_micros();
    let dag = w.dag;
    let rep = w.rep;
    let naive = tree_sizes(&dag)[root_id as usize];
    let mut indeg = vec![0u32; dag.len()];
    for kids in &dag.kids {
        for &k in kids {
            indeg[k as usize] += 1;
        }
    }
    let shared = indeg.iter().filter(|d| **d > 1).count();
    let mut cols = String::new();
    for t in THRESHOLDS {
        let (mints, emitted) = with_names(&dag, &indeg, t, root_id, false);
        let (cmints, cemitted) = with_names(&dag, &indeg, t, root_id, true);
        cols.push_str(&format!(" T{t}={mints}/{emitted}|codes={cmints}/{cemitted}"));
    }
    let (m, i) = crate::stats::current_item().unwrap_or(("-".into(), "-".into()));
    eprintln!(
        "rb count item={m}::{i} syntax={syntax} naive={naive} graph={} shared={shared} \
         bails={} stuck={} capped={} us={us}{cols}",
        dag.len(),
        rep.bails,
        rep.stuck,
        rep.capped as u8,
    );
}
