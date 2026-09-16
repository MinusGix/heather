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
    /// `Term::Var` occurrences. Zero for every closed piece of syntax; the
    /// free-variable instrument uses it to refuse a node whose mass includes
    /// embedded syntax it cannot resolve to levels (a code payload, a
    /// `TyApp`'s argument).
    pub(crate) vars: u64,
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
    if let Term::Var(_) = t {
        c.vars += 1;
    }
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

/// `HEATHER_RB=count` is §11.1's two columns and §11.2's threshold sweep;
/// `HEATHER_RB=fv` is the same walk with the free-variable instrument of the
/// name-per-value pass on top (see [`fv_report`]). The `count` line is
/// unchanged in either mode, so the two are comparable to the unit.
#[derive(PartialEq, Eq, Clone, Copy)]
pub(crate) enum Mode {
    Off,
    Count,
    Fv,
}

fn mode() -> Mode {
    static M: OnceLock<Mode> = OnceLock::new();
    *M.get_or_init(|| match std::env::var("HEATHER_RB").ok().as_deref() {
        Some("count") => Mode::Count,
        Some("fv") => Mode::Fv,
        _ => Mode::Off,
    })
}

pub(crate) fn enabled() -> bool {
    mode() != Mode::Off
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
    /// The fresh-neutral **levels** the node's own arms write down — a
    /// `Head::Var(lvl)` reached through this node's value and not through a
    /// child node. The name-per-value instrument's raw material.
    own_vars: Vec<Vec<u32>>,
    /// The levels the node itself opened: `(lvl, pending)` for a closure
    /// applied to `pending` fresh neutrals at `lvl`, `(0, 0)` otherwise.
    bound: Vec<(u32, u32)>,
    /// Whether the node's own arms write a `Head::BaseVar` — a variable of
    /// the abstract prefix, spelled at index `d + k`. Depth-relative in the
    /// *syntax* but not a dependency on any binder of the chain: re-scoped
    /// into a mint's Δ it is `|Δ| + k`. Counted so the claim is on the record
    /// rather than assumed.
    basevar: Vec<bool>,
    /// Whether the node's own mass includes embedded syntax with a free
    /// variable the walk cannot resolve to a level (see [`Walk::syn_ty`]).
    opaque: Vec<bool>,
    /// Whether the node is a **type** of the value language (`vty`) rather
    /// than a term (`val`). A Ψ binding names a term, so a type node is
    /// nameable only through its *code* (§12.1 item 1) — the device
    /// `docs/name-per-value-design.md` §5 keeps separate. The column exists
    /// so the term-only ceiling is on the record beside the `Δ = fv` one.
    is_ty: Vec<bool>,
    /// For a node of the type sort, which former it is — the tally the
    /// type-code device of `docs/name-per-value-design.md` §5 has to cover,
    /// since `code.rs`'s `code_of` is partial on purpose.
    ty_shape: Vec<&'static str>,
    /// For a node of the type sort, whether its **own former** has a code in
    /// `code.rs`'s `code_of`. Whether the node as a whole can be quoted is the
    /// bottom-up closure of this over the node's *type* children, since
    /// `code_of` recurses into them and clones its term children — that fold
    /// is the `tycode=` column, which is step 0 item 2 of the implementation
    /// brief (`docs/name-per-value-design.md` §8.3's last bullet, asked of the
    /// whole subtree rather than of the root former alone).
    code_shape: Vec<bool>,
    /// The level the node was opened at on the walk's **first** visit to it —
    /// the only visit, since the memo answers the rest. A 0-binder closure
    /// merged across depths keeps the first one, which is the whole question
    /// the instrument asks.
    open_lvl: Vec<u32>,
}

impl Dag {
    fn new_node(&mut self) -> u32 {
        self.kids.push(Vec::new());
        self.own.push(1);
        self.typable.push(false);
        self.own_vars.push(Vec::new());
        self.bound.push((0, 0));
        self.basevar.push(false);
        self.opaque.push(false);
        self.is_ty.push(false);
        self.ty_shape.push("-");
        self.code_shape.push(true);
        self.open_lvl.push(0);
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
    val: HashMap<(usize, u32), u32>,
    dag: Dag,
    /// The node under construction: its children so far, and its own mass.
    cur: (Vec<u32>, u64),
    /// Whether the node under construction is mintable as a code.
    cur_typable: bool,
    /// Nodes whose value is one `rbemit.rs` **declines** (a compressed run, a
    /// pending fold algebra). The counter walks them and the emitter does
    /// not, so a graph node of this class is sharing no emitter ever sees.
    declines: u64,
    /// The fresh-neutral levels and abstract-prefix hit of the node under
    /// construction; saved and restored around a child exactly as `cur` is.
    cur_vars: Vec<u32>,
    cur_basevar: bool,
    cur_opaque: bool,
    /// See [`Dag::is_ty`]; saved and restored around a child as `cur` is.
    cur_is_ty: bool,
    cur_shape: &'static str,
    /// See [`Dag::code_shape`]; saved and restored around a child as `cur` is.
    cur_code_shape: bool,
    /// The highest level any fresh neutral was opened at.
    max_lvl: u32,
    /// `HEATHER_RB=fv`: every opening gets its **own** binder identities from
    /// this counter rather than the walk's current depth, and every node is
    /// keyed on closure identity alone. Depth-keyed levels alias — two
    /// branches at the same depth name different binders `lvl`, and a scope
    /// analysis over them silently equates them — so the question "does every
    /// occurrence's chain contain this value's free variables" cannot be
    /// asked in the `count` walk's numbering. It can be asked in this one.
    uniq: bool,
    next: u32,
    /// See [`Walk::shared_node`]: key an out-of-line forced value the way
    /// `rbemit.rs` reads one, per depth, instead of on its address alone.
    split: bool,
    depth: u32,
    rep: Report,
}

impl<'a, 'v> Walk<'a, 'v> {
    fn fresh(&self, lvl: u32) -> &'v TmClo<'v> {
        self.arena.tm(TmClo::val(Rc::new(Val::var(lvl))))
    }

    /// Record that `id` opened `pending` fresh neutrals at `lvl`: those
    /// levels are the node's own binders, and a free variable of its body at
    /// one of them is bound, not free.
    /// The binder identities this opening uses: fresh ones from the counter
    /// under `HEATHER_RB=fv`, the walk's own depth otherwise.
    fn open_at(&mut self, pending: u32, lvl: u32) -> u32 {
        if self.uniq && pending > 0 {
            let b = self.next;
            self.next += pending;
            b
        } else {
            lvl
        }
    }

    fn bind(&mut self, id: u32, pending: u32, lvl: u32) {
        self.dag.open_lvl[id as usize] = lvl;
        if pending > 0 {
            self.dag.bound[id as usize] = (lvl, pending);
            self.max_lvl = self.max_lvl.max(lvl + pending);
        }
    }

    /// A piece of embedded syntax the walk counts as mass rather than
    /// entering: a code payload, a `TyApp`'s argument. Its size is the
    /// count; a `Term::Var` in it is a free variable at an index this walk
    /// does not resolve, so the node is marked **opaque** and the
    /// free-variable instrument refuses to name it.
    fn syn_ty(&mut self, t: &Type) -> u64 {
        let c = count_ty(t);
        if c.vars > 0 {
            self.cur_opaque = true;
        }
        c.nodes
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
        let saved_v = std::mem::take(&mut self.cur_vars);
        let saved_b = std::mem::take(&mut self.cur_basevar);
        let saved_o = std::mem::take(&mut self.cur_opaque);
        let saved_k = std::mem::take(&mut self.cur_is_ty);
        let saved_s = std::mem::replace(&mut self.cur_shape, "-");
        let saved_c = std::mem::replace(&mut self.cur_code_shape, true);
        self.depth += 1;
        let mass = body(self);
        self.depth -= 1;
        self.dag.typable[id as usize] = std::mem::replace(&mut self.cur_typable, saved_t);
        self.dag.own_vars[id as usize] = std::mem::replace(&mut self.cur_vars, saved_v);
        self.dag.basevar[id as usize] = std::mem::replace(&mut self.cur_basevar, saved_b);
        self.dag.opaque[id as usize] = std::mem::replace(&mut self.cur_opaque, saved_o);
        self.dag.is_ty[id as usize] = std::mem::replace(&mut self.cur_is_ty, saved_k);
        self.dag.ty_shape[id as usize] = std::mem::replace(&mut self.cur_shape, saved_s);
        self.dag.code_shape[id as usize] = std::mem::replace(&mut self.cur_code_shape, saved_c);
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
        let key = (c.ident(), if pending == 0 || self.uniq { 0 } else { lvl });
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
        let base = self.open_at(pending, lvl);
        let opened = if pending == 0 {
            self.ev.force(c)
        } else {
            let args: Vec<&'v TmClo<'v>> = (0..pending).map(|i| self.fresh(base + i)).collect();
            self.ev.apply(c, &args)
        };
        let id = match opened {
            Ok(v) => self.node(|w| w.val(&v, lvl + pending)),
            Err(_) => {
                self.rep.stuck += 1;
                self.leaf()
            }
        };
        self.bind(id, pending, base);
        self.tm.insert(key, id);
        id
    }

    fn ty_node(&mut self, c: &'v TyClo<'v>, pending: u32, lvl: u32) -> u32 {
        let key = (c.ident(), if pending == 0 || self.uniq { 0 } else { lvl });
        if let Some(id) = self.ty.get(&key) {
            return *id;
        }
        if !self.budget() {
            self.rep.bails += 1;
            return self.leaf();
        }
        let placeholder = self.dag.len() as u32;
        self.ty.insert(key, placeholder);
        let base = self.open_at(pending, lvl);
        let opened = if pending == 0 {
            self.ev.force_ty(c)
        } else {
            let args: Vec<&'v TmClo<'v>> = (0..pending).map(|i| self.fresh(base + i)).collect();
            self.ev.apply_ty(c, &args)
        };
        let id = match opened {
            Ok(v) => self.node(|w| w.vty(&v, lvl + pending)),
            Err(_) => {
                self.rep.stuck += 1;
                self.leaf()
            }
        };
        self.bind(id, pending, base);
        self.ty.insert(key, id);
        id
    }

    /// An already-forced value reached out of line (a neutral's substitution,
    /// a `Vec`'s length), keyed on its `Rc`'s address.
    fn shared_node(&mut self, v: &Rc<Val<'v>>, lvl: u32) -> u32 {
        // `rbemit.rs`'s own `shared` does **not** memoize — it re-reads an
        // out-of-line value at the depth it is met at. This walk does, on the
        // address alone, so it merges such a value across depths where the
        // emitter would not. `HEATHER_RB_FVSPLIT=1` keys it the emitter's way,
        // which is how the cross-length sharing of §3 is attributed.
        let key = (Rc::as_ptr(v) as usize, if self.split { lvl } else { 0 });
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
        self.bind(id, 0, lvl);
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
        self.cur_is_ty = false;
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
            Val::BoxTy(t) => self.syn_ty(t),
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
                self.declines += 1;
                4 * u64::from(*width) + self.tm(tail_len, 0, lvl) + self.tm(tail, 0, lvl)
            }
            Val::NatSync { tail, elim, .. } => {
                self.declines += 1;
                let e = self.elim(elim, lvl);
                self.tm(tail, 0, lvl) + e
            }
            Val::BitFold { tail, elim, apps, .. } => {
                self.declines += 1;
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
                    Head::Var(lvl) => {
                        self.cur_vars.push(*lvl);
                        self.max_lvl = self.max_lvl.max(*lvl + 1);
                        0
                    }
                    Head::BaseVar(_) => {
                        self.cur_basevar = true;
                        0
                    }
                    Head::Global { subst, .. } => {
                        let terms = subst.terms.clone();
                        let mut s = 0;
                        for t in &terms {
                            s += self.shared(t, lvl);
                        }
                        s
                    }
                    Head::BoxedGlobalTy(t) => self.syn_ty(t),
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
        self.cur_is_ty = true;
        self.cur_shape = match &**v {
            VTy::Nat => "Nat",
            VTy::Ty(_) => "Ty",
            VTy::Unit { .. } | VTy::Empty { .. } | VTy::SEmpty { .. } => "unit/empty",
            VTy::Squash { .. } => "Squash",
            VTy::Pi { .. } => "Pi",
            VTy::Sigma { .. } => "Sigma",
            VTy::W { .. } => "W",
            VTy::Wf { .. } => "Wf",
            VTy::Sum { .. } => "Sum",
            VTy::Id { .. } => "Id",
            VTy::SEq { .. } => "SEq",
            VTy::Vec { .. } => "Vec",
            VTy::Fin { .. } => "Fin",
            VTy::UPi { .. } | VTy::CtxPi { .. } | VTy::TyPi { .. } => "UPi/CtxPi/TyPi",
            VTy::CodeTy { .. } | VTy::CodeTm { .. } => "Code",
            VTy::Neutral(VNeTy::Global { .. }) => "GlobalTy",
            VTy::Neutral(VNeTy::El { .. }) => "El",
        };
        // Which formers `code.rs`'s `code_of` has a code for, arm for arm.
        self.cur_code_shape = !matches!(
            &**v,
            VTy::SEmpty { .. }
                | VTy::UPi { .. }
                | VTy::CtxPi { .. }
                | VTy::TyPi { .. }
                | VTy::CodeTy { .. }
                | VTy::CodeTm { .. }
                | VTy::Neutral(VNeTy::Global { .. })
        );
        self.cur_typable = true;
        let kids: u64 = match &**v {
            VTy::Nat
            | VTy::Ty(_)
            | VTy::Unit { .. }
            | VTy::Empty { .. }
            | VTy::SEmpty { .. }
            | VTy::CodeTy { .. } => 0,
            VTy::CodeTm { ty, .. } => self.syn_ty(ty),
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
            Elim::TyApp { arg } => self.syn_ty(arg),
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
                self.syn_ty(ty) + self.ty(motive, 1, lvl) + self.tm(body, 0, lvl)
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
    let lvl = gamma.entries.len() as u32;
    let mut w = Walk {
        ev: Eval::new(fuel, defs, gamma.base, &arena),
        arena: &arena,
        tm: HashMap::new(),
        ty: HashMap::new(),
        val: HashMap::new(),
        dag: Dag::default(),
        cur: (Vec::new(), 0),
        cur_typable: false,
        declines: 0,
        cur_vars: Vec::new(),
        cur_basevar: false,
        cur_opaque: false,
        cur_is_ty: false,
        cur_code_shape: true,
        cur_shape: "-",
        max_lvl: lvl,
        uniq: mode() == Mode::Fv && std::env::var("HEATHER_RB_FVDEPTH").is_err(),
        next: lvl,
        split: std::env::var("HEATHER_RB_FVSPLIT").is_ok(),
        depth: 0,
        rep: Report::default(),
    };
    let root_id = w.node(|x| x.vty(&root, lvl));
    let us = t0.elapsed().as_micros();
    let dag = w.dag;
    let rep = w.rep;
    let max_lvl = w.max_lvl.max(w.next);
    let declines = w.declines;
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
    if mode() == Mode::Fv {
        fv_report(&dag, &indeg, root_id, lvl, max_lvl, naive, declines, &m, &i);
    }
}

// ---------------------------------------------------------------------------
// The free-variable instrument (`HEATHER_RB=fv`): one name per *value*
// ---------------------------------------------------------------------------
//
// `docs/projected-tuple-tower-design.md` §12.5 concluded that the heavy
// shared sub-values of the tower are not closed, that one name per *depth* is
// all they can have, and that §11.2's price "was never reachable by any
// emitter". The reading this instrument tests is narrower and does not
// contradict the measurement it was drawn from: a value that is one pointer
// reached under two binder chains cannot depend on *either chain's* binders,
// because a closure under a binder is a different object and `Env` entries
// are values. What it can depend on is (a) the ambient Γ and (b) the fresh
// neutrals the walk itself introduced — and those, being levels, are the same
// object under both chains or are not reached at all.
//
// So the unit is not "the innermost `k` entries" (§12.5's minimal Δ, measured
// on syntax already keyed per depth) but the node's **exact free variables**:
// a mint `Δ = fv ⊢ body`, referenced under any chain by `u^δ` with δ
// substituting those variables at their indices in *that* chain. Depth
// independence is then by construction, and the two things the walk has to
// answer are
//
//   1. does every occurrence's chain actually contain all of `fv`? (it must,
//      or the reference cannot be spelled, and the reading is wrong), and
//   2. what does the emitted syntax then count?
//
// Both come off the same graph the two columns above already built.

/// A set of binder identities, as a **sorted vector**. Under
/// `HEATHER_RB=fv` every opening takes its own identities from a counter, so
/// the universe is as large as the graph — but the sets themselves are tiny
/// (a value's free variables, or one chain's binders), which a bitset over
/// that universe would not be.
#[derive(Clone, PartialEq, Eq, Default)]
struct Bits(Vec<u32>);

impl Bits {
    fn empty(_n: u32) -> Bits {
        Bits(Vec::new())
    }

    /// The ambient Γ: levels `0..n`, in scope everywhere.
    fn upto(n: u32, _cap: u32) -> Bits {
        Bits((0..n).collect())
    }

    fn set(&mut self, l: u32) {
        if let Err(i) = self.0.binary_search(&l) {
            self.0.insert(i, l);
        }
    }

    fn clear(&mut self, l: u32) {
        if let Ok(i) = self.0.binary_search(&l) {
            self.0.remove(i);
        }
    }

    fn get(&self, l: u32) -> bool {
        self.0.binary_search(&l).is_ok()
    }

    fn union(&mut self, o: &Bits) {
        if o.0.is_empty() {
            return;
        }
        let mut out = Vec::with_capacity(self.0.len() + o.0.len());
        let (mut a, mut b) = (0, 0);
        while a < self.0.len() && b < o.0.len() {
            match self.0[a].cmp(&o.0[b]) {
                std::cmp::Ordering::Less => {
                    out.push(self.0[a]);
                    a += 1;
                }
                std::cmp::Ordering::Greater => {
                    out.push(o.0[b]);
                    b += 1;
                }
                std::cmp::Ordering::Equal => {
                    out.push(self.0[a]);
                    a += 1;
                    b += 1;
                }
            }
        }
        out.extend_from_slice(&self.0[a..]);
        out.extend_from_slice(&o.0[b..]);
        self.0 = out;
    }

    fn intersect(&mut self, o: &Bits) {
        self.0.retain(|l| o.0.binary_search(l).is_ok());
    }

    /// Whether every identity of `o` is in `self` — the scope test.
    fn contains(&self, o: &Bits) -> bool {
        o.0.iter().all(|l| self.0.binary_search(l).is_ok())
    }

    fn count(&self) -> u64 {
        self.0.len() as u64
    }
}

/// The instrument's own result, one line per `build_ctor` reduct.
fn fv_report(
    dag: &Dag,
    indeg: &[u32],
    root: u32,
    gamma_len: u32,
    max_lvl: u32,
    naive: u64,
    declines: u64,
    m: &str,
    i: &str,
) {
    let cap = max_lvl.max(gamma_len) + 1;
    let n = dag.len();

    // (1) The free variables, bottom-up: a node's are its own head variables
    // and its children's, less the fresh neutrals it opened itself.
    let mut fv: Vec<Bits> = vec![Bits::empty(cap); n];
    for &x in &dag.finish {
        let x = x as usize;
        let mut b = Bits::empty(cap);
        for l in &dag.own_vars[x] {
            b.set(*l);
        }
        for &k in &dag.kids[x] {
            b.union(&fv[k as usize]);
        }
        let (lvl, pending) = dag.bound[x];
        for l in lvl..lvl + pending {
            b.clear(l);
        }
        fv[x] = b;
    }

    // (2) What is in scope at a node *on every path to it*: the ambient Γ at
    // the root, intersected over parents as the graph is walked top-down
    // (`finish` reversed is a topological order — a node finishes after all
    // its children, so a parent precedes every child in the reverse).
    let mut scope: Vec<Bits> = vec![Bits::empty(cap); n];
    // …and what is in scope on *some* path, the union. It is not a naming
    // rule — a name has to be spellable at every occurrence — but it is the
    // instrument's own self-test: a free variable outside it is one no path
    // binds at all, which is a defect in this analysis and not a finding.
    let mut smax: Vec<Bits> = vec![Bits::empty(cap); n];
    let mut seen = vec![false; n];
    let mut done = vec![false; n];
    let mut back = 0u64;
    scope[root as usize] = Bits::upto(gamma_len, cap);
    smax[root as usize] = Bits::upto(gamma_len, cap);
    seen[root as usize] = true;
    for &x in dag.finish.iter().rev() {
        let x = x as usize;
        done[x] = true;
        let mut cand = scope[x].clone();
        let mut candx = smax[x].clone();
        let (lvl, pending) = dag.bound[x];
        for l in lvl..lvl + pending {
            cand.set(l);
            candx.set(l);
        }
        for &k in &dag.kids[x] {
            let k = k as usize;
            if done[k] {
                // A cycle sentinel, or an edge the finish order does not
                // dominate: counted rather than silently mis-scoped.
                back += 1;
                continue;
            }
            if seen[k] {
                scope[k].intersect(&cand);
                smax[k].union(&candx);
            } else {
                scope[k] = cand.clone();
                smax[k] = candx.clone();
                seen[k] = true;
            }
        }
    }

    // (3) The counting rule. A node is nameable when its free variables are
    // in scope at every occurrence and its mass carries no syntax whose
    // variables the walk could not resolve; a reference then costs
    // `1 + |fv|` — the `u^δ` and δ's entries — and the mint is emitted once,
    // at every depth.
    let sizes = fv.iter().map(|b| b.count()).collect::<Vec<_>>();
    let nameable = |x: usize| -> bool {
        x != root as usize && !dag.opaque[x] && scope[x].contains(&fv[x])
    };

    // Contamination, propagated. A node whose free variables are not all
    // bound on *any* path to it is a node this analysis has got wrong (the
    // value graph reaches it from outside the extent of a binder it
    // mentions), and every node below it inherits a scope that is missing
    // those identities. Only the **clean** nodes' scope verdicts are
    // evidence, so the verdict column is taken over those.
    // The diagnostic the verdict turns on: which occurrences fail, and by
    // how much. `mind[x]` is the **shortest** binder chain any path reaches
    // `x` under; a free variable at a level at or above it is a variable the
    // shallower occurrence has no binder for at all, which is §12.5's
    // "chains of different length" seen per value.
    let mut mind = vec![u32::MAX; n];
    mind[root as usize] = gamma_len;
    for &x in dag.finish.iter().rev() {
        let x = x as usize;
        if mind[x] == u32::MAX {
            continue;
        }
        let d = mind[x] + dag.bound[x].1;
        for &k in &dag.kids[x] {
            mind[k as usize] = mind[k as usize].min(d);
        }
    }
    let mut clean = vec![false; n];
    clean[root as usize] = true;
    for &x in dag.finish.iter().rev() {
        let x = x as usize;
        let ok = clean[x] && smax[x].contains(&fv[x]);
        for &k in &dag.kids[x] {
            let k = k as usize;
            if !seen[k] {
                continue;
            }
            clean[k] = if done[k] && clean[k] { ok } else { clean[k] || ok };
        }
    }

    // The instrument's own self-test: every free variable of a node is bound
    // on at least one path to it, or nothing below may be believed. A node
    // reached by one edge cannot fail this; a shared one whose *intersected*
    // scope is short still cannot, because the union is what is asked.
    let solo = (0..n)
        .filter(|&x| x != root as usize && !smax[x].contains(&fv[x]))
        .count();

    // The same rule restricted to **term** nodes: a Ψ binding names a term,
    // so a shared node of the value language's *type* sort is nameable only
    // through its code, which `docs/name-per-value-design.md` §5 keeps as a
    // separate device. This column is the ceiling the term-only mint can
    // actually reach, beside the one §2's table quotes.
    let nameable_tm = |x: usize| -> bool { nameable(x) && !dag.is_ty[x] };

    // How many times each node appears in the tree the graph expands to. The
    // in-degree is the measure every threshold column here has used, and it
    // is the right one when each parent is itself written once; it is *not*
    // when the parent cannot be named — a type node under the term-only rule
    // — because then the parent's own multiplicity is what the child pays.
    let mut mult = vec![0u64; n];
    mult[root as usize] = 1;
    for &x in dag.finish.iter().rev() {
        let x = x as usize;
        for &k in &dag.kids[x] {
            mult[k as usize] = mult[k as usize].saturating_add(mult[x]);
        }
    }

    // Step 0 item 2 of the implementation brief: `code_of` is partial, and
    // what has to be covered is not a threshold-clearing type node's own
    // former but its whole **type** subtree, because quoting recurses through
    // type children (and clones term ones). One bottom-up fold says it.
    let mut code_ok = vec![true; n];
    for &x in &dag.finish {
        let x = x as usize;
        if !dag.is_ty[x] {
            continue;
        }
        let mut ok = dag.code_shape[x];
        for &k in &dag.kids[x] {
            let k = k as usize;
            if dag.is_ty[k] && !code_ok[k] {
                ok = false;
            }
        }
        code_ok[x] = ok;
    }

    let mut line = String::new();
    for t in [0u64, 16, 64, 1_024] {
        let (names, emitted) = fv_names(dag, indeg, &sizes, root, t, &nameable, false, false, None);
        let (tnames, temitted) =
            fv_names(dag, indeg, &sizes, root, t, &nameable_tm, false, false, None);
        let (cnames, cemitted) = fv_names(dag, indeg, &sizes, root, t, &nameable, false, true, None);
        let (enames, eemitted) =
            fv_names(dag, indeg, &sizes, root, t, &nameable_tm, false, false, Some(&mult));
        line.push_str(&format!(
            " TM{t}={tnames}/{temitted} TC{t}={cnames}/{cemitted} TE{t}={enames}/{eemitted}"
        ));
        let (inames, iemitted) = fv_names(dag, indeg, &sizes, root, t, &|_| true, false, false, None);
        let (_, femitted) = fv_names(dag, indeg, &sizes, root, t, &nameable, true, false, None);
        line.push_str(&format!(
            " T{t}={names}/{emitted}|ideal={inames}/{iemitted}|flat3={femitted}"
        ));
    }

    // The per-value table of the pass: of the shared nodes that clear T=64,
    // how many have a chain missing one of their free variables (the reading
    // failing), how many are closed, and how wide the Δs are.
    let (mut sh, mut thr, mut bad, mut closed, mut opq, mut basev) = (0, 0, 0, 0, 0, 0);
    let (mut unb, mut badc, mut short) = (0, 0, 0);
    // Of the threshold-clearing values, how many are of the **type** sort —
    // the ones only a minted code could name (§5 of the name-per-value doc).
    let mut tynode = 0;
    // Of those, the ones `code_of` cannot quote at all, and the saving they
    // carry — the mass the type spelling would have to decline.
    let (mut tyno, mut tyno_saves, mut ty_saves) = (0u64, 0u64, 0u64);
    let mut shapes: std::collections::BTreeMap<&'static str, u64> =
        std::collections::BTreeMap::new();
    let (mut fvsum, mut fvmax) = (0u64, 0u64);
    let mut cost = vec![0u64; n];
    for &x in &dag.finish {
        let x = x as usize;
        let mut c = dag.own[x];
        for &k in &dag.kids[x] {
            c = c.saturating_add(cost[k as usize]);
        }
        cost[x] = c;
        if indeg[x] <= 1 || x == root as usize {
            continue;
        }
        sh += 1;
        let saves = u64::from(indeg[x] - 1).saturating_mul(c.saturating_sub(1 + sizes[x]));
        if saves < 64 {
            continue;
        }
        thr += 1;
        if dag.is_ty[x] {
            tynode += 1;
            ty_saves += saves;
            if !code_ok[x] {
                tyno += 1;
                tyno_saves += saves;
            }
            *shapes.entry(dag.ty_shape[x]).or_insert(0u64) += 1;
        }
        fvsum += sizes[x];
        fvmax = fvmax.max(sizes[x]);
        if sizes[x] == 0 {
            closed += 1;
        }
        if dag.opaque[x] {
            opq += 1;
        }
        if dag.basevar[x] {
            basev += 1;
        }
        if !scope[x].contains(&fv[x]) {
            bad += 1;
        }
        if !smax[x].contains(&fv[x]) {
            unb += 1;
        }
        if clean[x] && !scope[x].contains(&fv[x]) {
            badc += 1;
        }
        // The length test, in depth numbering the only one the walk's own
        // levels support exactly: is the shortest chain to this value long
        // enough to have a binder at every position its body reads? This is
        // §12.5's "chains of different length" asked per value, and it is
        // free of the contamination above.
        if fv[x].0.last().is_some_and(|l| *l >= mind[x]) {
            short += 1;
        }
    }

    if let Ok(top) = std::env::var("HEATHER_RB_FVDUMP") {
        let top: usize = top.parse().unwrap_or(8);
        let mut rows: Vec<usize> = (0..n)
            .filter(|&x| {
                indeg[x] > 1 && x != root as usize && !scope[x].contains(&fv[x])
            })
            .collect();
        rows.sort_by_key(|&x| std::cmp::Reverse(cost[x]));
        // The **sources** of contamination: an unbound node none of whose
        // children is itself unbound, i.e. where a free variable first
        // appears with no binder above it. Everything else inherits.
        let unb_set: Vec<bool> =
            (0..n).map(|x| !smax[x].contains(&fv[x])).collect();
        let mut src: Vec<usize> = (0..n)
            .filter(|&x| {
                x != root as usize
                    && unb_set[x]
                    && !dag.kids[x].iter().any(|&k| unb_set[k as usize])
            })
            .collect();
        src.sort_by_key(|&x| std::cmp::Reverse(cost[x]));
        for x in src.into_iter().take(top) {
            let miss: Vec<u32> =
                fv[x].0.iter().copied().filter(|l| !smax[x].get(*l)).collect();
            let pars: Vec<(usize, (u32, u32))> = (0..n)
                .filter(|&a| dag.kids[a].contains(&(x as u32)))
                .map(|a| (a, dag.bound[a]))
                .collect();
            eprintln!(
                "rb fvsrc item={m}::{i} node={x} size={} indeg={} open={} \
                 own={:?} bound={:?} miss={miss:?} parents={pars:?}",
                cost[x],
                indeg[x],
                dag.open_lvl[x],
                dag.own_vars[x],
                dag.bound[x],
            );
            // Walk down to where the missing identity is actually written,
            // printing the chain: the arm that puts a variable into a value
            // reached from outside its binder is the finding, not the count.
            if let Some(l) = miss.first() {
                let mut cur = x;
                let mut hops = 0;
                while hops < 24 && !dag.own_vars[cur].contains(l) {
                    let nxt = dag.kids[cur]
                        .iter()
                        .map(|&k| k as usize)
                        .find(|&k| fv[k].get(*l));
                    match nxt {
                        Some(k) => {
                            eprintln!(
                                "rb fvpath item={m}::{i} {cur} -> {k} open={} \
                                 bound={:?} indeg={} kids={} own={:?}",
                                dag.open_lvl[k],
                                dag.bound[k],
                                indeg[k],
                                dag.kids[k].len(),
                                dag.own_vars[k],
                            );
                            cur = k;
                        }
                        None => break,
                    }
                    hops += 1;
                }
            }
        }
        let mut un: Vec<usize> = (0..n)
            .filter(|&x| x != root as usize && !smax[x].contains(&fv[x]))
            .collect();
        un.sort_by_key(|&x| std::cmp::Reverse(cost[x]));
        for x in un.into_iter().take(top) {
            let miss: Vec<u32> =
                fv[x].0.iter().copied().filter(|l| !smax[x].get(*l)).collect();
            for l in &miss {
                let owner = (0..n).find(|&b| {
                    dag.bound[b].1 > 0
                        && dag.bound[b].0 <= *l
                        && *l < dag.bound[b].0 + dag.bound[b].1
                });
                let holder = (0..n).find(|&b| dag.own_vars[b].contains(l));
                let par = |t: usize| -> Vec<usize> {
                    (0..n).filter(|&a| dag.kids[a].contains(&(t as u32))).collect()
                };
                eprintln!(
                    "rb fvown item={m}::{i} id={l} binder={owner:?} holder={holder:?} \
                     binder_fv_has={:?} holder_parents={:?} binder_parents={:?} \
                     binder_bound={:?} binder_finishpos={:?} holder_finishpos={:?}",
                    owner.map(|b| fv[b].get(*l)),
                    holder.map(par),
                    owner.map(par),
                    owner.map(|b| dag.bound[b]),
                    owner.and_then(|b| dag.finish.iter().position(|&z| z as usize == b)),
                    holder.and_then(|b| dag.finish.iter().position(|&z| z as usize == b)),
                );
            }
            eprintln!(
                "rb fvunb item={m}::{i} node={x} size={} indeg={} open={} kids={} \
                 miss={miss:?} own={:?} bound={:?}",
                cost[x],
                indeg[x],
                dag.open_lvl[x],
                dag.kids[x].len(),
                dag.own_vars[x],
                dag.bound[x],
            );
        }
        for x in rows.into_iter().take(top) {
            let lv: &[u32] = &fv[x].0;
            eprintln!(
                "rb fvbad item={m}::{i} node={x} size={} indeg={} open={} mind={} \
                 fv={lv:?} scope={} bound={:?}",
                cost[x],
                indeg[x],
                dag.open_lvl[x],
                mind[x],
                scope[x].count(),
                dag.bound[x],
            );
        }
    }
    eprintln!(
        "rb fv item={m}::{i} naive={naive} graph={n} shared={sh} thr={thr} bad={bad} \
         tynode={tynode} tycode_no={tyno} tycode_lost={tyno_saves}/{ty_saves} tyshapes={shapes:?} closed={closed} opaque={opq} basevar={basev} decl={declines} unb={unb} badc={badc} short={short} solo={solo} fvsum={fvsum} fvmax={fvmax} \
         gamma={gamma_len} maxlvl={max_lvl} back={back}{line}"
    );
}

/// The emitted count under "one mint per value, Δ = its free variables": the
/// root's term plus every minted body, a reference charged `1 + |fv|` (or
/// [`REF_COST`] flat, for the column that is comparable to §11.2's).
fn fv_names(
    dag: &Dag,
    indeg: &[u32],
    sizes: &[u64],
    root: u32,
    threshold: u64,
    nameable: &dyn Fn(usize) -> bool,
    flat: bool,
    code: bool,
    // `mult`: how many times the node appears in the **tree** the graph
    // expands to, when the saving is to be measured that way rather than by
    // the node's in-degree. The two differ exactly where an unnameable parent
    // is itself written many times: an `El` of the type sort cannot be a Ψ
    // binding, so its multiplicity has to reach the *term* under it, or the
    // term-only device loses the sharing for want of a name one node up.
    mult: Option<&[u64]>,
) -> (u64, u64) {
    let n = dag.len();
    // A **type** node is named through its code — mint `c : Ty l`, spell the
    // occurrence `El (c^δ)` — so its reference carries the `El` as well
    // (`docs/name-per-value-design.md` §5, §12.1 item 1). The bare rule
    // charges every occurrence `1 + |fv|`, which is the term half's price.
    let refc = |x: usize| {
        if flat {
            REF_COST
        } else {
            1 + sizes[x] + u64::from(code && dag.is_ty[x])
        }
    };
    let mut cost = vec![0u64; n];
    let mut named = vec![false; n];
    let mut mints = 0u64;
    let mut bodies = 0u64;
    for &x in &dag.finish {
        let x = x as usize;
        let mut c = dag.own[x];
        for &k in &dag.kids[x] {
            let k = k as usize;
            c = c.saturating_add(if named[k] { refc(k) } else { cost[k] });
        }
        cost[x] = c;
        let shares = match mult {
            Some(m) => m[x].saturating_sub(1),
            None => u64::from(indeg[x]).saturating_sub(1),
        };
        if shares > 0
            && shares.saturating_mul(c.saturating_sub(refc(x))) >= threshold
            && x != root as usize
            && nameable(x)
        {
            named[x] = true;
            mints += 1;
            bodies = bodies.saturating_add(c);
        }
    }
    (mints, bodies.saturating_add(cost[root as usize]))
}
