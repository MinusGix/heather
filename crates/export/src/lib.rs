//! Export of checked kernel declarations to Lean 4 and Rocq (Coq), through
//! one target-neutral intermediate language (`docs/export-fragment-design.md`).
//!
//! Prototype scope, stated by what it refuses: the translation is
//! syntax-directed over kernel terms, total on the *layer-free* fragment
//! (no `box`, `letbox`, code recursors, context or type meta-functions, no
//! global type variables, no universe polymorphism, empty local contexts on
//! globals) and refuses everything else with a named [`Refusal`]. A
//! declaration that mentions a refused one is refused too, so what is printed
//! is closed.
//!
//! The intermediate language [`Hx`] is a pure type system with constants:
//! every kernel former becomes an application of a **prelude constant**
//! (`Hx.pair`, `Hx.J`, `Hx.elimNat`, …) to all of its annotations. The two
//! printers are then dumb, and the only per-target trusted text is the hand
//! written prelude (`prelude/Hx.lean`, `prelude/Hx.v`). Checked spellings
//! (`pair@`, `fst@`, …) carry no components. The kernel's `⌊·⌋` writes the
//! introductions' components back before translation; `fst@`/`snd@` become
//! the targets' own projections ([`Hx::Proj`]), which need none, and `app@`
//! a plain application. An introduction `⌊·⌋` cannot spell becomes
//! [`Hx::Hole`]s that the target's elaborator fills from the expected or
//! inferred type. That is the one place the prototype leans on an
//! elaborator, and the design doc says how a typed exporter removes it.

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{Defs, whnf_term_delta, whnf_type_delta};
use heather_kernel::subst::{local_bound, local_bound_ty};
use heather_kernel::term::{CtxBase, GlobalBinding, GlobalCtx, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type};
use heather_kernel::typing::{DEFAULT_FUEL, spell_checked_for_export, spell_checked_for_export_ty};
use std::cell::RefCell;
use std::sync::Arc as Rc;
use std::fmt::Write as _;

mod share;
mod wf;

/// A universe level of the exported fragment: closed, because the library is
/// universe-monomorphic (`UPi` is layer m, which declarations never use).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Lvl(pub u64);

/// The intermediate language: de Bruijn terms over prelude constants.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Hx {
    Var(u32),
    /// `Type l` (Russell): the image of both `Ty l` and the code `TmTy l`.
    Sort(Lvl),
    Pi(Rc<Hx>, Rc<Hx>),
    Lam(Rc<Hx>, Rc<Hx>),
    App(Rc<Hx>, Rc<Hx>),
    /// Field `0` or `1` of a `Sig` pair, written without the pair's type:
    /// the target reads it off the pair (Lean's `Expr.proj`, Rocq's
    /// primitive projection). What `fst@`/`snd@` translate to, so that
    /// `⌊·⌋` never spells a projection (design §5.6).
    Proj(u8, Rc<Hx>),
    /// A prelude constant at explicit levels.
    Const(&'static str, Vec<Lvl>),
    /// An exported declaration, by absolute Ψ index.
    Global(usize),
    /// A constant only the target has, by Heather-style key, at raw target
    /// levels: a `Wf` realisation's constructors, recursor and helpers
    /// (`wf.rs`).
    Named(String, Vec<u64>),
    NatLit(String),
    /// A component the kernel term does not spell (a checked spelling's
    /// erased annotation); the target elaborator recovers it.
    Hole,
}

/// `Wf` has a realisation per target still to build: native inductives in
/// Lean, the positivity bypass in Rocq (design §5.1).
const WF: &str = "Wf (no target realisation yet: issues/export-wf-native-inductives.md)";

/// Why a term or declaration is outside the fragment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Refusal(pub String);

type R<T> = Result<T, Refusal>;

fn refuse<T>(what: &str) -> R<T> {
    Err(Refusal(what.to_string()))
}

fn lvl(l: &Level) -> R<Lvl> {
    Ok(Lvl(match l {
        Level::Zero => 0,
        Level::Succ(l) => lvl(l)?.0 + 1,
        Level::Max(a, b) => lvl(a)?.0.max(lvl(b)?.0),
        Level::Var(_) => return refuse("universe variable (level polymorphism)"),
        Level::Omega => return refuse("level ω"),
    }))
}

fn app(f: Hx, args: Vec<Hx>) -> Hx {
    args.into_iter().fold(f, |f, a| Hx::App(Rc::new(f), Rc::new(a)))
}

fn konst(name: &'static str, levels: &[&Level], args: Vec<Hx>) -> R<Hx> {
    let levels = levels.iter().map(|l| lvl(l)).collect::<R<Vec<_>>>()?;
    Ok(app(Hx::Const(name, levels), args))
}

/// `t` under one binder fewer: indices above `cut` drop by one. `None` when
/// `t` names the binder at `cut`.
fn strengthen(t: &Hx, cut: u32) -> Option<Hx> {
    fn go(t: &Hx, cut: u32, memo: &mut Nodes<Option<Rc<Hx>>>) -> Option<Rc<Hx>> {
        let key = (t as *const Hx as usize, cut);
        if let Some(out) = memo.get(&key) {
            return out.clone();
        }
        let out = (|| {
            Some(Rc::new(match t {
                Hx::Var(i) if *i == cut => return None,
                Hx::Var(i) if *i > cut => Hx::Var(i - 1),
                Hx::Pi(a, b) => Hx::Pi(go(a, cut, memo)?, go(b, cut + 1, memo)?),
                Hx::Lam(a, b) => Hx::Lam(go(a, cut, memo)?, go(b, cut + 1, memo)?),
                Hx::App(f, a) => Hx::App(go(f, cut, memo)?, go(a, cut, memo)?),
                Hx::Proj(i, p) => Hx::Proj(*i, go(p, cut, memo)?),
                _ => t.clone(),
            }))
        })();
        memo.insert(key, out.clone());
        out
    }
    go(t, cut, &mut Nodes::new()).map(|t| (*t).clone())
}

/// A rewrite's results by node address and the binder depth it is met at,
/// so that a rewrite of a shared node runs once (`Hx` is a DAG: the
/// translation shares what the kernel term shares). Addresses are those of
/// nodes alive for the whole rewrite.
type Nodes<T> = std::collections::HashMap<(usize, u32), T>;

/// Every node of `roots`, a shared node once.
fn each_node<'t>(roots: impl IntoIterator<Item = &'t Hx>, f: &mut dyn FnMut(&'t Hx)) {
    let mut seen = std::collections::HashSet::new();
    let mut todo: Vec<&Hx> = roots.into_iter().collect();
    while let Some(t) = todo.pop() {
        if !seen.insert(t as *const Hx) {
            continue;
        }
        f(t);
        match t {
            Hx::Pi(a, b) | Hx::Lam(a, b) | Hx::App(a, b) => {
                todo.push(b);
                todo.push(a);
            }
            Hx::Proj(_, p) => todo.push(p),
            _ => {}
        }
    }
}

/// The realised inductives' recursors (`list::List::rec`), each with its
/// parameter count and its constructors' fields.
type Recs = std::collections::HashMap<String, (usize, Vec<(u32, u32)>)>;

/// `t` with each realised recursor's minor premises in Rocq's order. Lean's
/// recursor takes a constructor's fields, then its children's hypotheses;
/// Rocq's `D_rect` puts each child's hypothesis right after the child. The
/// minor premises are `λ`-chains `wf.rs` wrote, so their binders reorder.
fn rocq_minors(t: &Hx, recs: &Recs, memo: &mut Nodes<Rc<Hx>>) -> Rc<Hx> {
    let key = (t as *const Hx as usize, 0);
    if let Some(out) = memo.get(&key) {
        return out.clone();
    }
    let out = Rc::new(rocq_minors_node(t, recs, memo));
    memo.insert(key, out.clone());
    out
}

fn rocq_minors_node(t: &Hx, recs: &Recs, memo: &mut Nodes<Rc<Hx>>) -> Hx {
    match t {
        Hx::App(..) => {
            let mut spine = Vec::new();
            let mut head = t;
            while let Hx::App(f, a) = head {
                spine.push((*rocq_minors(a, recs, memo)).clone());
                head = f;
            }
            spine.reverse();
            if let Hx::Named(key, _) = head
                && let Some((np, fields)) = recs.get(key)
            {
                for (k, &(q, n)) in fields.iter().enumerate() {
                    let Some(m) = spine.get_mut(np + 1 + k) else { break };
                    let mut order: Vec<usize> = (0..q as usize).collect();
                    for i in 0..n as usize {
                        order.extend([q as usize + i, (q + n) as usize + i]);
                    }
                    *m = permute_lams(m, &order).expect("a minor premise is a λ-chain over its fields and hypotheses");
                }
            }
            let head = match head {
                Hx::Named(..) | Hx::Const(..) | Hx::Global(_) => head.clone(),
                _ => (*rocq_minors(head, recs, memo)).clone(),
            };
            app(head, spine)
        }
        Hx::Pi(a, b) => Hx::Pi(rocq_minors(a, recs, memo), rocq_minors(b, recs, memo)),
        Hx::Lam(a, b) => Hx::Lam(rocq_minors(a, recs, memo), rocq_minors(b, recs, memo)),
        Hx::Proj(i, p) => Hx::Proj(*i, rocq_minors(p, recs, memo)),
        _ => t.clone(),
    }
}

/// `t`'s first `order.len()` binders, a `λ`-chain, in the order `order`
/// gives (new position ↦ old position), every index renumbered to follow.
/// `None` when `t` has fewer binders. The order must keep each binder after
/// those its domain mentions.
fn permute_lams(t: &Hx, order: &[usize]) -> Option<Hx> {
    let len = order.len();
    let (mut doms, mut body) = (Vec::new(), t);
    for _ in 0..len {
        let Hx::Lam(a, b) = body else { return None };
        doms.push(&**a);
        body = b;
    }
    let mut new_of = vec![0; len];
    for (new, &old) in order.iter().enumerate() {
        new_of[old] = new;
    }
    // A variable under `cut` inner binders in a context of the chain's old
    // binders 0..have, written for its new binders 0..now.
    fn go(t: &Hx, have: usize, now: usize, new_of: &[usize], cut: u32, memo: &mut Nodes<Rc<Hx>>) -> Rc<Hx> {
        let key = (t as *const Hx as usize, cut);
        if let Some(out) = memo.get(&key) {
            return out.clone();
        }
        let out = Rc::new(match t {
            Hx::Var(i) if *i >= cut => {
                let k = (i - cut) as usize;
                if k < have {
                    let level = new_of[have - 1 - k];
                    Hx::Var(cut + (now - 1 - level) as u32)
                } else {
                    Hx::Var(cut + (now + k - have) as u32)
                }
            }
            Hx::Pi(a, b) => Hx::Pi(go(a, have, now, new_of, cut, memo), go(b, have, now, new_of, cut + 1, memo)),
            Hx::Lam(a, b) => Hx::Lam(go(a, have, now, new_of, cut, memo), go(b, have, now, new_of, cut + 1, memo)),
            Hx::App(f, a) => Hx::App(go(f, have, now, new_of, cut, memo), go(a, have, now, new_of, cut, memo)),
            Hx::Proj(i, p) => Hx::Proj(*i, go(p, have, now, new_of, cut, memo)),
            _ => t.clone(),
        });
        memo.insert(key, out.clone());
        out
    }
    let mut out = go(body, len, len, &new_of, 0, &mut Nodes::new());
    for new in (0..len).rev() {
        let old = order[new];
        // Its domain is under the old binders before it, all of which come
        // before it in the new order too.
        let dom = go(doms[old], old, new, &new_of, 0, &mut Nodes::new());
        out = Rc::new(Hx::Lam(dom, out));
    }
    Some((*out).clone())
}

/// The levels Lean's prelude takes for constant `name`: Rocq's `etaSig` has
/// a third, the pair's own (it cannot write `max`), which Lean's computes.
fn lean_levels<'a>(name: &str, levels: &'a [Lvl]) -> &'a [Lvl] {
    if name == "etaSig" { &levels[..2] } else { levels }
}

fn lam(dom: Hx, body: Hx) -> Hx {
    Hx::Lam(Rc::new(dom), Rc::new(body))
}

/// The translation of one declaration's types and terms. `at` is the
/// declaration's absolute Ψ index, which resolves its global variables.
struct Tr<'a> {
    at: usize,
    /// The declaration's own Ψ prefix: what its globals unfold to.
    psi: &'a GlobalCtx,
    /// One entry per enclosing binder, innermost last: the canonical element
    /// of its domain when that domain is a closed singleton, translated and
    /// as a kernel term. Closed, so it needs no shifting to be used under
    /// further binders.
    ctx: RefCell<Vec<Option<(Hx, Rc<Term>)>>>,
    /// The tier-1 declarations met so far (`wf.rs`).
    wf: &'a wf::WfTable,
    /// The translation's sharing, which keeps it linear in the kernel
    /// term's DAG rather than in the tree it unfolds to (design §5.6).
    memo: RefCell<Memo>,
}

/// What [`Tr`]'s translation of a node depends on beyond the node: the
/// canonical elements `ctx` holds for the variables it names. Each context
/// gets an id, interned so that two binders with no canonical element under
/// the same context share one; a closed node is translated in context 0.
/// Nodes are keyed by address and carry a copy to check against, since a
/// node built during the translation can be freed and its address reused
/// (the copy's children are shared, so the check is shallow when it hits).
#[derive(Default)]
struct Memo {
    ids: Vec<u32>,
    /// Contexts by (enclosing context, the address of the domain whose
    /// canonical element the binder holds, or 0 for none), with that domain
    /// to check the address against.
    interned: std::collections::HashMap<(u32, usize), (Option<Type>, u32)>,
    next: u32,
    tms: std::collections::HashMap<(usize, u32), (Term, Hx)>,
    tys: std::collections::HashMap<(usize, u32), (Type, Hx)>,
}

impl Memo {
    fn push(&mut self, canonical: Option<&Type>) {
        let parent = self.ids.last().copied().unwrap_or(0);
        let key = (parent, canonical.map_or(0, |d| d as *const Type as usize));
        let id = match self.interned.get(&key) {
            Some((seen, id)) if seen.as_ref() == canonical => *id,
            _ => {
                self.next += 1;
                self.interned.insert(key, (canonical.cloned(), self.next));
                self.next
            }
        };
        self.ids.push(id);
    }

    fn pop(&mut self) {
        self.ids.pop();
    }

    fn at(&self, closed: bool) -> u32 {
        if closed { 0 } else { self.ids.last().copied().unwrap_or(0) }
    }
}

/// Fuel for the exporter's own reductions (the collapse test); a type that
/// does not settle within it is simply not collapsed.
const FUEL: u64 = 1 << 16;

fn lmax(a: &Level, b: &Level) -> Level {
    Level::max(a.clone(), b.clone())
}

impl Tr<'_> {
    /// The level of `t` when `t` is a **closed singleton**: a closed type
    /// whose whnf is `Unit`, an `sEq` between convertible endpoints, or a
    /// non-dependent `Σ` of singletons. Heather's η makes every two terms of
    /// such a type convertible, neutrals included; the targets' structure η
    /// does not reach two neutrals (design §5.2). So a term whose type is
    /// known to be a closed singleton translates to that type's canonical
    /// element ([`Self::canon`]), and a neutral the exporter cannot see the
    /// type of meets it through structure η, which fires against a
    /// constructor. The type itself is translated as written: collapsing it
    /// to `Unit` would disagree with the δ-unfolding of an open definition
    /// that reaches the same type only by substitution.
    fn singleton(&self, t: &Type) -> Option<Level> {
        if !matches!(t, Type::Unit { .. } | Type::SEq { .. } | Type::Sigma { .. } | Type::El { .. } | Type::Vec { .. }) {
            return None;
        }
        if local_bound_ty(&Rc::new(t.clone())) != 0 {
            return None;
        }
        let nil = LocalCtx::nil();
        let w = whnf_type_delta(t, &nil, Defs::transparent(self.psi), FUEL).ok()?;
        match &w {
            Type::Unit { level } => Some(level.clone()),
            Type::SEq { level, lhs, rhs, .. } => {
                let l = whnf_term_delta(lhs, &nil, Defs::transparent(self.psi), FUEL).ok()?;
                let r = whnf_term_delta(rhs, &nil, Defs::transparent(self.psi), FUEL).ok()?;
                (l == r).then(|| level.clone())
            }
            Type::Sigma { fst_level, snd_level, fst, snd } if local_bound_ty(snd) == 0 => {
                self.singleton(fst)?;
                self.singleton(snd)?;
                Some(lmax(fst_level, snd_level))
            }
            _ => None,
        }
    }

    /// The canonical element of a closed singleton ([`Self::singleton`]):
    /// `tt`, `srefl`, or a pair of canonical elements.
    pub(crate) fn canon(&self, t: &Type) -> Option<R<Hx>> {
        self.singleton(t)?;
        let nil = LocalCtx::nil();
        let w = whnf_type_delta(t, &nil, Defs::transparent(self.psi), FUEL).ok()?;
        Some(match &w {
            Type::Unit { level } => konst("tt", &[level], vec![]),
            Type::SEq { level, ty, lhs, .. } => (|| konst("srefl", &[level], vec![self.ty(ty)?, self.tm(lhs)?]))(),
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                let (a, b) = (self.canon(fst)?, self.canon(snd)?);
                (|| konst(
                    "pair",
                    &[fst_level, snd_level],
                    vec![self.ty(fst)?, self.lam_ty(fst, snd)?, a?, b?],
                ))()
            }
            _ => return None,
        })
    }

    /// [`Self::canon`] as a kernel term, for the terms `wf.rs` builds.
    pub(crate) fn canon_term(&self, t: &Type) -> Option<Term> {
        self.singleton(t)?;
        let nil = LocalCtx::nil();
        let w = whnf_type_delta(t, &nil, Defs::transparent(self.psi), FUEL).ok()?;
        Some(match w {
            Type::Unit { level } => Term::Triv { level },
            Type::SEq { level, ty, lhs, .. } => Term::SRefl { level, ty, tm: lhs },
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                let (a, b) = (self.canon_term(&fst)?, self.canon_term(&snd)?);
                Term::Pair { fst_level, snd_level, fst_ty: fst, snd_ty: snd, fst: Rc::new(a), snd: Rc::new(b) }
            }
            _ => return None,
        })
    }

    /// A proof that the canonical element of the closed singleton `t` is
    /// every element, `Π(x : t). canon = x` (`etaUnit`, `etaSEq`, `etaSig`):
    /// what a singleton-aware `case` transports its branch along (§5.3).
    pub(crate) fn eta(&self, t: &Type) -> Option<R<Hx>> {
        let level = self.singleton(t)?;
        let nil = LocalCtx::nil();
        let w = whnf_type_delta(t, &nil, Defs::transparent(self.psi), FUEL).ok()?;
        Some(match &w {
            Type::Unit { level } => konst("etaUnit", &[level], vec![]),
            Type::SEq { level, ty, lhs, .. } => (|| konst("etaSEq", &[level], vec![self.ty(ty)?, self.tm(lhs)?]))(),
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                let (a, b, ea, eb) = (self.canon(fst)?, self.canon(snd)?, self.eta(fst)?, self.eta(snd)?);
                (|| konst("etaSig", &[fst_level, snd_level, &level], vec![self.ty(fst)?, self.ty(snd)?, a?, b?, ea?, eb?]))()
            }
            _ => return None,
        })
    }

    /// A `case` branch over a closed singleton, stated at its canonical
    /// element: the branch's body, which never names the bound payload
    /// (`under` prints it as the canonical element), out from under its
    /// binder. `None` when the body names it after all.
    fn singleton_branch(&self, dom: &Type, branch: &Term) -> Option<R<Hx>> {
        if let Err(e) = self.canon(&self.close(dom)?)? {
            return Some(Err(e));
        }
        let body = match self.bound(dom, || self.tm(branch)) {
            Ok(Hx::Lam(_, body)) => body,
            Ok(_) => unreachable!("bound makes a binder"),
            Err(e) => return Some(Err(e)),
        };
        strengthen(&body, 0).map(Ok)
    }

    /// `t` with the enclosing binders that have canonical elements
    /// replaced by them, when that closes it: a domain such as
    /// `IsTrue(inr x)` under a branch whose payload `x` is a singleton is a
    /// closed singleton only once `x` is its canonical element. Heather's η
    /// sees that; Rocq does not, so the exporter must (design §5.3).
    fn close(&self, t: &Type) -> Option<Type> {
        if local_bound_ty(&Rc::new(t.clone())) == 0 {
            return Some(t.clone());
        }
        let ctx = self.ctx.borrow();
        if ctx.iter().all(Option::is_none) {
            return None;
        }
        let mut t = t.clone();
        for entry in ctx.iter().rev() {
            t = match entry {
                Some((_, c)) => t.inst_top(0, c),
                // A binder with no canonical element must not occur.
                None => {
                    let a = t.inst_top(0, &Term::Zero);
                    (a == t.inst_top(0, &Term::Succ(Rc::new(Term::Zero)))).then_some(a)?
                }
            };
            if local_bound_ty(&Rc::new(t.clone())) == 0 {
                return Some(t);
            }
        }
        None
    }

    /// Translate under one binder whose domain is `dom` (`None` when the
    /// exporter does not have it at hand).
    fn under<T>(&self, dom: Option<&Type>, f: impl FnOnce() -> R<T>) -> R<T> {
        let written = dom;
        let dom = dom.and_then(|d| self.close(d));
        let entry = match dom.as_ref().and_then(|d| Some((self.canon(d)?, self.canon_term(d)?))) {
            Some((c, k)) => Some((c?, Rc::new(k))),
            None => None,
        };
        self.memo.borrow_mut().push(entry.as_ref().and(written));
        self.ctx.borrow_mut().push(entry);
        let out = f();
        self.ctx.borrow_mut().pop();
        self.memo.borrow_mut().pop();
        out
    }

    /// `fun (x : dom) => cod` for a type family.
    fn lam_ty(&self, dom: &Type, cod: &Type) -> R<Hx> {
        Ok(lam(self.ty(dom)?, self.under(Some(dom), || self.ty(cod))?))
    }

    /// `fun (x : dom) => f()`, with `f` translated under the binder.
    fn bound(&self, dom: &Type, f: impl FnOnce() -> R<Hx>) -> R<Hx> {
        Ok(lam(self.ty(dom)?, self.under(Some(dom), f)?))
    }

    /// `n` binders the prelude constant's type determines, none of them at
    /// a domain the exporter has at hand.
    fn binds<T>(&self, n: usize, f: impl FnOnce() -> R<T>) -> R<T> {
        match n {
            0 => f(),
            _ => self.under(None, || self.binds(n - 1, f)),
        }
    }

    fn global(&self, var: u32, subst: &LocalSubst) -> R<Hx> {
        match subst.tail {
            // `·^k, t̄`: a global over the context t̄ substitutes (none for a
            // closed one), used under k binders: exported closed over its
            // context, so it applies to t̄, outermost first.
            SubstTail::Empty { base: CtxBase::Nil, .. } => {}
            _ => return refuse("global with a weakening substitution"),
        }
        match self.at.checked_sub(1 + var as usize) {
            Some(abs) => Ok(app(Hx::Global(abs), subst.terms.iter().map(|t| self.tm(t)).collect::<R<_>>()?)),
            None => refuse("global variable out of scope"),
        }
    }

    /// `f()`'s statement and body under the binders of a global's local
    /// context, closed over them: `Π Δ. T` and `λ Δ. t`.
    fn over(&self, ctx: &[Rc<Type>], f: &dyn Fn() -> R<(Hx, Option<Hx>)>) -> R<(Hx, Option<Hx>)> {
        let Some((first, rest)) = ctx.split_first() else { return f() };
        let dom = self.ty(first)?;
        let (ty, body) = self.under(Some(first), || self.over(rest, f))?;
        Ok((Hx::Pi(Rc::new(dom.clone()), Rc::new(ty)), body.map(|b| lam(dom, b))))
    }

    fn ty(&self, t: &Type) -> R<Hx> {
        let key = (t as *const Type as usize, self.memo.borrow().at(local_bound_ty(&Rc::new(t.clone())) == 0));
        if let Some((seen, out)) = self.memo.borrow().tys.get(&key) {
            if seen == t {
                return Ok(out.clone());
            }
        }
        let out = self.ty_node(t)?;
        self.memo.borrow_mut().tys.insert(key, (t.clone(), out.clone()));
        Ok(out)
    }

    fn ty_node(&self, t: &Type) -> R<Hx> {
        Ok(match t {
            Type::Nat => Hx::Const("Nat", vec![]),
            Type::Pi { dom, cod, .. } => Hx::Pi(Rc::new(self.ty(dom)?), Rc::new(self.under(Some(dom), || self.ty(cod))?)),
            Type::Ty(l) => Hx::Sort(lvl(l)?),
            Type::El { tm, .. } => self.tm(tm)?,
            Type::Id { level, ty, lhs, rhs } => konst("Id", &[level], vec![self.ty(ty)?, self.tm_at_ty(lhs, ty)?, self.tm_at_ty(rhs, ty)?])?,
            Type::SEq { level, ty, lhs, rhs } => konst("SEq", &[level], vec![self.ty(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Type::SEmpty { level } => konst("SEmpty", &[level], vec![])?,
            Type::Squash { level, ty } => konst("Squash", &[level], vec![self.ty(ty)?])?,
            Type::Sigma { fst_level, snd_level, fst, snd } => {
                konst("Sig", &[fst_level, snd_level], vec![self.ty(fst)?, self.lam_ty(fst, snd)?])?
            }
            Type::Unit { level } => konst("Unit", &[level], vec![])?,
            Type::Empty { level } => konst("Empty", &[level], vec![])?,
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => {
                konst("Sum", &[lhs_level, rhs_level], vec![self.ty(lhs)?, self.ty(rhs)?])?
            }
            Type::W { shape_level, pos_level, shape, pos } => {
                konst("W", &[shape_level, pos_level], vec![self.ty(shape)?, self.lam_ty(shape, pos)?])?
            }
            Type::Vec { level, elem, len } => konst("Vec", &[level], vec![self.ty(elem)?, self.tm(len)?])?,
            Type::Fin { len } => konst("Fin", &[], vec![self.tm(len)?])?,
            Type::Wf { level, shape, .. } => self.wf_type(level, shape)?,
            Type::DVec { .. } | Type::IWf { .. } => return refuse("DVec/IWf (not exported yet)"),
            Type::M { .. } => return refuse("M (not exported yet)"),
            Type::UPi { .. } => return refuse("ΠΠ (universe polymorphism)"),
            Type::GlobalTy { .. } => return refuse("global type variable (layer c/p meta binding)"),
            Type::CtxPi { .. } | Type::TyPi { .. } => return refuse("context/type meta-function"),
            Type::CodeTy { .. } | Type::CodeTm { .. } => return refuse("contextual (boxed) type"),
        })
    }

    /// The type of a term the exporter can read off without inference, when
    /// that type is closed: a variable's domain is in `ctx` already, so this
    /// covers globals, applications and projections.
    fn known_ty(&self, t: &Term) -> Option<Type> {
        match t {
            Term::GlobalTm { var, subst } if subst.terms.is_empty() => {
                let abs = self.at.checked_sub(1 + var.0 as usize)?;
                match self.psi.bindings.get(abs)? {
                    // A statement is scoped over its own binding's prefix of Ψ.
                    GlobalBinding::Tm { ctx, ty, .. } if ctx.is_empty() => Some(ty.shift_global(var.0 + 1)),
                    _ => None,
                }
            }
            Term::App { cod, .. } if local_bound_ty(cod) == 0 => Some((**cod).clone()),
            Term::Fst { fst_ty, .. } => Some((**fst_ty).clone()),
            Term::Snd { snd_ty, .. } if local_bound_ty(snd_ty) == 0 => Some((**snd_ty).clone()),
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, .. } => Some(Type::Sigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: fst_ty.clone(),
                snd: snd_ty.clone(),
            }),
            Term::SRefl { level, ty, tm } => {
                Some(Type::SEq { level: level.clone(), ty: ty.clone(), lhs: tm.clone(), rhs: tm.clone() })
            }
            _ => None,
        }
    }

    /// `t` where its type `ty` is at hand. A term of a squash type prints
    /// eta-long (`squashEta`): every two such terms are equal in Heather,
    /// and Rocq's record over an SProp field has no η to see it, while two
    /// eta-long ones convert by irrelevance of the field (design §5.3).
    fn tm_at_ty(&self, t: &Term, ty: &Type) -> R<Hx> {
        let squash = match ty {
            Type::Squash { level, ty } => Some((level, self.ty(ty))),
            Type::El { tm, .. } => match &**tm {
                Term::TmSquash { level, ty } => Some((level, self.tm(ty))),
                _ => None,
            },
            _ => None,
        };
        let out = self.tm(t)?;
        match squash {
            Some((level, a)) if !matches!(t, Term::Squash { .. }) => konst("squashEta", &[level], vec![a?, out]),
            _ => Ok(out),
        }
    }

    fn tm(&self, t: &Term) -> R<Hx> {
        let key = (t as *const Term as usize, self.memo.borrow().at(local_bound(&Rc::new(t.clone())) == 0));
        if let Some((seen, out)) = self.memo.borrow().tms.get(&key) {
            if seen == t {
                return Ok(out.clone());
            }
        }
        let out = self.tm_node(t)?;
        self.memo.borrow_mut().tms.insert(key, (t.clone(), out.clone()));
        Ok(out)
    }

    fn tm_node(&self, t: &Term) -> R<Hx> {
        if let Term::Var(v) = t {
            let ctx = self.ctx.borrow();
            if let Some(Some((c, _))) = ctx.len().checked_sub(1 + v.0 as usize).map(|i| &ctx[i]) {
                return Ok(c.clone());
            }
        }
        if let Some(c) = self.known_ty(t).and_then(|ty| self.canon(&ty)) {
            return c;
        }
        Ok(match t {
            Term::Var(v) => Hx::Var(v.0),
            // ---- codes decode to themselves (Tarski → Russell) ----
            Term::TmNat => Hx::Const("Nat", vec![]),
            Term::TmPi { dom, cod, .. } => Hx::Pi(Rc::new(self.tm(dom)?), Rc::new(self.binds(1, || self.tm(cod))?)),
            Term::TmTy(l) => Hx::Sort(lvl(l)?),
            Term::TmId { level, ty, lhs, rhs } => konst("Id", &[level], vec![self.tm(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Term::TmSEq { level, ty, lhs, rhs } => konst("SEq", &[level], vec![self.tm(ty)?, self.tm(lhs)?, self.tm(rhs)?])?,
            Term::TmSEmpty { level } => konst("SEmpty", &[level], vec![])?,
            Term::TmSquash { level, ty } => konst("Squash", &[level], vec![self.tm(ty)?])?,
            Term::TmSigma { fst_level, snd_level, fst, snd } => {
                konst("Sig", &[fst_level, snd_level], vec![self.tm(fst)?, lam(self.tm(fst)?, self.binds(1, || self.tm(snd))?)])?
            }
            Term::TmUnit { level } => konst("Unit", &[level], vec![])?,
            Term::TmEmpty { level } => konst("Empty", &[level], vec![])?,
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => {
                konst("Sum", &[lhs_level, rhs_level], vec![self.tm(lhs)?, self.tm(rhs)?])?
            }
            Term::TmW { shape_level, pos_level, shape, pos } => {
                konst("W", &[shape_level, pos_level], vec![self.tm(shape)?, lam(self.tm(shape)?, self.binds(1, || self.tm(pos))?)])?
            }
            Term::TmVec { level, elem, len } => konst("Vec", &[level], vec![self.tm(elem)?, self.tm(len)?])?,
            Term::TmFin { len } => konst("Fin", &[], vec![self.tm(len)?])?,
            Term::TmWf { level, shape, .. } => self.wf_type(level, &Type::El { level: level.clone(), tm: shape.clone() })?,
            // ---- Nat ----
            Term::Zero => Hx::NatLit("0".into()),
            Term::NatLit(n) => Hx::NatLit(n.to_string()),
            Term::Succ(n) => konst("succ", &[], vec![self.tm(n)?])?,
            Term::ElimNat { level, motive, base, step, scrut } => konst(
                "elimNat",
                &[level],
                vec![
                    self.bound(&Type::Nat, || self.ty(motive))?,
                    self.tm(base)?,
                    self.bound(&Type::Nat, || self.bound(motive, || self.tm(step)))?,
                    self.tm(scrut)?,
                ],
            )?,
            // ---- Id ----
            Term::Refl { level, ty, tm } => konst("refl", &[level], vec![self.ty(ty)?, self.tm_at_ty(tm, ty)?])?,
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => konst(
                "J",
                &[ty_level, motive_level],
                vec![
                    self.ty(ty)?,
                    self.tm(lhs)?,
                    self.bound(ty, || {
                        let id = Type::Id {
                            level: ty_level.clone(),
                            ty: Rc::new(ty.shift_local(1)),
                            lhs: Rc::new(lhs.shift_local(1)),
                            rhs: Rc::new(Term::Var(LocalVar(0))),
                        };
                        self.bound(&id, || self.ty(motive))
                    })?,
                    self.tm(case)?,
                    self.tm(rhs)?,
                    self.tm(proof)?,
                ],
            )?,
            // ---- strict equality and squash ----
            Term::SRefl { level, ty, tm } => konst("srefl", &[level], vec![self.ty(ty)?, self.tm(tm)?])?,
            Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
                konst(
                    "elimSEmpty",
                    &[level, scrut_level],
                    vec![self.bound(&Type::SEmpty { level: scrut_level.clone() }, || self.ty(motive))?, self.tm(scrut)?],
                )?
            }
            Term::Squash { level, ty, tm } => konst("squash", &[level], vec![self.ty(ty)?, self.tm(tm)?])?,
            Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => konst(
                "elimSquash",
                &[src_level, dst_level],
                vec![
                    self.ty(src_ty)?,
                    self.bound(&Type::Squash { level: src_level.clone(), ty: src_ty.clone() }, || self.ty(motive))?,
                    self.bound(src_ty, || self.tm(case))?,
                    self.tm(scrut)?,
                ],
            )?,
            // ---- Σ ----
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => konst(
                "pair",
                &[fst_level, snd_level],
                vec![self.ty(fst_ty)?, self.lam_ty(fst_ty, snd_ty)?, self.tm(fst)?, self.tm(snd)?],
            )?,
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => konst(
                "fst",
                &[fst_level, snd_level],
                vec![self.ty(fst_ty)?, self.lam_ty(fst_ty, snd_ty)?, self.tm(pair)?],
            )?,
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => konst(
                "snd",
                &[fst_level, snd_level],
                vec![self.ty(fst_ty)?, self.lam_ty(fst_ty, snd_ty)?, self.tm(pair)?],
            )?,
            // ---- checked spellings: the components are the target's to infer ----
            Term::PairAt { ty, fst, snd } => self.at_ty(ty, "pair", 2, vec![self.tm(fst)?, self.tm(snd)?])?,
            Term::InlAt { ty, val } => self.at_ty(ty, "inl", 2, vec![self.tm(val)?])?,
            Term::InrAt { ty, val } => self.at_ty(ty, "inr", 2, vec![self.tm(val)?])?,
            Term::FstAt { pair } => Hx::Proj(0, Rc::new(self.tm(pair)?)),
            Term::SndAt { pair } => Hx::Proj(1, Rc::new(self.tm(pair)?)),
            Term::AppAt { fun, arg } => app(self.tm(fun)?, vec![self.tm(arg)?]),
            // ---- Unit, Empty, sums ----
            Term::Triv { level } => konst("tt", &[level], vec![])?,
            Term::ElimEmpty { level, scrut_level, motive, scrut } => {
                konst(
                    "elimEmpty",
                    &[level, scrut_level],
                    vec![self.bound(&Type::Empty { level: scrut_level.clone() }, || self.ty(motive))?, self.tm(scrut)?],
                )?
            }
            Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => {
                konst("inl", &[lhs_level, rhs_level], vec![self.ty(lhs)?, self.ty(rhs)?, self.tm(val)?])?
            }
            Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => {
                konst("inr", &[lhs_level, rhs_level], vec![self.ty(lhs)?, self.ty(rhs)?, self.tm(val)?])?
            }
            Term::Case { lhs_level, rhs_level, motive_level, lhs, rhs, motive, case_l, case_r, scrut } => {
                let motive = self.bound(
                    &Type::Sum { lhs_level: lhs_level.clone(), rhs_level: rhs_level.clone(), lhs: lhs.clone(), rhs: rhs.clone() },
                    || self.ty(motive),
                )?;
                // A side whose payload is a closed singleton is stated at its
                // canonical element (`caseL`/`caseR`/`caseLR`, design §5.3):
                // Rocq has no unit η to convert `M (inl x)` with it.
                let side = |dom: &Type, branch: &Term| -> R<Option<(Hx, Hx, Hx)>> {
                    let Some(closed) = self.close(dom) else { return Ok(None) };
                    let (Some(c), Some(e), Some(b)) = (self.canon(&closed), self.eta(&closed), self.singleton_branch(dom, branch)) else {
                        return Ok(None);
                    };
                    Ok(Some((c?, e?, b?)))
                };
                let levels = [lhs_level, rhs_level, motive_level];
                let (a, b) = (self.ty(lhs)?, self.ty(rhs)?);
                match (side(lhs, case_l)?, side(rhs, case_r)?) {
                    (Some((ca, ea, bl)), Some((cb, eb, br))) => konst("caseLR", &levels, vec![a, b, ca, cb, ea, eb, motive, bl, br, self.tm(scrut)?])?,
                    (Some((ca, ea, bl)), None) => {
                        konst("caseL", &levels, vec![a, b, ca, ea, motive, bl, self.bound(rhs, || self.tm(case_r))?, self.tm(scrut)?])?
                    }
                    (None, Some((cb, eb, br))) => {
                        konst("caseR", &levels, vec![a, b, cb, eb, motive, self.bound(lhs, || self.tm(case_l))?, br, self.tm(scrut)?])?
                    }
                    (None, None) => konst(
                        "case",
                        &levels,
                        vec![a, b, motive, self.bound(lhs, || self.tm(case_l))?, self.bound(rhs, || self.tm(case_r))?, self.tm(scrut)?],
                    )?,
                }
            }
            // ---- W and Wf ----
            Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => konst(
                "sup",
                &[shape_level, pos_level],
                vec![self.ty(shape_ty)?, self.lam_ty(shape_ty, pos_ty)?, self.tm(label)?, self.tm(children)?],
            )?,
            Term::ElimW { shape_level, pos_level, motive_level, shape, pos, motive, step, scrut } => {
                let w = Type::W {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    shape: shape.clone(),
                    pos: pos.clone(),
                };
                // The step telescope (a : S, f : Π(y : T a). W,
                // ih : Π(y : T a). M[f y/z]) as the kernel builds it, with
                // `inst_top` in place of its Γ-identity substitution.
                let lmax = Level::join(shape_level.clone(), pos_level.clone());
                let f_ty = Type::Pi {
                    dom_level: pos_level.clone(),
                    cod_level: lmax.clone(),
                    dom: pos.clone(),
                    cod: Rc::new(w.shift_local(2)),
                };
                let f_y = Term::App {
                    fun: Rc::new(Term::Var(LocalVar(1))),
                    dom_level: pos_level.clone(),
                    cod_level: lmax,
                    dom: Rc::new(pos.shift_local(2)),
                    cod: Rc::new(w.shift_local(4)),
                    arg: Rc::new(Term::Var(LocalVar(0))),
                };
                let ih_ty = Type::Pi {
                    dom_level: pos_level.clone(),
                    cod_level: motive_level.clone(),
                    dom: Rc::new(pos.shift_local(1)),
                    cod: Rc::new(motive.inst_top(3, &f_y)),
                };
                let step = self.bound(shape, || self.bound(&f_ty, || self.bound(&ih_ty, || self.tm(step))))?;
                konst(
                    "elimW",
                    &[shape_level, pos_level, motive_level],
                    vec![self.ty(shape)?, self.lam_ty(shape, pos)?, self.bound(&w, || self.ty(motive))?, step, self.tm(scrut)?],
                )?
            }
            Term::Supf { level, shape, label, children, .. } => self.wf_supf(level, shape, label, children)?,
            Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => {
                self.wf_elim(level, motive_level, shape, arity, motive, step, scrut)?
            }
            Term::Supi { .. } | Term::ElimIWf { .. } | Term::TmDVec { .. } | Term::TmIWf { .. } => {
                return refuse("DVec/IWf (not exported yet)")
            }
            Term::Corec { .. } | Term::Out { .. } | Term::TmM { .. } => return refuse("M (not exported yet)"),
            // ---- functions ----
            Term::Lam { dom, body, .. } => lam(self.ty(dom)?, self.under(Some(dom), || self.tm(body))?),
            Term::App { fun, arg, dom, .. } => app(self.tm(fun)?, vec![self.tm_at_ty(arg, dom)?]),
            Term::GlobalTm { var, subst } => self.global(var.0, subst)?,
            Term::ULam { .. } | Term::UApp { .. } => return refuse("universe abstraction/application"),
            Term::CtxLam { .. } | Term::CtxApp { .. } | Term::TyLam { .. } | Term::TyApp { .. } => {
                return refuse("context/type meta-function");
            }
            Term::BoxTy(_) | Term::BoxTm(_) | Term::LetBoxTy { .. } | Term::LetBoxTm { .. } => {
                return refuse("box/letbox (code layer)");
            }
            Term::ElimCodeTy { .. } | Term::ElimCodeTm { .. } => return refuse("code recursor"),
        })
    }

    /// A checked-spelling intro: `ty`, when present, is the un-reduced type
    /// it was checked at; the prelude constant's own components are holes.
    fn at_ty(&self, ty: &Option<std::sync::Arc<Type>>, name: &'static str, holes: usize, args: Vec<Hx>) -> R<Hx> {
        let mut all = vec![Hx::Hole; holes];
        all.extend(args);
        let t = app(Hx::Const(name, vec![]), all);
        Ok(match ty {
            Some(ty) => app(Hx::Const("the", vec![]), vec![self.ty(ty)?, t]),
            None => t,
        })
    }
}

/// One exported declaration.
#[derive(Clone, Debug)]
pub struct Decl {
    pub abs: usize,
    /// The module-qualified Heather name (`nat::Nat::add`), when the
    /// binding has one.
    pub name: Option<String>,
    pub ty: Hx,
    /// The definition's body, or the proof of a theorem; `None` for an
    /// assumption (an axiom, or a theorem whose proof Ψ did not keep) and
    /// for an inductive.
    pub body: Option<Hx>,
    /// Set when the binding is a tier-1 type code realised as a native
    /// inductive (`wf.rs`); `ty` is then the inductive's type.
    pub inductive: Option<Inductive>,
    /// Target-only definitions to declare just before this one (the
    /// eliminators it is the first to use) and just after it.
    pub before: Vec<Aux>,
    pub after: Vec<Aux>,
}

/// A native inductive: its parameters are the first `nparams` binders of its
/// type and of each constructor's.
#[derive(Clone, Debug)]
pub struct Inductive {
    pub nparams: usize,
    /// Each constructor's key and full type.
    pub ctors: Vec<(String, Hx)>,
    /// Each constructor's fields after the parameters: how many come first
    /// that are not children (0 or 1, the payload), then how many children.
    pub fields: Vec<(u32, u32)>,
}

/// A definition the target needs that Ψ has no binding for.
#[derive(Clone, Debug)]
pub struct Aux {
    pub name: String,
    pub ty: Hx,
    pub body: Hx,
}

/// What the exporter reads: Ψ, plus what the elaborator knows beside it.
/// The kernel crate cannot see the elaborator, so the two are lookups.
pub struct Source<'a> {
    pub psi: &'a GlobalCtx,
    /// A theorem's proof by absolute index, when Ψ itself keeps none
    /// (`Elaborator::export_proof`).
    pub proof: &'a dyn Fn(usize) -> Option<std::sync::Arc<Term>>,
    /// A binding's module-qualified name (`Elaborator::global_key_at`).
    pub name: &'a dyn Fn(usize) -> Option<String>,
    /// A nominal tag's constructor names, in declaration order
    /// (`Elaborator::constructor_names`): what a native inductive's
    /// constructors are called.
    pub ctors: &'a dyn Fn(u64) -> Option<Vec<String>>,
}

impl<'a> Source<'a> {
    /// Ψ alone: sealed proofs only, and no names.
    pub fn psi(psi: &'a GlobalCtx) -> Source<'a> {
        Source { psi, proof: &|_| None, name: &|_| None, ctors: &|_| None }
    }
}

/// One binding's export: its index, its Heather name, and the declaration
/// or why it was refused.
#[derive(Clone, Debug)]
pub struct Exported {
    pub abs: usize,
    pub name: Option<String>,
    pub decl: R<Decl>,
}

/// Translate every binding of Ψ. A binding is refused when it is outside the
/// fragment *or mentions a refused binding*, so the `Ok` declarations are
/// closed under dependency.

pub fn export(src: &Source) -> Vec<Exported> {
    let psi = src.psi;
    let mut out: Vec<Exported> = Vec::new();
    let mut refused = vec![false; psi.bindings.len()];
    let table = wf::WfTable::default();
    let mut interned = Interned::default();
    for (abs, b) in psi.bindings.iter().enumerate() {
        let prefix = psi.prefix(abs);
        let tr = Tr { at: abs, psi: &prefix, ctx: RefCell::new(Vec::new()), wf: &table, memo: RefCell::default() };
        let mut name = (src.name)(abs);
        table.wanted.borrow_mut().clear();
        let decl = (|| -> R<Decl> {
            let GlobalBinding::Tm { ctx, ty, body, level, .. } = b else {
                return refuse("context or type global binding");
            };
            if ctx.base != CtxBase::Nil {
                return refuse("global over a context variable");
            }
            let proof = body.clone().or_else(|| psi.sealed_proof(abs).cloned()).or_else(|| (src.proof)(abs));
            // The checked spellings first: the kernel's own `⌊·⌋` writes
            // each one's components back, so the translation never guesses
            // them (design §5.6). Statements are types, checked at layer p.
            // A global over a local context Δ (a helper the elaborator
            // abstracted out of a body) is exported closed, over Δ's
            // entries, and its uses `g[σ]` apply it to σ's terms.
            let entries: Vec<_> = ctx.entries.iter().cloned().collect();
            let spelled_ctx = entries
                .iter()
                .enumerate()
                .map(|(i, e)| {
                    spell_checked_for_export_ty(&prefix, 0, Layer::Prog, &ctx.prefix(i), e.ty.clone(), &e.level, DEFAULT_FUEL)
                        .map_err(|e| Refusal(format!("context spelling: {e:?}")))
                })
                .collect::<R<Vec<_>>>()?;
            let spelled_ty = spell_checked_for_export_ty(&prefix, 0, Layer::Prog, ctx, ty.clone(), level, DEFAULT_FUEL)
                .map_err(|e| Refusal(format!("statement spelling: {e:?}")))?;
            // A body the eager checker cannot spell keeps its checked
            // spellings, which print as holes for the target to fill.
            let spelled = proof.map(|t| {
                spell_checked_for_export(&prefix, 0, Layer::Code, ctx, Rc::clone(&t), ty, level, DEFAULT_FUEL).unwrap_or(t)
            });
            if let Some(code) = body.as_ref().filter(|_| entries.is_empty()) {
                if let Some(w) = tr.register_wf(name.as_deref(), code, ty_tag_ctors(src, &prefix, code))? {
                    name = Some(w.key.clone());
                    return tr.wf_inductive(&w, tr.ty(&spelled_ty)?);
                }
            }
            let (ty, body) = tr.over(&spelled_ctx, &|| Ok((tr.ty(&spelled_ty)?, spelled.as_ref().map(|t| tr.tm(t)).transpose()?)))?;
            let mut d = Decl { abs, name: name.clone(), ty, body, inductive: None, before: Vec::new(), after: Vec::new() };
            // The eliminators this declaration is the first to use, each
            // translated where its declaration is.
            let wanted = std::mem::take(&mut *table.wanted.borrow_mut());
            for (tag, ml) in wanted {
                if !table.emitted.borrow_mut().insert((tag, ml)) {
                    continue;
                }
                let w = table.by_tag.borrow()[&tag].clone();
                let at = Tr { at: w.abs, psi: &w.psi, ctx: RefCell::new(Vec::new()), wf: &table, memo: RefCell::default() };
                match at.wf_elim_def(&w, ml) {
                    Ok(aux) => d.before.push(aux),
                    Err(e) => {
                        table.emitted.borrow_mut().remove(&(tag, ml));
                        return Err(e);
                    }
                }
            }
            if let Some(dep) = mentions(&d).into_iter().find(|&g| refused[g]) {
                let dep = (src.name)(dep).unwrap_or_else(|| format!("g{dep}"));
                return Err(Refusal(format!("mentions refused declaration {dep}")));
            }
            Ok(d)
        })();
        let decl = decl.map(|d| interned.decl(d));
        refused[abs] = decl.is_err();
        out.push(Exported { abs, name, decl });
    }
    out
}

/// The exported terms, hash-consed across declarations: a library's
/// statements repeat the same instantiated types from one declaration to
/// the next, and each translation shares only within its own.
#[derive(Default)]
struct Interned {
    nodes: std::collections::HashMap<Node, Rc<Hx>>,
}

/// A node by its interned children's addresses, or a leaf.
#[derive(PartialEq, Eq, Hash)]
enum Node {
    Pi(usize, usize),
    Lam(usize, usize),
    App(usize, usize),
    Proj(u8, usize),
    Leaf(Hx),
}

impl Interned {
    fn node(&mut self, t: &Hx, memo: &mut std::collections::HashMap<usize, Rc<Hx>>) -> Rc<Hx> {
        if let Some(out) = memo.get(&(t as *const Hx as usize)) {
            return out.clone();
        }
        let addr = |r: &Rc<Hx>| Rc::as_ptr(r) as usize;
        let (key, rebuilt) = match t {
            Hx::Pi(a, b) | Hx::Lam(a, b) | Hx::App(a, b) => {
                let (a, b) = (self.node(a, memo), self.node(b, memo));
                let key = match t {
                    Hx::Pi(..) => Node::Pi(addr(&a), addr(&b)),
                    Hx::Lam(..) => Node::Lam(addr(&a), addr(&b)),
                    _ => Node::App(addr(&a), addr(&b)),
                };
                let rebuilt = match t {
                    Hx::Pi(..) => Hx::Pi(a, b),
                    Hx::Lam(..) => Hx::Lam(a, b),
                    _ => Hx::App(a, b),
                };
                (key, rebuilt)
            }
            Hx::Proj(i, p) => {
                let p = self.node(p, memo);
                (Node::Proj(*i, addr(&p)), Hx::Proj(*i, p))
            }
            leaf => (Node::Leaf(leaf.clone()), leaf.clone()),
        };
        let out = self.nodes.entry(key).or_insert_with(|| Rc::new(rebuilt)).clone();
        memo.insert(t as *const Hx as usize, out.clone());
        out
    }

    fn decl(&mut self, d: Decl) -> Decl {
        let mut memo = std::collections::HashMap::new();
        let mut f = |t: &Hx| (*self.node(t, &mut memo)).clone();
        let aux = |a: &Aux, f: &mut dyn FnMut(&Hx) -> Hx| Aux { name: a.name.clone(), ty: f(&a.ty), body: f(&a.body) };
        Decl {
            ty: f(&d.ty),
            body: d.body.as_ref().map(&mut f),
            inductive: d.inductive.as_ref().map(|i| Inductive { ctors: i.ctors.iter().map(|(k, t)| (k.clone(), f(t))).collect(), ..i.clone() }),
            before: d.before.iter().map(|a| aux(a, &mut f)).collect(),
            after: d.after.iter().map(|a| aux(a, &mut f)).collect(),
            ..d
        }
    }
}

/// The constructor names of the tier-1 declaration whose type code `code`
/// is, by the tag its shape carries (read again by `register_wf`; here only
/// to name things).
fn ty_tag_ctors(src: &Source, prefix: &GlobalCtx, code: &Term) -> Option<Vec<String>> {
    let (mut cur, mut depth) = (code, 0);
    while let Term::Lam { body, .. } = cur {
        (cur, depth) = (body, depth + 1);
    }
    let Term::TmWf { level, shape, .. } = cur else { return None };
    let shape = Type::El { level: level.clone(), tm: Rc::clone(shape) };
    (src.ctors)(Tr::tag_in(prefix, &shape, depth)?)
}

/// Every term `d` declares: its statement, body, constructors and helpers.
fn roots(d: &Decl) -> Vec<&Hx> {
    let mut out = vec![&d.ty];
    out.extend(&d.body);
    out.extend(d.inductive.iter().flat_map(|i| &i.ctors).map(|(_, t)| t));
    for a in d.before.iter().chain(&d.after) {
        out.extend([&a.ty, &a.body]);
    }
    out
}

fn mentions(d: &Decl) -> Vec<usize> {
    let mut out = Vec::new();
    each_node(roots(d), &mut |t| {
        if let Hx::Global(g) = t {
            out.push(*g);
        }
    });
    out.sort_unstable();
    out.dedup();
    out.retain(|&g| g != d.abs);
    out
}

// ---------------------------------------------------------------------------
// Printers. Both name bound variables `x<depth>` and globals `g<abs>`.

/// Which target a printer writes for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    Lean,
    Coq,
}

struct Printer {
    target: Target,
    out: String,
    /// The target spelling of each exported binding, by absolute index.
    names: Vec<String>,
}

/// Lean's keywords that can also be Heather name components; a component
/// that is one, or is not a plain identifier, is written `«…»`.
const LEAN_KEYWORDS: &[&str] = &[
    "fun", "at", "by", "do", "then", "else", "if", "let", "in", "have", "show", "from", "match", "with", "end",
    "where", "deriving", "instance", "structure", "class", "theorem", "def", "axiom", "example", "open",
    "namespace", "section", "universe", "variable", "import", "Type", "Sort", "Prop", "forall", "exists",
    "calc", "mut", "for", "unless", "return", "try", "catch", "finally", "local", "private", "protected",
];

fn plain_ident(s: &str) -> bool {
    let mut cs = s.chars();
    cs.next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// The target spelling of a module-qualified Heather name. Lean keeps the
/// structure (`nat::Nat::add` is `Heather.nat.Nat.add`); Rocq identifiers
/// have no dots inside a file, so its components join with `__`.
fn target_name(target: Target, key: &str) -> String {
    let parts: Vec<&str> = key.split("::").collect();
    match target {
        Target::Lean => {
            let parts: Vec<String> = parts
                .iter()
                .map(|p| if plain_ident(p) && !LEAN_KEYWORDS.contains(p) { p.to_string() } else { format!("«{p}»") })
                .collect();
            format!("Heather.{}", parts.join("."))
        }
        Target::Coq => {
            let parts: Vec<String> = parts
                .iter()
                .map(|p| p.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect())
                .collect();
            format!("H__{}", parts.join("__"))
        }
    }
}

/// One spelling per binding: its name where it has one, `g<abs>` where it
/// has none or where the name is already taken.
fn spellings(target: Target, exported: &[Exported]) -> Vec<String> {
    let mut seen = std::collections::HashSet::new();
    let len = exported.iter().map(|e| e.abs + 1).max().unwrap_or(0);
    let mut names = (0..len).map(|g| format!("g{g}")).collect::<Vec<_>>();
    for e in exported {
        if let Some(key) = &e.name {
            let n = target_name(target, key);
            if seen.insert(n.clone()) {
                names[e.abs] = n;
            }
        }
    }
    names
}

impl Printer {
    fn level(&self, l: Lvl) -> String {
        match self.target {
            Target::Lean => l.0.to_string(),
            // Closed levels are a chain of global universes in the prelude
            // (Rocq instances cannot be algebraic, and need not be here).
            Target::Coq if l.0 == 0 => "Set".into(),
            Target::Coq => format!("Hx.u{}", l.0),
        }
    }

    /// Print `t`, parenthesised only where it is an argument (`arg`) and not
    /// an atom. Lean's parser is far from linear in parenthesis nesting: a
    /// fully parenthesised library file spent nearly all its check time
    /// parsing.
    fn term(&mut self, t: &Hx, depth: u32, arg: bool) {
        let atom = match t {
            Hx::Var(_) | Hx::Hole | Hx::NatLit(_) => true,
            // Rocq parses `f @c` as a syntax error, so there a constant is
            // an atom only in head position.
            Hx::Const(..) | Hx::Global(_) | Hx::Named(..) => self.target == Target::Lean,
            Hx::Sort(_) => self.target == Target::Coq,
            Hx::Pi(..) | Hx::Lam(..) | Hx::App(..) => false,
            Hx::Proj(..) => self.target == Target::Lean,
        };
        let open = arg && !atom;
        if open {
            self.out.push('(');
        }
        match t {
            Hx::Var(i) => {
                let _ = write!(self.out, "x{}", depth - 1 - i);
            }
            Hx::Sort(l) => {
                let _ = match self.target {
                    Target::Lean => write!(self.out, "Type {}", self.level(*l)),
                    Target::Coq => write!(self.out, "Type@{{{}}}", self.level(*l)),
                };
            }
            Hx::Pi(a, b) => {
                let _ = write!(self.out, "forall (x{depth} : ");
                self.term(a, depth, false);
                self.out.push_str("), ");
                self.term(b, depth + 1, false);
            }
            Hx::Lam(a, b) => {
                let _ = write!(self.out, "fun (x{depth} : ");
                self.term(a, depth, false);
                self.out.push_str(") => ");
                self.term(b, depth + 1, false);
            }
            Hx::App(..) => {
                let mut spine = Vec::new();
                let mut head = t;
                while let Hx::App(f, a) = head {
                    spine.push(a);
                    head = f;
                }
                match head {
                    Hx::Const(..) | Hx::Global(_) | Hx::Named(..) => self.atom(head),
                    _ => self.term(head, depth, true),
                }
                for a in spine.into_iter().rev() {
                    self.out.push(' ');
                    self.term(a, depth, true);
                }
            }
            Hx::Const(..) | Hx::Global(_) | Hx::Named(..) => self.atom(t),
            Hx::NatLit(n) => {
                let _ = write!(self.out, "({n} : Hx.Nat)");
            }
            Hx::Hole => self.out.push('_'),
            Hx::Proj(i, p) => {
                // `@Hx.c.1` would read as one name; only a variable or
                // another projection goes bare.
                let bare = matches!(**p, Hx::Var(_) | Hx::Proj(..));
                if !bare {
                    self.out.push('(');
                }
                self.term(p, depth, false);
                if !bare {
                    self.out.push(')');
                }
                let _ = match self.target {
                    Target::Lean => write!(self.out, ".{}", i + 1),
                    // Rocq's primitive projection takes the record's
                    // parameters, which it infers from the pair.
                    Target::Coq => write!(self.out, ".(@Hx.{} _ _)", if *i == 0 { "fst_" } else { "snd_" }),
                };
            }
        }
        if open {
            self.out.push(')');
        }
    }

    fn def(&mut self, name: &str, ty: &Hx, body: Option<&Hx>) {
        let kw = match (self.target, body) {
            (Target::Lean, Some(_)) => "@[reducible] def",
            (Target::Lean, None) => "axiom",
            (Target::Coq, Some(_)) => "Definition",
            (Target::Coq, None) => "Axiom",
        };
        let _ = write!(self.out, "{kw} {name} : ");
        self.term(ty, 0, false);
        if let Some(b) = body {
            self.out.push_str(" :=\n  ");
            self.term(b, 0, false);
        }
        self.out.push_str(match self.target {
            Target::Lean => "\n\n",
            Target::Coq => ".\n\n",
        });
    }

    /// A shared subterm's definition (`share.rs`), its type left to Lean.
    fn shared(&mut self, name: &str, body: &Hx) {
        let kw = if self.target == Target::Lean { "@[reducible] def" } else { "Definition" };
        let _ = write!(self.out, "{kw} {name} :=\n  ");
        self.term(body, 0, false);
        self.out.push_str(if self.target == Target::Lean { "\n\n" } else { ".\n\n" });
    }

    /// A native inductive, its parameters as binders. Rocq has no
    /// realisation of `Wf` here (design §5.1), so it gets a comment.
    fn inductive(&mut self, name: &str, ty: &Hx, ind: &Inductive) {
        let strip = |mut t: &Hx, out: &mut Vec<Hx>| {
            for _ in 0..ind.nparams {
                let Hx::Pi(a, b) = t else { unreachable!("an inductive's parameters are binders") };
                out.push((**a).clone());
                t = b;
            }
            t.clone()
        };
        let mut params = Vec::new();
        let rest = strip(ty, &mut params);
        let _ = write!(self.out, "{} {name}", if self.target == Target::Lean { "inductive" } else { "Inductive" });
        for (i, a) in params.iter().enumerate() {
            let _ = write!(self.out, " (x{i} : ");
            self.term(a, i as u32, false);
            self.out.push(')');
        }
        self.out.push_str(" : ");
        self.term(&rest, ind.nparams as u32, false);
        self.out.push_str(if self.target == Target::Lean { " where\n" } else { " :=\n" });
        for (key, cty) in &ind.ctors {
            // Lean names a constructor inside its inductive's namespace;
            // Rocq's constructors are file-level names.
            let ctor = match self.target {
                Target::Lean => {
                    let short = key.rsplit("::").next().unwrap_or(key);
                    if plain_ident(short) && !LEAN_KEYWORDS.contains(&short) { short.to_string() } else { format!("«{short}»") }
                }
                Target::Coq => target_name(Target::Coq, key),
            };
            let _ = write!(self.out, "  | {ctor} : ");
            let c = strip(cty, &mut Vec::new());
            self.term(&c, ind.nparams as u32, false);
            self.out.push('\n');
        }
        self.out.push_str(if self.target == Target::Lean { "\n" } else { ".\n\n" });
    }

    /// A constant or global, explicit (`@`), with its levels.
    fn atom(&mut self, t: &Hx) {
        match t {
            Hx::Const(name, levels) => {
                let _ = write!(self.out, "@Hx.{name}");
                let levels = if self.target == Target::Lean { lean_levels(name, levels) } else { levels };
                if !levels.is_empty() {
                    let ls: Vec<String> = levels.iter().map(|l| self.level(*l)).collect();
                    let _ = match self.target {
                        Target::Lean => write!(self.out, ".{{{}}}", ls.join(", ")),
                        Target::Coq => write!(self.out, "@{{{}}}", ls.join(" ")),
                    };
                }
            }
            Hx::Global(g) => {
                let _ = write!(self.out, "@{}", self.names[*g]);
            }
            // Rocq names a monomorphic inductive's recursor into `Type`
            // `D_rect`, at no instance.
            Hx::Named(key, _) if self.target == Target::Coq && key.ends_with("::rec") => {
                let _ = write!(self.out, "@{}_rect", target_name(self.target, &key[..key.len() - 5]));
            }
            Hx::Named(key, levels) => {
                let _ = write!(self.out, "@{}", target_name(self.target, key));
                if !levels.is_empty() {
                    let ls: Vec<String> = levels.iter().map(|l| l.to_string()).collect();
                    let _ = match self.target {
                        Target::Lean => write!(self.out, ".{{{}}}", ls.join(", ")),
                        Target::Coq => write!(self.out, "@{{{}}}", ls.join(" ")),
                    };
                }
            }
            _ => unreachable!("atom: a constant or a global"),
        }
    }
}

const LEAN_HEADER: &str = "set_option autoImplicit false\nset_option linter.unusedVariables false\nnoncomputable section\n\n";

/// Print the exported declarations as a source file for `target`, which
/// imports the prelude. Refused declarations become comments naming why.
pub fn print(target: Target, decls: &[Exported]) -> String {
    let mut p = Printer { target, out: String::new(), names: spellings(target, decls) };
    p.out.push_str(match target {
        Target::Lean => "import Hx\n\n",
        Target::Coq => "Require Import Hx.\n\n",
    });
    if target == Target::Lean {
        p.out.push_str(LEAN_HEADER);
    }
    print_run(&mut p, decls.iter(), "");
    p.out
}

/// [`print`] for Lean, one file per Heather module: `(module name, text)`
/// in dependency order, each importing `Hx` and the files whose
/// declarations it mentions. Ψ elaborates a module's bindings together, so
/// a module is one run of consecutive declarations (a module that came
/// back later would be a second file).
pub fn print_lean_files(decls: &[Exported]) -> Vec<(String, String)> {
    let names = spellings(Target::Lean, decls);
    let module = |e: &Exported| e.name.as_deref().and_then(|k| k.split("::").next()).unwrap_or("anon").to_string();
    let mut runs: Vec<(String, Vec<&Exported>)> = Vec::new();
    for e in decls {
        let m = module(e);
        match runs.last_mut() {
            Some((last, run)) if *last == m => run.push(e),
            _ => runs.push((m, vec![e])),
        }
    }
    // Who declares what: bindings by index, target-only constants by key.
    let mut file_of_abs = std::collections::HashMap::new();
    let mut file_of_key = std::collections::HashMap::new();
    let mut seen = std::collections::HashSet::new();
    let mut files = Vec::new();
    for (i, (m, run)) in runs.iter().enumerate() {
        let mut file = format!("Heather_{m}");
        while !seen.insert(file.clone()) {
            file.push('_');
        }
        for e in run {
            file_of_abs.insert(e.abs, i);
            if let Ok(d) = &e.decl {
                let keys = d.before.iter().chain(&d.after).map(|a| &a.name).chain(d.inductive.iter().flat_map(|ind| ind.ctors.iter().map(|c| &c.0)));
                for k in keys.chain(d.name.iter()) {
                    file_of_key.insert(k.clone(), i);
                }
            }
        }
        files.push(file);
    }
    let mut out = Vec::new();
    for (i, (m, run)) in runs.iter().enumerate() {
        let mut p = Printer { target: Target::Lean, out: String::new(), names: names.clone() };
        print_run(&mut p, run.iter().copied(), &format!("{m}::"));
        let mut deps = std::collections::BTreeSet::new();
        for e in run {
            let Ok(d) = &e.decl else { continue };
            for_each_constant(d, &mut |c| {
                let dep = match c {
                    Hx::Global(g) => file_of_abs.get(g).copied(),
                    // A recursor is its inductive's (`D::rec`).
                    Hx::Named(k, _) => file_of_key.get(k).or_else(|| k.rsplit_once("::").and_then(|(d, _)| file_of_key.get(d))).copied(),
                    _ => None,
                };
                if let Some(j) = dep.filter(|&j| j != i) {
                    deps.insert(j);
                }
            });
        }
        let mut text = String::from("import Hx\n");
        for j in deps {
            let _ = writeln!(text, "import {}", files[j]);
        }
        text.push('\n');
        text.push_str(LEAN_HEADER);
        text.push_str(&p.out);
        out.push((files[i].clone(), text));
    }
    out
}

/// The longest numeral Rocq gets: `65536` appears in every collection
/// literal's tag and checks; `10^21` does not finish.
const COQ_MAX_LITERAL_DIGITS: usize = 5;

/// Every numeral `d` spells.
fn for_each_literal(d: &Decl, f: &mut dyn FnMut(&str)) {
    each_node(roots(d), &mut |t| {
        if let Hx::NatLit(n) = t {
            f(n)
        }
    });
}

/// Every global and target-only constant `d` mentions.
fn for_each_constant(d: &Decl, f: &mut dyn FnMut(&Hx)) {
    each_node(roots(d), &mut |t| {
        if let Hx::Global(_) | Hx::Named(..) = t {
            f(t)
        }
    });
}

/// The declarations of one output file. Shared subterms' definitions are
/// named under `ns` (a module's key prefix, so files do not collide).
fn print_run<'e>(p: &mut Printer, decls: impl Iterator<Item = &'e Exported> + Clone, ns: &str) {
    // Rocq's recursor takes its minor premises in another order; rewrite
    // them first, so the sharing below sees the terms as printed.
    let rocq: Vec<Exported>;
    let decls: Vec<&Exported> = if p.target == Target::Coq {
        let mut recs = Recs::new();
        for e in decls.clone() {
            if let Ok(Decl { name: Some(key), inductive: Some(ind), .. }) = &e.decl {
                recs.insert(format!("{key}::rec"), (ind.nparams, ind.fields.clone()));
            }
        }
        let memo = RefCell::new(Nodes::new());
        let fix = |t: &Hx| (*rocq_minors(t, &recs, &mut memo.borrow_mut())).clone();
        rocq = decls
            // The memo is keyed by node address, so it reads the
            // declarations in place, never a copy that is dropped after.
            .map(|e| Exported {
                decl: e.decl.as_ref().map(|d| Decl {
                    ty: fix(&d.ty),
                    body: d.body.as_ref().map(fix),
                    before: d.before.iter().map(|a| Aux { name: a.name.clone(), ty: fix(&a.ty), body: fix(&a.body) }).collect(),
                    after: d.after.iter().map(|a| Aux { name: a.name.clone(), ty: fix(&a.ty), body: fix(&a.body) }).collect(),
                    ..d.clone()
                }).map_err(Refusal::clone),
                ..e.clone()
            })
            .collect();
        rocq.iter().collect()
    } else {
        decls.collect()
    };
    let decls = decls.into_iter();
    // Both targets get the kernel term's sharing back (`share.rs`):
    // unshared, the `List` closure is too large for Lean's parser.
    let mut share = Some(share::Share::new(ns));
    if let Some(s) = &mut share {
        for e in decls.clone() {
            if let Ok(d) = &e.decl {
                for a in d.before.iter().chain(&d.after) {
                    s.count(&a.ty);
                    s.count(&a.body);
                }
                if d.inductive.is_none() {
                    s.count(&d.ty);
                    d.body.as_ref().map(|b| s.count(b));
                }
            }
        }
    }
    // Rocq's `nat` is unary: a large literal is a term of its size, and a
    // conversion that forces one runs out of memory (design §5.4). Such
    // declarations, and what mentions them, are refused for Rocq alone.
    let mut too_large = std::collections::HashMap::new();
    if p.target == Target::Coq {
        for e in decls.clone() {
            let Ok(d) = &e.decl else { continue };
            let mut why = None;
            for_each_literal(d, &mut |n| {
                if why.is_none() && n.len() > COQ_MAX_LITERAL_DIGITS {
                    why = Some(format!("numeral {n} is too large for Rocq's unary nat"));
                }
            });
            let why = why.or_else(|| mentions(d).into_iter().find(|g| too_large.contains_key(g)).map(|g| format!("mentions refused {}", p.names[g])));
            if let Some(why) = why {
                too_large.insert(e.abs, why);
            }
        }
    }
    for e in decls {
        let name = p.names[e.abs].clone();
        let refused = too_large.get(&e.abs).map(|why| Err(Refusal(why.clone())));
        let d = match refused.as_ref().unwrap_or(&e.decl) {
            Err(Refusal(why)) => {
                let _ = match p.target {
                    Target::Lean => writeln!(p.out, "-- {name}: refused: {why}\n"),
                    Target::Coq => writeln!(p.out, "(* {name}: refused: {why} *)\n"),
                };
                continue;
            }
            Ok(d) => d,
        };
        // Each definition's shared subterms are declared just before it, so
        // after whatever they mention (a realised inductive comes before the
        // helpers that follow it).
        let mut def = |p: &mut Printer, name: &str, ty: &Hx, body: Option<&Hx>| match &mut share {
            Some(s) => {
                let (ty, body) = (s.rewrite(ty), body.map(|b| s.rewrite(b)));
                for (n, b) in std::mem::take(&mut s.fresh) {
                    p.shared(&target_name(p.target, &n), &b);
                }
                p.def(name, &ty, body.as_ref());
            }
            None => p.def(name, ty, body),
        };
        for a in &d.before {
            def(p, &target_name(p.target, &a.name), &a.ty, Some(&a.body));
        }
        match &d.inductive {
            Some(ind) => p.inductive(&name, &d.ty, ind),
            None => def(p, &name, &d.ty, d.body.as_ref()),
        }
        for a in &d.after {
            def(p, &target_name(p.target, &a.name), &a.ty, Some(&a.body));
        }
    }
}

/// Hash-consed nodes for [`print_kernel`]: one line per distinct subterm,
/// children named by their line number among the node lines.
struct Dag {
    out: String,
    /// Lines by their text, and by the node they were made for: a shared
    /// node is visited once.
    ids: std::collections::HashMap<String, usize>,
    by_node: std::collections::HashMap<*const Hx, usize>,
    names: Vec<String>,
    /// Declarations the kernel route skipped, which their dependents skip.
    skipped: std::collections::HashSet<usize>,
}

impl Dag {
    fn node(&mut self, t: &Hx) -> Result<usize, String> {
        if let Some(&id) = self.by_node.get(&(t as *const Hx)) {
            return Ok(id);
        }
        let line = match t {
            Hx::Var(i) => format!("v\t{i}"),
            Hx::Sort(l) => format!("s\t{}", l.0),
            Hx::Pi(a, b) => format!("p\t{}\t{}", self.node(a)?, self.node(b)?),
            Hx::Lam(a, b) => format!("l\t{}\t{}", self.node(a)?, self.node(b)?),
            Hx::App(f, a) => format!("a\t{}\t{}", self.node(f)?, self.node(a)?),
            Hx::Const(name, levels) => {
                let mut s = format!("c\t{name}");
                for l in lean_levels(name, levels) {
                    let _ = write!(s, "\t{}", l.0);
                }
                s
            }
            Hx::Global(g) if self.skipped.contains(g) => return Err(format!("mentions skipped {}", self.names[*g])),
            Hx::Global(g) => format!("g\t{}", self.names[*g]),
            Hx::Named(key, levels) => {
                let mut s = format!("g\t{key}");
                for l in levels {
                    let _ = write!(s, "\t{l}");
                }
                s
            }
            Hx::NatLit(n) => format!("n\t{n}"),
            Hx::Proj(i, p) => format!("j\t{i}\t{}", self.node(p)?),
            Hx::Hole => return Err("a hole (a component only the target's elaborator can infer)".into()),
        };
        let next = self.ids.len();
        let id = *self.ids.entry(line).or_insert_with_key(|line| {
            self.out.push_str(line);
            self.out.push('\n');
            next
        });
        self.by_node.insert(t as *const Hx, id);
        Ok(id)
    }
}

/// Print the exported declarations for Lean's **kernel**: the hash-consed
/// line format `prelude/Import.lean` reads and hands to `addDecl`, with no
/// parser and no elaborator in between (design §5.6). Names are Heather
/// keys (`nat::Nat::add`, or `g<abs>` where a binding has none or shares
/// one), which the importer roots at `Heather`. A declaration with a hole,
/// or one mentioning such a declaration, is written as skipped (`x`).
pub fn print_kernel(decls: &[Exported]) -> String {
    let mut seen = std::collections::HashSet::new();
    let len = decls.iter().map(|e| e.abs + 1).max().unwrap_or(0);
    let mut names = (0..len).map(|g| format!("g{g}")).collect::<Vec<_>>();
    for e in decls {
        if let Some(key) = &e.name {
            if seen.insert(key.clone()) {
                names[e.abs] = key.clone();
            }
        }
    }
    let mut dag = Dag { out: String::new(), ids: Default::default(), by_node: Default::default(), names, skipped: Default::default() };
    for e in decls {
        let name = dag.names[e.abs].clone();
        let line = match &e.decl {
            Err(Refusal(why)) => Err(format!("refused: {why}")),
            Ok(d) => (|| {
                let mut lines = Vec::new();
                let aux = |dag: &mut Dag, a: &Aux| -> Result<String, String> {
                    Ok(format!("d\t{}\t{}\t{}", a.name, dag.node(&a.ty)?, dag.node(&a.body)?))
                };
                for a in &d.before {
                    lines.push(aux(&mut dag, a)?);
                }
                let ty = dag.node(&d.ty)?;
                lines.push(match (&d.inductive, &d.body) {
                    (Some(ind), _) => {
                        let mut l = format!("i\t{name}\t{}\t{ty}", ind.nparams);
                        for (key, cty) in &ind.ctors {
                            let _ = write!(l, "\t{key}\t{}", dag.node(cty)?);
                        }
                        l
                    }
                    (None, Some(b)) => format!("d\t{name}\t{ty}\t{}", dag.node(b)?),
                    (None, None) => format!("ax\t{name}\t{ty}"),
                });
                for a in &d.after {
                    lines.push(aux(&mut dag, a)?);
                }
                Ok(lines.join("\n"))
            })(),
        };
        match line {
            Ok(line) => {
                dag.out.push_str(&line);
                dag.out.push('\n');
            }
            Err(why) => {
                dag.skipped.insert(e.abs);
                let _ = writeln!(dag.out, "x\t{name}\t{why}");
            }
        }
    }
    dag.out
}
