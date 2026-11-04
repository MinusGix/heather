//! `Wf` realised as native Lean inductives (design §5.1,
//! `issues/export-wf-native-inductives.md`).
//!
//! Lean cannot declare the `Wf` former, but each lowered tier-1 declaration
//! can be a native inductive with one constructor per summand of its shape,
//! holding the summand's payload and the children as fields. The exporter
//! meets a declaration as its whole-type code, `D#tycode` or
//! `D#tycode_fn : Π(A : Ty l)…(v : T)…. Ty l := λ…. Wf(x : S). n`, and emits there
//!
//! - the inductive `D (A…) : Type l`, constructor `k` taking the payload
//!   `P_k` and `n_k` children (the arity at summand `k` must be a literal);
//! - `D::supf# : Π A… (a : S) (cs : Vec(D A…; n[a])). D A…`, a case on the
//!   shape that hands the projected children to the constructor;
//!
//! and, before the first declaration that eliminates at motive level `l'`,
//! `D::elim#l'`, the `elim_Wf` rule through `D.rec`: each minor premise calls
//! the step at the canonical tag, with the children re-tupled and the
//! induction hypothesis as a case over the index.
//!
//! An instance `Wf(S; n)` anywhere is recognised by its **nominal tag**,
//! the literal every constructor's payload starts with (`sEq(Nat; t; t)`),
//! never by its spelling. Its parameters are read off by walking the
//! instance's payload types beside the declaration's own: where the
//! declaration has a parameter, the instance has its argument. The walk is
//! lenient (it compares nothing), because Lean checks the result: a wrong
//! argument is a rejected declaration, never an accepted wrong one.
//!
//! A parameter may be a value (`Trace<R>(E: Events)`), read off the
//! instance where the declaration's spelling has the variable. A use at
//! another type-parameter level profile (`List<A → B → Type>`) names that
//! profile's own native inductive (`list::List::at#1`), lowered by the
//! elaborator at the profile and declared before the binding that first
//! needs it (design §5.1).
//!
//! What the realisation lacks is `elim_Wf`'s β at an *open* tag, which
//! Heather has and `D.rec` cannot (`probes/WfNative.lean`, (3)). Generated
//! code does not use it (`crates/kernel/DESIGN.md`, the `Wf` paragraph); a
//! declaration that does is rejected by Lean, which is the side condition
//! checked rather than assumed.

use super::*;
use heather_kernel::term::{Numeral, nth};
use std::collections::{HashMap, HashSet};

/// One tier-1 declaration as the exporter realises it. Every type and term
/// here is scoped under the declaration's parameters Δ, at its own Ψ
/// position `abs`.
pub(crate) struct WfDecl {
    pub abs: usize,
    pub tag: u64,
    /// The inductive's key (`list::List`); its constructors, `supf#` and
    /// eliminators live under it.
    pub key: String,
    /// How a use names the inductive: the binding at `abs` for the
    /// declaration's own level profile, a target-only constant
    /// (`list::List::at#1`) for another one.
    pub head: Hx,
    pub ctors: Vec<String>,
    /// The parameters, outermost first, each `(domain, level)` scoped under
    /// the ones before it: a type parameter `A_i : Ty l_i`, or a value
    /// parameter `v : T` (`Trace<R>(E: Events)`).
    pub params: Vec<(Rc<Type>, Level)>,
    pub level: Level,
    pub shape: Rc<Type>,
    /// Under (Δ, x : S).
    pub arity: Rc<Term>,
    /// The shape's `+` nodes in preorder, `spine[0]` the whole shape: the
    /// tree is read off the shape by evaluation, whatever its nesting
    /// ([`SumNode`]).
    pub spine: Vec<SumNode>,
    /// `(P_k, n_k)`: each summand and its literal arity.
    pub summands: Vec<(Rc<Type>, u64)>,
    /// Each summand's injection path: the nodes crossed and whether each
    /// takes its right side, outermost first.
    pub paths: Vec<Vec<(usize, bool)>>,
    /// Ψ up to the declaration, which its own types unfold in.
    pub psi: GlobalCtx,
}

/// One `+` node of a shape: `L + R` at its two levels, and what each side is.
#[derive(Clone)]
pub struct SumNode {
    pub lhs_level: Level,
    pub rhs_level: Level,
    pub lhs: Rc<Type>,
    pub rhs: Rc<Type>,
    pub sides: [Side; 2],
    /// The nodes above this one, as [`WfDecl::paths`] records them.
    pub path: Vec<(usize, bool)>,
}

/// A side of a [`SumNode`]: summand `k`, or node `j`.
#[derive(Clone, Copy)]
pub enum Side {
    Summand(usize),
    Node(usize),
}

/// A shape's `+` tree, by evaluation ([`WfDecl::summands_in`]).
pub(crate) struct Summands {
    pub(crate) nodes: Vec<SumNode>,
    pub(crate) summands: Vec<Rc<Type>>,
    pub(crate) paths: Vec<Vec<(usize, bool)>>,
}

impl WfDecl {
    pub fn supf_key(&self) -> String {
        format!("{}::supf#", self.key)
    }

    pub fn elim_key(&self, motive: u64) -> String {
        format!("{}::elim#{motive}", self.key)
    }

    fn np(&self) -> u32 {
        self.params.len() as u32
    }

    /// The type parameters' levels: which profile this realisation is.
    fn profile(&self) -> R<Vec<u64>> {
        self.params.iter().filter_map(|(dom, _)| if let Type::Ty(l) = &**dom { Some(lvl(l).map(|l| l.0)) } else { None }).collect()
    }

    /// `Wf(S; n)` weakened past `by` binders beyond Δ.
    fn wf_at(&self, by: u32) -> Type {
        Type::Wf {
            level: self.level.clone(),
            shape: Rc::new(self.shape.shift_local(by)),
            arity: Rc::new(self.arity.shift_local_above(by, 1)),
        }
    }

    /// `t`, injected into the whole shape along `path` (outermost first);
    /// the annotations are weakened past `by` binders.
    fn wrap_path(&self, path: &[(usize, bool)], mut t: Term, by: u32) -> Term {
        for &(j, right) in path.iter().rev() {
            let node = &self.spine[j];
            let (lhs_level, rhs_level) = (node.lhs_level.clone(), node.rhs_level.clone());
            let (lhs, rhs) = (Rc::new(node.lhs.shift_local(by)), Rc::new(node.rhs.shift_local(by)));
            let val = Rc::new(t);
            t = if right {
                Term::Inr { lhs_level, rhs_level, lhs, rhs, val }
            } else {
                Term::Inl { lhs_level, rhs_level, lhs, rhs, val }
            };
        }
        t
    }

    /// `t : L + R`, the value at spine node `j`, injected into the whole
    /// shape; the annotations are weakened past `by` binders.
    fn wrap(&self, j: usize, t: Term, by: u32) -> Term {
        self.wrap_path(&self.spine[j].path, t, by)
    }

    /// Summand `k`'s injection of `t : P_k` into the shape.
    fn inj(&self, k: usize, t: Term, by: u32) -> Term {
        self.wrap_path(&self.paths[k], t, by)
    }
}

/// The declarations met so far, and what the declaration being translated
/// asked for: eliminators (by declaration key and motive level), and
/// realisations at another level profile, which it declares first.
pub(crate) struct WfTable<'s> {
    /// Each declaration at its own profile, by nominal tag.
    pub by_tag: RefCell<HashMap<u64, Rc<WfDecl>>>,
    /// Every realisation, the other profiles' included, by key.
    pub by_key: RefCell<HashMap<String, Rc<WfDecl>>>,
    pub wanted: RefCell<Vec<(String, u64)>>,
    pub emitted: RefCell<HashSet<(String, u64)>>,
    /// The declarations the current binding added: the realisations (as
    /// the inductive and its `supf#`) and the eliminators it emits.
    pub fresh: RefCell<Vec<Aux>>,
    created: RefCell<Vec<String>>,
    created_tags: RefCell<Vec<u64>>,
    pub emitted_here: RefCell<Vec<(String, u64)>>,
    /// Ψ whole, which another profile's code function is scoped in.
    full: GlobalCtx,
    tycode_at: &'s dyn Fn(u64, &[Level]) -> Option<(String, Term)>,
    ctors: &'s dyn Fn(u64) -> Option<Vec<String>>,
}

impl<'s> WfTable<'s> {
    pub fn new(src: &Source<'s>) -> WfTable<'s> {
        WfTable {
            by_tag: RefCell::default(),
            by_key: RefCell::default(),
            wanted: RefCell::default(),
            emitted: RefCell::default(),
            fresh: RefCell::default(),
            created: RefCell::default(),
            created_tags: RefCell::default(),
            emitted_here: RefCell::default(),
            full: src.psi.prefix(src.psi.bindings.len()),
            tycode_at: src.tycode_at,
            ctors: src.ctors,
        }
    }

    /// End a binding: what it added stays when it was exported and is
    /// forgotten when it was refused, since a refused binding's `before`
    /// is never printed.
    pub fn settle(&self, exported: bool) {
        self.wanted.borrow_mut().clear();
        self.fresh.borrow_mut().clear();
        let created = std::mem::take(&mut *self.created.borrow_mut());
        let emitted = std::mem::take(&mut *self.emitted_here.borrow_mut());
        let tags = std::mem::take(&mut *self.created_tags.borrow_mut());
        if !exported {
            let mut by_tag = self.by_tag.borrow_mut();
            for tag in tags {
                by_tag.remove(&tag);
            }
            let mut by_key = self.by_key.borrow_mut();
            for key in created {
                by_key.remove(&key);
            }
            let mut done = self.emitted.borrow_mut();
            for e in emitted {
                done.remove(&e);
            }
        }
    }
}

/// A parameter's argument, read off an instance: a type (and the level the
/// instance has it at, where an annotation says), or a value.
#[derive(Clone)]
enum Arg {
    Ty(Type, Option<Level>),
    Tm(Term),
}

fn var(i: u32) -> Rc<Term> {
    Rc::new(Term::Var(LocalVar(i)))
}

fn lit(n: u64) -> Rc<Term> {
    Rc::new(if n == 0 { Term::Zero } else { Term::NatLit(Numeral::from(n)) })
}

fn fin(n: u64) -> Type {
    Type::Fin { len: lit(n) }
}

impl Tr<'_> {
    /// Translate a piece of a definition this module writes, which sits
    /// under `depth` binders the translation did not enter itself.
    fn ty_at(&self, depth: u32, t: &Type) -> R<Hx> {
        self.at_depth(depth, || self.ty(t))
    }

    fn tm_at(&self, depth: u32, t: &Term) -> R<Hx> {
        self.at_depth(depth, || self.tm(t))
    }

    fn at_depth<T>(&self, depth: u32, f: impl FnOnce() -> R<T>) -> R<T> {
        debug_assert!(self.ctx.borrow().is_empty(), "a written definition is translated from the top");
        self.ctx.borrow_mut().extend((0..depth).map(|_| None));
        (0..depth).for_each(|_| self.memo.borrow_mut().push(None));
        let out = f();
        self.ctx.borrow_mut().clear();
        self.memo.borrow_mut().ids.clear();
        out
    }

    /// Reduction needs a context as long as the term's own (a global's
    /// `·^k` weakening addresses it); the entries' types are never read.
    fn dummy(depth: u32) -> LocalCtx {
        (0..depth).fold(LocalCtx::nil(), |g, _| g.extended(Rc::new(Type::Nat), Level::Zero))
    }

    fn whnf_in(psi: &GlobalCtx, t: &Type, depth: u32) -> Option<Type> {
        whnf_type_delta(t, &Self::dummy(depth), Defs::transparent(psi), FUEL).ok()
    }

    fn nat_in(psi: &GlobalCtx, t: &Term, depth: u32) -> Option<u64> {
        match whnf_term_delta(t, &Self::dummy(depth), Defs::transparent(psi), FUEL).ok()? {
            Term::Zero => Some(0),
            Term::NatLit(n) => n.as_u64(),
            Term::Succ(n) => Some(1 + Self::nat_in(psi, &n, depth)?),
            _ => None,
        }
    }

    /// The shape's `+` tree and its summands, by evaluation: a side that
    /// evaluates to a `+` is a node, any other side a summand (a payload
    /// starts with its nominal tag, so it is never a sum). A right summand is
    /// kept as evaluated, a left one as written.
    fn summands_in(psi: &GlobalCtx, shape: &Type, depth: u32) -> Option<Summands> {
        let mut out = Summands { nodes: Vec::new(), summands: Vec::new(), paths: Vec::new() };
        let root = Self::whnf_in(psi, shape, depth)?;
        // Preorder, the left side first, so the summands come out in
        // declaration order and a node's children number after it.
        fn walk(whnf: &dyn Fn(&Type) -> Option<Type>, cur: Type, written: Option<Rc<Type>>, path: Vec<(usize, bool)>, out: &mut Summands) -> Option<Side> {
            let Type::Sum { lhs_level, rhs_level, lhs, rhs } = cur else {
                out.summands.push(written.unwrap_or_else(|| Rc::new(cur)));
                out.paths.push(path);
                return Some(Side::Summand(out.summands.len() - 1));
            };
            let j = out.nodes.len();
            out.nodes.push(SumNode {
                lhs_level,
                rhs_level,
                lhs: Rc::clone(&lhs),
                rhs: Rc::clone(&rhs),
                sides: [Side::Summand(0); 2],
                path: path.clone(),
            });
            let step = |right| path.iter().copied().chain([(j, right)]).collect::<Vec<_>>();
            // A left side that does not evaluate is a summand, as written.
            let lhs_whnf = whnf(&lhs).unwrap_or_else(|| (*lhs).clone());
            let l = walk(whnf, lhs_whnf, Some(lhs), step(false), out)?;
            let r = walk(whnf, whnf(&rhs)?, None, step(true), out)?;
            out.nodes[j].sides = [l, r];
            Some(Side::Node(j))
        }
        walk(&|t| Self::whnf_in(psi, t, depth), root, None, Vec::new(), &mut out)?;
        Some(out)
    }

    /// The nominal tag of a shape: the literal its first payload starts with.
    pub(crate) fn tag_in(psi: &GlobalCtx, shape: &Type, depth: u32) -> Option<u64> {
        let tree = Self::summands_in(psi, shape, depth)?;
        let Type::Sigma { fst, .. } = Self::whnf_in(psi, &tree.summands[0], depth)? else { return None };
        let Type::SEq { lhs, .. } = Self::whnf_in(psi, &fst, depth)? else { return None };
        Self::nat_in(psi, &lhs, depth)
    }

    /// Register the binding being translated when it is a tier-1 type code,
    /// `λ(A : Ty l)…(v : T)…. Wf(x : S). n`. `None` for any other binding.
    pub(crate) fn register_wf(&self, key: Option<&str>, body: &Term, ctors: Option<Vec<String>>) -> R<Option<Rc<WfDecl>>> {
        let base = key.map(|k| k.trim_end_matches("#tycode_fn").trim_end_matches("#tycode").to_string());
        let key = base.unwrap_or_else(|| format!("g{}", self.at));
        let Some(d) = self.wf_decl(key, Hx::Global(self.at), body, ctors)? else { return Ok(None) };
        let d = Rc::new(d);
        self.wf.by_tag.borrow_mut().insert(d.tag, Rc::clone(&d));
        self.wf.by_key.borrow_mut().insert(d.key.clone(), Rc::clone(&d));
        Ok(Some(d))
    }

    /// The realisation a code function `body` describes, named `key` and
    /// used as `head`, scoped at this translation's position.
    fn wf_decl(&self, key: String, head: Hx, body: &Term, ctors: Option<Vec<String>>) -> R<Option<WfDecl>> {
        let mut params = Vec::new();
        let mut cur = body;
        while let Term::Lam { dom, dom_level, body, .. } = cur {
            params.push((Rc::clone(dom), dom_level.clone()));
            cur = body;
        }
        let Term::TmWf { level, shape, arity } = cur else { return Ok(None) };
        let shape = Rc::new(Type::El { level: level.clone(), tm: Rc::clone(shape) });
        let psi = self.psi;
        let np = params.len() as u32;
        let Some(tree) = Self::summands_in(psi, &shape, np) else { return refuse("Wf shape does not evaluate to a sum") };
        let Some(tag) = Self::tag_in(psi, &shape, np) else { return refuse("Wf shape carries no nominal tag") };
        let mut d = WfDecl {
            abs: self.at,
            tag,
            ctors: Vec::new(),
            key,
            head,
            params,
            level: level.clone(),
            shape,
            arity: Rc::clone(arity),
            spine: tree.nodes,
            summands: Vec::new(),
            paths: tree.paths,
            psi: psi.clone(),
        };
        for (k, p) in tree.summands.into_iter().enumerate() {
            let at = d.arity.inst_top(1, &d.inj(k, Term::Var(LocalVar(0)), 1));
            let Some(n) = Self::nat_in(psi, &at, np + 1) else { return refuse("Wf arity depends on the payload") };
            d.summands.push((p, n));
        }
        let names = ctors.filter(|c| c.len() == d.summands.len());
        d.ctors = (0..d.summands.len())
            .map(|k| format!("{}::{}", d.key, names.as_ref().map_or_else(|| format!("c{k}"), |c| c[k].clone())))
            .collect();
        Ok(Some(d))
    }

    /// `base` realised at another type-parameter level profile: its own
    /// native inductive (`list::List::at#1`), from the code function the
    /// elaborator lowers at that profile. The library is level-monomorphic,
    /// so a realisation per profile used stands in for one level-polymorphic
    /// inductive, and works the same in both targets.
    fn realise_at(&self, base: &WfDecl, profile: &[u64]) -> R<Rc<WfDecl>> {
        let key = format!("{}::at#{}", base.key, profile.iter().map(u64::to_string).collect::<Vec<_>>().join("_"));
        if let Some(d) = self.wf.by_key.borrow().get(&key) {
            return Ok(Rc::clone(d));
        }
        let levels: Vec<Level> = profile.iter().map(|&l| Level::constant(l)).collect();
        let Some((_, code)) = (self.wf.tycode_at)(base.tag, &levels) else {
            return refuse("Wf instance at a level other than its declaration's");
        };
        let names = base.ctors.iter().map(|c| c.rsplit("::").next().unwrap_or(c).to_string()).collect();
        self.realise(key, base.tag, &code, Some(names), false)
    }

    /// A declaration Ψ has no code binding for (its own code declined at
    /// registration, so every use spells it inline), realised from the
    /// code the elaborator lowers for it now and named as the declaration.
    /// Only a declaration with no type parameters: with them, which profile
    /// to ask for is not known before there is a template to walk.
    fn realise_unmet(&self, tag: u64) -> R<Rc<WfDecl>> {
        let Some((key, code)) = (self.wf.tycode_at)(tag, &[]) else {
            return refuse("Wf instance of a declaration the exporter has not met");
        };
        self.realise(key, tag, &code, (self.wf.ctors)(tag), true)
    }

    /// The realisation of `code` (closed in Ψ whole) as the native inductive
    /// `key`, declared with its `supf#` just before the binding that first
    /// needs it; its eliminators are keyed by it like any other's. `own`:
    /// it is the declaration at its own profile, which uses find by tag.
    fn realise(&self, key: String, tag: u64, code: &Term, ctors: Option<Vec<String>>, own: bool) -> R<Rc<WfDecl>> {
        let full = &self.wf.full;
        let tr = Tr { at: full.bindings.len(), psi: full, ctx: RefCell::new(Vec::new()), wf: self.wf, memo: RefCell::default() };
        let Some(d) = tr.wf_decl(key.clone(), Hx::Named(key.clone(), vec![]), code, ctors)? else {
            return refuse("Wf instance whose declaration's code is not a Wf");
        };
        if d.tag != tag {
            return refuse("Wf instance whose declaration's code is another declaration's");
        }
        // `Π Δ. Ty l`, the inductive's statement.
        let ty = Self::param_pis(&d, &Level::succ(d.level.clone()), Type::Ty(d.level.clone()));
        // Registered first: its own `supf#` names it.
        let d = Rc::new(d);
        self.wf.by_key.borrow_mut().insert(key.clone(), Rc::clone(&d));
        self.wf.created.borrow_mut().push(key.clone());
        if own {
            self.wf.by_tag.borrow_mut().insert(tag, Rc::clone(&d));
            self.wf.created_tags.borrow_mut().push(tag);
        }
        let decl = tr.wf_inductive(&d, tr.ty(&ty)?)?;
        let mut fresh = self.wf.fresh.borrow_mut();
        fresh.push(Aux { name: key, ty: decl.ty, body: None, inductive: decl.inductive });
        fresh.extend(decl.after);
        Ok(d)
    }

    /// The parameter a template variable at `k` binders deep is, if it is
    /// one: its index into `d.params`.
    fn param_at(d: &WfDecl, v: u32, k: u32) -> Option<usize> {
        (v >= k && v - k < d.np()).then(|| (d.np() - 1 - (v - k)) as usize)
    }

    /// Walk a declaration's type (`tmpl`, under Δ) beside an instance's
    /// (`inst`, here), recording each parameter's argument where the
    /// declaration has the parameter itself; `at` is the level the
    /// instance's annotation gives `inst`. The two are compared as spelled
    /// first, which is what finds a value parameter at a closed argument
    /// (`E.Cmd` beside `Linux.Cmd`, which evaluation would take apart), and
    /// after evaluation where the spellings part.
    #[allow(clippy::too_many_arguments)]
    fn bind_params(&self, d: &WfDecl, tmpl: &Type, inst: &Type, at: Option<&Level>, k: u32, out: &mut [Option<Arg>], fuel: &mut u32) {
        if *fuel == 0 {
            return;
        }
        *fuel -= 1;
        let same = std::mem::discriminant(tmpl) == std::mem::discriminant(inst);
        if same {
            self.bind_node(d, tmpl, inst, at, k, out, fuel);
        }
        if !same || matches!(tmpl, Type::El { .. }) {
            let depth = self.ctx.borrow().len() as u32;
            let (Some(t), Some(i)) = (Self::whnf_in(&d.psi, tmpl, d.np() + k), Self::whnf_in(self.psi, inst, depth + k)) else { return };
            self.bind_node(d, &t, &i, at, k, out, fuel);
        }
    }

    /// One step of [`Self::bind_params`], at two nodes taken as they are.
    #[allow(clippy::too_many_arguments)]
    fn bind_node(&self, d: &WfDecl, t: &Type, i: &Type, at: Option<&Level>, k: u32, out: &mut [Option<Arg>], fuel: &mut u32) {
        // Back out of the binders walked under; a field type that mentions
        // one is no argument, and Lean says so.
        let back = |i: &Type| (0..k).fold(i.clone(), |t, _| t.inst_top(0, &Term::Zero));
        match (t, i) {
            (Type::El { tm, .. }, _) if matches!(&**tm, Term::Var(LocalVar(v)) if Self::param_at(d, *v, k).is_some()) => {
                let Term::Var(LocalVar(v)) = &**tm else { unreachable!() };
                let slot = &mut out[Self::param_at(d, *v, k).expect("a parameter")];
                if slot.is_none() {
                    let level = match i {
                        Type::El { level, .. } => Some(level.clone()),
                        _ => at.cloned(),
                    };
                    *slot = Some(Arg::Ty(back(i), level));
                }
            }
            (Type::El { tm: a, .. }, Type::El { tm: b, .. }) => self.bind_term(d, a, b, k, out, fuel),
            (Type::Sigma { fst: a, snd: b, .. }, Type::Sigma { fst_level: la, snd_level: lb, fst: a2, snd: b2 })
            | (Type::Pi { dom: a, cod: b, .. }, Type::Pi { dom_level: la, cod_level: lb, dom: a2, cod: b2 })
            | (Type::W { shape: a, pos: b, .. }, Type::W { shape_level: la, pos_level: lb, shape: a2, pos: b2 }) => {
                self.bind_params(d, a, a2, Some(la), k, out, fuel);
                self.bind_params(d, b, b2, Some(lb), k + 1, out, fuel);
            }
            (Type::Sum { lhs: a, rhs: b, .. }, Type::Sum { lhs_level: la, rhs_level: lb, lhs: a2, rhs: b2 }) => {
                self.bind_params(d, a, a2, Some(la), k, out, fuel);
                self.bind_params(d, b, b2, Some(lb), k, out, fuel);
            }
            (Type::Id { ty: a, lhs, rhs, .. }, Type::Id { level, ty: a2, lhs: lhs2, rhs: rhs2 })
            | (Type::SEq { ty: a, lhs, rhs, .. }, Type::SEq { level, ty: a2, lhs: lhs2, rhs: rhs2 }) => {
                self.bind_params(d, a, a2, Some(level), k, out, fuel);
                self.bind_term(d, lhs, lhs2, k, out, fuel);
                self.bind_term(d, rhs, rhs2, k, out, fuel);
            }
            (Type::Vec { elem: a, len, .. }, Type::Vec { level, elem: a2, len: len2 }) => {
                self.bind_params(d, a, a2, Some(level), k, out, fuel);
                self.bind_term(d, len, len2, k, out, fuel);
            }
            (Type::Squash { ty: a, .. }, Type::Squash { level, ty: a2 }) | (Type::Wf { shape: a, .. }, Type::Wf { level, shape: a2, .. }) => {
                self.bind_params(d, a, a2, Some(level), k, out, fuel)
            }
            (Type::GlobalTy { subst: s, .. }, Type::GlobalTy { subst: s2, .. }) => {
                for (a, b) in s.terms.iter().zip(&s2.terms) {
                    self.bind_term(d, a, b, k, out, fuel);
                }
            }
            _ => {}
        }
    }

    /// [`Self::bind_params`] over terms, as spelled: a value parameter is
    /// recorded where the template has the variable, a type parameter where
    /// it has the code. Applications, projections and the substitutions of
    /// globals are walked; a node the two spell differently ends the walk
    /// there.
    #[allow(clippy::too_many_arguments)]
    fn bind_term(&self, d: &WfDecl, tmpl: &Term, inst: &Term, k: u32, out: &mut [Option<Arg>], fuel: &mut u32) {
        if *fuel == 0 {
            return;
        }
        *fuel -= 1;
        match (tmpl, inst) {
            (Term::Var(LocalVar(v)), _) => {
                let Some(p) = Self::param_at(d, *v, k) else { return };
                if out[p].is_none() {
                    let back = (0..k).fold(inst.clone(), |t, _| t.inst_top(0, &Term::Zero));
                    out[p] = Some(match &*d.params[p].0 {
                        Type::Ty(l) => Arg::Ty(Type::El { level: l.clone(), tm: Rc::new(back) }, None),
                        _ => Arg::Tm(back),
                    });
                }
            }
            (Term::App { fun: f, arg: a, .. } | Term::AppAt { fun: f, arg: a }, Term::App { fun: f2, arg: a2, .. } | Term::AppAt { fun: f2, arg: a2 }) => {
                self.bind_term(d, f, f2, k, out, fuel);
                self.bind_term(d, a, a2, k, out, fuel);
            }
            (Term::Fst { pair: a, .. } | Term::FstAt { pair: a }, Term::Fst { pair: a2, .. } | Term::FstAt { pair: a2 })
            | (Term::Snd { pair: a, .. } | Term::SndAt { pair: a }, Term::Snd { pair: a2, .. } | Term::SndAt { pair: a2 })
            | (Term::Succ(a), Term::Succ(a2)) => self.bind_term(d, a, a2, k, out, fuel),
            (Term::GlobalTm { subst: s, .. }, Term::GlobalTm { subst: s2, .. }) => {
                for (a, b) in s.terms.iter().zip(&s2.terms) {
                    self.bind_term(d, a, b, k, out, fuel);
                }
            }
            _ => {}
        }
    }

    /// Which declaration `Wf(shape; arity)` is, and its arguments. A use at
    /// the declaration's own level profile is the declaration; one at
    /// another (`List<A → B → Type>`) is that profile's realisation.
    fn recognise(&self, level: &Level, shape: &Type) -> R<(Rc<WfDecl>, Vec<Hx>)> {
        let depth = self.ctx.borrow().len() as u32;
        let Some(tag) = Self::tag_in(self.psi, shape, depth) else { return refuse(WF) };
        let met = self.wf.by_tag.borrow().get(&tag).cloned();
        let base = match met {
            Some(base) => base,
            None => self.realise_unmet(tag)?,
        };
        let mut out = vec![None; base.params.len()];
        if !out.is_empty() {
            let Some(inst) = Self::summands_in(self.psi, shape, depth) else { return refuse(WF) };
            let mut fuel = 4096;
            for ((tmpl, _), inst) in base.summands.iter().zip(&inst.summands) {
                self.bind_params(&base, tmpl, inst, None, 0, &mut out, &mut fuel);
            }
        }
        // Each type parameter's level is its argument's, where an annotation
        // of the instance says; the declaration's own where none does (the
        // argument is then refused below, or the level check is).
        let mut profile = Vec::new();
        for ((dom, _), a) in base.params.iter().zip(&out) {
            if let Type::Ty(l) = &**dom {
                profile.push(lvl(match a {
                    Some(Arg::Ty(_, Some(at))) => at,
                    _ => l,
                })?.0);
            }
        }
        let d = if profile == base.profile()? { base } else { self.realise_at(&base, &profile)? };
        if lvl(level)? != lvl(&d.level)? {
            return refuse("Wf instance at a level other than its declaration's");
        }
        let args = out
            .iter()
            .map(|a| match a {
                Some(Arg::Ty(t, _)) => self.ty(t),
                Some(Arg::Tm(t)) => self.tm(t),
                None => refuse("Wf parameter that no field of the instance determines"),
            })
            .collect::<R<Vec<_>>>()?;
        Ok((d, args))
    }

    /// `⟦Wf(x : S). n⟧ = D args`.
    pub(crate) fn wf_type(&self, level: &Level, shape: &Type) -> R<Hx> {
        let (d, args) = self.recognise(level, shape)?;
        Ok(app(d.head.clone(), args))
    }

    /// `⟦sup_f(a; cs)⟧ = D::supf# args a cs`.
    pub(crate) fn wf_supf(&self, level: &Level, shape: &Type, label: &Term, children: &Term) -> R<Hx> {
        let (d, mut args) = self.recognise(level, shape)?;
        args.push(self.tm(label)?);
        args.push(self.tm(children)?);
        Ok(app(Hx::Named(d.supf_key(), vec![]), args))
    }

    /// `⟦elim_Wf(z. M; a cs ih. s; t)⟧ = D::elim#l' args (λz. M) (λa cs ih. s) t`,
    /// with the step's binder types the kernel's own telescope.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn wf_elim(
        &self,
        level: &Level,
        motive_level: &Level,
        shape: &Rc<Type>,
        arity: &Rc<Term>,
        motive: &Type,
        step: &Term,
        scrut: &Term,
    ) -> R<Hx> {
        let (d, mut args) = self.recognise(level, shape)?;
        let ml = lvl(motive_level)?.0;
        if !self.wf.emitted.borrow().contains(&(d.key.clone(), ml)) {
            self.wf.wanted.borrow_mut().push((d.key.clone(), ml));
        }
        let wf = Type::Wf { level: level.clone(), shape: Rc::clone(shape), arity: Rc::clone(arity) };
        let (cs_ty, ih_ty) = telescope(level, motive_level, &wf, arity, motive);
        args.push(self.bound(&wf, || self.ty(motive))?);
        args.push(self.bound(shape, || self.bound(&cs_ty, || self.bound(&ih_ty, || self.tm(step))))?);
        args.push(self.tm(scrut)?);
        Ok(app(Hx::Named(d.elim_key(ml), vec![]), args))
    }

    // ---- the declarations the realisation adds ----

    fn param_vars(d: &WfDecl, above: u32) -> Vec<Hx> {
        (0..d.np()).map(|t| Hx::Var(d.np() - 1 - t + above)).collect()
    }

    /// The parameters' domains, outermost first: `Type l_i`, or a value
    /// parameter's type under the parameters before it.
    fn param_doms(&self, d: &WfDecl) -> R<Vec<Hx>> {
        d.params.iter().enumerate().map(|(i, (dom, _))| self.ty_at(i as u32, dom)).collect()
    }

    /// `λ(A_1 : Type l_1)…. body`.
    fn param_lams(&self, d: &WfDecl, body: Hx) -> R<Hx> {
        Ok(self.param_doms(d)?.into_iter().rev().fold(body, |b, dom| lam(dom, b)))
    }

    /// `Π Δ. t` over a kernel type under Δ.
    fn param_pis(d: &WfDecl, cod_level: &Level, t: Type) -> Type {
        d.params.iter().rev().fold(t, |cod, (dom, l)| Type::Pi { dom_level: l.clone(), cod_level: cod_level.clone(), dom: Rc::clone(dom), cod: Rc::new(cod) })
    }

    /// The inductive: its statement and its constructors' types.
    pub(crate) fn wf_inductive(&self, d: &WfDecl, ty: Hx) -> R<Decl> {
        let (mut ctors, mut fields) = (Vec::new(), Vec::new());
        let doms = self.param_doms(d)?;
        for (k, (p, n)) in d.summands.iter().enumerate() {
            // Π Δ. Π(p : P_k). Π(x_1 … x_n : D Δ). D Δ, innermost first. A
            // closed singleton payload is no field: Rocq has no unit η to
            // convert a bound one with its canonical element (design §5.3).
            let field = self.canon_term(p).is_none();
            let q = field as u32;
            let mut t = app(d.head.clone(), Self::param_vars(d, q + *n as u32));
            for i in (0..*n as u32).rev() {
                t = Hx::Pi(Rc::new(app(d.head.clone(), Self::param_vars(d, q + i))), Rc::new(t));
            }
            if field {
                t = Hx::Pi(Rc::new(self.ty_at(d.np(), p)?), Rc::new(t));
            }
            for dom in doms.iter().rev() {
                t = Hx::Pi(Rc::new(dom.clone()), Rc::new(t));
            }
            ctors.push((d.ctors[k].clone(), t));
            fields.push((q, *n as u32));
        }
        Ok(Decl {
            abs: d.abs,
            name: Some(d.key.clone()),
            ty,
            body: None,
            inductive: Some(Inductive { nparams: d.params.len(), ctors, fields }),
            before: Vec::new(),
            after: vec![self.wf_supf_def(d)?],
        })
    }

    /// `D::supf# := λ Δ a cs. (case a of k ↦ λcs. c_k Δ p (fst cs) …) cs`.
    fn wf_supf_def(&self, d: &WfDecl) -> R<Aux> {
        // Π Δ. Π(a : S). Π(cs : Vec(D; n[a])). D, as a kernel type.
        let cs_ty = Type::Vec { level: d.level.clone(), elem: Rc::new(d.wf_at(1)), len: Rc::clone(&d.arity) };
        let ty = Type::Pi {
            dom_level: d.level.clone(),
            cod_level: d.level.clone(),
            dom: Rc::clone(&d.shape),
            cod: Rc::new(Type::Pi {
                dom_level: d.level.clone(),
                cod_level: d.level.clone(),
                dom: Rc::new(cs_ty.clone()),
                cod: Rc::new(d.wf_at(2)),
            }),
        };
        let ty = Self::param_pis(d, &d.level, ty);
        let chain = if d.summands.len() == 1 { self.supf_arm(d, 0, 0, None)? } else { self.supf_chain(d, 0)? };
        let body = app(chain, vec![Hx::Var(0)]);
        let body = lam(self.ty_at(d.np(), &d.shape)?, lam(self.ty_at(d.np() + 1, &cs_ty)?, body));
        Ok(Aux { name: d.supf_key(), ty: self.ty(&ty)?, body: Some(self.param_lams(d, body)?), inductive: None })
    }

    /// The case at spine node `j`, in (Δ, a, cs, r_1 … r_t) for the `t`
    /// nodes above it, on `a` at the root and on `r_t` below it. Its value is
    /// `Π(cs : Vec(D; n)). D`.
    fn supf_chain(&self, d: &WfDecl, j: usize) -> R<Hx> {
        let node = &d.spine[j];
        let (ll, rl, l, r) = (&node.lhs_level, &node.rhs_level, &node.lhs, &node.rhs);
        let depth = node.path.len();
        let by = depth as u32 + 2;
        let scrut = Hx::Var(if j == 0 { 1 } else { 0 });
        // Motive in (Δ, a, cs, r…, z).
        let zfull = d.wrap(j, Term::Var(LocalVar(0)), by + 1);
        let motive = Type::Pi {
            dom_level: d.level.clone(),
            cod_level: d.level.clone(),
            dom: Rc::new(Type::Vec { level: d.level.clone(), elem: Rc::new(d.wf_at(by + 1)), len: Rc::new(d.arity.inst_top(by + 1, &zfull)) }),
            cod: Rc::new(d.wf_at(by + 2)),
        };
        let sum = Type::Sum { lhs_level: ll.clone(), rhs_level: rl.clone(), lhs: Rc::new(l.shift_local(by)), rhs: Rc::new(r.shift_local(by)) };
        let at = d.np() + by;
        let motive = lam(self.ty_at(at, &sum)?, self.ty_at(at + 1, &motive)?);
        let (lt, rt) = (self.ty_at(at, &l.shift_local(by))?, self.ty_at(at, &r.shift_local(by))?);
        // A summand whose payload is a closed singleton has its arm at the
        // canonical element, under no binder (`caseL`/`caseR`/`caseLR`).
        let canon = |side: Side, t: &Type| match side {
            Side::Summand(_) => self.canon_term(t),
            Side::Node(_) => None,
        };
        let (cl, cr) = (canon(node.sides[0], l), canon(node.sides[1], r));
        let arm = |side: Side, c: &Option<Term>, t: &Hx| -> R<Hx> {
            Ok(match (side, c) {
                (Side::Summand(k), Some(c)) => self.supf_arm(d, k, depth, Some(c.clone()))?,
                (Side::Summand(k), None) => lam(t.clone(), self.supf_arm(d, k, depth + 1, None)?),
                (Side::Node(m), _) => lam(t.clone(), self.supf_chain(d, m)?),
            })
        };
        let left = arm(node.sides[0], &cl, &lt)?;
        let right = arm(node.sides[1], &cr, &rt)?;
        let levels = [ll, rl, &d.level];
        let single = |t: &Type| -> R<(Hx, Hx)> { Ok((self.canon(t).expect("a singleton")?, self.eta(t).expect("a singleton")?)) };
        match (cl.is_some(), cr.is_some()) {
            (true, true) => {
                let ((ca, ea), (cb, eb)) = (single(l)?, single(r)?);
                konst("caseLR", &levels, vec![lt, rt, ca, cb, ea, eb, motive, left, right, scrut])
            }
            (true, false) => {
                let (ca, ea) = single(l)?;
                konst("caseL", &levels, vec![lt, rt, ca, ea, motive, left, right, scrut])
            }
            (false, true) => {
                let (cb, eb) = single(r)?;
                konst("caseR", &levels, vec![lt, rt, cb, eb, motive, left, right, scrut])
            }
            (false, false) => konst("case", &levels, vec![lt, rt, motive, left, right, scrut]),
        }
    }

    /// `λ(cs : Vec(D; n_k)). c_k Δ p (fst cs) (fst (snd cs)) …`, in
    /// (Δ, a, cs, r_1 … r_depth) whose last binder is `p : P_k` (or `a`
    /// itself when the shape has one summand).
    /// `single` is the payload's canonical element when it is a closed
    /// singleton under no binder of its own; a singleton payload is no
    /// constructor field either way.
    fn supf_arm(&self, d: &WfDecl, k: usize, depth: usize, single: Option<Term>) -> R<Hx> {
        let n = d.summands[k].1;
        // In (Δ, a, cs, r…, cs'): the binders beyond Δ.
        let by = depth as u32 + 2;
        let field = self.canon_term(&d.summands[k].0).is_none();
        let p = match single {
            Some(c) => c,
            None if depth == 0 => Term::Var(LocalVar(1)),
            None => Term::Var(LocalVar(0)),
        };
        let cs_ty = Type::Vec {
            level: d.level.clone(),
            elem: Rc::new(d.wf_at(by)),
            len: Rc::new(d.arity.inst_top(by, &d.inj(k, p.clone(), by))),
        };
        let mut args = Self::param_vars(d, by + 1);
        let at = d.np() + by;
        if field {
            args.push(self.tm_at(at + 1, &p.shift_local(1))?);
        }
        let mut cur = Term::Var(LocalVar(0));
        for i in 0..n {
            let (fst_ty, snd_ty) = (Rc::new(d.wf_at(by + 1)), Rc::new(Type::Vec { level: d.level.clone(), elem: Rc::new(d.wf_at(by + 2)), len: lit(n - 1 - i) }));
            let fst = Term::Fst { fst_level: d.level.clone(), snd_level: d.level.clone(), fst_ty: Rc::clone(&fst_ty), snd_ty: Rc::clone(&snd_ty), pair: Rc::new(cur.clone()) };
            args.push(self.tm_at(at + 1, &fst)?);
            cur = Term::Snd { fst_level: d.level.clone(), snd_level: d.level.clone(), fst_ty, snd_ty, pair: Rc::new(cur) };
        }
        Ok(lam(self.ty_at(at, &cs_ty)?, app(Hx::Named(d.ctors[k].clone(), vec![]), args)))
    }

    /// `D::elim#l' : Π Δ (M : D → Ty l') (step : …) (t : D). M t`, through
    /// the native recursor.
    pub(crate) fn wf_elim_def(&self, d: &WfDecl, ml: u64) -> R<Aux> {
        let level = &d.level;
        let mlv = (0..ml).fold(Level::Zero, |l, _| Level::succ(l.clone()));
        let m_ty = Type::Pi { dom_level: level.clone(), cod_level: Level::succ(mlv.clone()), dom: Rc::new(d.wf_at(0)), cod: Rc::new(Type::Ty(mlv.clone())) };
        // The motive in (Δ, M, z): El(M z).
        let motive = Type::El {
            level: mlv.clone(),
            tm: Rc::new(Term::App {
                fun: var(1),
                dom_level: level.clone(),
                cod_level: Level::succ(mlv.clone()),
                dom: Rc::new(d.wf_at(2)),
                cod: Rc::new(Type::Ty(mlv.clone())),
                arg: var(0),
            }),
        };
        let shape1 = Rc::new(d.shape.shift_local(1));
        let arity1 = Rc::new(d.arity.shift_local_above(1, 1));
        let wf1 = d.wf_at(1);
        let (cs_ty, ih_ty) = telescope(level, &mlv, &wf1, &arity1, &motive);
        let sup_ac = Term::Supf {
            level: level.clone(),
            shape: Rc::new(shape1.shift_local(2)),
            arity: Rc::new(arity1.shift_local_above(2, 1)),
            label: var(1),
            children: var(0),
        };
        let step_res = motive.inst_top(3, &sup_ac.shift_local(1));
        let step_ty = Type::Pi {
            dom_level: level.clone(),
            cod_level: mlv.clone(),
            dom: Rc::clone(&shape1),
            cod: Rc::new(Type::Pi {
                dom_level: level.clone(),
                cod_level: mlv.clone(),
                dom: Rc::new(cs_ty),
                cod: Rc::new(Type::Pi { dom_level: mlv.clone(), cod_level: mlv.clone(), dom: Rc::new(ih_ty), cod: Rc::new(step_res) }),
            }),
        };
        // M t in (Δ, M, step, t).
        let m_t = Type::El {
            level: mlv.clone(),
            tm: Rc::new(Term::App { fun: var(2), dom_level: level.clone(), cod_level: Level::succ(mlv.clone()), dom: Rc::new(d.wf_at(3)), cod: Rc::new(Type::Ty(mlv.clone())), arg: var(0) }),
        };
        let ty = Type::Pi {
            dom_level: Level::succ(mlv.clone()),
            cod_level: mlv.clone(),
            dom: Rc::new(m_ty.clone()),
            cod: Rc::new(Type::Pi {
                dom_level: mlv.clone(),
                cod_level: mlv.clone(),
                dom: Rc::new(step_ty.clone()),
                cod: Rc::new(Type::Pi { dom_level: level.clone(), cod_level: mlv.clone(), dom: Rc::new(d.wf_at(2)), cod: Rc::new(m_t) }),
            }),
        };
        let ty = Self::param_pis(d, &mlv, ty);
        // λ Δ M step t. D.rec Δ M minor… t
        let mut rec_args = Self::param_vars(d, 3);
        rec_args.push(Hx::Var(2));
        for k in 0..d.summands.len() {
            rec_args.push(self.wf_minor(d, k, &mlv)?);
        }
        rec_args.push(Hx::Var(0));
        let rec = Hx::Named(format!("{}::rec", d.key), vec![ml + 1]);
        let np = d.np();
        let body = lam(self.ty_at(np, &m_ty)?, lam(self.ty_at(np + 1, &step_ty)?, lam(self.ty_at(np + 2, &d.wf_at(2))?, app(rec, rec_args))));
        Ok(Aux { name: d.elim_key(ml), ty: self.ty(&ty)?, body: Some(self.param_lams(d, body)?), inductive: None })
    }

    /// The minor premise for constructor `k`, in (Δ, M, step, t):
    /// `λ p x_1 … x_n ih_1 … ih_n. step (inj_k p) ⟨x_1, …⟩ (λi. case i …)`.
    fn wf_minor(&self, d: &WfDecl, k: usize, mlv: &Level) -> R<Hx> {
        let (p, n) = (&d.summands[k].0, d.summands[k].1);
        let n32 = n as u32;
        let el_m = |m: u32, x: u32, wf_by: u32| Type::El {
            level: mlv.clone(),
            tm: Rc::new(Term::App { fun: var(m), dom_level: d.level.clone(), cod_level: Level::succ(mlv.clone()), dom: Rc::new(d.wf_at(wf_by)), cod: Rc::new(Type::Ty(mlv.clone())), arg: var(x) }),
        };
        // Binder domains, outermost first. A closed singleton payload is no
        // field (`wf_inductive`): the label takes its canonical element.
        let np = d.np();
        let single = self.canon_term(p);
        let q = single.is_none() as u32;
        let mut doms = Vec::new();
        if single.is_none() {
            doms.push(self.ty_at(np + 3, &p.shift_local(3))?);
        }
        for i in 0..n32 {
            doms.push(self.ty_at(np + 3 + q + i, &d.wf_at(3 + q + i))?);
        }
        for i in 1..=n32 {
            doms.push(self.ty_at(np + 3 + q + n32 + i - 1, &el_m(n32 + i + 1 + q, n32 - 1, 3 + q + n32 + i - 1))?);
        }
        // The body, in C = (Δ, M, step, t, [p], x_1 … x_n, ih_1 … ih_n).
        let cdelta = 3 + q + 2 * n32;
        let (step_ix, m_ix) = (2 * n32 + 1 + q, 2 * n32 + 2 + q);
        let label = d.inj(k, single.unwrap_or(Term::Var(LocalVar(2 * n32))), cdelta);
        let mut tuple = Term::Triv { level: d.level.clone() };
        for i in (1..=n).rev() {
            tuple = Term::Pair {
                fst_level: d.level.clone(),
                snd_level: d.level.clone(),
                fst_ty: Rc::new(d.wf_at(cdelta)),
                snd_ty: Rc::new(Type::Vec { level: d.level.clone(), elem: Rc::new(d.wf_at(cdelta + 1)), len: lit(n - i) }),
                fst: var(2 * n32 - i as u32),
                snd: Rc::new(tuple),
            };
        }
        let ih = Term::Lam {
            dom_level: Level::Zero,
            cod_level: mlv.clone(),
            dom: Rc::new(fin(n)),
            body: Rc::new(self.ih_select(d, n, 0, 1, &mut Vec::new(), &tuple, m_ix, cdelta, mlv)),
        };
        let at = np + cdelta;
        let mut body = app(Hx::Var(step_ix), vec![self.tm_at(at, &label)?, self.tm_at(at, &tuple)?, self.tm_at(at, &ih)?]);
        for dom in doms.into_iter().rev() {
            body = lam(dom, body);
        }
        Ok(body)
    }

    /// The induction hypothesis at child `c` onwards, in `C + e` whose
    /// innermost binder is the index into `Fin(rem)`; `wraps` are the
    /// enclosing levels' lengths, outermost first.
    #[allow(clippy::too_many_arguments)]
    fn ih_select(&self, d: &WfDecl, rem: u64, c: u64, e: u32, wraps: &mut Vec<u64>, tuple: &Term, m_ix: u32, cdelta: u32, mlv: &Level) -> Term {
        let total = wraps.first().copied().unwrap_or(rem);
        // The motive, in (C + e, z): M (nth(D; total; tuple; full z)), the
        // index rebuilt through the enclosing levels' `inr`s.
        let mut idx = Term::Var(LocalVar(0));
        for &r in wraps.iter().rev() {
            idx = Term::Inr {
                lhs_level: Level::Zero,
                rhs_level: Level::Zero,
                lhs: Rc::new(Type::Unit { level: Level::Zero }),
                rhs: Rc::new(fin(r - 1)),
                val: Rc::new(idx),
            };
        }
        let at = nth(&d.level, &Rc::new(d.wf_at(cdelta + e + 1)), &lit(total), Rc::new(tuple.shift_local(e + 1)), Rc::new(idx));
        let motive = Rc::new(Type::El {
            level: mlv.clone(),
            tm: Rc::new(Term::App {
                fun: var(m_ix + e + 1),
                dom_level: d.level.clone(),
                cod_level: Level::succ(mlv.clone()),
                dom: Rc::new(d.wf_at(cdelta + e + 1)),
                cod: Rc::new(Type::Ty(mlv.clone())),
                arg: Rc::new(at),
            }),
        });
        if rem == 0 {
            return Term::ElimEmpty { level: mlv.clone(), scrut_level: Level::Zero, motive, scrut: var(0) };
        }
        let ih_c = (total - 1 - c) as u32;
        wraps.push(rem);
        let right = self.ih_select(d, rem - 1, c + 1, e + 1, wraps, tuple, m_ix, cdelta, mlv);
        wraps.pop();
        Term::Case {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            motive_level: mlv.clone(),
            lhs: Rc::new(Type::Unit { level: Level::Zero }),
            rhs: Rc::new(fin(rem - 1)),
            motive,
            case_l: var(ih_c + e + 1),
            case_r: Rc::new(right),
            scrut: var(0),
        }
    }
}

/// `elim_Wf`'s step telescope `(cs, ih)` for `wf = Wf(S; n)` in Γ, with
/// `arity` the `n` scoped at `a`'s position and `motive` in (Γ, z): the
/// kernel's `wf_step_telescope_at`, written with `inst_top` so it needs no Γ.
fn telescope(level: &Level, motive_level: &Level, wf: &Type, arity: &Rc<Term>, motive: &Type) -> (Type, Type) {
    let cs_ty = Type::Vec { level: level.clone(), elem: Rc::new(wf.shift_local(1)), len: Rc::clone(arity) };
    let nth_at_i = nth(level, &Rc::new(wf.shift_local(3)), &Rc::new(arity.shift_local(2)), var(1), var(0));
    let ih_ty = Type::Pi {
        dom_level: Level::Zero,
        cod_level: motive_level.clone(),
        dom: Rc::new(Type::Fin { len: Rc::new(arity.shift_local(1)) }),
        cod: Rc::new(motive.inst_top(3, &nth_at_i)),
    };
    (cs_ty, ih_ty)
}
