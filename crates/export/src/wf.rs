//! `Wf` realised as native Lean inductives (design §5.1,
//! `issues/export-wf-native-inductives.md`).
//!
//! Lean cannot declare the `Wf` former, but each lowered tier-1 declaration
//! can be a native inductive with one constructor per summand of its shape,
//! holding the summand's payload and the children as fields. The exporter
//! meets a declaration as its whole-type code, `D#tycode` or
//! `D#tycode_fn : Π(A : Ty l)…. Ty l := λ…. Wf(x : S). n`, and emits there
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
    pub ctors: Vec<String>,
    /// The parameters' levels, outermost first: `A_i : Ty l_i`.
    pub params: Vec<Level>,
    pub level: Level,
    pub shape: Rc<Type>,
    /// Under (Δ, x : S).
    pub arity: Rc<Term>,
    /// The shape's `+` spine: node `j` is `P_j + R_j`, `R_{m-2} = P_{m-1}`.
    pub spine: Vec<(Level, Level, Rc<Type>, Rc<Type>)>,
    /// `(P_k, n_k)`: each summand and its literal arity.
    pub summands: Vec<(Rc<Type>, u64)>,
    /// Ψ up to the declaration, which its own types unfold in.
    pub psi: GlobalCtx,
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

    /// `Wf(S; n)` weakened past `by` binders beyond Δ.
    fn wf_at(&self, by: u32) -> Type {
        Type::Wf {
            level: self.level.clone(),
            shape: Rc::new(self.shape.shift_local(by)),
            arity: Rc::new(self.arity.shift_local_above(by, 1)),
        }
    }

    /// `t : P_j + R_j`, the value at spine node `upto`, injected into the
    /// whole shape; the annotations are weakened past `by` binders.
    fn wrap(&self, upto: usize, mut t: Term, by: u32) -> Term {
        for j in (0..upto).rev() {
            let (ll, rl, l, r) = &self.spine[j];
            t = Term::Inr {
                lhs_level: ll.clone(),
                rhs_level: rl.clone(),
                lhs: Rc::new(l.shift_local(by)),
                rhs: Rc::new(r.shift_local(by)),
                val: Rc::new(t),
            };
        }
        t
    }

    /// Summand `k`'s injection of `t : P_k` into the shape.
    fn inj(&self, k: usize, t: Term, by: u32) -> Term {
        let m = self.spine.len() + 1;
        if k + 1 < m {
            let (ll, rl, l, r) = &self.spine[k];
            let inl = Term::Inl {
                lhs_level: ll.clone(),
                rhs_level: rl.clone(),
                lhs: Rc::new(l.shift_local(by)),
                rhs: Rc::new(r.shift_local(by)),
                val: Rc::new(t),
            };
            self.wrap(k, inl, by)
        } else {
            self.wrap(m - 1, t, by)
        }
    }
}

/// The declarations met so far, and the eliminators the declaration being
/// translated asked for.
#[derive(Default)]
pub(crate) struct WfTable {
    pub by_tag: RefCell<HashMap<u64, Rc<WfDecl>>>,
    pub wanted: RefCell<Vec<(u64, u64)>>,
    pub emitted: RefCell<HashSet<(u64, u64)>>,
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
        let out = f();
        self.ctx.borrow_mut().clear();
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

    /// The shape's `+` spine and its summands, by evaluation.
    fn summands_in(psi: &GlobalCtx, shape: &Type, depth: u32) -> Option<(Vec<(Level, Level, Rc<Type>, Rc<Type>)>, Vec<Rc<Type>>)> {
        let (mut spine, mut summands) = (Vec::new(), Vec::new());
        let mut cur = Self::whnf_in(psi, shape, depth)?;
        loop {
            match cur {
                Type::Sum { lhs_level, rhs_level, lhs, rhs } => {
                    summands.push(Rc::clone(&lhs));
                    spine.push((lhs_level, rhs_level, lhs, Rc::clone(&rhs)));
                    cur = Self::whnf_in(psi, &rhs, depth)?;
                }
                last => {
                    summands.push(Rc::new(last));
                    return Some((spine, summands));
                }
            }
        }
    }

    /// The nominal tag of a shape: the literal its first payload starts with.
    pub(crate) fn tag_in(psi: &GlobalCtx, shape: &Type, depth: u32) -> Option<u64> {
        let (_, summands) = Self::summands_in(psi, shape, depth)?;
        let Type::Sigma { fst, .. } = Self::whnf_in(psi, &summands[0], depth)? else { return None };
        let Type::SEq { lhs, .. } = Self::whnf_in(psi, &fst, depth)? else { return None };
        Self::nat_in(psi, &lhs, depth)
    }

    /// Register the binding being translated when it is a tier-1 type code,
    /// `λ(A : Ty l)…. Wf(x : S). n`. `None` for any other binding.
    pub(crate) fn register_wf(&self, key: Option<&str>, body: &Term, ctors: Option<Vec<String>>) -> R<Option<Rc<WfDecl>>> {
        let mut params = Vec::new();
        let mut cur = body;
        while let Term::Lam { dom, body, .. } = cur {
            let Type::Ty(l) = &**dom else { return Ok(None) };
            params.push(l.clone());
            cur = body;
        }
        let Term::TmWf { level, shape, arity } = cur else { return Ok(None) };
        let shape = Rc::new(Type::El { level: level.clone(), tm: Rc::clone(shape) });
        let psi = self.psi;
        let np = params.len() as u32;
        let Some((spine, summands)) = Self::summands_in(psi, &shape, np) else { return refuse("Wf shape does not evaluate to a sum") };
        let Some(tag) = Self::tag_in(psi, &shape, np) else { return refuse("Wf shape carries no nominal tag") };
        let base = key.map(|k| k.trim_end_matches("#tycode_fn").trim_end_matches("#tycode").to_string());
        let key = base.unwrap_or_else(|| format!("g{}", self.at));
        let mut d = WfDecl {
            abs: self.at,
            tag,
            ctors: Vec::new(),
            key,
            params,
            level: level.clone(),
            shape,
            arity: Rc::clone(arity),
            spine,
            summands: Vec::new(),
            psi: psi.clone(),
        };
        for (k, p) in summands.into_iter().enumerate() {
            let at = d.arity.inst_top(1, &d.inj(k, Term::Var(LocalVar(0)), 1));
            let Some(n) = Self::nat_in(psi, &at, np + 1) else { return refuse("Wf arity depends on the payload") };
            d.summands.push((p, n));
        }
        let names = ctors.filter(|c| c.len() == d.summands.len());
        d.ctors = (0..d.summands.len())
            .map(|k| format!("{}::{}", d.key, names.as_ref().map_or_else(|| format!("c{k}"), |c| c[k].clone())))
            .collect();
        let d = Rc::new(d);
        self.wf.by_tag.borrow_mut().insert(tag, Rc::clone(&d));
        Ok(Some(d))
    }

    /// Walk a declaration's type (`tmpl`, under Δ) beside an instance's
    /// (`inst`, here), recording each parameter's argument where the
    /// declaration has the parameter itself.
    fn bind_params(&self, d: &WfDecl, tmpl: &Type, inst: &Type, k: u32, out: &mut [Option<Type>], fuel: &mut u32) {
        if *fuel == 0 {
            return;
        }
        *fuel -= 1;
        let depth = self.ctx.borrow().len() as u32;
        let (Some(t), Some(i)) = (Self::whnf_in(&d.psi, tmpl, d.np() + k), Self::whnf_in(self.psi, inst, depth + k)) else { return };
        match (&t, &i) {
            (Type::El { tm, .. }, _) => {
                if let Term::Var(LocalVar(v)) = &**tm {
                    if *v >= k && v - k < d.np() {
                        let slot = &mut out[(d.np() - 1 - (v - k)) as usize];
                        if slot.is_none() {
                            // Back out of the binders walked under; a field
                            // type that mentions one is no argument, and
                            // Lean says so.
                            let at = (0..k).fold(i.clone(), |t, _| t.inst_top(0, &Term::Zero));
                            *slot = Some(at);
                        }
                    }
                }
            }
            (Type::Sigma { fst: a, snd: b, .. }, Type::Sigma { fst: a2, snd: b2, .. })
            | (Type::Pi { dom: a, cod: b, .. }, Type::Pi { dom: a2, cod: b2, .. })
            | (Type::W { shape: a, pos: b, .. }, Type::W { shape: a2, pos: b2, .. }) => {
                self.bind_params(d, a, a2, k, out, fuel);
                self.bind_params(d, b, b2, k + 1, out, fuel);
            }
            (Type::Sum { lhs: a, rhs: b, .. }, Type::Sum { lhs: a2, rhs: b2, .. }) => {
                self.bind_params(d, a, a2, k, out, fuel);
                self.bind_params(d, b, b2, k, out, fuel);
            }
            (Type::Vec { elem: a, .. }, Type::Vec { elem: a2, .. })
            | (Type::Id { ty: a, .. }, Type::Id { ty: a2, .. })
            | (Type::SEq { ty: a, .. }, Type::SEq { ty: a2, .. })
            | (Type::Squash { ty: a, .. }, Type::Squash { ty: a2, .. })
            | (Type::Wf { shape: a, .. }, Type::Wf { shape: a2, .. }) => self.bind_params(d, a, a2, k, out, fuel),
            _ => {}
        }
    }

    /// Which declaration `Wf(shape; arity)` is, and its arguments.
    fn recognise(&self, shape: &Type) -> R<(Rc<WfDecl>, Vec<Hx>)> {
        let depth = self.ctx.borrow().len() as u32;
        let Some(tag) = Self::tag_in(self.psi, shape, depth) else { return refuse(WF) };
        let Some(d) = self.wf.by_tag.borrow().get(&tag).cloned() else {
            return refuse("Wf instance of a declaration the exporter has not met");
        };
        let mut out = vec![None; d.params.len()];
        if !out.is_empty() {
            let Some((_, inst)) = Self::summands_in(self.psi, shape, depth) else { return refuse(WF) };
            let mut fuel = 4096;
            for ((tmpl, _), inst) in d.summands.iter().zip(&inst) {
                self.bind_params(&d, tmpl, inst, 0, &mut out, &mut fuel);
            }
        }
        let args = out
            .iter()
            .map(|a| match a {
                Some(t) => self.ty(t),
                None => refuse("Wf parameter that no field of the instance determines"),
            })
            .collect::<R<Vec<_>>>()?;
        Ok((d, args))
    }

    /// `⟦Wf(x : S). n⟧ = D args`.
    pub(crate) fn wf_type(&self, shape: &Type) -> R<Hx> {
        let (d, args) = self.recognise(shape)?;
        Ok(app(Hx::Global(d.abs), args))
    }

    /// `⟦sup_f(a; cs)⟧ = D::supf# args a cs`.
    pub(crate) fn wf_supf(&self, shape: &Type, label: &Term, children: &Term) -> R<Hx> {
        let (d, mut args) = self.recognise(shape)?;
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
        let (d, mut args) = self.recognise(shape)?;
        let ml = lvl(motive_level)?.0;
        if !self.wf.emitted.borrow().contains(&(d.tag, ml)) {
            self.wf.wanted.borrow_mut().push((d.tag, ml));
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

    /// `λ(A_1 : Type l_1)…. body`.
    fn param_lams(d: &WfDecl, body: Hx) -> R<Hx> {
        d.params.iter().rev().try_fold(body, |b, l| Ok(lam(Hx::Sort(lvl(l)?), b)))
    }

    /// The inductive: its statement and its constructors' types.
    pub(crate) fn wf_inductive(&self, d: &WfDecl, ty: Hx) -> R<Decl> {
        let mut ctors = Vec::new();
        for (k, (p, n)) in d.summands.iter().enumerate() {
            // Π Δ. Π(p : P_k). Π(x_1 … x_n : D Δ). D Δ, innermost first.
            let mut t = app(Hx::Global(d.abs), Self::param_vars(d, 1 + *n as u32));
            for i in (0..*n as u32).rev() {
                t = Hx::Pi(Box::new(app(Hx::Global(d.abs), Self::param_vars(d, 1 + i))), Box::new(t));
            }
            t = Hx::Pi(Box::new(self.ty_at(d.np(), p)?), Box::new(t));
            for l in d.params.iter().rev() {
                t = Hx::Pi(Box::new(Hx::Sort(lvl(l)?)), Box::new(t));
            }
            ctors.push((d.ctors[k].clone(), t));
        }
        Ok(Decl {
            abs: d.abs,
            name: Some(d.key.clone()),
            ty,
            body: None,
            inductive: Some(Inductive { nparams: d.params.len(), ctors }),
            before: Vec::new(),
            after: vec![self.wf_supf_def(d)?],
        })
    }

    /// `D::supf# := λ Δ a cs. (case a of k ↦ λcs. c_k Δ p (fst cs) …) cs`.
    fn wf_supf_def(&self, d: &WfDecl) -> R<Aux> {
        // Π Δ. Π(a : S). Π(cs : Vec(D; n[a])). D, as a kernel type.
        let cs_ty = Type::Vec { level: d.level.clone(), elem: Rc::new(d.wf_at(1)), len: Rc::clone(&d.arity) };
        let mut ty = Type::Pi {
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
        for l in d.params.iter().rev() {
            ty = Type::Pi { dom_level: Level::succ(l.clone()), cod_level: d.level.clone(), dom: Rc::new(Type::Ty(l.clone())), cod: Rc::new(ty) };
        }
        let chain = if d.summands.len() == 1 { self.supf_arm(d, 0, 0)? } else { self.supf_chain(d, 0)? };
        let body = app(chain, vec![Hx::Var(0)]);
        let body = lam(self.ty_at(d.np(), &d.shape)?, lam(self.ty_at(d.np() + 1, &cs_ty)?, body));
        Ok(Aux { name: d.supf_key(), ty: self.ty(&ty)?, body: Self::param_lams(d, body)? })
    }

    /// The case at spine node `j`, in (Δ, a, cs, r_1 … r_j), on `a` at the
    /// top and on `r_j` below it. Its value is `Π(cs : Vec(D; n)). D`.
    fn supf_chain(&self, d: &WfDecl, j: usize) -> R<Hx> {
        let (ll, rl, l, r) = &d.spine[j];
        let by = j as u32 + 2;
        let scrut = Hx::Var(if j == 0 { 1 } else { 0 });
        // Motive in (Δ, a, cs, r…, z).
        let zfull = d.wrap(j, Term::Var(LocalVar(0)), by + 1);
        let motive = Type::Pi {
            dom_level: d.level.clone(),
            cod_level: d.level.clone(),
            dom: Rc::new(Type::Vec { level: d.level.clone(), elem: Rc::new(d.wf_at(by + 1)), len: Rc::new(d.arity.inst_top(by + 1, &zfull)) }),
            cod: Rc::new(d.wf_at(by + 2)),
        };
        let node = Type::Sum { lhs_level: ll.clone(), rhs_level: rl.clone(), lhs: Rc::new(l.shift_local(by)), rhs: Rc::new(r.shift_local(by)) };
        let at = d.np() + by;
        let motive = lam(self.ty_at(at, &node)?, self.ty_at(at + 1, &motive)?);
        let left = lam(self.ty_at(at, &l.shift_local(by))?, self.supf_arm(d, j, j + 1)?);
        let right_arm = if j + 2 < d.summands.len() { self.supf_chain(d, j + 1)? } else { self.supf_arm(d, j + 1, j + 1)? };
        let right = lam(self.ty_at(at, &r.shift_local(by))?, right_arm);
        konst("case", &[ll, rl, &d.level], vec![self.ty_at(at, &l.shift_local(by))?, self.ty_at(at, &r.shift_local(by))?, motive, left, right, scrut])
    }

    /// `λ(cs : Vec(D; n_k)). c_k Δ p (fst cs) (fst (snd cs)) …`, in
    /// (Δ, a, cs, r_1 … r_depth) whose last binder is `p : P_k` (or `a`
    /// itself when the shape has one summand).
    fn supf_arm(&self, d: &WfDecl, k: usize, depth: usize) -> R<Hx> {
        let n = d.summands[k].1;
        // In (Δ, a, cs, r…, cs'): the binders beyond Δ.
        let by = depth as u32 + 2;
        let p = if depth == 0 { Term::Var(LocalVar(1)) } else { Term::Var(LocalVar(0)) };
        let cs_ty = Type::Vec {
            level: d.level.clone(),
            elem: Rc::new(d.wf_at(by)),
            len: Rc::new(d.arity.inst_top(by, &d.inj(k, p.clone(), by))),
        };
        let mut args = Self::param_vars(d, by + 1);
        let at = d.np() + by;
        args.push(self.tm_at(at + 1, &p.shift_local(1))?);
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
        let mut ty = Type::Pi {
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
        for l in d.params.iter().rev() {
            ty = Type::Pi { dom_level: Level::succ(l.clone()), cod_level: mlv.clone(), dom: Rc::new(Type::Ty(l.clone())), cod: Rc::new(ty) };
        }
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
        Ok(Aux { name: d.elim_key(ml), ty: self.ty(&ty)?, body: Self::param_lams(d, body)? })
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
        // Binder domains, outermost first.
        let np = d.np();
        let mut doms = vec![self.ty_at(np + 3, &p.shift_local(3))?];
        for i in 0..n32 {
            doms.push(self.ty_at(np + 4 + i, &d.wf_at(4 + i))?);
        }
        for i in 1..=n32 {
            doms.push(self.ty_at(np + 4 + n32 + i - 1, &el_m(n32 + i + 2, n32 - 1, 4 + n32 + i - 1))?);
        }
        // The body, in C = (Δ, M, step, t, p, x_1 … x_n, ih_1 … ih_n).
        let cdelta = 4 + 2 * n32;
        let (step_ix, m_ix, p_ix) = (2 * n32 + 2, 2 * n32 + 3, 2 * n32);
        let label = d.inj(k, Term::Var(LocalVar(p_ix)), cdelta);
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
