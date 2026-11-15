//! Corecursion up to friends (docs/inductives/codata-elaborator-design.md §5.5, §5.6).
//!
//! A corecursive call may sit under a **friend**, a function of the
//! definition's own codata family that reads each codata argument at most
//! one layer deep to produce one layer of output (`add` in the Leibniz
//! product `mul(f, g) = SCons(hd f * hd g, add(mul(tl f, g), mul(f, tl g)))`,
//! `trans` in a bisimilarity up to transitivity, `bind_cong` in one up to
//! `bind`). The carrier is the free algebra of the friends over seeds,
//! existing trees and pending constructor nodes, a well-founded tree
//!
//! ```text
//! W₀ = W(x : V + Σi.⟦D⟧(i) + Σi.S(i) + A₁ + … + A_m). P(x)
//! C(i) = Σ(t : W₀). El(ok(t)(i))            (indexed; C = W₀ unindexed)
//! ```
//!
//! whose leaves are a seed (`V`, the varying tuple, at its own index
//! `g[v]`) or an existing tree, whose pending node is one constructor of the
//! declaration with carrier children (present only when constructors nest
//! above a call), and whose node `A_f` is friend `f` applied to its data
//! arguments, with one position per plain codata argument and a function's
//! worth for a function one. `ok` says each node sits at the index the
//! carrier value claims and each child at the index its parent wrote, which
//! is what lets a friend's arguments sit at other indices than its result
//! (`trans(r₁ : R(a, b), r₂ : R(b, c)) : R(a, c)`). The step is structural
//! recursion on the tree: a seed runs the body, a tree is observed, a
//! pending node is emitted, and a friend node runs the friend's own body
//! over its arguments' first nodes (the recursion's `ih`), re-elaborated
//! from the friend's source over `C` ("friend mode").
//!
//! Scoping as in the parent: `k` counts the binders past the definition's
//! body context (the site's `depth`), where every stored type is scoped.

use super::*;

use heather_syntax::{Decl, Pat, Ty};

use crate::ElabError;
use crate::TyVar;
use crate::names::Scope;
use crate::codata::Codata;

/// Whether `name`'s innermost binding in `cx` is `alias` itself.
fn binds(cx: &Cx, name: &str, alias: &Rc<Alias>) -> bool {
    let Some(a) = cx.aliases.iter().rev().find(|a| a.name == name) else {
        return false;
    };
    let shadowed = cx.names.iter().rposition(|n| n == name).is_some_and(|i| i >= a.depth);
    !shadowed && Rc::ptr_eq(a, alias)
}

fn locally_bound(cx: &Cx, name: &str) -> bool {
    cx.names.iter().any(|n| n == name) || cx.aliases.iter().any(|a| a.name == name)
}

/// The head name, written type arguments and arguments of a plain call
/// `f(…)` (or `f<…>(…)`).
fn call_parts(e: &Expr) -> Option<(&str, &[Ty], Vec<&Expr>)> {
    let ExprKind::App { head, args, named, .. } = &e.kind else {
        return None;
    };
    if !named.is_empty() {
        return None;
    }
    let (head, tys): (&Expr, &[Ty]) = match &head.kind {
        ExprKind::TyApp { head, args } => (head, args),
        _ => (head, &[]),
    };
    match &head.kind {
        ExprKind::Var(name) => Some((name.as_str(), tys, args.iter().collect())),
        _ => None,
    }
}

fn join(a: &Level, b: &Level) -> Level {
    Level::join(a.clone(), b.clone())
}

fn pi(dom_level: &Level, cod_level: &Level, dom: Type, cod: Type) -> Type {
    Type::Pi { dom_level: dom_level.clone(), cod_level: cod_level.clone(), dom: Rc::new(dom), cod: Rc::new(cod) }
}

fn lam(dom_level: &Level, cod_level: &Level, dom: Type, body: Term) -> Term {
    Term::Lam { dom_level: dom_level.clone(), cod_level: cod_level.clone(), dom: Rc::new(dom), body: Rc::new(body) }
}

fn app(fun: Rc<Term>, arg: Rc<Term>) -> Rc<Term> {
    Rc::new(Term::AppAt { fun, arg })
}

fn fst(pair: Rc<Term>) -> Rc<Term> {
    Rc::new(Term::FstAt { pair })
}

fn snd(pair: Rc<Term>) -> Rc<Term> {
    Rc::new(Term::SndAt { pair })
}

/// A function value applied to the innermost binder, one binder further
/// in: a `λ`'s own body, anything else applied (a β-redex never infers).
fn under_app(f: &Rc<Term>) -> Rc<Term> {
    match &**f {
        Term::Lam { body, .. } => Rc::clone(body),
        _ => app(Rc::new(f.shift_local(1)), var(0)),
    }
}

/// One summand of a right-nested sum: its type at a depth, and its level.
type Part<'a> = &'a dyn Fn(usize, u32) -> Type;

/// The case on a value `scrut` (at depth `k`) of the right-nested sum
/// `T₀ + (T₁ + … + T_{n-1})` (`part(j, depth)` gives `T_j`, each at
/// `levels[j]`), at the motive `motive(depth, z)` (`z` the scrutinee
/// re-injected into the whole sum at that depth): `branch(j, depth, y)`
/// with `y : T_j`. No summand is `Empty`: the motive is eliminated from it.
#[allow(clippy::too_many_arguments)]
fn sum_case(
    part: Part<'_>,
    levels: &[Level],
    k: u32,
    scrut: Rc<Term>,
    motive: &dyn Fn(u32, Rc<Term>) -> Type,
    mlvl: &Level,
    branch: &dyn Fn(usize, u32, Rc<Term>) -> Term,
) -> Term {
    fn tail_level(levels: &[Level], j: usize) -> Level {
        levels[j..].iter().fold(Level::Zero, |acc, l| Level::join(acc, l.clone()))
    }
    fn tail(part: Part<'_>, levels: &[Level], j: usize, k: u32) -> Type {
        if j + 1 == levels.len() {
            return part(j, k);
        }
        Type::Sum {
            lhs_level: levels[j].clone(),
            rhs_level: tail_level(levels, j + 1),
            lhs: Rc::new(part(j, k)),
            rhs: Rc::new(tail(part, levels, j + 1, k)),
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn go(
        part: Part<'_>,
        levels: &[Level],
        j: usize,
        k: u32,
        scrut: Rc<Term>,
        wrap: &dyn Fn(u32, Rc<Term>) -> Rc<Term>,
        motive: &dyn Fn(u32, Rc<Term>) -> Type,
        mlvl: &Level,
        branch: &dyn Fn(usize, u32, Rc<Term>) -> Term,
    ) -> Term {
        if levels.is_empty() {
            return Term::ElimEmpty {
                level: mlvl.clone(),
                scrut_level: Level::Zero,
                motive: Rc::new(motive(k + 1, wrap(k + 1, var(0)))),
                scrut,
            };
        }
        if j + 1 == levels.len() {
            return branch(j, k, scrut);
        }
        let rest = |d: u32, z: Rc<Term>| -> Rc<Term> {
            wrap(
                d,
                Rc::new(Term::Inr {
                    lhs_level: levels[j].clone(),
                    rhs_level: tail_level(levels, j + 1),
                    lhs: Rc::new(part(j, d)),
                    rhs: Rc::new(tail(part, levels, j + 1, d)),
                    val: z,
                }),
            )
        };
        Term::Case {
            lhs_level: levels[j].clone(),
            rhs_level: tail_level(levels, j + 1),
            motive_level: mlvl.clone(),
            lhs: Rc::new(part(j, k)),
            rhs: Rc::new(tail(part, levels, j + 1, k)),
            motive: Rc::new(motive(k + 1, wrap(k + 1, var(0)))),
            case_l: Rc::new(branch(j, k + 1, var(0))),
            case_r: Rc::new(go(part, levels, j + 1, k + 1, var(0), &rest, motive, mlvl, branch)),
            scrut,
        }
    }
    go(part, levels, 0, k, scrut, &|_, z| z, motive, mlvl, branch)
}

/// `v` injected as summand `j` of the right-nested sum (at depth `k`).
fn sum_inj(part: Part<'_>, levels: &[Level], j: usize, k: u32, v: Rc<Term>) -> Rc<Term> {
    let n = levels.len();
    let tail_level = |r: usize| levels[r..].iter().fold(Level::Zero, |acc, l| Level::join(acc, l.clone()));
    let tail = |r: usize| -> Type {
        let mut t = part(n - 1, k);
        for q in (r..n - 1).rev() {
            t = Type::Sum { lhs_level: levels[q].clone(), rhs_level: tail_level(q + 1), lhs: Rc::new(part(q, k)), rhs: Rc::new(t) };
        }
        t
    };
    let mut t = if j + 1 == n {
        v
    } else {
        Rc::new(Term::Inl {
            lhs_level: levels[j].clone(),
            rhs_level: tail_level(j + 1),
            lhs: Rc::new(part(j, k)),
            rhs: Rc::new(tail(j + 1)),
            val: v,
        })
    };
    for q in (0..j).rev() {
        t = Rc::new(Term::Inr {
            lhs_level: levels[q].clone(),
            rhs_level: tail_level(q + 1),
            lhs: Rc::new(part(q, k)),
            rhs: Rc::new(tail(q + 1)),
            val: t,
        });
    }
    t
}

/// The right-nested sum itself at depth `k` (`Empty` at no summand).
fn sum_ty(part: Part<'_>, levels: &[Level], k: u32, empty: &Level) -> Type {
    let n = levels.len();
    if n == 0 {
        return Type::Empty { level: empty.clone() };
    }
    let mut t = part(n - 1, k);
    let mut lvl = levels[n - 1].clone();
    for q in (0..n - 1).rev() {
        t = Type::Sum { lhs_level: levels[q].clone(), rhs_level: lvl.clone(), lhs: Rc::new(part(q, k)), rhs: Rc::new(t) };
        lvl = join(&levels[q], &lvl);
    }
    t
}

// -- friends --------------------------------------------------------------------

/// A friend's codata parameter: a plain child `D(e)` or a function child
/// `(y: A) → D(e(y))`.
#[derive(Clone)]
struct TreeParam {
    /// The domain of a function child, scoped over `(site, d̄)`.
    dom: Option<(Type, Level)>,
    /// The child's index, scoped over `(site, d̄)` (and `y` for a function).
    index: Rc<Term>,
}

/// What a friend's type parameter is at a definition.
#[derive(Clone)]
enum TyArg {
    /// Read off the definition's codata type: the type, at the site.
    Fixed(Type, Level),
    /// Not determined by it: a data component holding the type's code.
    Data(usize, Level),
}

/// What a friend's value parameter is at a definition.
#[derive(Clone)]
enum Role {
    /// Read off the definition's codata type (`E` in `Eutt<R>(E, t, u)`):
    /// the value at the site, and the parameter's type over the first `m`
    /// data components.
    Fixed(Rc<Term>, Type, Level, usize),
    /// Stored in the node's label, component `m`.
    Data(usize),
    /// A child of the node, codata parameter `j`.
    Tree(usize),
}

/// A friend of one corecursive definition: a function of its codata family
/// whose calls the body's children may hold calls under, its signature
/// instantiated at the definition (§5.6).
pub(crate) struct Friend {
    /// The name the body writes.
    pub(super) written: String,
    decl: Rc<Decl>,
    scope: Option<Rc<Scope>>,
    tyargs: Vec<TyArg>,
    roles: Vec<Role>,
    /// The data components' types: component `m` over `(site, d₀ … d_{m-1})`.
    data: Vec<(Type, Level)>,
    trees: Vec<TreeParam>,
    /// The result index over `(site, d̄)`.
    result: Rc<Term>,
    /// The first call, for diagnostics.
    pub(super) span: Span,
}

impl Friend {
    fn nd(&self) -> usize {
        self.data.len()
    }

    /// The substitution taking a term over `(site, d̄, extra binders)` to
    /// `(site, Δ_k, extra binders)` with `d̄ := vals` (each scoped at `k`).
    fn subst(&self, g: &LocalCtx, k: u32, vals: &[Rc<Term>], extra: u32) -> LocalSubst {
        let mut s = embed(g, k + extra);
        for v in vals {
            s = s.extended(Rc::new(v.shift_local(extra)));
        }
        for e in (0..extra).rev() {
            s = s.extended(var(e));
        }
        s
    }

    /// The data components of a label `a` (at depth `k`).
    fn projections(&self, a: &Rc<Term>) -> Vec<Rc<Term>> {
        let nd = self.nd();
        (0..nd).map(|m| Rc::new(tuple_proj(nd, m, (**a).clone()))).collect()
    }

    /// `A_f`, the label's type at depth `k`: the data components as a
    /// right-nested dependent `Σ` (`Unit` at none).
    fn label_ty(&self, k: u32) -> (Type, Level) {
        fn go(data: &[(Type, Level)], m: usize, k: u32) -> (Type, Level) {
            let (t, l) = &data[m];
            let t = t.shift_local_above(k, m as u32);
            if m + 1 == data.len() {
                return (t, l.clone());
            }
            let (r, rl) = go(data, m + 1, k);
            let lvl = join(l, &rl);
            (Type::Sigma { fst_level: l.clone(), snd_level: rl, fst: Rc::new(t), snd: Rc::new(r) }, lvl)
        }
        if self.data.is_empty() {
            return (Type::Unit { level: Level::Zero }, Level::Zero);
        }
        go(&self.data, 0, k)
    }

    /// The label from its components' values (each at depth `k`, checked).
    fn label(&self, k: u32, vals: &[Rc<Term>]) -> Term {
        if vals.is_empty() {
            return Term::Triv { level: Level::Zero };
        }
        let (mut cur, _) = self.label_ty(k);
        let mut parts = Vec::new();
        for v in &vals[..vals.len() - 1] {
            let Type::Sigma { fst_level, snd_level, fst, snd } = cur else {
                unreachable!("a label of several components is a Σ")
            };
            cur = snd.inst_top(0, v);
            parts.push((fst_level, snd_level, fst, snd, Rc::clone(v)));
        }
        let mut acc = Rc::clone(vals.last().expect("nonempty"));
        while let Some((fl, sl, f, s, v)) = parts.pop() {
            acc = Rc::new(Term::Pair { fst_level: fl, snd_level: sl, fst_ty: f, snd_ty: s, fst: v, snd: acc });
        }
        (*acc).clone()
    }
}

// -- the carrier ------------------------------------------------------------------

/// A summand's positions: one per plain child (`Unit`) or function child
/// (its domain, over `(site, v)`).
type Comp = Option<(Type, Rc<Term>)>;

/// The free carrier's types, scoped at the site's depth.
pub(crate) struct FreeTy {
    g: LocalCtx,
    indexed: bool,
    /// The index type `I`, its code and level.
    idx: Type,
    idx_code: Rc<Term>,
    li: Level,
    /// `⟦D⟧`'s signature (its family at any index) and level.
    dsig: Rc<MSig>,
    lw: Level,
    /// The shape's summands `[V, Σi.⟦D⟧(i), (Σi.S(i),) A₁, …, A_m]`.
    sums: Vec<(Type, Level)>,
    /// The summand of the first friend: 2, or 3 with a pending summand.
    first_friend: usize,
    pending: bool,
    /// Per summand: its positions, over `(site, v)` (a function child's
    /// domain with its code).
    comps: Vec<Vec<Comp>>,
    /// Per summand: the index its node sits at, over `(site, v)`.
    outs: Vec<Rc<Term>>,
    /// Per summand and position: the child's index, over `(site, v, y)`.
    kid_idx: Vec<Vec<Rc<Term>>>,
    /// `W₀`'s shape and position levels, and the predicate's.
    ls: Level,
    lp: Level,
    lk: Level,
    /// `C`'s level.
    pub(super) level: Level,
}

/// A child of a carrier node being built: a carrier value (at the node's
/// depth `k`), or a function into the carrier (at `k + 1`, `y = Var(0)`).
#[derive(Clone)]
pub(super) enum ChildVal {
    Plain(Rc<Term>),
    Fun(Rc<Term>),
}

impl FreeTy {
    fn levels(&self) -> Vec<Level> {
        self.sums.iter().map(|(_, l)| l.clone()).collect()
    }

    fn shape(&self, k: u32) -> Type {
        sum_ty(&|r, d| self.sums[r].0.shift_local(d), &self.levels(), k, &Level::Zero)
    }

    /// `v : sums[r]` as a shape.
    fn inj(&self, r: usize, k: u32, v: Rc<Term>) -> Rc<Term> {
        sum_inj(&|q, d| self.sums[q].0.shift_local(d), &self.levels(), r, k, v)
    }

    /// The case on a shape `x` (at depth `k`).
    fn shape_case(
        &self,
        k: u32,
        x: Rc<Term>,
        motive: &dyn Fn(u32, Rc<Term>) -> Type,
        mlvl: &Level,
        branch: &dyn Fn(usize, u32, Rc<Term>) -> Term,
    ) -> Term {
        sum_case(&|q, d| self.sums[q].0.shift_local(d), &self.levels(), k, x, motive, mlvl, branch)
    }

    /// Summand `r`'s position `j`'s type at the label `v` (at depth `k`).
    fn comp_ty(&self, r: usize, j: usize, k: u32, v: &Rc<Term>) -> Type {
        match &self.comps[r][j] {
            None => Type::Unit { level: self.lp.clone() },
            Some((t, _)) => t.inst_top(k, v),
        }
    }

    fn comp_levels(&self, r: usize) -> Vec<Level> {
        vec![self.lp.clone(); self.comps[r].len()]
    }

    /// `P(inj_r v)` decoded: the positions' sum at the label `v`.
    fn comps_ty(&self, r: usize, k: u32, v: &Rc<Term>) -> Type {
        sum_ty(&|j, d| self.comp_ty(r, j, d, &Rc::new(v.shift_local(d - k))), &self.comp_levels(r), k, &self.lp)
    }

    /// Position `j` of summand `r` with payload `y` (`⟨⟩` for a plain child).
    fn posn(&self, r: usize, j: usize, k: u32, v: &Rc<Term>, y: Rc<Term>) -> Rc<Term> {
        sum_inj(&|q, d| self.comp_ty(r, q, d, &Rc::new(v.shift_local(d - k))), &self.comp_levels(r), j, k, y)
    }

    /// The case on a position `q` of summand `r` at the label `v`.
    #[allow(clippy::too_many_arguments)]
    fn pos_case(
        &self,
        r: usize,
        k: u32,
        v: &Rc<Term>,
        q: Rc<Term>,
        motive: &dyn Fn(u32, Rc<Term>) -> Type,
        mlvl: &Level,
        branch: &dyn Fn(usize, u32, Rc<Term>) -> Term,
    ) -> Term {
        sum_case(
            &|j, d| self.comp_ty(r, j, d, &Rc::new(v.shift_local(d - k))),
            &self.comp_levels(r),
            k,
            q,
            motive,
            mlvl,
            branch,
        )
    }

    /// The code of `P(x)`: a case on the shape into `Ty lp`.
    fn pos_code(&self, k: u32, x: Rc<Term>) -> Term {
        let ty_lp = Type::Ty(self.lp.clone());
        self.shape_case(k, x, &|_, _| ty_lp.clone(), &Level::succ(self.lp.clone()), &|r, d, v| {
            let comps = &self.comps[r];
            if comps.is_empty() {
                return Term::TmEmpty { level: self.lp.clone() };
            }
            let code = |j: usize| -> Term {
                match &comps[j] {
                    None => Term::TmUnit { level: self.lp.clone() },
                    Some((_, c)) => c.inst_top(d, &v),
                }
            };
            let mut t = code(comps.len() - 1);
            for j in (0..comps.len() - 1).rev() {
                t = Term::TmSum { lhs_level: self.lp.clone(), rhs_level: self.lp.clone(), lhs: Rc::new(code(j)), rhs: Rc::new(t) };
            }
            t
        })
    }

    /// `P(x)`.
    fn pos(&self, k: u32, x: Rc<Term>) -> Type {
        Type::El { level: self.lp.clone(), tm: Rc::new(self.pos_code(k, x)) }
    }

    fn lw0(&self) -> Level {
        join(&self.ls, &self.lp)
    }

    /// `W₀` at depth `k`.
    fn w0(&self, k: u32) -> Type {
        Type::W { shape_level: self.ls.clone(), pos_level: self.lp.clone(), shape: Rc::new(self.shape(k)), pos: Rc::new(self.pos(k + 1, var(0))) }
    }

    fn sup(&self, k: u32, label: Rc<Term>, kids: Rc<Term>) -> Term {
        Term::Sup {
            shape_level: self.ls.clone(),
            pos_level: self.lp.clone(),
            shape_ty: Rc::new(self.shape(k)),
            pos_ty: Rc::new(self.pos(k + 1, var(0))),
            label,
            children: kids,
        }
    }

    /// The index the node `x` sits at.
    fn out(&self, k: u32, x: Rc<Term>) -> Term {
        if !self.indexed {
            return Term::Triv { level: Level::Zero };
        }
        let i = self.idx.clone();
        self.shape_case(k, x, &|d, _| i.shift_local(d), &self.li, &|r, d, v| self.outs[r].inst_top(d, &v))
    }

    /// Summand `r`'s node's index at the label `v`.
    fn out_r(&self, r: usize, k: u32, v: &Rc<Term>) -> Rc<Term> {
        if !self.indexed {
            return triv();
        }
        Rc::new(self.outs[r].inst_top(k, v))
    }

    /// Position `j` of summand `r`'s child index at `(v, y)`.
    fn kid_index(&self, r: usize, j: usize, k: u32, v: &Rc<Term>, y: &Rc<Term>) -> Rc<Term> {
        if !self.indexed {
            return triv();
        }
        Rc::new(self.kid_idx[r][j].apply_local(&embed(&self.g, k).extended(Rc::clone(v)).extended(Rc::clone(y))))
    }

    /// The child index at position `q` of summand `r` at the label `v`.
    fn child_r(&self, r: usize, k: u32, v: &Rc<Term>, q: Rc<Term>) -> Term {
        let i = self.idx.clone();
        self.pos_case(r, k, v, q, &|d, _| i.shift_local(d), &self.li, &|j, d, y| {
            (*self.kid_index(r, j, d, &Rc::new(v.shift_local(d - k)), &y)).clone()
        })
    }

    /// The child index at position `p` of the node `x` (a convoy: `p`'s type
    /// is `P(x)`).
    fn child(&self, k: u32, x: Rc<Term>, p: Rc<Term>) -> Term {
        let i = self.idx.clone();
        let li = self.li.clone();
        let lp = self.lp.clone();
        let cased = self.shape_case(
            k,
            x,
            &|d, xx| pi(&lp, &li, self.pos(d, xx), i.shift_local(d + 1)),
            &join(&lp, &li),
            &|r, d, v| lam(&lp, &li, self.comps_ty(r, d, &v), self.child_r(r, d + 1, &Rc::new(v.shift_local(1)), var(0))),
        );
        (*app(Rc::new(cased), p)).clone()
    }

    /// `ok(t) : Π(j : I). Ty lk`, the predicate that `t`'s nodes sit at the
    /// indices their parents wrote (an `elim_W` into codes).
    fn ok(&self, k: u32, t: Rc<Term>) -> Term {
        let succ_lk = Level::succ(self.lk.clone());
        let mot = |d: u32| pi(&self.li, &succ_lk, self.idx.shift_local(d), Type::Ty(self.lk.clone()));
        // Over (a, f, ih, j), at depth k + 4.
        let code = Term::TmSigma {
            fst_level: self.li.clone(),
            snd_level: self.lk.clone(),
            fst: Rc::new(Term::TmId {
                level: self.li.clone(),
                ty: Rc::new(self.idx_code.shift_local(k + 4)),
                lhs: Rc::new(self.out(k + 4, var(3))),
                rhs: var(0),
            }),
            snd: Rc::new(Term::TmPi {
                dom_level: self.lp.clone(),
                cod_level: self.lk.clone(),
                dom: Rc::new(self.pos_code(k + 5, var(4))),
                cod: app(app(var(3), var(0)), Rc::new(self.child(k + 6, var(5), var(0)))),
            }),
        };
        Term::ElimW {
            shape_level: self.ls.clone(),
            pos_level: self.lp.clone(),
            motive_level: join(&self.li, &succ_lk),
            shape: Rc::new(self.shape(k)),
            pos: Rc::new(self.pos(k + 1, var(0))),
            motive: Rc::new(mot(k + 1)),
            step: Rc::new(lam(&self.li, &succ_lk, self.idx.shift_local(k + 3), code)),
            scrut: t,
        }
    }

    /// `El(ok(t)(idx))`.
    fn ok_at(&self, k: u32, t: Rc<Term>, idx: Rc<Term>) -> Type {
        Type::El { level: self.lk.clone(), tm: app(Rc::new(self.ok(k, t)), idx) }
    }

    /// `C(idx)` at depth `k`.
    pub(super) fn c_at(&self, k: u32, idx: &Rc<Term>) -> Type {
        if !self.indexed {
            return self.w0(k);
        }
        Type::Sigma {
            fst_level: self.lw0(),
            snd_level: self.lk.clone(),
            fst: Rc::new(self.w0(k)),
            snd: Rc::new(self.ok_at(k + 1, var(0), Rc::new(idx.shift_local(1)))),
        }
    }

    /// The carrier family over `(g, i)`.
    pub(super) fn fam(&self) -> Type {
        self.c_at(1, &var(0))
    }

    /// The tree of a carrier value (at depth `k`).
    fn tree_of(&self, c: Rc<Term>) -> Rc<Term> {
        if self.indexed { fst(c) } else { c }
    }

    /// A node of `C(idx)`: summand `r` at the label `v`, which sits at
    /// `out_r(v)` (convertible with `idx`, which the caller has checked),
    /// with the children `chs`, one per position.
    fn node(&self, k: u32, r: usize, v: Rc<Term>, idx: &Rc<Term>, chs: &[ChildVal]) -> Term {
        let lw0 = self.lw0();
        let at = |j: usize, d: u32, y: &Rc<Term>| -> Rc<Term> {
            match &chs[j] {
                ChildVal::Plain(c) => Rc::new(c.shift_local(d - k)),
                ChildVal::Fun(c) => Rc::new(c.shift_local_above(d - k, 1).inst_top(0, y)),
            }
        };
        // The children function's body at the position `q` (depth `d`).
        let kids_at = |d: u32, q: Rc<Term>| -> Term {
            let w = self.w0(0);
            self.pos_case(r, d, &Rc::new(v.shift_local(d - k)), q, &|dd, _| w.shift_local(dd), &lw0, &|j, dd, y| {
                (*self.tree_of(at(j, dd, &y))).clone()
            })
        };
        let kids = lam(&self.lp, &lw0, self.comps_ty(r, k, &v), kids_at(k + 1, var(0)));
        let sup = self.sup(k, self.inj(r, k, Rc::clone(&v)), Rc::new(kids));
        if !self.indexed {
            return sup;
        }
        let proofs = lam(
            &self.lp,
            &self.lk,
            self.comps_ty(r, k, &v),
            self.pos_case(
                r,
                k + 1,
                &Rc::new(v.shift_local(1)),
                var(0),
                &|d, q| self.ok_at(d, Rc::new(kids_at(d, Rc::clone(&q))), Rc::new(self.child_r(r, d, &Rc::new(v.shift_local(d - k)), q))),
                &self.lk,
                &|j, d, y| (*snd(at(j, d, &y))).clone(),
            ),
        );
        let out = self.out_r(r, k, &v);
        Term::PairAt {
            ty: Some(Rc::new(self.c_at(k, idx))),
            fst: Rc::new(sup),
            snd: Rc::new(Term::PairAt {
                ty: None,
                fst: Rc::new(Term::Refl { level: self.li.clone(), ty: Rc::new(self.idx.shift_local(k)), tm: out }),
                snd: Rc::new(proofs),
            }),
        }
    }

    /// A seed `s : X(idx)` (`⟨v, e⟩` indexed, `v` unindexed) as a leaf.
    pub(super) fn seed_leaf(&self, k: u32, idx: &Rc<Term>, s: Rc<Term>) -> Term {
        if !self.indexed {
            return self.node(k, 0, s, idx, &[]);
        }
        // Built from the seed's own equation rather than `refl`: the call's
        // index was checked against `idx` when the seed was built.
        let v = fst(Rc::clone(&s));
        let kids = Rc::new(lam(&self.lp, &self.lw0(), self.comps_ty(0, k, &v), self.pos_case(0, k + 1, &Rc::new(v.shift_local(1)), var(0), &|d, _| self.w0(d), &self.lw0(), &|_, _, _| unreachable!("a seed has no children"))));
        let sup = self.sup(k, self.inj(0, k, Rc::clone(&v)), Rc::clone(&kids));
        // Each (absent) child's proof, at the type a node's proofs have.
        let proof_ty = |d: u32, q: Rc<Term>| {
            self.ok_at(d, app(Rc::new(kids.shift_local(d - k)), Rc::clone(&q)), Rc::new(self.child_r(0, d, &Rc::new(v.shift_local(d - k)), q)))
        };
        let proofs = lam(
            &self.lp,
            &self.lk,
            self.comps_ty(0, k, &v),
            self.pos_case(0, k + 1, &Rc::new(v.shift_local(1)), var(0), &proof_ty, &self.lk, &|_, _, _| unreachable!("a seed has no children")),
        );
        Term::PairAt {
            ty: Some(Rc::new(self.c_at(k, idx))),
            fst: Rc::new(sup),
            snd: Rc::new(Term::PairAt { ty: None, fst: snd(s), snd: Rc::new(proofs) }),
        }
    }

    /// An existing tree `t : ⟦D⟧(idx)` as a leaf.
    pub(super) fn tree_leaf(&self, k: u32, idx: &Rc<Term>, t: Rc<Term>) -> Term {
        let v = if self.indexed {
            Rc::new(Term::Pair {
                fst_level: self.li.clone(),
                snd_level: self.lw.clone(),
                fst_ty: Rc::new(self.idx.shift_local(k)),
                snd_ty: Rc::new(self.dsig.shift_local(k + 1).at(var(0))),
                fst: Rc::clone(idx),
                snd: t,
            })
        } else {
            t
        };
        self.node(k, 1, v, idx, &[])
    }

    /// `y : C(idx) + ⟦D⟧(idx)` as a `C(idx)`: a carrier value stays, a tree
    /// becomes a leaf.
    pub(super) fn embed(&self, k: u32, idx: &Rc<Term>, y: Rc<Term>) -> Term {
        Term::Case {
            lhs_level: self.level.clone(),
            rhs_level: self.lw.clone(),
            motive_level: self.level.clone(),
            lhs: Rc::new(self.c_at(k, idx)),
            rhs: Rc::new(self.dsig.shift_local(k).at(Rc::clone(idx))),
            motive: Rc::new(self.c_at(k + 1, &Rc::new(idx.shift_local(1)))),
            case_l: var(0),
            case_r: Rc::new(self.tree_leaf(k + 1, &Rc::new(idx.shift_local(1)), var(0))),
            scrut: y,
        }
    }

    /// The index `C(idx)` (whnf'd or as built) is at, read off its type:
    /// the carrier's own `W₀`, then the predicate's index.
    fn index_of_c(&self, k: u32, ty: &Type) -> Option<Rc<Term>> {
        if !self.indexed {
            return (*ty == self.w0(k)).then(triv);
        }
        let Type::Sigma { fst, snd, .. } = ty else {
            return None;
        };
        if **fst != self.w0(k) {
            return None;
        }
        let Type::El { tm, .. } = &**snd else {
            return None;
        };
        let Term::AppAt { fun, arg } = &**tm else {
            return None;
        };
        if **fun != self.ok(k + 1, var(0)) {
            return None;
        }
        // The index is scoped under the Σ's binder, which it does not use.
        let back = arg.inst_top(0, &Term::Zero);
        (Rc::new(back.shift_local(1)) == *arg).then(|| Rc::new(back))
    }
}

/// A definition's free carrier: its types, its friends, and each friend's
/// step over it (scoped at the site's depth plus `(p : A_f, f : Π(q :
/// P_f). W₀, ih : Π(q : P_f). M(f q), ok : Π(q : P_f). El(ok(f q)(c(q))))`,
/// the last `Unit` unindexed).
pub(crate) struct Free {
    pub(super) ty: Rc<FreeTy>,
    pub(super) friends: Vec<Rc<Friend>>,
    arms: Vec<Term>,
}

/// A friend's body while it is re-elaborated over a free carrier (§5.5): its
/// codata parameters are the node's children, read through the step's `ih`.
pub(crate) struct FriendMode {
    /// The corecursive site's depth, where `d_ty`, `carrier` and `free` are
    /// scoped.
    depth: usize,
    ind: Rc<Inductive>,
    carrier: Carrier,
    free: Rc<FreeTy>,
    /// The friend's summand.
    r: usize,
    /// The friend, as the definition calls it, and the definition.
    friend: String,
    user: String,
    selfref: Rc<SelfRef>,
    /// The friend's instantiated signature (shared with the definition's
    /// `Free`).
    sig: Rc<Friend>,
    /// The depth at which `(p, f, ih, ok)` are the last four binders.
    base: usize,
    /// The codata parameters' aliases and their positions.
    trees: Vec<(Rc<Alias>, usize)>,
    /// Children bound by a `match` on a codata parameter (`C + ⟦D⟧`, or a
    /// function into it).
    children: Vec<Rc<Alias>>,
}

impl FriendMode {
    pub(super) fn with_children(&self, more: Vec<Rc<Alias>>) -> FriendMode {
        let mut children = self.children.clone();
        children.extend(more);
        FriendMode {
            depth: self.depth,
            ind: Rc::clone(&self.ind),
            carrier: self.carrier.clone(),
            free: Rc::clone(&self.free),
            r: self.r,
            friend: self.friend.clone(),
            user: self.user.clone(),
            selfref: Rc::clone(&self.selfref),
            sig: Rc::clone(&self.sig),
            base: self.base,
            trees: self.trees.clone(),
            children,
        }
    }

    /// The codata parameter `name` names here, as its position.
    fn tree_param(&self, cx: &Cx, name: &str) -> Option<usize> {
        self.trees.iter().find(|(a, _)| a.name == name && binds(cx, name, a)).map(|(_, j)| *j)
    }

    /// Whether `name` is a child a `match` on a codata parameter bound.
    fn child_param(&self, cx: &Cx, name: &str) -> bool {
        self.children.iter().any(|a| a.name == name && binds(cx, name, a))
    }

    /// The first codata parameter or child `e` mentions, by name.
    fn mentioned(&self, cx: &Cx, e: &Expr) -> Option<(String, Span)> {
        let mut found = None;
        crate::surface::walk_expr(e, &mut |x| {
            if found.is_none()
                && let ExprKind::Var(n) = &x.kind
                && (self.tree_param(cx, n).is_some() || self.child_param(cx, n))
            {
                found = Some((n.clone(), x.span));
            }
        });
        found
    }

    fn refuse<T>(&self, what: &str, span: Span) -> R<T> {
        err(
            format!(
                "`{}` is not a friend of the corecursive `{}` (docs/inductives/codata-elaborator-design.md §5.5): {what}",
                self.friend, self.user
            ),
            span,
        )
    }

    /// The step's binders `(p, f, ih, ok)` seen from depth `now`.
    fn binders(&self, now: usize) -> (Rc<Term>, Rc<Term>, Rc<Term>, Rc<Term>) {
        let up = (now - self.base) as u32;
        (var(up + 3), var(up + 2), var(up + 1), var(up))
    }

    /// The label's data components, seen from depth `now`.
    fn data_vals(&self, now: usize) -> Vec<Rc<Term>> {
        let (p, ..) = self.binders(now);
        let nd = self.sig.data.len();
        (0..nd).map(|m| Rc::new(tuple_proj(nd, m, (*p).clone()))).collect()
    }

    /// Codata parameter `j`'s index at the payload `y` (at depth `now`,
    /// `k = now - site depth`).
    fn param_index(&self, now: usize, j: usize, y: &Rc<Term>) -> Rc<Term> {
        let k = (now - self.depth) as u32;
        let (p, ..) = self.binders(now);
        self.free.kid_index(self.r, j, k, &p, y)
    }

    /// Codata parameter `j` at the payload `y`, as a carrier value.
    fn child_value(&self, now: usize, j: usize, y: Rc<Term>) -> Rc<Term> {
        let k = (now - self.depth) as u32;
        let (p, f, _, ok) = self.binders(now);
        let idx = self.param_index(now, j, &y);
        let pos = self.free.posn(self.r, j, k, &p, y);
        let t = app(f, Rc::clone(&pos));
        if !self.free.indexed {
            return t;
        }
        Rc::new(Term::PairAt { ty: Some(Rc::new(self.free.c_at(k, &idx))), fst: t, snd: app(ok, pos) })
    }

    /// Codata parameter `j`'s first node at the payload `y`, from `ih`.
    fn node_of(&self, now: usize, j: usize, y: Rc<Term>) -> Rc<Term> {
        let k = (now - self.depth) as u32;
        let (p, _, ih, ok) = self.binders(now);
        let pos = self.free.posn(self.r, j, k, &p, Rc::clone(&y));
        let at = app(ih, Rc::clone(&pos));
        if !self.free.indexed {
            return at;
        }
        app(app(at, self.param_index(now, j, &y)), app(ok, pos))
    }
}

/// What a corecursive definition's sites see of `D`: enough to read a
/// friend's signature against it.
pub(crate) struct SiteTy<'a> {
    pub(super) ind: &'a Inductive,
    pub(super) d_ty: &'a Type,
}

/// Corecursion up to friends' part of the elaborator.
pub(crate) struct UpTo<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for UpTo<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl UpTo<'_> {
    // -- finding the friends ---------------------------------------------------

    /// The friends a corecursive body calls: a call inside one of the
    /// declaration's constructors, to a global function of the definition's
    /// own codata family, with a corecursive call among its arguments. A
    /// function whose result is some other type is not a candidate (the
    /// guard's own diagnostics apply to it).
    pub(super) fn corec_friends(&self, cx: &Cx, selfref: &SelfRef, site: &SiteTy<'_>, body: &Expr) -> R<Vec<Friend>> {
        fn go(el: &Elaborator, cx: &Cx, selfref: &SelfRef, ind: &Inductive, e: &Expr, under: bool, out: &mut Vec<(String, Span)>) {
            let ctor = Codata(el).codata_ctor_app(cx, ind, e).is_some();
            if under
                && !ctor
                && surface_self_call(selfref, e).is_none()
                && let Some((name, _, _)) = call_parts(e)
                && nested_self_call(selfref, e).is_some()
                && !locally_bound(cx, name)
                && !out.iter().any(|(n, _)| *n == name)
            {
                out.push((name.to_string(), e.span));
            }
            crate::surface::for_each_child(e, &mut |c| go(el, cx, selfref, ind, c, under || ctor, out));
        }
        let mut found = Vec::new();
        go(self, cx, selfref, site.ind, body, false, &mut found);
        let mut friends = Vec::new();
        for (name, span) in found {
            if let Some(f) = self.friend_signature(cx, site, &name, span)? {
                friends.push(f);
            }
        }
        Ok(friends)
    }

    /// The type-and-value-argument telescope of a named codata signature (the
    /// shape's arguments before its index binder).
    fn sig_tel(&self, sig: &MSig) -> Option<Vec<Rc<Term>>> {
        let Type::El { tm, .. } = &*sig.shape else {
            return None;
        };
        let (GenDef::MShape(_), mut args) = self.gen_app_of(tm)? else {
            return None;
        };
        args.pop()?;
        // The shape is scoped under the index binder, which the other
        // arguments do not mention.
        Some(args.iter().map(|a| Rc::new(a.inst_top(0, &Term::Zero))).collect())
    }

    /// Read `name`'s signature as a friend's at this definition: `None` when
    /// it is not a global function of the definition's codata family; an
    /// error when it is one but its signature is outside the friends this
    /// round reads (§5.6).
    fn friend_signature(&self, cx: &Cx, site: &SiteTy<'_>, name: &str, span: Span) -> R<Option<Friend>> {
        let Some(key) = self.key_of(name) else {
            return Ok(None);
        };
        let Some((module, base)) = crate::names::split_qual(&key) else {
            return Ok(None);
        };
        let Some(decl) = self.names.surface_decl_in(module, base).cloned() else {
            return Ok(None);
        };
        if decl.kind != heather_syntax::DeclKind::Fn || decl.is_meta || decl.value {
            return Ok(None);
        }
        let Some(p) = MParts::read(site.d_ty, &cx.gamma) else {
            return Ok(None);
        };
        let scope = self.names.module_scope(module).cloned().map(Rc::new);
        let _scope = scope.as_ref().map(|s| self.use_scope(s));
        let refuse = |what: String| -> R<Option<Friend>> {
            err(format!("`{name}` cannot be a friend of this corecursion (docs/inductives/codata-elaborator-design.md §5.6): {what}"), span)
        };
        let hcx = cx.hygienic();
        let site_len = hcx.names.len();
        // Pass 1: the whole telescope as binders, to read which of the
        // friend's parameters its codata type's arguments are.
        let mut c1 = hcx.clone();
        for tv in &decl.tyvars {
            let level = Level::constant(tv.level);
            c1.push(tv.name.clone(), Type::Ty(level.clone()), Level::succ(level.clone()));
            c1.tyvars.push(TyVar { name: tv.name.clone(), ty: Type::El { level: level.clone(), tm: var(0) }, level, depth: c1.names.len() });
        }
        for q in &decl.params {
            let Ok((ty, lvl)) = self.elab_ty(&c1, &q.ty) else {
                return Ok(None);
            };
            c1.push(q.name.clone(), ty.clone(), lvl);
            if let Type::Ty(level) = &ty {
                c1.tyvars.push(TyVar { name: q.name.clone(), ty: Type::El { level: level.clone(), tm: var(0) }, level: level.clone(), depth: c1.names.len() });
            }
        }
        let Ok((res, _)) = self.elab_ty(&c1, &decl.result) else {
            return Ok(None);
        };
        let Ok(res) = self.whnf(&c1, &res, span) else {
            return Ok(None);
        };
        if self.tag_of(&res).is_none_or(|i| i.tag != site.ind.tag) {
            return Ok(None);
        }
        let Some(rp) = MParts::read(&res, &c1.gamma) else {
            return Ok(None);
        };
        let nt = decl.tyvars.len();
        let nb = (nt + decl.params.len()) as u32;
        let mut assign: Vec<Option<Rc<Term>>> = vec![None; nb as usize];
        match (self.sig_tel(&rp.sig), self.sig_tel(&p.sig)) {
            (Some(tf), Some(td)) if tf.len() == td.len() => {
                for (a, b) in tf.iter().zip(&td) {
                    if let Term::Var(LocalVar(v)) = &**a
                        && *v < nb
                    {
                        let slot = &mut assign[(nb - 1 - v) as usize];
                        if slot.is_none() {
                            *slot = Some(Rc::clone(b));
                        }
                    }
                }
            }
            _ => {}
        }
        if decl.params.iter().any(|q| q.implicit) {
            let q = decl.params.iter().find(|q| q.implicit).expect("checked");
            return refuse(format!("its parameter `{}` is implicit, and a friend takes its parameters explicitly", q.name));
        }
        if decl.decreases.is_some() {
            return refuse("it is a `decreases` definition".into());
        }
        // Pass 2: the determined parameters are the definition's, the rest
        // are data (binders) or codata (children, not binders).
        let mut c2 = hcx.clone();
        let mut tyargs = Vec::new();
        let mut data: Vec<(Type, Level)> = Vec::new();
        let push_data = |c2: &mut Cx, data: &mut Vec<(Type, Level)>, name: &str, ty: Type, lvl: Level| {
            c2.push(name.to_string(), ty.clone(), lvl.clone());
            if let Type::Ty(level) = &ty {
                c2.tyvars.push(TyVar { name: name.to_string(), ty: Type::El { level: level.clone(), tm: var(0) }, level: level.clone(), depth: c2.names.len() });
            }
            data.push((ty, lvl));
        };
        for (b, tv) in decl.tyvars.iter().enumerate() {
            let level = Level::constant(tv.level);
            match &assign[b] {
                Some(code) => {
                    // Read at the site; here, past the data binders pushed so far.
                    let ty = Type::El { level: level.clone(), tm: Rc::clone(code) };
                    c2.tyvars.push(TyVar { name: tv.name.clone(), ty: ty.shift_local(data.len() as u32), level: level.clone(), depth: c2.names.len() });
                    tyargs.push(TyArg::Fixed(ty, level));
                }
                None => {
                    tyargs.push(TyArg::Data(data.len(), level.clone()));
                    push_data(&mut c2, &mut data, &tv.name, Type::Ty(level.clone()), Level::succ(level));
                }
            }
        }
        let mut roles = Vec::new();
        let mut trees: Vec<(TreeParam, usize)> = Vec::new();
        for (i, q) in decl.params.iter().enumerate() {
            let m = data.len();
            let Ok((ty, lvl)) = self.elab_ty(&c2, &q.ty) else {
                return refuse(format!(
                    "the type of its parameter `{}` mentions one of its codata parameters, which are the node's children and not part of its label",
                    q.name
                ));
            };
            if let Some(val) = &assign[nt + i] {
                let val = Rc::new(val.shift_local(m as u32));
                c2.aliases.push(Rc::new(Alias {
                    skel: None,
                    name: q.name.clone(),
                    depth: c2.names.len(),
                    term: Rc::clone(&val),
                    ty: ty.clone(),
                    level: lvl.clone(),
                    spliced: None,
                    shifted: Default::default(),
                }));
                if let Type::Ty(level) = &ty {
                    c2.tyvars.push(TyVar { name: q.name.clone(), ty: Type::El { level: level.clone(), tm: Rc::clone(&val) }, level: level.clone(), depth: c2.names.len() });
                }
                roles.push(Role::Fixed(val, ty, lvl, m));
                continue;
            }
            // A codata parameter: the definition's family at some index,
            // plainly or under one arrow.
            let fam_at = |cx: &Cx, d: u32, t: &Type| -> Option<Rc<Term>> {
                let w = self.whnf(cx, t, q.span).ok()?;
                let Type::M { index, .. } = &*decoded(&w) else {
                    return None;
                };
                let want = p.d_of(d, Rc::clone(index));
                self.conv_types(cx, &w, &want, &p.lw).then(|| Rc::clone(index))
            };
            let tree = match self.whnf(&c2, &ty, q.span) {
                Ok(Type::Pi { dom_level, dom, cod, .. }) => {
                    let mut cy = c2.clone();
                    cy.push("#y".into(), (*dom).clone(), dom_level.clone());
                    fam_at(&cy, (m + 1) as u32, &cod).map(|index| TreeParam { dom: Some(((*dom).clone(), dom_level)), index })
                }
                Ok(_) => fam_at(&c2, m as u32, &ty).map(|index| TreeParam { dom: None, index }),
                Err(_) => None,
            };
            match tree {
                Some(t) => {
                    roles.push(Role::Tree(trees.len()));
                    trees.push((t, m));
                }
                None => {
                    roles.push(Role::Data(m));
                    push_data(&mut c2, &mut data, &q.name, ty, lvl);
                }
            }
        }
        if trees.is_empty() {
            return refuse("it takes no argument of the definition's codata type".into());
        }
        let nd = data.len() as u32;
        let Ok((res2, _)) = self.elab_ty(&c2, &decl.result) else {
            return refuse("its result type does not elaborate at the definition's type".into());
        };
        let Ok(res2) = self.whnf(&c2, &res2, span) else {
            return Ok(None);
        };
        let result = match &*decoded(&res2) {
            Type::M { index, .. } if self.conv_types(&c2, &res2, &p.d_of(nd, Rc::clone(index)), &p.lw) => Rc::clone(index),
            _ => {
                return refuse(
                    "its result is not the definition's own codata type: a friend's type and value arguments of the codata family must be its own parameters, read off the definition's type".into(),
                );
            }
        };
        let trees = trees
            .into_iter()
            .map(|(t, m)| {
                let by = nd - m as u32;
                TreeParam {
                    index: Rc::new(if t.dom.is_some() { t.index.shift_local_above(by, 1) } else { t.index.shift_local(by) }),
                    dom: t.dom.map(|(d, l)| (d.shift_local(by), l)),
                }
            })
            .collect();
        let _ = site_len;
        Ok(Some(Friend { written: name.to_string(), decl: Rc::new(decl), scope, tyargs, roles, data, trees, result, span }))
    }

    // -- the carrier -----------------------------------------------------------

    /// The free carrier's types over the seeds (the varying tuple `vtuple`,
    /// sitting at `seed_out` over `(site, v)`), the codata type `d_ty`, and
    /// the friends; `pending` adds the pending-node summand.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn free_ty(
        &self,
        cx: &Cx,
        p: &MParts,
        vtuple: (&Type, &Level),
        seed_out: Rc<Term>,
        friends: &[Friend],
        pending: bool,
        span: Span,
    ) -> R<FreeTy> {
        let g = cx.gamma.clone();
        let indexed = p.indexed;
        let idx = (*p.sig.idx).clone();
        let li = p.sig.idx_level.clone();
        let Some(idx_code) = crate::code::code_of(&idx) else {
            return err("corecursion up to a friend needs the codata's index type to have a code", span);
        };
        let dsig = Rc::clone(&p.sig);
        let lw = p.lw.clone();
        let mut sums = vec![(vtuple.0.clone(), vtuple.1.clone())];
        let mut comps: Vec<Vec<Comp>> = vec![Vec::new()];
        let mut outs: Vec<Rc<Term>> = vec![seed_out];
        let mut kid_idx: Vec<Vec<Rc<Term>>> = vec![Vec::new()];
        // Existing trees, at their own index.
        let tree_ty = if indexed {
            Type::Sigma { fst_level: li.clone(), snd_level: lw.clone(), fst: Rc::new(idx.clone()), snd: Rc::new(dsig.shift_local(1).at(var(0))) }
        } else {
            dsig.at(triv())
        };
        sums.push((tree_ty, join(&li, &lw)));
        comps.push(Vec::new());
        outs.push(if indexed { fst(var(0)) } else { triv() });
        kid_idx.push(Vec::new());
        let mut lp_parts: Vec<Level> = Vec::new();
        // Pending nodes: one constructor's label at its index, its
        // positions the declaration's own.
        if pending {
            let pq = p.reindexed(1, if indexed { fst(var(0)) } else { triv() });
            let shape_ty = if indexed {
                Type::Sigma { fst_level: li.clone(), snd_level: p.ls.clone(), fst: Rc::new(idx.clone()), snd: Rc::new(dsig.shift_local(1).shape_at(&var(0))) }
            } else {
                (*p.shape).clone()
            };
            sums.push((shape_ty, join(&li, &p.ls)));
            let lab = if indexed { snd(var(0)) } else { var(0) };
            let pos_ty = pq.pos_at(0, lab);
            let Some(code) = crate::code::code_of(&pos_ty) else {
                return err("corecursion up to a friend beside nested constructors needs the codata's positions to have a code", span);
            };
            comps.push(vec![Some((pos_ty, Rc::new(code)))]);
            lp_parts.push(p.lp.clone());
            outs.push(if indexed { fst(var(0)) } else { triv() });
            // Over (site, v, y): the child at position y of the label.
            let lab2 = if indexed { snd(var(1)) } else { var(1) };
            let pq2 = p.reindexed(2, if indexed { fst(var(1)) } else { triv() });
            kid_idx.push(vec![pq2.next_tm(0, lab2, var(0))]);
        }
        let first_friend = sums.len();
        for f in friends {
            let (a, al) = f.label_ty(0);
            sums.push((a, al));
            let v = var(0);
            let vals = f.projections(&v);
            let mut cs = Vec::new();
            let mut ks = Vec::new();
            for t in &f.trees {
                match &t.dom {
                    None => {
                        cs.push(None);
                        // Over (site, v, y) with y unused.
                        ks.push(Rc::new(t.index.apply_local(&f.subst(&g, 1, &vals, 0)).shift_local(1)));
                    }
                    Some((dom, dl)) => {
                        let dom = dom.apply_local(&f.subst(&g, 1, &vals, 0));
                        let Some(code) = crate::code::code_of(&dom) else {
                            return err(format!("the friend `{}` has a function argument whose domain has no code", f.written), f.span);
                        };
                        lp_parts.push(dl.clone());
                        cs.push(Some((dom, Rc::new(code))));
                        ks.push(Rc::new(t.index.apply_local(&f.subst(&g, 1, &vals, 1))));
                    }
                }
            }
            comps.push(cs);
            outs.push(if indexed { Rc::new(f.result.apply_local(&f.subst(&g, 1, &vals, 0))) } else { triv() });
            kid_idx.push(ks);
        }
        // Every position lives at one level, so the positions' case tree is
        // a family of codes at one universe.
        let lp = lp_parts.iter().fold(Level::Zero, |acc, l| Level::join(acc, l.clone()));
        if lp_parts.iter().any(|l| !l.equiv(&lp)) {
            return err(
                "corecursion up to a friend needs every function argument's domain (and the codata's positions, beside nested constructors) at one universe level this round",
                span,
            );
        }
        let ls = sums.iter().fold(Level::Zero, |acc, (_, l)| Level::join(acc, l.clone()));
        let lk = join(&li, &lp);
        let lw0 = join(&ls, &lp);
        let level = if indexed { join(&lw0, &lk) } else { lw0 };
        Ok(FreeTy { g, indexed, idx, idx_code: Rc::new(idx_code), li, dsig, lw, sums, first_friend, pending, comps, outs, kid_idx, ls, lp, lk, level })
    }

    /// `Mot(z)`, the step's elimination motive at the tree `z` (scoped at
    /// `k`): `Π(j : I). El(ok z j) → F(C)(j)`, or `F(C)` unindexed.
    fn free_mot(&self, p: &MParts, ty: &FreeTy, carrier: &Carrier, sl: &Level, k: u32, z: Rc<Term>) -> Type {
        if !ty.indexed {
            return Codata(self).step_ty(p, k, carrier);
        }
        let f = Codata(self).node_ty_at(p, k + 2, &var(1), carrier);
        pi(&ty.li, &join(&ty.lk, sl), ty.idx.shift_local(k), pi(&ty.lk, sl, ty.ok_at(k + 1, Rc::new(z.shift_local(1)), var(0)), f))
    }

    fn free_mot_level(ty: &FreeTy, sl: &Level) -> Level {
        if ty.indexed { join(&ty.li, &join(&ty.lk, sl)) } else { sl.clone() }
    }

    /// The types of a friend arm's four binders at summand `r` (`(p, f, ih,
    /// ok)`), each scoped past the earlier ones.
    fn free_arm_binders(&self, p: &MParts, ty: &FreeTy, carrier: &Carrier, sl: &Level, r: usize, k: u32, lab: (Type, Level)) -> Vec<(Type, Level)> {
        let lw0 = ty.lw0();
        let ml = Self::free_mot_level(ty, sl);
        let pv = |d: u32| var(d);
        let f_ty = pi(&ty.lp, &lw0, ty.comps_ty(r, k + 1, &pv(0)), ty.w0(k + 2));
        let ih_ty = pi(&ty.lp, &ml, ty.comps_ty(r, k + 2, &pv(1)), self.free_mot(p, ty, carrier, sl, k + 3, app(var(1), var(0))));
        let ok_ty = if ty.indexed {
            pi(
                &ty.lp,
                &ty.lk,
                ty.comps_ty(r, k + 3, &pv(2)),
                ty.ok_at(k + 4, app(var(2), var(0)), Rc::new(ty.child_r(r, k + 4, &var(3), var(0)))),
            )
        } else {
            Type::Unit { level: Level::Zero }
        };
        let ok_level = if ty.indexed { ty.lk.clone() } else { Level::Zero };
        vec![lab, (f_ty, join(&ty.lp, &lw0)), (ih_ty, join(&ty.lp, &ml)), (ok_ty, ok_level)]
    }

    /// Re-elaborate each friend's body over the carrier, its codata
    /// parameters bound to the node's children (§5.5).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn free_arms(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        p: &MParts,
        carrier: &Carrier,
        ty: Rc<FreeTy>,
        friends: Vec<Friend>,
        user: &str,
        step_level: &Level,
    ) -> R<Free> {
        let friends: Vec<Rc<Friend>> = friends.into_iter().map(Rc::new).collect();
        let mut arms = Vec::with_capacity(friends.len());
        for (f, friend) in friends.iter().enumerate() {
            let r = ty.first_friend + f;
            let lab = friend.label_ty(0);
            let mut acx = cx.clone();
            for (name, (t, l)) in ["#fp", "#ff", "#fih", "#fok"].iter().zip(self.free_arm_binders(p, &ty, carrier, step_level, r, 0, lab)) {
                acx.push((*name).into(), t, l);
            }
            let mut fcx = acx.hygienic();
            let base = fcx.names.len();
            let sig = Rc::clone(friend);
            let pv = var(3);
            let vals = friend.projections(&pv);
            for (tv, a) in friend.decl.tyvars.iter().zip(&friend.tyargs) {
                let (t, level) = match a {
                    TyArg::Fixed(t, l) => (t.shift_local(4), l.clone()),
                    TyArg::Data(m, l) => (Type::El { level: l.clone(), tm: Rc::clone(&vals[*m]) }, l.clone()),
                };
                fcx.tyvars.push(TyVar { name: tv.name.clone(), ty: t, level, depth: base });
            }
            let mut trees = Vec::new();
            let mode_stub = FriendMode {
                depth: cx.names.len(),
                ind: Rc::clone(ind),
                carrier: carrier.clone(),
                free: Rc::clone(&ty),
                r,
                friend: friend.written.clone(),
                user: user.to_string(),
                selfref: Rc::new(SelfRef::of_decl(&friend.decl)),
                sig: Rc::clone(&sig),
                base,
                trees: Vec::new(),
                children: Vec::new(),
            };
            for (q, role) in friend.decl.params.iter().zip(&friend.roles) {
                let (term, ty_q, level) = match role {
                    Role::Fixed(v, t, l, m) => {
                        let s = friend.subst(&cx.gamma, 4, &vals[..*m], 0);
                        // `v` is scoped over (site, d₀ … d_{m-1}) already.
                        (Rc::new(v.apply_local(&s)), t.apply_local(&s), l.clone())
                    }
                    Role::Data(m) => {
                        let s = friend.subst(&cx.gamma, 4, &vals[..*m], 0);
                        let (t, l) = &friend.data[*m];
                        (Rc::clone(&vals[*m]), t.apply_local(&s), l.clone())
                    }
                    Role::Tree(j) => {
                        let t = &friend.trees[*j];
                        match &t.dom {
                            None => {
                                let idx = mode_stub.param_index(base, *j, &triv());
                                (mode_stub.child_value(base, *j, Rc::new(Term::Triv { level: ty.lp.clone() })), ty.c_at(4, &idx), ty.level.clone())
                            }
                            Some((dom, dl)) => {
                                let dom = dom.apply_local(&friend.subst(&cx.gamma, 4, &vals, 0));
                                let body = mode_stub.child_value(base + 1, *j, var(0));
                                let idx = mode_stub.param_index(base + 1, *j, &var(0));
                                let fty = pi(dl, &ty.level, dom.clone(), ty.c_at(5, &idx));
                                (Rc::new(lam(dl, &ty.level, dom, (*body).clone())), fty, join(dl, &ty.level))
                            }
                        }
                    }
                };
                let alias = Rc::new(Alias {
                    skel: None,
                    name: q.name.clone(),
                    depth: base,
                    term,
                    ty: ty_q.clone(),
                    level,
                    spliced: None,
                    shifted: Default::default(),
                });
                if let Role::Tree(j) = role {
                    trees.push((Rc::clone(&alias), *j));
                }
                if let (Role::Fixed(..) | Role::Data(_), Type::Ty(level)) = (role, &ty_q) {
                    fcx.tyvars.push(TyVar { name: q.name.clone(), ty: Type::El { level: level.clone(), tm: Rc::clone(&alias.term) }, level: level.clone(), depth: base });
                }
                fcx.aliases.push(alias);
            }
            let res = Rc::new(friend.result.apply_local(&friend.subst(&cx.gamma, 4, &vals, 0)));
            let want = Codata(self).node_ty_at(p, 4, &res, carrier);
            fcx.friend = Some(Rc::new(FriendMode { trees, ..mode_stub }));
            let arm = {
                let _scope = friend.scope.as_ref().map(|s| self.use_scope(s));
                crate::statements::check_block(self.0, &fcx, &friend.decl.body, &want, step_level, None, None, true)
            };
            match arm {
                Ok(t) => arms.push(t),
                // Said at the definition's call, whatever span the friend's
                // own body reported it at.
                Err(ElabError::Elab { msg, .. }) => {
                    let msg = if msg.contains("is not a friend of") {
                        msg
                    } else {
                        format!(
                            "`{}` is not a friend of the corecursive `{user}` (docs/inductives/codata-elaborator-design.md §5.5): its body does not elaborate over the free carrier: {msg}",
                            friend.written
                        )
                    };
                    return err(msg, friend.span);
                }
                Err(other) => return Err(other),
            }
        }
        Ok(Free { ty, friends, arms })
    }

    // -- carrier positions -----------------------------------------------------

    /// `C(idx)` at depth `k`, the index read off when `expected` is one.
    fn free_c_index(&self, cx: &Cx, free: &FreeTy, k: u32, expected: &Type, span: Span) -> Option<Rc<Term>> {
        if let Some(i) = free.index_of_c(k, expected) {
            return Some(i);
        }
        let w = self.whnf(cx, expected, span).ok()?;
        free.index_of_c(k, &w)
    }

    /// `Π(y : A). C(idx(y))`: the domain, its level and the index over `y`.
    fn free_c_fn(&self, cx: &Cx, free: &FreeTy, k: u32, expected: &Type, span: Span) -> Option<(Rc<Type>, Level, Rc<Term>)> {
        let Ok(Type::Pi { dom_level, dom, cod, .. }) = self.whnf(cx, expected, span) else {
            return None;
        };
        let mut cy = cx.clone();
        cy.push("#y".into(), (*dom).clone(), dom_level.clone());
        let i = self.free_c_index(&cy, free, k + 1, &cod, span)?;
        Some((dom, dom_level, i))
    }

    /// `C(o) + ⟦D⟧(o)` at depth `k`: the child position's index `o`.
    fn free_child_index(&self, cx: &Cx, free: &FreeTy, k: u32, expected: &Type, span: Span) -> Option<Rc<Term>> {
        let w = self.whnf(cx, expected, span).ok()?;
        let Type::Sum { lhs, rhs, .. } = &w else {
            return None;
        };
        let i = self.free_c_index(cx, free, k, lhs, span)?;
        let want = free.dsig.shift_local(k).at(Rc::clone(&i));
        (**rhs == want || self.conv_types(cx, rhs, &want, &free.lw)).then_some(i)
    }

    /// Whether `res` (a friend's result index) is `idx`, said at the call.
    fn free_same_index(&self, cx: &Cx, free: &FreeTy, k: u32, res: &Rc<Term>, idx: &Rc<Term>, who: &str, span: Span) -> R<()> {
        if !free.indexed {
            return Ok(());
        }
        let a = free.dsig.shift_local(k).at(Rc::clone(res));
        let b = free.dsig.shift_local(k).at(Rc::clone(idx));
        if res == idx || self.conv_types(cx, &a, &b, &free.lw) {
            return Ok(());
        }
        err(
            format!(
                "this call to `{who}` is at `{}`, but the place it stands in is at `{}`: a friend's result index must be the one its position wrote (docs/inductives/codata-elaborator-design.md §5.6)",
                self.display_type(cx, &a),
                self.display_type(cx, &b)
            ),
            span,
        )
    }

    /// A friend's data arguments, each checked at its component's type with
    /// the earlier ones substituted; a type parameter stored as data takes
    /// the written type argument, or `own` (the friend's own label, in
    /// friend mode) when none is written.
    #[allow(clippy::too_many_arguments)]
    fn free_data(
        &self,
        cx: &Cx,
        g: &LocalCtx,
        friend: &Friend,
        k: u32,
        tys: &[Ty],
        args: &[&Expr],
        own: Option<&[Rc<Term>]>,
        check: &dyn Fn(&Expr) -> R<()>,
        span: Span,
    ) -> R<Vec<Rc<Term>>> {
        let nd = friend.nd();
        let mut vals: Vec<Option<Rc<Term>>> = vec![None; nd];
        if !tys.is_empty() && tys.len() != friend.tyargs.len() {
            return err(format!("`{}` takes {} type argument(s), found {}", friend.written, friend.tyargs.len(), tys.len()), span);
        }
        for (i, a) in friend.tyargs.iter().enumerate() {
            match a {
                TyArg::Data(m, _) => {
                    let v = if let Some(t) = tys.get(i) {
                        let (t, _) = self.elab_ty(cx, t)?;
                        let Some(c) = crate::code::code_of(&t) else {
                            return err(format!("the type argument of `{}` has no code", friend.written), span);
                        };
                        Rc::new(c)
                    } else if let Some(own) = own {
                        Rc::clone(&own[*m])
                    } else {
                        return err(
                            format!(
                                "write `{}`'s type arguments at this call (`{}<…>(…)`): its type parameter `{}` is not read off the definition's type, so the friend's node stores it (docs/inductives/codata-elaborator-design.md §5.6)",
                                friend.written,
                                friend.written,
                                friend.decl.tyvars[i].name
                            ),
                            span,
                        );
                    };
                    vals[*m] = Some(v);
                }
                TyArg::Fixed(t, l) => {
                    if let Some(w) = tys.get(i) {
                        let (w, _) = self.elab_ty(cx, w)?;
                        if !self.conv_types(cx, &w, &t.shift_local(k), &Level::succ(l.clone())) {
                            return err(format!("the type argument `{}` of `{}` is the definition's own", friend.decl.tyvars[i].name, friend.written), span);
                        }
                    }
                }
            }
        }
        for (i, role) in friend.roles.iter().enumerate() {
            match role {
                Role::Data(m) => {
                    check(args[i])?;
                    let done: Vec<Rc<Term>> = vals[..*m].iter().map(|v| Rc::clone(v.as_ref().expect("earlier data is in hand"))).collect();
                    let (t, l) = &friend.data[*m];
                    let want = t.apply_local(&friend.subst(g, k, &done, 0));
                    vals[*m] = Some(Rc::new(self.elab_check(cx, args[i], &want, l)?));
                }
                Role::Fixed(v, t, l, m) => {
                    check(args[i])?;
                    let done: Vec<Rc<Term>> = vals[..*m].iter().map(|v| Rc::clone(v.as_ref().expect("earlier data is in hand"))).collect();
                    let s = friend.subst(g, k, &done, 0);
                    let want = t.apply_local(&s);
                    let got = self.elab_check(cx, args[i], &want, l)?;
                    let v = v.apply_local(&s);
                    let eq = Type::Id { level: l.clone(), ty: Rc::new(want.clone()), lhs: Rc::new(got.clone()), rhs: Rc::new(v.clone()) };
                    let refl = Type::Id { level: l.clone(), ty: Rc::new(want), lhs: Rc::new(v.clone()), rhs: Rc::new(v.clone()) };
                    if got != v && !self.conv_types(cx, &eq, &refl, l) {
                        return err(
                            format!(
                                "the argument `{}` of the friend `{}` is read off the definition's codata type, so it must be the definition's own",
                                friend.decl.params[i].name, friend.written
                            ),
                            args[i].span,
                        );
                    }
                }
                Role::Tree(_) => {}
            }
        }
        Ok(vals.into_iter().map(|v| v.expect("every data component is filled")).collect())
    }

    /// A friend node at `idx` from its call's arguments (at depth `k`): data
    /// by [`Self::free_data`], each codata argument checked at its carrier
    /// position `C(c_j)` (or `Π(y : A_j). C(c_j(y))`), whose hooks build the
    /// value.
    #[allow(clippy::too_many_arguments)]
    fn free_friend_node(
        &self,
        cx: &Cx,
        free: &FreeTy,
        friend: &Friend,
        r: usize,
        k: u32,
        tys: &[Ty],
        args: &[&Expr],
        idx: &Rc<Term>,
        own: Option<&[Rc<Term>]>,
        check: &dyn Fn(&Expr) -> R<()>,
        span: Span,
    ) -> R<Term> {
        if args.len() != friend.roles.len() {
            return err(format!("`{}` takes {} argument(s), found {}", friend.written, friend.roles.len(), args.len()), span);
        }
        let vals = self.free_data(cx, &free.g, friend, k, tys, args, own, check, span)?;
        let res = Rc::new(friend.result.apply_local(&friend.subst(&free.g, k, &vals, 0)));
        self.free_same_index(cx, free, k, &res, idx, &friend.written, span)?;
        let mut chs = Vec::new();
        for (i, role) in friend.roles.iter().enumerate() {
            let Role::Tree(j) = role else {
                continue;
            };
            let t = &friend.trees[*j];
            match &t.dom {
                None => {
                    let ci = Rc::new(t.index.apply_local(&friend.subst(&free.g, k, &vals, 0)));
                    let v = self.elab_check(cx, args[i], &free.c_at(k, &ci), &free.level)?;
                    chs.push(ChildVal::Plain(Rc::new(v)));
                }
                Some((dom, dl)) => {
                    let dom = dom.apply_local(&friend.subst(&free.g, k, &vals, 0));
                    let ci = Rc::new(t.index.apply_local(&friend.subst(&free.g, k, &vals, 1)));
                    let fty = pi(dl, &free.level, dom, free.c_at(k + 1, &ci));
                    let v = Rc::new(self.elab_check(cx, args[i], &fty, &join(dl, &free.level))?);
                    chs.push(ChildVal::Fun(under_app(&v)));
                }
            }
        }
        let label = Rc::new(friend.label(k, &vals));
        Ok(free.node(k, r, label, idx, &chs))
    }

    /// A constructor of the declaration with corecursive calls in it, at a
    /// carrier position `C(idx)`: a pending node (§5.6), its children
    /// elaborated at the child positions as the body's own are.
    #[allow(clippy::too_many_arguments)]
    fn free_pending(&self, cx: &Cx, p: &MParts, free: &FreeTy, ind: &Inductive, carrier: &Carrier, k: u32, idx: &Rc<Term>, i: usize, args: &[&Expr], span: Span) -> R<Term> {
        let q = if free.indexed { p.reindexed(0, Rc::clone(idx)) } else { p.reindexed(0, triv()) };
        let node = Rc::new(Codata(self).corec_node(cx, &q, ind, carrier, i, args, span)?);
        let lab = fst(Rc::clone(&node));
        let v = if free.indexed {
            Rc::new(Term::Pair {
                fst_level: free.li.clone(),
                snd_level: p.ls.clone(),
                fst_ty: Rc::new(free.idx.shift_local(k)),
                snd_ty: Rc::new(free.dsig.shift_local(k + 1).shape_at(&var(0))),
                fst: Rc::clone(idx),
                snd: lab,
            })
        } else {
            lab
        };
        // Each child `C(o) + ⟦D⟧(o)` as a `C(o)`, `o` read at the position.
        let o = q.next_tm(1, Rc::new(fst(Rc::new(node.shift_local(1))).as_ref().clone()), var(0));
        let child = free.embed(k + 1, &o, app(snd(Rc::new(node.shift_local(1))), var(0)));
        Ok(free.node(k, 2, v, idx, &[ChildVal::Fun(Rc::new(child))]))
    }

    // -- the definition's side -------------------------------------------------

    /// `e` as a call to one of the definition's friends, if it is one.
    pub(super) fn friend_call<'e>(&self, cx: &Cx, free: &Free, e: &'e Expr) -> Option<(usize, &'e [Ty], Vec<&'e Expr>)> {
        let (name, tys, args) = call_parts(e)?;
        if locally_bound(cx, name) {
            return None;
        }
        let f = free.friends.iter().position(|f| f.written == name)?;
        Some((f, tys, args))
    }

    /// The checking hook at a carrier position of a definition over a free
    /// carrier (`C(idx)`, or a function into it): a corecursive call is a
    /// seed, a friend's call a friend node, a constructor with calls in it a
    /// pending node, anything else an existing tree.
    pub(super) fn free_site_check(&self, cx: &Cx, site: &CorecSite, free: &Free, e: &Expr, expected: &Type) -> R<Option<Term>> {
        let k = site.by(cx);
        let ty = &free.ty;
        let control = matches!(e.kind, ExprKind::Match { .. } | ExprKind::Block(..) | ExprKind::Lam { .. });
        if let Some(idx) = self.free_c_index(cx, ty, k, expected, e.span) {
            if control {
                return Ok(None);
            }
            let Some(p) = MParts::read(&site.d_ty.shift_local(k), &cx.gamma) else {
                return err("internal: a codata declaration did not lower to its `M` encoding", e.span);
            };
            if let Some((args, _)) = surface_self_call(&site.selfref, e) {
                if let ExprKind::App { head, .. } = &e.kind
                    && matches!(head.kind, ExprKind::TyApp { .. })
                {
                    return err("a corecursive call takes no type arguments: they are the definition's own", e.span);
                }
                let seed = Codata(self).corec_seed(cx, site, &p, &site.seeds.under(k), &idx, &args, e.span)?;
                return Ok(Some(ty.seed_leaf(k, &idx, Rc::new(seed))));
            }
            if let Some((f, tys, args)) = self.friend_call(cx, free, e)
                && nested_self_call(&site.selfref, e).is_some()
            {
                let friend = &free.friends[f];
                let selfref = Rc::clone(&site.selfref);
                let check = move |a: &Expr| -> R<()> {
                    match nested_self_call(&selfref, a) {
                        Some(at) => err(
                            format!(
                                "this call to `{}` sits in a data argument of the friend `{}`, where no corecursive call is guarded (docs/inductives/codata-elaborator-design.md §5.5)",
                                selfref.written_name, friend.written
                            ),
                            at,
                        ),
                        None => Ok(()),
                    }
                };
                return Ok(Some(self.free_friend_node(cx, ty, friend, ty.first_friend + f, k, tys, &args, &idx, None, &check, e.span)?));
            }
            if nested_self_call(&site.selfref, e).is_some() {
                if ty.pending
                    && let Some((i, args)) = Codata(self).codata_ctor_app(cx, &site.ind, e)
                {
                    let carrier = site.carrier.under(k);
                    return Ok(Some(self.free_pending(cx, &p, ty, &site.ind, &carrier, k, &idx, i, &args, e.span)?));
                }
                let at = nested_self_call(&site.selfref, e).expect("checked");
                return err(nested_guard_msg(&site.selfref.written_name), at);
            }
            let t = self.elab_check(cx, e, &ty.dsig.shift_local(k).at(Rc::clone(&idx)), &ty.lw)?;
            return Ok(Some(ty.tree_leaf(k, &idx, Rc::new(t))));
        }
        // A function into the carrier given as a function: its η-expansion
        // over existing trees.
        if !control
            && let Some((dom, dl, idx)) = self.free_c_fn(cx, ty, k, expected, e.span)
        {
            if let Some(at) = nested_self_call(&site.selfref, e) {
                return err(nested_guard_msg(&site.selfref.written_name), at);
            }
            let fty = pi(&dl, &ty.lw, (*dom).clone(), ty.dsig.shift_local(k + 1).at(Rc::clone(&idx)));
            let f = Rc::new(self.elab_check(cx, e, &fty, &join(&dl, &ty.lw))?);
            return Ok(Some(lam(&dl, &ty.level, (*dom).clone(), ty.tree_leaf(k + 1, &idx, under_app(&f)))));
        }
        Ok(None)
    }

    // -- friend mode -----------------------------------------------------------

    /// The checking-mode hook while a friend's body is re-elaborated over a
    /// free carrier (§5.5): a `match` on a codata parameter reads its node,
    /// a call to the friend itself is a node of `C`, a codata parameter at a
    /// child is its own child, at the node its first node.
    pub(crate) fn friend_check(&self, cx: &Cx, mode: &Rc<FriendMode>, e: &Expr, expected: &Type, lvl: &Level) -> R<Option<Term>> {
        let _ = lvl;
        let now = cx.names.len();
        let k = (now - mode.depth) as u32;
        let free = &mode.free;
        let carrier = mode.carrier.under(k);
        let friend = Rc::clone(&mode.sig);
        let (pv, ..) = mode.binders(now);
        let res = Rc::new(friend.result.apply_local(&friend.subst(&free.g, k, &friend.projections(&pv), 0)));
        let Some(p) = MParts::read(&free.dsig.shift_local(k).at(Rc::clone(&res)), &cx.gamma) else {
            return err("internal: a codata declaration did not lower to its `M` encoding", e.span);
        };
        let node_ty = Codata(self).step_ty(&p, 0, &carrier);
        let node_level = Codata::node_level(&p, &carrier);
        let at_node = *expected == node_ty || {
            let head = self.whnf(cx, expected, e.span).ok();
            matches!(head, Some(Type::Sigma { .. })) && self.conv_types(cx, expected, &node_ty, &node_level)
        };
        let child_idx = if at_node { None } else { self.free_child_index(cx, free, k, expected, e.span) };
        let c_idx = if at_node || child_idx.is_some() { None } else { self.free_c_index(cx, free, k, expected, e.span) };
        fn applied<'e>(mode: &FriendMode, cx: &Cx, friend: &Friend, s: &'e Expr) -> Option<(usize, Option<&'e Expr>)> {
            match &s.kind {
                ExprKind::Var(n) => mode.tree_param(cx, n).map(|j| (j, None)),
                ExprKind::App { head, args, named, .. } if named.is_empty() && args.len() == 1 => match &head.kind {
                    ExprKind::Var(n) => mode.tree_param(cx, n).filter(|j| friend.trees[*j].dom.is_some()).map(|j| (j, Some(&args[0]))),
                    _ => None,
                },
                _ => None,
            }
        }
        let applied_param = |s| applied(mode, cx, &friend, s);
        // The payload a function parameter is applied at, elaborated.
        let payload = |j: usize, a: Option<&Expr>| -> R<Rc<Term>> {
            match (a, &friend.trees[j].dom) {
                (None, _) => Ok(Rc::new(Term::Triv { level: free.lp.clone() })),
                (Some(a), Some((dom, dl))) => {
                    let dom = dom.apply_local(&friend.subst(&free.g, k, &friend.projections(&pv), 0));
                    if let Some((n, at)) = mode.mentioned(cx, a) {
                        return mode.refuse(&format!("it applies a codata argument at something built from `{n}`"), at);
                    }
                    Ok(Rc::new(self.elab_check(cx, a, &dom, dl)?))
                }
                (Some(_), None) => unreachable!("only a function parameter is applied"),
            }
        };
        // A `match` on a codata parameter (or a function one, applied) reads
        // the node `ih` computed for it.
        if let ExprKind::Match { scrut, eqbind, motive, arms, .. } = &e.kind {
            if let Some((j, a)) = applied_param(scrut) {
                let s = match &scrut.kind {
                    ExprKind::Var(n) => n.clone(),
                    _ => mode.trees.iter().find(|(_, jj)| *jj == j).map(|(al, _)| al.name.clone()).unwrap_or_default(),
                };
                if friend.trees[j].dom.is_some() && a.is_none() {
                    return mode.refuse(&format!("it matches on `{s}`, a function: apply it first"), scrut.span);
                }
                if eqbind.is_some() || motive.is_some() {
                    return mode.refuse(&format!("its `match` on `{s}` names an equation or a motive, which a friend's step cannot keep"), e.span);
                }
                let y = payload(j, a)?;
                let n = mode.ind.ctors.len();
                let mut ordered: Vec<Option<&heather_syntax::Arm>> = vec![None; n];
                for a in arms {
                    if a.binders.iter().any(|b| !matches!(b, Pat::Var { .. })) {
                        return mode.refuse(&format!("its `match` on `{s}` reads deeper than `{s}`'s first layer"), a.span);
                    }
                    if a.default {
                        for slot in ordered.iter_mut().filter(|o| o.is_none()) {
                            *slot = Some(a);
                        }
                        continue;
                    }
                    let Some(i) = crate::inductive::arm_ctor_index(&mode.ind, &a.ctor) else {
                        return err(format!("`{}` is not a constructor of `{}`", a.ctor, mode.ind.name), a.span);
                    };
                    if a.binders.len() != mode.ind.ctors[i].fields.len() {
                        return err(
                            format!("`{}` binds {} field(s), found {}", a.ctor, mode.ind.ctors[i].fields.len(), a.binders.len()),
                            a.span,
                        );
                    }
                    ordered[i] = Some(a);
                }
                if ordered.iter().any(|a| a.is_none()) {
                    return err(format!("this `match` on `{s}` is missing an arm"), e.span);
                }
                if ordered.iter().zip(&mode.ind.ctors).any(|(a, c)| a.is_some_and(|a| a.default && !c.fields.is_empty())) {
                    return mode.refuse(&format!("its `match` on `{s}` has a `_` arm, which binds no children; write the arms out"), e.span);
                }
                let arms: Vec<&heather_syntax::Arm> = ordered.into_iter().map(|a| a.expect("checked above")).collect();
                let pi_idx = mode.param_index(now, j, &y);
                let Some(q) = MParts::read(&free.dsig.shift_local(k).at(pi_idx), &cx.gamma) else {
                    return err("internal: a codata declaration did not lower to its `M` encoding", e.span);
                };
                let t = Codata(self).match_m_over(cx, &mode.ind, &arms, &q, expected.clone(), lvl.clone(), Observed::Node(mode.node_of(now, j, y), &carrier), e.span)?;
                return Ok(Some(t));
            }
            if let ExprKind::Var(s) = &scrut.kind
                && mode.child_param(cx, s)
            {
                return mode.refuse(&format!("it matches on `{s}`, a child of its argument: a friend reads one layer of each argument"), scrut.span);
            }
        }
        let control = matches!(e.kind, ExprKind::Match { .. } | ExprKind::Block(..));
        let unfriendly = |e: &Expr| -> R<()> {
            if let Some((n, span)) = mode.mentioned(cx, e) {
                return mode.refuse(
                    &format!("it reads `{n}` inside a tree it builds: a friend may only `match` on a codata argument, pass it or its children to itself, or return them as children"),
                    span,
                );
            }
            if let Some(span) = nested_self_call(&mode.selfref, e) {
                return mode.refuse("it calls itself inside a tree other than its own result's constructor", span);
            }
            Ok(())
        };
        // Its own call: a friend node of the carrier.
        let own_node = |idx: &Rc<Term>, args: &[&Expr], tys: &[Ty]| -> R<Term> {
            let check = |a: &Expr| -> R<()> {
                if let Some((n, at)) = mode.mentioned(cx, a) {
                    return mode.refuse(&format!("it passes `{n}` inside a data argument to itself"), at);
                }
                if let Some(at) = nested_self_call(&mode.selfref, a) {
                    return mode.refuse("it calls itself inside a data argument to itself", at);
                }
                Ok(())
            };
            let own = mode.data_vals(now);
            self.free_friend_node(cx, free, &friend, mode.r, k, tys, args, idx, Some(&own), &check, e.span)
        };
        let self_call = surface_self_call(&mode.selfref, e).map(|(args, _)| {
            let tys: &[Ty] = match &e.kind {
                ExprKind::App { head, .. } => match &head.kind {
                    ExprKind::TyApp { args, .. } => args,
                    _ => &[],
                },
                _ => &[],
            };
            (args, tys)
        });
        // A codata parameter's index must be the place's.
        let same = |j: usize, y: &Rc<Term>, idx: &Rc<Term>, span: Span| -> R<()> {
            let pi_idx = mode.param_index(now, j, y);
            self.free_same_index(cx, free, k, &pi_idx, idx, &mode.friend, span)
        };
        // A function child passed whole at a function child position: its
        // η-expansion, whose body meets the child position applied.
        if let ExprKind::Var(s) = &e.kind
            && mode.child_param(cx, s)
            && matches!(self.whnf(cx, expected, e.span), Ok(Type::Pi { .. }))
        {
            let y = "#eta".to_string();
            let at = |kind| Expr { kind, span: e.span };
            let lam = at(ExprKind::Lam {
                binders: vec![heather_syntax::LamBinder { name: y.clone(), ty: None, implicit: false, span: e.span }],
                body: Box::new(at(ExprKind::App {
                    head: Box::new(e.clone()),
                    args: vec![at(ExprKind::Var(y))],
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                })),
            });
            return Ok(Some(self.elab_check(cx, &lam, expected, lvl)?));
        }
        if let Some(idx) = child_idx {
            if let Some((args, tys)) = &self_call {
                let v = own_node(&idx, args, tys)?;
                return Ok(Some(Term::Inl {
                    lhs_level: free.level.clone(),
                    rhs_level: free.lw.clone(),
                    lhs: Rc::new(free.c_at(k, &idx)),
                    rhs: Rc::new(free.dsig.shift_local(k).at(Rc::clone(&idx))),
                    val: Rc::new(v),
                }));
            }
            if let Some((j, a)) = applied_param(e) {
                let y = payload(j, a)?;
                same(j, &y, &idx, e.span)?;
                return Ok(Some(Term::Inl {
                    lhs_level: free.level.clone(),
                    rhs_level: free.lw.clone(),
                    lhs: Rc::new(free.c_at(k, &idx)),
                    rhs: Rc::new(free.dsig.shift_local(k).at(Rc::clone(&idx))),
                    val: mode.child_value(now, j, y),
                }));
            }
            if let ExprKind::Var(s) = &e.kind
                && mode.child_param(cx, s)
            {
                return Ok(None);
            }
            if control || matches!(e.kind, ExprKind::Lam { .. }) {
                return Ok(None);
            }
            if let ExprKind::App { head, .. } = &e.kind
                && let ExprKind::Var(s) = &head.kind
                && mode.child_param(cx, s)
            {
                return Ok(None);
            }
            unfriendly(e)?;
            let d_here = free.dsig.shift_local(k).at(Rc::clone(&idx));
            let t = self.elab_check(cx, e, &d_here, &free.lw)?;
            return Ok(Some(Term::Inr {
                lhs_level: free.level.clone(),
                rhs_level: free.lw.clone(),
                lhs: Rc::new(free.c_at(k, &idx)),
                rhs: Rc::new(d_here),
                val: Rc::new(t),
            }));
        }
        if let Some(idx) = c_idx {
            if let Some((args, tys)) = &self_call {
                return Ok(Some(own_node(&idx, args, tys)?));
            }
            if let Some((j, a)) = applied_param(e) {
                let y = payload(j, a)?;
                same(j, &y, &idx, e.span)?;
                return Ok(Some((*mode.child_value(now, j, y)).clone()));
            }
            if control {
                return Ok(None);
            }
            if mode.mentioned(cx, e).is_some() {
                // A child (or something built from one) whose type is `C(o) +
                // ⟦D⟧(o)`: a carrier value stays, a tree becomes a leaf.
                let (t, ty, _) = self.elab_infer(cx, e)?;
                let Some(o) = self.free_child_index(cx, free, k, &ty, e.span) else {
                    let (n, _) = mode.mentioned(cx, e).expect("checked above");
                    return mode.refuse(&format!("it passes something built from `{n}` to itself, where only a child of its argument may go"), e.span);
                };
                self.free_same_index(cx, free, k, &o, &idx, &mode.friend, e.span)?;
                return Ok(Some(free.embed(k, &idx, Rc::new(t))));
            }
            if let Some(at) = nested_self_call(&mode.selfref, e) {
                return mode.refuse("it calls itself inside an argument to itself that is not a call", at);
            }
            let t = self.elab_check(cx, e, &free.dsig.shift_local(k).at(Rc::clone(&idx)), &free.lw)?;
            return Ok(Some(free.tree_leaf(k, &idx, Rc::new(t))));
        }
        if !at_node {
            // A function into the carrier: a function parameter passed on
            // whole, a function child η-expanded, an existing function's
            // trees as leaves.
            if !control
                && !matches!(e.kind, ExprKind::Lam { .. })
                && let Some((dom, dl, idx)) = self.free_c_fn(cx, free, k, expected, e.span)
            {
                if let ExprKind::Var(s) = &e.kind {
                    if let Some(j) = mode.tree_param(cx, s).filter(|j| friend.trees[*j].dom.is_some()) {
                        let mut cy = cx.clone();
                        cy.push("#y".into(), (*dom).clone(), dl.clone());
                        let pi_idx = mode.param_index(now + 1, j, &var(0));
                        self.free_same_index(&cy, free, k + 1, &pi_idx, &idx, &mode.friend, e.span)?;
                        return Ok(Some(lam(&dl, &free.level, (*dom).clone(), (*mode.child_value(now + 1, j, var(0))).clone())));
                    }
                    if mode.child_param(cx, s) {
                        let (t, _, _) = self.elab_infer(cx, e)?;
                        let applied = under_app(&Rc::new(t));
                        return Ok(Some(lam(&dl, &free.level, (*dom).clone(), free.embed(k + 1, &idx, applied))));
                    }
                }
                unfriendly(e)?;
                let fty = pi(&dl, &free.lw, (*dom).clone(), free.dsig.shift_local(k + 1).at(Rc::clone(&idx)));
                let f = Rc::new(self.elab_check(cx, e, &fty, &join(&dl, &free.lw))?);
                return Ok(Some(lam(&dl, &free.level, (*dom).clone(), free.tree_leaf(k + 1, &idx, under_app(&f)))));
            }
            if let Some((_, _)) = &self_call {
                return mode.refuse(
                    "a call to itself must be a child of the constructor it returns (one layer of output for each layer it reads)",
                    e.span,
                );
            }
            if let ExprKind::Var(s) = &e.kind
                && mode.tree_param(cx, s).is_some()
            {
                return mode.refuse(
                    &format!("it uses `{s}` as a tree; a friend may only `match` on a codata argument, pass it to itself, or return it"),
                    e.span,
                );
            }
            if let ExprKind::Var(s) = &e.kind
                && mode.child_param(cx, s)
            {
                if control {
                    return Ok(None);
                }
                return mode.refuse(
                    &format!("it uses `{s}`, a child of its argument, other than as a child of its result or an argument to itself: a friend reads one layer of each argument"),
                    e.span,
                );
            }
            return Ok(None);
        }
        // The node position.
        if control {
            return Ok(None);
        }
        if let Some((j, a)) = applied_param(e) {
            // The output is the argument's own first node: `ih` at it.
            let y = payload(j, a)?;
            same(j, &y, &res, e.span)?;
            return Ok(Some((*mode.node_of(now, j, y)).clone()));
        }
        if self_call.is_some() {
            return mode.refuse(
                "a call to itself must be a child of the constructor it returns (one layer of output for each layer it reads)",
                e.span,
            );
        }
        if let ExprKind::Var(s) = &e.kind
            && mode.child_param(cx, s)
        {
            return mode.refuse(
                &format!("it uses `{s}`, a child of its argument, other than as a child of its result or an argument to itself: a friend reads one layer of each argument"),
                e.span,
            );
        }
        if let Some((i, args)) = Codata(self).codata_ctor_app(cx, &mode.ind, e) {
            return Ok(Some(Codata(self).corec_node(cx, &p, &mode.ind, &carrier, i, &args, e.span)?));
        }
        unfriendly(e)?;
        let t = Rc::new(self.elab_check(cx, e, &p.d_at(0), &p.lw)?);
        Ok(Some(Codata(self).observe_node(&p, 0, &carrier, &node_level, t)))
    }

    /// The step over a free carrier, in `(body, i, x)`: structural recursion
    /// on the tree, `elim_W(x; z. Mot(z); a f ih. (case a of …) f ih)` (at
    /// `i` and the carrier value's predicate when indexed), a seed running
    /// the body (`body_at(K, v)`, `v` the varying tuple at depth `K` past the
    /// body), a tree observed, a pending node emitted, a friend node running
    /// the friend's step; each moved from its own index to `i` along the
    /// predicate's equation.
    pub(super) fn free_step(&self, cx: &Cx, site: &CorecSite, free: &Free, p: &MParts, body_at: &dyn Fn(u32, Rc<Term>) -> Term) -> Term {
        let ty = &free.ty;
        let sl = site.step_level.clone();
        let carrier = &site.carrier;
        let lw0 = ty.lw0();
        let ml = Self::free_mot_level(ty, &sl);
        let mot = |k: u32, z: Rc<Term>| self.free_mot(p, ty, carrier, &sl, k, z);
        // The convoy's motive at the shape `a` (at depth `d`).
        let q = |d: u32, a: Rc<Term>| -> Type {
            let f_ty = pi(&ty.lp, &lw0, ty.pos(d, Rc::clone(&a)), ty.w0(d + 1));
            let ih_ty = pi(&ty.lp, &ml, ty.pos(d + 1, Rc::new(a.shift_local(1))), mot(d + 2, app(var(1), var(0))));
            let sup = ty.sup(d + 2, Rc::new(a.shift_local(2)), var(1));
            pi(&join(&ty.lp, &lw0), &join(&join(&ty.lp, &ml), &ml), f_ty, pi(&join(&ty.lp, &ml), &ml, ih_ty, mot(d + 2, Rc::new(sup))))
        };
        let q_level = join(&join(&ty.lp, &lw0), &join(&ty.lp, &ml));
        // The branch for summand `r` at `v` (depth `d`): `λ f ih. …`.
        let branch = |r: usize, d: u32, v: Rc<Term>| -> Term {
            let f_ty = pi(&ty.lp, &lw0, ty.comps_ty(r, d, &v), ty.w0(d + 1));
            let ih_ty = pi(&ty.lp, &ml, ty.comps_ty(r, d + 1, &Rc::new(v.shift_local(1))), mot(d + 2, app(var(1), var(0))));
            // In (…, f, ih[, j, okp]) at depth `kk`: the node at out_r(v).
            let body = |kk: u32, okrest: Rc<Term>, under: u32| -> Term {
                let v = Rc::new(v.shift_local(kk - d));
                let f = var(1 + under);
                let ih = var(under);
                match r {
                    0 => body_at(kk, v),
                    1 if ty.indexed => {
                        let q = p.reindexed(kk, fst(Rc::clone(&v)));
                        Codata(self).observe_node(&q, 0, &carrier.under(kk), &sl, snd(v))
                    }
                    1 => Codata(self).observe_node(p, kk, carrier, &sl, v),
                    2 if ty.pending => {
                        // Emit the pending node: its label, its children the
                        // tree's children at the same positions.
                        let at = if ty.indexed { fst(Rc::clone(&v)) } else { triv() };
                        let lab = if ty.indexed { snd(Rc::clone(&v)) } else { Rc::clone(&v) };
                        let pq = p.reindexed(kk, Rc::clone(&at));
                        let c = carrier.under(kk);
                        let o = pq.next_tm(1, Rc::new(lab.shift_local(1)), var(0));
                        let kid = if ty.indexed {
                            Rc::new(Term::PairAt {
                                ty: Some(Rc::new(ty.c_at(kk + 1, &o))),
                                fst: app(Rc::new(f.shift_local(1)), var(0)),
                                snd: app(Rc::new(okrest.shift_local(1)), var(0)),
                            })
                        } else {
                            app(Rc::new(f.shift_local(1)), var(0))
                        };
                        let kids = lam(
                            &pq.lp,
                            &join(&c.level, &pq.lw),
                            pq.pos_at(0, Rc::clone(&lab)),
                            Term::Inl {
                                lhs_level: c.level.clone(),
                                rhs_level: pq.lw.clone(),
                                lhs: Rc::new(c.at(1, &o)),
                                rhs: Rc::new(pq.d_of(1, Rc::clone(&o))),
                                val: kid,
                            },
                        );
                        Codata(self).step_pair(&pq, 0, lab, &c, kids)
                    }
                    _ => free.arms[r - ty.first_friend].apply_local(&embed(&cx.gamma, kk).extended(v).extended(f).extended(ih).extended(okrest)),
                }
            };
            let inner = if ty.indexed {
                // λ j okp. J(out_r(v) ⇝ j; body).
                let kk = d + 4;
                let okp = var(0);
                let j_ty = ty.idx.shift_local(d + 2);
                let okp_ty = ty.ok_at(d + 3, Rc::new(ty.sup(d + 3, ty.inj(r, d + 3, Rc::new(v.shift_local(3))), var(2))), var(0));
                let jterm = Term::J {
                    ty_level: ty.li.clone(),
                    motive_level: sl.clone(),
                    ty: Rc::new(ty.idx.shift_local(kk)),
                    lhs: ty.out_r(r, kk, &Rc::new(v.shift_local(kk - d))),
                    motive: Rc::new(Codata(self).node_ty_at(p, kk + 2, &var(1), carrier)),
                    case: Rc::new(body(kk, snd(Rc::clone(&okp)), 2)),
                    rhs: var(1),
                    proof: fst(okp),
                };
                lam(&ty.li, &join(&ty.lk, &sl), j_ty, lam(&ty.lk, &sl, okp_ty, jterm))
            } else {
                body(d + 2, Rc::new(Term::Triv { level: Level::Zero }), 0)
            };
            lam(&join(&ty.lp, &lw0), &join(&join(&ty.lp, &ml), &ml), f_ty, lam(&join(&ty.lp, &ml), &ml, ih_ty, inner))
        };
        // In (body, i, x, a, f, ih): the case on `a`, applied to `f`, `ih`.
        let cases = ty.shape_case(5, var(2), &q, &join(&q_level, &ml), &branch);
        let step = app(app(Rc::new(cases), var(1)), var(0));
        let elim = Term::ElimW {
            shape_level: ty.ls.clone(),
            pos_level: ty.lp.clone(),
            motive_level: ml.clone(),
            shape: Rc::new(ty.shape(2)),
            pos: Rc::new(ty.pos(3, var(0))),
            motive: Rc::new(mot(3, var(0))),
            step,
            scrut: if ty.indexed { fst(var(0)) } else { var(0) },
        };
        if ty.indexed { (*app(app(Rc::new(elim), var(1)), snd(var(0)))).clone() } else { elim }
    }
}

