//! Corecursion up to friends (docs/codata-elaborator-design.md §5.5).
//!
//! A corecursive call may sit under a **friend**, a function of the
//! definition's own codata type that reads each codata argument at most one
//! layer deep to produce one layer of output (`add` in the Leibniz product
//! `mul(f, g) = SCons(hd f * hd g, add(mul(tl f, g), mul(f, tl g)))`). The
//! carrier is then the free algebra of the friends over seeds and existing
//! trees, a finitary `Wf` tree
//!
//! ```text
//! C = Wf(a : X + (⟦D⟧ + (A₁ + … + A_m))). n(a)
//! ```
//!
//! whose leaves are a seed (`X`, arity 0) or an existing tree (`⟦D⟧`, arity
//! 0), and whose node `A_f` is friend `f` applied to its data arguments with
//! one child per codata argument. The step is structural recursion on that
//! tree: a seed runs the body, a tree is observed, and a friend node runs the
//! friend's own body over its arguments' first nodes (the recursion's `ih`),
//! re-elaborated from the friend's source over `C` ("friend mode").
//!
//! Scoping as in the parent: `k` counts the binders past the definition's
//! body context (the site's `depth`), where every stored type is scoped.

use super::*;

use heather_syntax::{Decl, Pat};

use crate::ElabError;
use crate::names::Scope;

/// The numeral `n` as `Succ`s over `Zero`.
fn nat(n: usize) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(Rc::new(t));
    }
    t
}

/// Element `j` of `Fin(m)` (`Fin(S k) ⇝ Unit + Fin(k)`), fully annotated.
fn fin(j: usize, m: usize) -> Term {
    let rest = Rc::new(Type::Fin { len: Rc::new(nat(m - 1)) });
    let unit = Rc::new(Type::Unit { level: Level::Zero });
    if j == 0 {
        Term::Inl {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: unit,
            rhs: rest,
            val: Rc::new(Term::Triv { level: Level::Zero }),
        }
    } else {
        Term::Inr { lhs_level: Level::Zero, rhs_level: Level::Zero, lhs: unit, rhs: rest, val: Rc::new(fin(j - 1, m - 1)) }
    }
}

/// Component `j` of a `Vec` value `cs`.
fn nth(j: usize, cs: Rc<Term>) -> Term {
    let mut t = cs;
    for _ in 0..j {
        t = Rc::new(Term::SndAt { pair: t });
    }
    Term::FstAt { pair: t }
}

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

/// The head name and arguments of a plain call `f(…)` (or `f<…>(…)`).
fn call_parts(e: &Expr) -> Option<(&str, Vec<&Expr>)> {
    let ExprKind::App { head, args, named, .. } = &e.kind else {
        return None;
    };
    if !named.is_empty() {
        return None;
    }
    let head = match &head.kind {
        ExprKind::TyApp { head, .. } => head,
        _ => head,
    };
    match &head.kind {
        ExprKind::Var(name) => Some((name.as_str(), args.iter().collect())),
        _ => None,
    }
}

/// A friend of one corecursive definition: a function of its codata type
/// whose calls the body's children may hold calls under.
pub(crate) struct Friend {
    /// The name the body writes.
    pub(super) written: String,
    decl: Rc<Decl>,
    scope: Option<Rc<Scope>>,
    /// Per value parameter: a codata argument (a child of the node) or a
    /// data argument (part of the node's label).
    tree: Vec<bool>,
    /// The data parameters' types, scoped at the site's depth.
    data_tys: Vec<(Type, Level)>,
    /// The first call, for diagnostics.
    pub(super) span: Span,
}

impl Friend {
    fn arity(&self) -> usize {
        self.tree.iter().filter(|t| **t).count()
    }
}

/// `A_f`, the data arguments' tuple, at depth `k`: `Unit` when there are
/// none, the one type when there is one, a non-dependent `Σ` otherwise.
fn data_ty(tys: &[(Type, Level)], k: u32) -> (Type, Level) {
    match tys {
        [] => (Type::Unit { level: Level::Zero }, Level::Zero),
        [(t, l)] => (t.shift_local(k), l.clone()),
        [(t, l), rest @ ..] => {
            let (r, rl) = data_ty(rest, k);
            let lvl = Level::join(l.clone(), rl.clone());
            (
                Type::Sigma { fst_level: l.clone(), snd_level: rl, fst: Rc::new(t.shift_local(k)), snd: Rc::new(r.shift_local(1)) },
                lvl,
            )
        }
    }
}

/// The data arguments' tuple value at depth `k`.
fn data_tuple(tys: &[(Type, Level)], k: u32, vals: &[Rc<Term>]) -> Term {
    match (tys, vals) {
        ([], _) => Term::Triv { level: Level::Zero },
        ([_], [v]) => (**v).clone(),
        ([(t, l), rest @ ..], [v, vs @ ..]) => {
            let (r, rl) = data_ty(rest, k);
            Term::Pair {
                fst_level: l.clone(),
                snd_level: rl,
                fst_ty: Rc::new(t.shift_local(k)),
                snd_ty: Rc::new(r.shift_local(1)),
                fst: Rc::clone(v),
                snd: Rc::new(data_tuple(rest, k, vs)),
            }
        }
        _ => unreachable!("one value per data parameter"),
    }
}

/// The free carrier's types, scoped at the site's depth.
pub(crate) struct FreeTy {
    /// The shape's summands, `[X, ⟦D⟧, A₁, …, A_m]`.
    sums: Vec<(Type, Level)>,
    /// Each summand's arity: `0`, `0`, then each friend's codata arguments.
    arities: Vec<usize>,
    /// The shape's level, which is `C`'s.
    pub(super) level: Level,
}

impl FreeTy {
    fn n(&self) -> usize {
        self.sums.len()
    }

    fn tail_level(&self, r: usize) -> Level {
        self.sums[r..].iter().fold(Level::Zero, |acc, (_, l)| Level::join(acc, l.clone()))
    }

    /// `sums[r] + (sums[r + 1] + …)` at depth `k`.
    fn tail(&self, r: usize, k: u32) -> Type {
        let (t, l) = &self.sums[r];
        if r + 1 == self.n() {
            return t.shift_local(k);
        }
        Type::Sum {
            lhs_level: l.clone(),
            rhs_level: self.tail_level(r + 1),
            lhs: Rc::new(t.shift_local(k)),
            rhs: Rc::new(self.tail(r + 1, k)),
        }
    }

    fn shape(&self, k: u32) -> Type {
        self.tail(0, k)
    }

    /// `z : tail(r)` as a shape, `inr(…inr(z))`.
    fn wrap(&self, r: usize, k: u32, z: Rc<Term>) -> Rc<Term> {
        let mut t = z;
        for j in (0..r).rev() {
            t = Rc::new(Term::Inr {
                lhs_level: self.sums[j].1.clone(),
                rhs_level: self.tail_level(j + 1),
                lhs: Rc::new(self.sums[j].0.shift_local(k)),
                rhs: Rc::new(self.tail(j + 1, k)),
                val: t,
            });
        }
        t
    }

    /// `v : sums[r]` as a shape.
    fn inj(&self, r: usize, k: u32, v: Rc<Term>) -> Rc<Term> {
        let z = if r + 1 == self.n() {
            v
        } else {
            Rc::new(Term::Inl {
                lhs_level: self.sums[r].1.clone(),
                rhs_level: self.tail_level(r + 1),
                lhs: Rc::new(self.sums[r].0.shift_local(k)),
                rhs: Rc::new(self.tail(r + 1, k)),
                val: v,
            })
        };
        self.wrap(r, k, z)
    }

    /// `n(a)`, the arity of the shape `a` (scoped at `k`).
    fn arity_of(&self, k: u32, a: Rc<Term>) -> Term {
        self.arity_at(0, k, a)
    }

    fn arity_at(&self, r: usize, k: u32, scrut: Rc<Term>) -> Term {
        if r + 1 == self.n() {
            return nat(self.arities[r]);
        }
        Term::Case {
            lhs_level: self.sums[r].1.clone(),
            rhs_level: self.tail_level(r + 1),
            motive_level: Level::Zero,
            lhs: Rc::new(self.sums[r].0.shift_local(k)),
            rhs: Rc::new(self.tail(r + 1, k)),
            motive: Rc::new(Type::Nat),
            case_l: Rc::new(nat(self.arities[r])),
            case_r: Rc::new(self.arity_at(r + 1, k + 1, var(0))),
            scrut,
        }
    }

    /// `C` itself at depth `k`.
    pub(super) fn c(&self, k: u32) -> Type {
        Type::Wf { level: self.level.clone(), shape: Rc::new(self.shape(k)), arity: Rc::new(self.arity_of(k + 1, var(0))) }
    }

    fn vec(&self, k: u32, len: usize) -> Type {
        Type::Vec { level: self.level.clone(), elem: Rc::new(self.c(k)), len: Rc::new(nat(len)) }
    }

    fn sup(&self, r: usize, k: u32, v: Rc<Term>, children: Term) -> Term {
        Term::Supf {
            level: self.level.clone(),
            shape: Rc::new(self.shape(k)),
            arity: Rc::new(self.arity_of(k + 1, var(0))),
            label: self.inj(r, k, v),
            children: Rc::new(children),
        }
    }

    /// A seed (`r = 0`) or an existing tree (`r = 1`) as a leaf of `C`.
    pub(super) fn leaf(&self, r: usize, k: u32, v: Rc<Term>) -> Term {
        self.sup(r, k, v, Term::Triv { level: self.level.clone() })
    }

    /// The children tuple `⟨c₀, ⟨c₁, …⟨⟩⟩⟩ : Vec(C; m)`.
    fn children(&self, k: u32, cs: Vec<Rc<Term>>) -> Term {
        let m = cs.len();
        let mut acc = Term::Triv { level: self.level.clone() };
        for (j, c) in cs.into_iter().enumerate().rev() {
            acc = Term::Pair {
                fst_level: self.level.clone(),
                snd_level: self.level.clone(),
                fst_ty: Rc::new(self.c(k)),
                snd_ty: Rc::new(self.vec(k + 1, m - 1 - j)),
                fst: c,
                snd: Rc::new(acc),
            };
        }
        acc
    }

    /// `y : C + ⟦D⟧` as a `C`: a carrier value stays, a tree becomes a leaf.
    fn embed(&self, k: u32, y: Rc<Term>) -> Term {
        Term::Case {
            lhs_level: self.level.clone(),
            rhs_level: self.sums[1].1.clone(),
            motive_level: self.level.clone(),
            lhs: Rc::new(self.c(k)),
            rhs: Rc::new(self.sums[1].0.shift_local(k)),
            motive: Rc::new(self.c(k + 1)),
            case_l: var(0),
            case_r: Rc::new(self.leaf(1, k + 1, var(0))),
            scrut: y,
        }
    }
}

/// A definition's free carrier: its types, its friends, and each friend's
/// step over it (scoped at the site's depth plus `(p : A_f, cs : Vec(C;
/// m), ih : Π(i : Fin m). F(C))`).
pub(crate) struct Free {
    pub(super) ty: Rc<FreeTy>,
    pub(super) friends: Vec<Friend>,
    arms: Vec<Term>,
}

/// A friend's body while it is re-elaborated over a free carrier (§5.5): its
/// codata parameters are the node's children, read through the step's `ih`.
pub(crate) struct FriendMode {
    /// The corecursive site's depth, where `d_ty`, `carrier` and `free` are
    /// scoped.
    depth: usize,
    d_ty: Type,
    ind: Rc<Inductive>,
    carrier: Carrier,
    free: Rc<FreeTy>,
    /// The friend's summand is `2 + f`.
    f: usize,
    /// The friend, as the definition calls it, and the definition.
    friend: String,
    user: String,
    selfref: Rc<SelfRef>,
    tree: Vec<bool>,
    data_tys: Vec<(Type, Level)>,
    /// The depth at which `(p, cs, ih)` are the last three binders.
    base: usize,
    /// The codata parameters' aliases and their child positions.
    trees: Vec<(Rc<Alias>, usize)>,
    /// Children bound by a `match` on a codata parameter (`C + ⟦D⟧`).
    children: Vec<Rc<Alias>>,
}

impl FriendMode {
    pub(super) fn with_children(&self, more: Vec<Rc<Alias>>) -> FriendMode {
        let mut children = self.children.clone();
        children.extend(more);
        FriendMode {
            depth: self.depth,
            d_ty: self.d_ty.clone(),
            ind: Rc::clone(&self.ind),
            carrier: self.carrier.clone(),
            free: Rc::clone(&self.free),
            f: self.f,
            friend: self.friend.clone(),
            user: self.user.clone(),
            selfref: Rc::clone(&self.selfref),
            tree: self.tree.clone(),
            data_tys: self.data_tys.clone(),
            base: self.base,
            trees: self.trees.clone(),
            children,
        }
    }

    fn arity(&self) -> usize {
        self.trees.len()
    }

    /// The codata parameter `name` names here, as its child position.
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
                "`{}` is not a friend of the corecursive `{}` (docs/codata-elaborator-design.md §5.5): {what}",
                self.friend, self.user
            ),
            span,
        )
    }
}

impl Elaborator {
    // -- finding the friends ---------------------------------------------------

    /// The friends a corecursive body calls: a call inside one of the
    /// declaration's constructors, to a global function of the definition's
    /// own codata type, with a corecursive call among its arguments. A
    /// function whose result is some other type is not a candidate (the
    /// guard's own diagnostics apply to it).
    pub(super) fn corec_friends(&self, cx: &Cx, selfref: &SelfRef, ind: &Inductive, d_ty: &Type, body: &Expr) -> R<Vec<Friend>> {
        fn go(el: &Elaborator, cx: &Cx, selfref: &SelfRef, ind: &Inductive, e: &Expr, under: bool, out: &mut Vec<(String, Span)>) {
            let ctor = el.codata_ctor_app(cx, ind, e).is_some();
            if under
                && !ctor
                && surface_self_call(selfref, e).is_none()
                && let Some((name, _)) = call_parts(e)
                && nested_self_call(selfref, e).is_some()
                && !locally_bound(cx, name)
                && !out.iter().any(|(n, _)| *n == name)
            {
                out.push((name.to_string(), e.span));
            }
            crate::surface::for_each_child(e, &mut |c| go(el, cx, selfref, ind, c, under || ctor, out));
        }
        let mut found = Vec::new();
        go(self, cx, selfref, ind, body, false, &mut found);
        let mut friends = Vec::new();
        for (name, span) in found {
            if let Some(f) = self.friend_signature(cx, d_ty, &name, span)? {
                friends.push(f);
            }
        }
        Ok(friends)
    }

    /// Read `name`'s signature as a friend's: `None` when it is not a global
    /// function of the codata type `d_ty`; an error when it is one but its
    /// signature is outside this round's friends.
    fn friend_signature(&self, cx: &Cx, d_ty: &Type, name: &str, span: Span) -> R<Option<Friend>> {
        let Some(key) = self.key_of(name) else {
            return Ok(None);
        };
        let Some((module, base)) = crate::names::split_qual(&key) else {
            return Ok(None);
        };
        let Some(decl) = self.names.surface_decl_in(module, base).cloned() else {
            return Ok(None);
        };
        if decl.kind != heather_syntax::DeclKind::Fn || decl.is_meta || decl.value || !decl.tyvars.is_empty() {
            return Ok(None);
        }
        let scope = self.names.module_scope(module).cloned().map(Rc::new);
        let _scope = scope.as_ref().map(|s| self.use_scope(s));
        let hcx = cx.hygienic();
        let Ok((res, _)) = self.elab_ty(&hcx, &decl.result) else {
            return Ok(None);
        };
        let lw = MParts::read(d_ty, &cx.gamma).map(|p| p.lw).unwrap_or(Level::Zero);
        if !self.conv_types(&hcx, &res, d_ty, &lw) {
            return Ok(None);
        }
        let refuse = |what: String| -> R<Option<Friend>> {
            err(
                format!(
                    "`{name}` cannot be a friend of this corecursion (docs/codata-elaborator-design.md §5.5): {what}"
                ),
                span,
            )
        };
        if let Some(q) = decl.params.iter().find(|q| q.implicit) {
            return refuse(format!("its parameter `{}` is implicit, and a friend takes its parameters explicitly", q.name));
        }
        if decl.decreases.is_some() {
            return refuse("it is a `decreases` definition".into());
        }
        let mut tree = Vec::new();
        let mut data_tys = Vec::new();
        for q in &decl.params {
            let Ok((ty, lvl)) = self.elab_ty(&hcx, &q.ty) else {
                return refuse(format!(
                    "the type of its parameter `{}` does not stand alone (a friend's parameter types may not mention its other parameters this round)",
                    q.name
                ));
            };
            let is_tree = self.conv_types(&hcx, &ty, d_ty, &lw);
            tree.push(is_tree);
            if !is_tree {
                data_tys.push((ty, lvl));
            }
        }
        if !tree.iter().any(|t| *t) {
            return refuse("it takes no argument of the definition's codata type".into());
        }
        Ok(Some(Friend { written: name.to_string(), decl: Rc::new(decl), scope, tree, data_tys, span }))
    }

    // -- the carrier -----------------------------------------------------------

    /// The free carrier's types over the seeds `x` (the varying tuple, at the
    /// site's depth) and the codata type `d_ty`.
    pub(super) fn free_ty(x: (&Type, &Level), d_ty: &Type, lw: &Level, friends: &[Friend]) -> FreeTy {
        let mut sums = vec![(x.0.clone(), x.1.clone()), (d_ty.clone(), lw.clone())];
        let mut arities = vec![0, 0];
        for f in friends {
            sums.push(data_ty(&f.data_tys, 0));
            arities.push(f.arity());
        }
        let level = sums.iter().fold(Level::Zero, |acc, (_, l)| Level::join(acc, l.clone()));
        FreeTy { sums, arities, level }
    }

    /// Re-elaborate each friend's body over the carrier, its codata
    /// parameters bound to the node's children (§5.5).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn free_arms(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        d_ty: &Type,
        carrier: &Carrier,
        ty: Rc<FreeTy>,
        friends: Vec<Friend>,
        user: &str,
        step_level: &Level,
    ) -> R<Free> {
        let Some(p) = MParts::read(d_ty, &cx.gamma) else {
            let span = friends.first().map(|f| f.span).expect("a free carrier has a friend");
            return err("internal: a codata declaration did not lower to its `M` encoding", span);
        };
        let mut arms = Vec::with_capacity(friends.len());
        for (f, friend) in friends.iter().enumerate() {
            let m = friend.arity();
            let (a_ty, a_lvl) = data_ty(&friend.data_tys, 0);
            let mut acx = cx.clone();
            acx.push("#fp".into(), a_ty, a_lvl);
            acx.push("#fcs".into(), ty.vec(1, m), ty.level.clone());
            let ih_ty = Type::Pi {
                dom_level: Level::Zero,
                cod_level: step_level.clone(),
                dom: Rc::new(Type::Fin { len: Rc::new(nat(m)) }),
                cod: Rc::new(self.step_ty(&p, 3, carrier)),
            };
            acx.push("#fih".into(), ih_ty, step_level.clone());
            let mut fcx = acx.hygienic();
            let base = fcx.names.len();
            let nd = friend.data_tys.len();
            let (mut r, mut j) = (0usize, 0usize);
            let mut trees = Vec::new();
            for (i, q) in friend.decl.params.iter().enumerate() {
                let (term, ty_q, level) = if friend.tree[i] {
                    let t = (Rc::new(nth(j, var(1))), ty.c(3), ty.level.clone());
                    j += 1;
                    t
                } else {
                    let (dt, dl) = &friend.data_tys[r];
                    let t = (Rc::new(tuple_proj(nd, r, Term::Var(LocalVar(2)))), dt.shift_local(3), dl.clone());
                    r += 1;
                    t
                };
                let alias = Rc::new(Alias {
                    skel: None,
                    name: q.name.clone(),
                    depth: base,
                    term,
                    ty: ty_q,
                    level,
                    spliced: None,
                    shifted: Default::default(),
                });
                if friend.tree[i] {
                    trees.push((Rc::clone(&alias), j - 1));
                }
                fcx.aliases.push(alias);
            }
            fcx.friend = Some(Rc::new(FriendMode {
                depth: cx.names.len(),
                d_ty: d_ty.clone(),
                ind: Rc::clone(ind),
                carrier: carrier.clone(),
                free: Rc::clone(&ty),
                f,
                friend: friend.written.clone(),
                user: user.to_string(),
                selfref: Rc::new(SelfRef::of_decl(&friend.decl)),
                tree: friend.tree.clone(),
                data_tys: friend.data_tys.clone(),
                base,
                trees,
                children: Vec::new(),
            }));
            let arm = {
                let _scope = friend.scope.as_ref().map(|s| self.use_scope(s));
                crate::statements::check_block(self, &fcx, &friend.decl.body, &self.step_ty(&p, 3, carrier), step_level, None, None, true)
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
                            "`{}` is not a friend of the corecursive `{user}` (docs/codata-elaborator-design.md §5.5): its body does not elaborate over the free carrier: {msg}",
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

    // -- friend mode -----------------------------------------------------------

    /// The checking-mode hook while a friend's body is re-elaborated over a
    /// free carrier (§5.5): a `match` on a codata parameter reads its node,
    /// a call to the friend itself is a node of `C`, a codata parameter at a
    /// child is its own child, at the node its first node.
    pub(crate) fn friend_check(&self, cx: &Cx, mode: &Rc<FriendMode>, e: &Expr, expected: &Type, lvl: &Level) -> R<Option<Term>> {
        let now = cx.names.len();
        let k = (now - mode.depth) as u32;
        let up = (now - mode.base) as u32;
        let Some(p) = MParts::read(&mode.d_ty.shift_local(k), &cx.gamma) else {
            return err("internal: a codata declaration did not lower to its `M` encoding", e.span);
        };
        let carrier = mode.carrier.under(k);
        let child_ty = self.child_sum(&p, &carrier, 0, triv());
        let child_level = Level::join(carrier.level.clone(), p.lw.clone());
        let node_ty = self.step_ty(&p, 0, &carrier);
        let node_level = Self::node_level(&p, &carrier);
        let at = |want: &Type, wlvl: &Level| -> bool {
            *expected == *want || {
                let head = self.whnf(cx, expected, e.span).ok();
                matches!(head, Some(Type::Sigma { .. } | Type::Sum { .. })) && self.conv_types(cx, expected, want, wlvl)
            }
        };
        let node_of = |j: usize| Term::AppAt { fun: var(up), arg: Rc::new(fin(j, mode.arity())) };
        // A `match` on a codata parameter reads the node `ih` computed for it.
        if let ExprKind::Match { scrut, eqbind, motive, arms, .. } = &e.kind
            && let ExprKind::Var(s) = &scrut.kind
        {
            if let Some(j) = mode.tree_param(cx, s) {
                if eqbind.is_some() || motive.is_some() {
                    return mode.refuse(&format!("its `match` on `{s}` names an equation or a motive, which a friend's step cannot keep"), e.span);
                }
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
                let t = self.match_m_over(cx, &mode.ind, &arms, &p, expected.clone(), lvl.clone(), Observed::Node(Rc::new(node_of(j)), &carrier), e.span)?;
                return Ok(Some(t));
            }
            if mode.child_param(cx, s) {
                return mode.refuse(&format!("it matches on `{s}`, a child of its argument: a friend reads one layer of each argument"), scrut.span);
            }
        }
        // Its own call: a node of the carrier, at a child.
        if let Some((args, _)) = surface_self_call(&mode.selfref, e) {
            if !at(&child_ty, &child_level) {
                return mode.refuse(
                    "a call to itself must be a child of the constructor it returns (one layer of output for each layer it reads)",
                    e.span,
                );
            }
            let v = self.friend_value(cx, mode, k, up, &args, e.span)?;
            return Ok(Some(Term::Inl {
                lhs_level: carrier.level.clone(),
                rhs_level: p.lw.clone(),
                lhs: Rc::new(mode.free.c(k)),
                rhs: Rc::new(p.d_at(0)),
                val: Rc::new(v),
            }));
        }
        if let ExprKind::Var(s) = &e.kind {
            if let Some(j) = mode.tree_param(cx, s) {
                if at(&child_ty, &child_level) {
                    return Ok(Some(Term::Inl {
                        lhs_level: carrier.level.clone(),
                        rhs_level: p.lw.clone(),
                        lhs: Rc::new(mode.free.c(k)),
                        rhs: Rc::new(p.d_at(0)),
                        val: Rc::new(nth(j, var(up + 1))),
                    }));
                }
                if at(&node_ty, &node_level) {
                    // The output is the argument's own first node: `ih` at it.
                    return Ok(Some(node_of(j)));
                }
                return mode.refuse(
                    &format!("it uses `{s}` as a tree; a friend may only `match` on a codata argument, pass it to itself, or return it"),
                    e.span,
                );
            }
            if mode.child_param(cx, s) {
                if at(&child_ty, &child_level) {
                    return Ok(None);
                }
                return mode.refuse(
                    &format!("it uses `{s}`, a child of its argument, other than as a child of its result or an argument to itself: a friend reads one layer of each argument"),
                    e.span,
                );
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
        if at(&child_ty, &child_level) {
            if control || matches!(e.kind, ExprKind::Lam { .. }) {
                return Ok(None);
            }
            unfriendly(e)?;
            let d_here = p.d_at(0);
            let t = self.elab_check(cx, e, &d_here, &p.lw)?;
            return Ok(Some(Term::Inr {
                lhs_level: carrier.level.clone(),
                rhs_level: p.lw.clone(),
                lhs: Rc::new(mode.free.c(k)),
                rhs: Rc::new(d_here),
                val: Rc::new(t),
            }));
        }
        if at(&node_ty, &node_level) {
            if control {
                return Ok(None);
            }
            if let Some((i, args)) = self.codata_ctor_app(cx, &mode.ind, e) {
                return Ok(Some(self.corec_node(cx, &p, &mode.ind, &carrier, i, &args, e.span)?));
            }
            unfriendly(e)?;
            let t = Rc::new(self.elab_check(cx, e, &p.d_at(0), &p.lw)?);
            return Ok(Some(self.observe_node(&p, 0, &carrier, &node_level, t)));
        }
        Ok(None)
    }

    /// The friend applied to `args` inside its own body: a node of `C`.
    fn friend_value(&self, cx: &Cx, mode: &FriendMode, k: u32, up: u32, args: &[&Expr], span: Span) -> R<Term> {
        if args.len() != mode.tree.len() {
            return err(format!("`{}` takes {} argument(s), found {}", mode.friend, mode.tree.len(), args.len()), span);
        }
        let mut kids = Vec::new();
        let mut data = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            if !mode.tree[i] {
                let (ty, l) = &mode.data_tys[data.len()];
                if let Some((n, at)) = mode.mentioned(cx, arg) {
                    return mode.refuse(&format!("it passes `{n}` inside a data argument to itself"), at);
                }
                data.push(Rc::new(self.elab_check(cx, arg, &ty.shift_local(k), l)?));
                continue;
            }
            let v = if let Some((inner, _)) = surface_self_call(&mode.selfref, arg) {
                self.friend_value(cx, mode, k, up, &inner, arg.span)?
            } else if let ExprKind::Var(s) = &arg.kind
                && let Some(j) = mode.tree_param(cx, s)
            {
                nth(j, var(up + 1))
            } else if mode.mentioned(cx, arg).is_some() {
                // A child (or something built from one) whose type is `C +
                // ⟦D⟧`: a carrier value stays, a tree becomes a leaf.
                let (t, ty, _) = self.elab_infer(cx, arg)?;
                let Some(pp) = MParts::read(&mode.d_ty.shift_local(k), &cx.gamma) else {
                    return err("internal: a codata declaration did not lower to its `M` encoding", span);
                };
                let carrier = mode.carrier.under(k);
                let want = self.child_sum(&pp, &carrier, 0, triv());
                if !self.conv_types(cx, &ty, &want, &Level::join(carrier.level.clone(), pp.lw.clone())) {
                    let (n, _) = mode.mentioned(cx, arg).expect("checked above");
                    return mode.refuse(&format!("it passes something built from `{n}` to itself, where only a child of its argument may go"), arg.span);
                }
                mode.free.embed(k, Rc::new(t))
            } else {
                if let Some(at) = nested_self_call(&mode.selfref, arg) {
                    return mode.refuse("it calls itself inside an argument to itself that is not a call", at);
                }
                let d_here = mode.d_ty.shift_local(k);
                let lw = MParts::read(&d_here, &cx.gamma).map(|q| q.lw).unwrap_or(Level::Zero);
                let t = self.elab_check(cx, arg, &d_here, &lw)?;
                mode.free.leaf(1, k, Rc::new(t))
            };
            kids.push(Rc::new(v));
        }
        let label = Rc::new(data_tuple(&mode.data_tys, k, &data));
        Ok(mode.free.sup(2 + mode.f, k, label, mode.free.children(k, kids)))
    }

    // -- the definition's side -------------------------------------------------

    /// `e` as a call to one of the definition's friends, if it is one.
    pub(super) fn friend_call<'e>(&self, cx: &Cx, free: &Free, e: &'e Expr) -> Option<(usize, Vec<&'e Expr>)> {
        let (name, args) = call_parts(e)?;
        if locally_bound(cx, name) {
            return None;
        }
        let f = free.friends.iter().position(|f| f.written == name)?;
        Some((f, args))
    }

    /// A friend applied to `args` in the definition's body: a node of `C`
    /// whose codata arguments are corecursive calls (seeds), friend calls,
    /// or existing trees.
    pub(super) fn user_friend_value(&self, cx: &Cx, site: &CorecSite, free: &Free, p: &MParts, f: usize, args: &[&Expr], span: Span) -> R<Term> {
        let friend = &free.friends[f];
        let k = site.by(cx);
        if args.len() != friend.tree.len() {
            return err(format!("`{}` takes {} argument(s), found {}", friend.written, friend.tree.len(), args.len()), span);
        }
        let mut kids = Vec::new();
        let mut data = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            if !friend.tree[i] {
                let (ty, l) = &friend.data_tys[data.len()];
                if let Some(at) = nested_self_call(&site.selfref, arg) {
                    return err(
                        format!(
                            "this call to `{}` sits in a data argument of the friend `{}`, where no corecursive call is guarded (docs/codata-elaborator-design.md §5.5)",
                            site.selfref.written_name, friend.written
                        ),
                        at,
                    );
                }
                data.push(Rc::new(self.elab_check(cx, arg, &ty.shift_local(k), l)?));
                continue;
            }
            let v = if let Some((call, _)) = surface_self_call(&site.selfref, arg) {
                if let ExprKind::App { head, .. } = &arg.kind
                    && matches!(head.kind, ExprKind::TyApp { .. })
                {
                    return err("a corecursive call takes no type arguments: they are the definition's own", arg.span);
                }
                let seed = self.corec_seed(cx, site, p, &site.seeds.under(k), &triv(), &call, arg.span)?;
                free.ty.leaf(0, k, Rc::new(seed))
            } else if let Some((g, inner)) = self.friend_call(cx, free, arg)
                && nested_self_call(&site.selfref, arg).is_some()
            {
                self.user_friend_value(cx, site, free, p, g, &inner, arg.span)?
            } else {
                if let Some(at) = nested_self_call(&site.selfref, arg) {
                    return err(
                        format!(
                            "this call to `{}` sits inside a tree passed to the friend `{}`: a friend's codata argument may be a corecursive call, another friend's call, or a tree with no corecursive call in it (constructors nested above a call under a friend are not supported, docs/codata-elaborator-design.md §5.5)",
                            site.selfref.written_name, friend.written
                        ),
                        at,
                    );
                }
                let t = self.elab_check(cx, arg, &p.d_at(0), &p.lw)?;
                free.ty.leaf(1, k, Rc::new(t))
            };
            kids.push(Rc::new(v));
        }
        let label = Rc::new(data_tuple(&friend.data_tys, k, &data));
        Ok(free.ty.sup(2 + f, k, label, free.ty.children(k, kids)))
    }

    /// The step over a free carrier, in `(body, i, x)`: structural recursion
    /// on `x : C`, `elim_Wf(x; a cs ih. (case a of …) cs ih)`, a seed running
    /// the body (`body_at(extra, v)`, `v` scoped `extra` binders past `(body,
    /// i, x)`), a tree observed, a friend node running the friend's step.
    pub(super) fn free_step(&self, cx: &Cx, site: &CorecSite, free: &Free, p: &MParts, body_at: &dyn Fn(u32, Rc<Term>) -> Term) -> Term {
        let ty = &free.ty;
        let l = ty.level.clone();
        let sl = site.step_level.clone();
        let fc = |k: u32| self.step_ty(p, k, &site.carrier);
        // The convoy's motive at the shape `a` (scoped at `k`):
        // `Π(cs : Vec(C; n a)). Π(ih : Π(i : Fin(n a)). F(C)). F(C)`.
        let mo = |k: u32, a: Rc<Term>| -> Type {
            let n = Rc::new(ty.arity_of(k, a));
            Type::Pi {
                dom_level: l.clone(),
                cod_level: sl.clone(),
                dom: Rc::new(Type::Vec { level: l.clone(), elem: Rc::new(ty.c(k)), len: Rc::clone(&n) }),
                cod: Rc::new(Type::Pi {
                    dom_level: sl.clone(),
                    cod_level: sl.clone(),
                    dom: Rc::new(Type::Pi {
                        dom_level: Level::Zero,
                        cod_level: sl.clone(),
                        dom: Rc::new(Type::Fin { len: Rc::new(n.shift_local(1)) }),
                        cod: Rc::new(fc(k + 2)),
                    }),
                    cod: Rc::new(fc(k + 2)),
                }),
            }
        };
        let mo_level = Level::join(l.clone(), sl.clone());
        // Summand `r`'s arm at `v` (scoped at `k`): `λ cs ih. …`.
        let arm = |r: usize, k: u32, v: Rc<Term>| -> Term {
            let m = ty.arities[r];
            let v2 = Rc::new(v.shift_local(2));
            let body = match r {
                0 => body_at(k, v2),
                1 => self.observe_node(p, k + 2, &site.carrier, &sl, v2),
                _ => free.arms[r - 2].apply_local(&embed(&cx.gamma, k + 2).extended(v2).extended(var(1)).extended(var(0))),
            };
            Term::Lam {
                dom_level: l.clone(),
                cod_level: sl.clone(),
                dom: Rc::new(ty.vec(k, m)),
                body: Rc::new(Term::Lam {
                    dom_level: sl.clone(),
                    cod_level: sl.clone(),
                    dom: Rc::new(Type::Pi {
                        dom_level: Level::Zero,
                        cod_level: sl.clone(),
                        dom: Rc::new(Type::Fin { len: Rc::new(nat(m)) }),
                        cod: Rc::new(fc(k + 2)),
                    }),
                    body: Rc::new(body),
                }),
            }
        };
        fn cases(ty: &FreeTy, arm: &dyn Fn(usize, u32, Rc<Term>) -> Term, mo: &dyn Fn(u32, Rc<Term>) -> Type, mo_level: &Level, r: usize, k: u32, scrut: Rc<Term>) -> Term {
            if r + 1 == ty.n() {
                return arm(r, k, scrut);
            }
            Term::Case {
                lhs_level: ty.sums[r].1.clone(),
                rhs_level: ty.tail_level(r + 1),
                motive_level: mo_level.clone(),
                lhs: Rc::new(ty.sums[r].0.shift_local(k)),
                rhs: Rc::new(ty.tail(r + 1, k)),
                motive: Rc::new(mo(k + 1, ty.wrap(r, k + 1, var(0)))),
                case_l: Rc::new(arm(r, k + 1, var(0))),
                case_r: Rc::new(cases(ty, arm, mo, mo_level, r + 1, k + 1, var(0))),
                scrut,
            }
        }
        // In (body, i, x, a, cs, ih): the case on `a`, applied to `cs`, `ih`.
        let step = Term::AppAt {
            fun: Rc::new(Term::AppAt { fun: Rc::new(cases(ty, &arm, &mo, &mo_level, 0, 5, var(2))), arg: var(1) }),
            arg: var(0),
        };
        Term::ElimWf {
            level: l,
            motive_level: sl,
            shape: Rc::new(ty.shape(2)),
            arity: Rc::new(ty.arity_of(3, var(0))),
            motive: Rc::new(fc(3)),
            step: Rc::new(step),
            scrut: var(0),
        }
    }
}
