//! Mutual structural recursion over a mutual family
//! (`docs/mutual-inductive-design.md` §6): a group of `fn`s (or of
//! `theorem`s), each one `match` on a member of one mutual family, lowered to
//! **one** structural recursion on the whole family, so one `elim_IWf`.
//!
//! Nothing here builds a kernel term. A group is generated as surface
//! declarations and checked the ordinary way:
//!
//! ```text
//! fn f#mot<p̄>(#j: D#members) -> D#mutual<ā>(#j) -> Type<ℓ> {
//!     match #j { D_t#member(n_t) => λ t => (x̄_t) -> R_t, …, D_u#member(_) => λ _ => True }
//! }
//! fn f#rec<p̄>(#j: D#members, #z: D#mutual<ā>(#j)) -> f#mot<p̄>(#j, #z) {
//!     match #z { every member's arms, each `λ x̄_t => body` }
//! }
//! fn f_t<p̄>(params_t) -> R_t { f#rec<p̄>(D_t#member(n_t), t, x̄_t) }
//! ```
//!
//! `f#rec` recurses on the family at a *variable* index, which is the
//! `IWf` route's ordinary structural recursion: a call `f_u(ā)` inside an arm
//! is rewritten to `f#rec(D_u#member(a_n), a_t, ā_rest)`, whose guard finds
//! the child and rebinds the index through it, and whose extra arguments are
//! applied to the child's ih. What this module owns is the surface: forming
//! the group, the refusals in the members' terms, and the rewrite.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc as Rc;

use heather_kernel::level::LevelNf;
use heather_syntax::ast::{
    Arm, Block, Decl, DeclKind, Item, LamBinder, MatchForm, NamedArg, Param, ParamOrigin, Pat,
    RecordLitField, Stmt,
};
use heather_syntax::{Expr, ExprKind, Span, Ty, TyKind};

use crate::inductive::{IdxTy, Inductive, named_head};
use crate::measure::{mentions, mentions_ty, pat_names, subst};
use crate::{ElabError, Elaborator, R, base_name, count_holes, err};

/// `f#mot` — the group's motive, keyed on its first member.
fn mot_name(first: &str) -> String {
    format!("{first}#mot")
}

/// `f#rec` — the group's one recursion.
fn rec_name(first: &str) -> String {
    format!("{first}#rec")
}

/// A declaration that may be part of a structural group: an ordinary `fn` or
/// `theorem` without a measure.
fn candidate(d: &Decl) -> bool {
    d.decreases.is_none()
        && !d.is_meta
        && !d.is_evidence
        && d.elaborates.is_none()
        && d.kind != DeclKind::Axiom
}

/// The groups of §6: within each maximal run of consecutive candidate
/// declarations, the strongly connected components of size > 1 under "calls
/// by base name" with a member that recurses over a mutual family — its
/// body one `match` on a parameter whose written type names a member, by
/// `is_member` — as item indices in declaration order.
///
/// Every other cycle is left alone, so its members are elaborated one at a
/// time and report the forward reference they always did. A run with no
/// declaration over a member is skipped before its calls are walked.
pub(crate) fn structural_groups(items: &[Item], is_member: &dyn Fn(&str) -> bool) -> Vec<Vec<usize>> {
    let mut groups = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let start = i;
        while i < items.len() && matches!(&items[i], Item::Decl(d) if candidate(d)) {
            i += 1;
        }
        if i == start {
            i += 1;
            continue;
        }
        let run: Vec<&Decl> = items[start..i]
            .iter()
            .map(|it| match it {
                Item::Decl(d) => d,
                _ => unreachable!("the run holds declarations only"),
            })
            .collect();
        let over: Vec<bool> = run
            .iter()
            .map(|d| recursive_param_type(d).is_some_and(|(name, ..)| is_member(name)))
            .collect();
        if !over.contains(&true) {
            continue;
        }
        let mut by_name: HashMap<&str, Vec<usize>> = HashMap::new();
        for (a, d) in run.iter().enumerate() {
            by_name.entry(base_name(&d.name)).or_default().push(a);
        }
        let edges: Vec<Vec<usize>> = run.iter().map(|d| callees(d, &by_name)).collect();
        if !edges.iter().enumerate().any(|(a, es)| es.iter().any(|&b| b > a)) {
            continue;
        }
        for comp in components(&edges) {
            if comp.len() > 1 && comp.iter().any(|&b| over[b]) {
                groups.push(comp.into_iter().map(|b| start + b).collect());
            }
        }
    }
    groups
}

/// A body that is one `match` on a parameter: the parameter's position, its
/// written type's head name, type arguments and, for `D<ā>(e)`, the index.
fn recursive_param_type(d: &Decl) -> Option<(&str, &[Ty], Option<&Expr>, usize)> {
    if !d.body.stmts.is_empty() {
        return None;
    }
    let ExprKind::Match { form, scrut, .. } = &d.body.result.kind else {
        return None;
    };
    if *form == MatchForm::If {
        return None;
    }
    let ExprKind::Var(p) = &scrut.kind else {
        return None;
    };
    let at = d.params.iter().position(|q| &q.name == p)?;
    match &d.params[at].ty.kind {
        TyKind::Named { name, args } => Some((name.as_str(), args.as_slice(), None, at)),
        TyKind::OfExpr(e) => match &e.kind {
            ExprKind::App { head, args, named, .. } if args.len() == 1 && named.is_empty() => {
                named_head(head).map(|(n, t)| (n, t, Some(&args[0]), at))
            }
            _ => None,
        },
        _ => None,
    }
}

/// The run positions `d` calls: heads of applications, by name.
fn callees(d: &Decl, by_name: &HashMap<&str, Vec<usize>>) -> Vec<usize> {
    let mut out = Vec::new();
    let mut scan = |e: &Expr| {
        crate::surface::walk_expr(e, &mut |x| {
            let ExprKind::App { head, .. } = &x.kind else {
                return;
            };
            if let Some((n, _)) = named_head(head)
                && let Some(hits) = by_name.get(n)
            {
                for &b in hits {
                    if !out.contains(&b) {
                        out.push(b);
                    }
                }
            }
        });
    };
    for s in &d.body.stmts {
        match s {
            Stmt::Let { expr, .. } | Stmt::LetRecord { expr, .. } | Stmt::LetCode { expr, .. } => {
                scan(expr)
            }
        }
    }
    scan(&d.body.result);
    for on in &d.body.ons {
        scan(&on.expr);
    }
    out
}

/// Tarjan's strongly connected components, each sorted, ordered by their
/// first member.
fn components(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct T<'a> {
        edges: &'a [Vec<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        out: Vec<Vec<usize>>,
    }
    fn visit(t: &mut T, v: usize) {
        t.index[v] = Some(t.next);
        t.low[v] = t.next;
        t.next += 1;
        t.stack.push(v);
        t.on[v] = true;
        let edges = t.edges;
        for &w in &edges[v] {
            match t.index[w] {
                None => {
                    visit(t, w);
                    t.low[v] = t.low[v].min(t.low[w]);
                }
                Some(iw) if t.on[w] => t.low[v] = t.low[v].min(iw),
                Some(_) => {}
            }
        }
        if t.index[v] == Some(t.low[v]) {
            let mut comp = Vec::new();
            loop {
                let w = t.stack.pop().expect("v is on the stack");
                t.on[w] = false;
                comp.push(w);
                if w == v {
                    break;
                }
            }
            comp.sort_unstable();
            t.out.push(comp);
        }
    }
    let n = edges.len();
    let mut t = T {
        edges,
        index: vec![None; n],
        low: vec![0; n],
        on: vec![false; n],
        stack: Vec::new(),
        next: 0,
        out: Vec::new(),
    };
    for v in 0..n {
        if t.index[v].is_none() {
            visit(&mut t, v);
        }
    }
    let mut out = t.out;
    out.sort_by_key(|c| c[0]);
    out
}

/// One group member, validated: which family member it recurses on, through
/// which parameter, at which index parameter, by which arms.
struct Rec<'a> {
    decl: &'a Decl,
    member: usize,
    scrut: usize,
    index: Option<usize>,
    arms: &'a [Arm],
    span: Span,
}

impl Rec<'_> {
    fn base(&self) -> &str {
        base_name(&self.decl.name)
    }

    fn scrut_name(&self) -> &str {
        &self.decl.params[self.scrut].name
    }

    fn index_name(&self) -> Option<&str> {
        self.index.map(|i| self.decl.params[i].name.as_str())
    }

    /// `x̄`: every parameter but the recursive one and its index, in order.
    fn rest(&self) -> impl DoubleEndedIterator<Item = &Param> {
        self.decl
            .params
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != self.scrut && Some(*i) != self.index)
            .map(|(_, p)| p)
    }
}

/// What a declaration's head says about §6.
enum Head<'a> {
    /// Not one `match` on a member of a mutual family.
    Not,
    /// One, over this family; `String` is the qualifier the member was
    /// written with, which the generated names are spelled under.
    Over(Rc<Inductive>, String, &'a [Ty], Rec<'a>),
    /// One, in a form §7 refuses.
    Refused(ElabError),
}

/// A validated group: the family, the qualifier its names are spelled with,
/// the type arguments it is used at, and the members.
struct Group<'a> {
    fam: Rc<Inductive>,
    prefix: String,
    targs: &'a [Ty],
    recs: Vec<Rec<'a>>,
    /// Every rewritten call: its span and the member it calls, so an error
    /// the recursion raises at a call is told in the callee's terms.
    sites: RefCell<Vec<(Span, usize)>>,
}

impl Group<'_> {
    fn first(&self) -> &Decl {
        self.recs[0].decl
    }

    fn members_ty(&self, span: Span) -> Ty {
        let Some(IdxTy::Decl(iind)) = &self.fam.index_ty else {
            unreachable!("a mutual family is indexed by its members");
        };
        Ty {
            kind: TyKind::Named {
                name: format!("{}{}", self.prefix, base_name(&iind.name)),
                args: Vec::new(),
            },
            span,
        }
    }

    /// Member `u`'s index constructor, applied to `index` for an indexed
    /// member.
    fn member_at(&self, u: usize, index: Option<Expr>, span: Span) -> Expr {
        let Some(IdxTy::Decl(iind)) = &self.fam.index_ty else {
            unreachable!("a mutual family is indexed by its members");
        };
        let tag = var(&format!("{}{}", self.prefix, base_name(&iind.ctors[u].name)), span);
        match index {
            None => tag,
            Some(e) => app(tag, vec![e], span),
        }
    }

    /// `D#mutual<ā>(j)`.
    fn family_ty(&self, j: Expr, span: Span) -> Ty {
        let head = var(&format!("{}{}", self.prefix, base_name(&self.fam.name)), span);
        let head = tyapp(head, self.targs.to_vec(), span);
        Ty { kind: TyKind::OfExpr(Box::new(app(head, vec![j], span))), span }
    }

    /// A generated declaration's name with the group's type parameters
    /// pinned, as the measure route's companions are.
    fn generated_ref(&self, name: &str, span: Span) -> Expr {
        let tyvars = self
            .first()
            .tyvars
            .iter()
            .map(|t| Ty { kind: TyKind::Named { name: t.name.clone(), args: Vec::new() }, span })
            .collect();
        tyapp(var(name, span), tyvars, span)
    }

    fn rec_of_member(&self, u: usize) -> Option<&Rec<'_>> {
        self.recs.iter().find(|r| r.member == u)
    }

    fn describe(&self) -> String {
        self.recs.iter().map(|r| format!("`{}`", r.base())).collect::<Vec<_>>().join(", ")
    }
}

impl Elaborator {
    /// A group of `structural_groups` (§6): generate the motive, the
    /// recursion and the members, and elaborate them.
    pub(crate) fn elab_structural_group(&mut self, decls: &[&Decl]) -> R<()> {
        let Some(group) = self.structural_plan(decls)? else {
            // The written type named a member syntactically and resolves to
            // none: the group has no family to recurse over, and its members'
            // own elaboration says what is wrong.
            for d in decls {
                self.elab_decl(d)?;
            }
            return Ok(());
        };
        let level = self.group_universe(&group)?;
        let mot = mot_decl(&group, level);
        let rec = self.rec_decl(&group)?;
        self.elab_decl_one(&mot, None)?;
        self.elab_decl_one(&rec, None).map_err(|e| reword(&group, e))?;
        for r in &group.recs {
            self.elab_decl_one(&wrapper(&group, r), None)?;
        }
        Ok(())
    }

    fn structural_head<'a>(&self, d: &'a Decl) -> Head<'a> {
        let b = &d.body;
        let Some((name, targs, idx, scrut_at)) = recursive_param_type(d) else {
            return Head::Not;
        };
        let ExprKind::Match { eqbind, motive, arms, .. } = &b.result.kind else {
            unreachable!("`recursive_param_type` read a `match`");
        };
        let p = &d.params[scrut_at].name;
        let Some((fam, member)) = self.lookup_member(name) else {
            return Head::Not;
        };
        let refuse = |msg: String, span: Span| Head::Refused(ElabError::Elab { msg, span });
        let mname = fam.members[member].name.clone();
        if eqbind.is_some() || motive.is_some() {
            return refuse(
                format!(
                    "`{}` recurses on the mutual member `{mname}` in a group, whose \
                     recursion is one `match` on the whole family; an explicit motive or \
                     equation binder on it is not lowered (docs/mutual-inductive-design.md \
                     §7)",
                    d.name
                ),
                b.result.span,
            );
        }
        let index = match (idx, &fam.members[member].index) {
            (None, None) => None,
            (Some(e), Some(_)) => {
                let at = match &e.kind {
                    ExprKind::Var(n) => d.params.iter().position(|q| &q.name == n),
                    _ => None,
                };
                match at {
                    Some(i) if i != scrut_at => Some(i),
                    _ => {
                        return refuse(
                            format!(
                                "`{}` recurses on `{p}` at an index that is not one of its \
                                 parameters: the group's motive binds a member's index, so \
                                 take it as a parameter, `(n: …, {p}: {mname}(n))` \
                                 (docs/mutual-inductive-design.md §7)",
                                d.name
                            ),
                            e.span,
                        );
                    }
                }
            }
            // A member at the wrong arity: the type's own lowering says so.
            _ => return Head::Not,
        };
        let prefix = name.rsplit_once("::").map(|(q, _)| format!("{q}::")).unwrap_or_default();
        Head::Over(
            Rc::clone(&fam),
            prefix,
            targs,
            Rec { decl: d, member, scrut: scrut_at, index, arms, span: b.result.span },
        )
    }

    /// §6's requirements on a group, each refused in the members' terms;
    /// `None` when no member recurses over a mutual family, which leaves the
    /// group to the ordinary rules (and their forward-reference message).
    fn structural_plan<'a>(&self, decls: &[&'a Decl]) -> R<Option<Group<'a>>> {
        let heads: Vec<Head<'a>> = decls.iter().map(|d| self.structural_head(d)).collect();
        if !heads.iter().any(|h| matches!(h, Head::Over(..))) {
            return Ok(None);
        }
        let names = decls.iter().map(|d| format!("`{}`", base_name(&d.name))).collect::<Vec<_>>().join(", ");
        let mut recs = Vec::new();
        let mut family: Option<(Rc<Inductive>, String, &'a [Ty])> = None;
        for (d, h) in decls.iter().zip(heads) {
            match h {
                Head::Not => {
                    return err(
                        format!(
                            "{names} are mutually recursive, and a member recurses over a \
                             mutual family: such a group is one structural recursion, so each \
                             member's body is one `match` on a parameter whose type is a member \
                             of the family, and `{}`'s is not. Write it as one, or give every \
                             member a `decreases` measure (docs/mutual-inductive-design.md §6)",
                            base_name(&d.name)
                        ),
                        d.span,
                    );
                }
                Head::Refused(e) => return Err(e),
                Head::Over(fam, prefix, targs, rec) => {
                    match &family {
                        None => family = Some((fam, prefix, targs)),
                        Some((f, ..)) if Rc::ptr_eq(f, &fam) => {}
                        Some((f, ..)) => {
                            return err(
                                format!(
                                    "{names} are mutually recursive over two different mutual \
                                     families, `{}` and `{}`: one structural recursion is on one \
                                     family (docs/mutual-inductive-design.md §6)",
                                    f.members[0].name, fam.members[0].name
                                ),
                                d.span,
                            );
                        }
                    }
                    recs.push(rec);
                }
            }
        }
        let (fam, prefix, targs) = family.expect("some member recurses over a family");
        let first = recs[0].decl;
        for r in &recs {
            let d = r.decl;
            if let Some(o) = recs.iter().find(|o| o.member == r.member && !std::ptr::eq(o.decl, d)) {
                return err(
                    format!(
                        "`{}` and `{}` both recurse on `{}`: a structural group has one member \
                         per member of the family, which is what the recursion's motive is \
                         indexed by (docs/mutual-inductive-design.md §6)",
                        base_name(&o.decl.name),
                        base_name(&d.name),
                        fam.members[r.member].name
                    ),
                    d.span,
                );
            }
            if d.kind != first.kind {
                return err(
                    format!(
                        "{names} are one structural recursion, so they are all `fn`s or all \
                         `theorem`s; `{}` and `{}` differ (docs/mutual-inductive-design.md §6)",
                        base_name(&first.name),
                        base_name(&d.name)
                    ),
                    d.span,
                );
            }
            let same_tyvars = d.tyvars.len() == first.tyvars.len()
                && d.tyvars.iter().zip(&first.tyvars).all(|(a, b)| a.name == b.name && a.level == b.level);
            if !same_tyvars {
                return err(
                    format!(
                        "the members of a structural group declare the same type parameters, \
                         in the same order: `{}` and `{}` differ (docs/mutual-inductive-design.md \
                         §6)",
                        base_name(&first.name),
                        base_name(&d.name)
                    ),
                    d.span,
                );
            }
            if let Some(p) = d.params.iter().find(|p| p.implicit || p.solver.is_some() || p.default.is_some()) {
                return err(
                    format!(
                        "`{}` is a member of the structural group {names}, whose members take \
                         explicit parameters only; `{}` is implicit or has a default \
                         (docs/mutual-inductive-design.md §7)",
                        base_name(&d.name),
                        p.name
                    ),
                    p.span,
                );
            }
            // The motive binds the index and the recursive parameter before
            // the rest, so neither's type may mention the rest.
            let heads = [Some(r.scrut), r.index];
            for at in heads.into_iter().flatten() {
                let p = &d.params[at];
                if let Some(x) = r.rest().find(|x| mentions_ty(&p.ty, &x.name)) {
                    return err(
                        format!(
                            "`{}`'s type mentions `{}`: the group's motive binds `{}` first, \
                             at the member's index, so its type is over the index alone \
                             (docs/mutual-inductive-design.md §6)",
                            p.name, x.name, p.name
                        ),
                        p.ty.span,
                    );
                }
            }
        }
        Ok(Some(Group { fam, prefix, targs, recs, sites: RefCell::new(Vec::new()) }))
    }

    /// `ℓ` in `f#mot … -> Type<ℓ>`: the largest level of the members'
    /// `(x̄_t) -> R_t`, elaborated over each member's own parameters.
    fn group_universe(&mut self, g: &Group) -> R<u64> {
        let mut level = 0;
        for r in &g.recs {
            let pi = pi_over(r.rest(), r.decl.result.clone(), r.span);
            self.attempt.prepare();
            self.attempt.goal_arena.configure(count_holes(r.decl), 0);
            self.refresh_delta_psi();
            let l = self.decl_head_cx(r.decl).and_then(|cx| self.elab_ty(&cx, &pi).map(|(_, l)| l));
            self.attempt.finish();
            self.refresh_delta_psi();
            match l?.normalize() {
                LevelNf::Finite { konst, vars } if vars.is_empty() => {
                    level = level.max(konst.unwrap_or(0));
                }
                _ => {
                    return err(
                        format!(
                            "`{}`'s result is at a universe-polymorphic level; a structural \
                             group's motive is at a numeral level (docs/mutual-inductive-design.md \
                             §6)",
                            r.base()
                        ),
                        r.decl.result.span,
                    );
                }
            }
        }
        Ok(level)
    }

    /// `f#rec`: one `match` on the whole family, holding every member's arms
    /// and, for a family member no group member recurses on, `trivial`.
    fn rec_decl(&self, g: &Group) -> R<Decl> {
        let first = g.first();
        let span = g.recs[0].span;
        let mut arms = Vec::new();
        for r in &g.recs {
            self.member_arms(g, r, &mut arms)?;
        }
        for (u, m) in g.fam.members.iter().enumerate() {
            if g.rec_of_member(u).is_some() {
                continue;
            }
            for &k in &m.ctors {
                let c = &g.fam.ctors[k];
                arms.push(Arm {
                    ctor: format!("{}{}", g.prefix, c.name),
                    default: false,
                    binders: (0..c.fields.len()).map(|_| pvar("_", span)).collect(),
                    body: var("trivial", span),
                    span,
                });
            }
        }
        let mut ons = Vec::new();
        for r in &g.recs {
            let mut calls = Calls::new(g);
            calls.bound.extend(r.decl.params.iter().map(|p| p.name.clone()));
            for on in &r.decl.body.ons {
                let expr = calls.expr(&on.expr);
                ons.push(heather_syntax::ast::OnStmt { expr, ..on.clone() });
            }
            calls.finish()?;
        }
        let j = var("#j", span);
        let z = var("#z", span);
        let result = Ty {
            kind: TyKind::OfExpr(Box::new(app(
                g.generated_ref(&mot_name(&first.name), span),
                vec![j.clone(), z.clone()],
                span,
            ))),
            span,
        };
        let body = Expr {
            kind: ExprKind::Match {
                form: MatchForm::Match,
                generated: false,
                scrut: Box::new(z),
                eqbind: None,
                motive: None,
                arms,
            },
            span,
        };
        Ok(Decl {
            kind: first.kind,
            is_meta: false,
            is_evidence: false,
            is_interface: false,
            value: false,
            elaborates: None,
            name: rec_name(&first.name),
            tyvars: first.tyvars.clone(),
            params: vec![
                param("#j", g.members_ty(span), span),
                param("#z", g.family_ty(var("#j", span), span), span),
            ],
            result,
            decreases: None,
            unfolding: Vec::new(),
            body: Block { stmts: Vec::new(), result: Box::new(body), ons, span: first.body.span },
            span: first.span,
        })
    }

    /// Member `r`'s arms, for its own constructors only, each under
    /// `λ x̄_r`, with `n_r` and the recursive parameter bound to this level's
    /// values where the arm reads them.
    fn member_arms(&self, g: &Group, r: &Rec, out: &mut Vec<Arm>) -> R<()> {
        let mname = &g.fam.members[r.member].name;
        let own = &g.fam.members[r.member].ctors;
        // The user's arms, grouped by constructor in written order.
        let mut by_ctor: Vec<(usize, Vec<&Arm>)> = Vec::new();
        let mut default: Option<&Arm> = None;
        for a in r.arms {
            if a.default {
                default = Some(a);
                continue;
            }
            let k = match self.lookup_ctor(&a.ctor) {
                Some((ind, k)) if Rc::ptr_eq(&ind, &g.fam) => k,
                _ => {
                    return err(
                        format!("`{}` is not a constructor of `{mname}`", a.ctor),
                        a.span,
                    );
                }
            };
            if !own.contains(&k) {
                return err(
                    format!(
                        "`{}` is a constructor of `{}`, not of `{mname}`: `{}` matches on \
                         `{mname}`, whose arms are its own constructors",
                        a.ctor,
                        Elaborator::member_name_of(&g.fam, k),
                        r.base()
                    ),
                    a.span,
                );
            }
            match by_ctor.iter_mut().find(|(c, _)| *c == k) {
                Some((_, v)) => v.push(a),
                None => by_ctor.push((k, vec![a])),
            }
        }
        // A bare constructor name in a field position is a pattern, not a
        // binder (docs/nested-match-patterns-design.md §3.5).
        let is_ctor = |n: &str| n != "_" && self.lookup_ctor(n).is_some();
        for &k in own {
            let c = &g.fam.ctors[k];
            let arms = by_ctor.iter().find(|(c, _)| *c == k).map(|(_, v)| v.as_slice()).unwrap_or(&[]);
            match arms {
                [] => match default {
                    Some(d) => out.push(self.arm_at(g, r, k, &vec!["_".to_string(); c.fields.len()], &d.body, d.span)?),
                    None => {
                        return err(
                            format!("`{}`'s `match` on `{mname}` has no arm for `{}`", r.base(), c.name),
                            r.span,
                        );
                    }
                },
                [a] => {
                    let names = binder_names(c, a, r, &is_ctor)?;
                    out.push(self.arm_at(g, r, k, &names, &a.body, a.span)?);
                }
                [_, a, ..] => {
                    // Two arms for one constructor are a nested pattern's
                    // split, or a duplicate.
                    for b in arms {
                        binder_names(c, b, r, &is_ctor)?;
                    }
                    return err(format!("duplicate arm for `{}`", c.name), a.span);
                }
            }
        }
        Ok(())
    }

    /// One arm at constructor `k`, the user's binders `names` (`_` for
    /// none), and `body`:
    /// `C(b̄) => λ x̄ => { let n = e_C[b̄]; let t: T = C(b̄); let user = b; body }`,
    /// each `let` only where the body reads it.
    fn arm_at(&self, g: &Group, r: &Rec, k: usize, names: &[String], body: &Expr, span: Span) -> R<Arm> {
        let c = &g.fam.ctors[k];
        let rest: Vec<&Param> = r.rest().collect();
        let t = r.scrut_name();
        let n = r.index_name();
        let reserved = |s: &str| s == t || Some(s) == n || rest.iter().any(|x| x.name == s);
        let mut pats: Vec<String> = Vec::with_capacity(names.len());
        for (i, u) in names.iter().enumerate() {
            let fresh = u == "_" || reserved(u) || pats.contains(u);
            pats.push(if fresh { format!("#b{i}") } else { u.clone() });
        }
        let mut stmts = Vec::new();
        let read_t = mentions(body, t);
        if let Some(n) = n
            && (read_t || mentions(body, n))
        {
            let Some(res) = &c.res_expr else {
                unreachable!("every constructor of an indexed member states its index");
            };
            let ExprKind::App { args, .. } = &res.kind else {
                unreachable!("a family result is a member index constructor applied");
            };
            let fields: Vec<(&str, Expr)> = c
                .fields
                .iter()
                .zip(&pats)
                .filter_map(|((f, _), p)| f.as_deref().map(|f| (f, var(p, span))))
                .collect();
            let map: Vec<(&str, &Expr)> = fields.iter().map(|(f, e)| (*f, e)).collect();
            stmts.push(let_(n, None, subst(&args[0], &map, &mut Vec::new()), span));
        }
        if read_t {
            let ctor = tyapp(var(&format!("{}{}", g.prefix, c.name), span), g.targs.to_vec(), span);
            let value = if pats.is_empty() {
                ctor
            } else {
                app(ctor, pats.iter().map(|p| var(p, span)).collect(), span)
            };
            stmts.push(let_(t, Some(r.decl.params[r.scrut].ty.clone()), value, span));
        }
        for (u, p) in names.iter().zip(&pats) {
            if u != "_" && u != p {
                stmts.push(let_(u, None, var(p, span), span));
            }
        }
        // The arm's own binders, the parameters and the `let`s shadow a
        // member's name as they do in the written arm.
        let mut calls = Calls::new(g);
        calls.bound.extend(names.iter().cloned());
        calls.bound.extend(r.decl.params.iter().map(|p| p.name.clone()));
        let body = calls.expr(body);
        calls.finish()?;
        let body = if stmts.is_empty() {
            body
        } else {
            Expr {
                kind: ExprKind::Block(Box::new(Block {
                    stmts,
                    result: Box::new(body),
                    ons: Vec::new(),
                    span,
                })),
                span,
            }
        };
        Ok(Arm {
            ctor: format!("{}{}", g.prefix, c.name),
            default: false,
            binders: pats.iter().map(|p| pvar(p, span)).collect(),
            body: lam(&rest, body, span),
            span,
        })
    }
}

/// `f#mot`: by the member index, `λ t => (x̄_t) -> R_t`, and `True` at a
/// member no group member recurses on.
fn mot_decl(g: &Group, level: u64) -> Decl {
    let first = g.first();
    let span = g.recs[0].span;
    let arms = g
        .fam
        .members
        .iter()
        .enumerate()
        .map(|(u, m)| {
            let (binders, body) = match g.rec_of_member(u) {
                Some(r) => {
                    let pi = pi_over(r.rest(), r.decl.result.clone(), r.span);
                    let t = if mentions_ty(&pi, r.scrut_name()) { r.scrut_name() } else { "_" };
                    let n = r.index_name().map(|n| if mentions_ty(&pi, n) { n } else { "_" });
                    let body = Expr { kind: ExprKind::TyLit(Box::new(pi)), span };
                    (n.into_iter().map(|n| pvar(n, span)).collect(), lam_named(t, body, span))
                }
                None => {
                    let truth = Ty { kind: TyKind::Named { name: "True".into(), args: Vec::new() }, span };
                    let body = Expr { kind: ExprKind::TyLit(Box::new(truth)), span };
                    (m.index.iter().map(|_| pvar("_", span)).collect(), lam_named("_", body, span))
                }
            };
            let Some(IdxTy::Decl(iind)) = &g.fam.index_ty else {
                unreachable!("a mutual family is indexed by its members");
            };
            Arm {
                ctor: format!("{}{}", g.prefix, base_name(&iind.ctors[u].name)),
                default: false,
                binders,
                body,
                span,
            }
        })
        .collect();
    let result = Ty {
        kind: TyKind::Fn {
            binder: None,
            implicit: false,
            dom: Box::new(g.family_ty(var("#j", span), span)),
            cod: Box::new(Ty { kind: TyKind::Univ { level }, span }),
        },
        span,
    };
    let body = Expr {
        kind: ExprKind::Match {
            form: MatchForm::Match,
            generated: true,
            scrut: Box::new(var("#j", span)),
            eqbind: None,
            motive: None,
            arms,
        },
        span,
    };
    Decl {
        kind: DeclKind::Fn,
        is_meta: false,
        is_evidence: false,
        is_interface: false,
            value: false,
        elaborates: None,
        name: mot_name(&first.name),
        tyvars: first.tyvars.clone(),
        params: vec![param("#j", g.members_ty(span), span)],
        result,
        decreases: None,
        unfolding: Vec::new(),
        body: Block { stmts: Vec::new(), result: Box::new(body), ons: Vec::new(), span },
        span: first.span,
    }
}

/// Member `r` as written, its body the recursion at its own member:
/// `f#rec<p̄>(D_t#member(n), t, x̄)`.
fn wrapper(g: &Group, r: &Rec) -> Decl {
    let span = r.span;
    let index = r.index_name().map(|n| var(n, span));
    let mut args = vec![g.member_at(r.member, index, span), var(r.scrut_name(), span)];
    args.extend(r.rest().map(|x| var(&x.name, span)));
    let call = app(g.generated_ref(&rec_name(&g.first().name), span), args, span);
    Decl {
        body: Block { stmts: Vec::new(), result: Box::new(call), ons: Vec::new(), span: r.decl.body.span },
        ..r.decl.clone()
    }
}

/// The call rewrite of §6 over one arm's body: a saturated call to a group
/// member `f_u(ā)` becomes `f#rec(D_u#member(a_n), a_t, ā_rest, spill…)`. A
/// name shadowed by a binder around the call is left alone.
struct Calls<'a, 'g> {
    g: &'a Group<'g>,
    bound: Vec<String>,
    error: Option<ElabError>,
}

impl<'a, 'g> Calls<'a, 'g> {
    fn new(g: &'a Group<'g>) -> Self {
        Calls { g, bound: Vec::new(), error: None }
    }

    fn finish(self) -> R<()> {
        match self.error {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    fn fail(&mut self, msg: String, span: Span) {
        if self.error.is_none() {
            self.error = Some(ElabError::Elab { msg, span });
        }
    }

    /// The group member `n` names here, if it is one and not shadowed.
    fn member(&self, n: &str) -> Option<usize> {
        if self.bound.iter().any(|b| b == n) {
            return None;
        }
        self.g.recs.iter().position(|r| r.base() == n || r.decl.name == n)
    }

    fn call(&mut self, at: usize, head: &Expr, args: Vec<Expr>, named: &[NamedArg], span: Span) -> Expr {
        let r = &self.g.recs[at];
        let arity = r.decl.params.len();
        if !named.is_empty() {
            self.fail(
                format!(
                    "a call to `{}` within its structural group passes its arguments by \
                     position (docs/mutual-inductive-design.md §6)",
                    r.base()
                ),
                span,
            );
            return Expr { kind: ExprKind::Hole(None), span };
        }
        if args.len() < arity {
            self.fail(
                format!(
                    "a call to `{}` within its structural group passes all {arity} argument(s), \
                     found {} (docs/mutual-inductive-design.md §6)",
                    r.base(),
                    args.len()
                ),
                span,
            );
            return Expr { kind: ExprKind::Hole(None), span };
        }
        let tyargs = match &head.kind {
            ExprKind::TyApp { args, .. } => args.clone(),
            _ => Vec::new(),
        };
        let index = r.index.map(|i| args[i].clone());
        let mut out = vec![self.g.member_at(r.member, index, span), args[r.scrut].clone()];
        for (i, a) in args.iter().enumerate() {
            if i >= arity || (i != r.scrut && Some(i) != r.index) {
                out.push(a.clone());
            }
        }
        self.g.sites.borrow_mut().push((span, at));
        let head = tyapp(var(&rec_name(&self.g.first().name), head.span), tyargs, head.span);
        app(head, out, span)
    }

    fn bind<T>(&mut self, names: impl IntoIterator<Item = String>, go: impl FnOnce(&mut Self) -> T) -> T {
        let n = self.bound.len();
        self.bound.extend(names);
        let out = go(self);
        self.bound.truncate(n);
        out
    }

    fn named(&mut self, named: &[NamedArg]) -> Vec<NamedArg> {
        named.iter().map(|n| NamedArg { expr: self.expr(&n.expr), ..n.clone() }).collect()
    }

    fn fields(&mut self, fields: &[RecordLitField]) -> Vec<RecordLitField> {
        fields.iter().map(|f| RecordLitField { expr: self.expr(&f.expr), ..f.clone() }).collect()
    }

    fn arm(&mut self, a: &Arm, eqbind: Option<&String>) -> Arm {
        let mut names = Vec::new();
        for p in &a.binders {
            pat_names(p, &mut names);
        }
        names.extend(eqbind.cloned());
        let body = self.bind(names, |me| me.expr(&a.body));
        Arm { body, ..a.clone() }
    }

    fn block(&mut self, b: &Block) -> Block {
        let n = self.bound.len();
        let mut stmts = Vec::with_capacity(b.stmts.len());
        for s in &b.stmts {
            stmts.push(match s {
                Stmt::Let { name, ty, expr, span, opaque } => {
                    let expr = self.expr(expr);
                    self.bound.push(name.clone());
                    Stmt::Let { name: name.clone(), ty: ty.clone(), expr, span: *span, opaque: *opaque }
                }
                Stmt::LetRecord { fields, expr, span } => {
                    let expr = self.expr(expr);
                    for f in fields {
                        pat_names(&f.pat, &mut self.bound);
                    }
                    Stmt::LetRecord { fields: fields.clone(), expr, span: *span }
                }
                Stmt::LetCode { name, expr, span } => {
                    let expr = self.expr(expr);
                    self.bound.push(name.clone());
                    Stmt::LetCode { name: name.clone(), expr, span: *span }
                }
            });
        }
        let result = self.expr(&b.result);
        let ons = b
            .ons
            .iter()
            .map(|on| heather_syntax::ast::OnStmt { expr: self.expr(&on.expr), ..on.clone() })
            .collect();
        self.bound.truncate(n);
        Block { stmts, result: Box::new(result), ons, span: b.span }
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        let span = e.span;
        let kind = match &e.kind {
            ExprKind::Var(n) => {
                if let Some(at) = self.member(n) {
                    self.fail(
                        format!(
                            "`{}` recurses structurally with {}: within the group it is \
                             called, with all its arguments, not passed as a value \
                             (docs/mutual-inductive-design.md §6)",
                            self.g.recs[at].base(),
                            self.g.describe()
                        ),
                        span,
                    );
                }
                ExprKind::Var(n.clone())
            }
            ExprKind::App { head, args, named, explicit, goal_oriented } => {
                let args: Vec<Expr> = args.iter().map(|a| self.expr(a)).collect();
                if let Some((n, _)) = named_head(head)
                    && let Some(at) = self.member(n)
                {
                    let named = self.named(named);
                    return self.call(at, head, args, &named, span);
                }
                ExprKind::App {
                    head: Box::new(self.expr(head)),
                    args,
                    named: self.named(named),
                    explicit: *explicit,
                    goal_oriented: *goal_oriented,
                }
            }
            ExprKind::TyApp { head, args } => {
                ExprKind::TyApp { head: Box::new(self.expr(head)), args: args.clone() }
            }
            ExprKind::Lam { binders, body } => {
                let body = self.bind(binders.iter().map(|b| b.name.clone()), |me| me.expr(body));
                ExprKind::Lam { binders: binders.clone(), body: Box::new(body) }
            }
            ExprKind::CollectionLit(xs) => ExprKind::CollectionLit(xs.iter().map(|x| self.expr(x)).collect()),
            ExprKind::Eq(a, b) => ExprKind::Eq(Box::new(self.expr(a)), Box::new(self.expr(b))),
            ExprKind::Match { form, generated, scrut, eqbind, motive, arms } => ExprKind::Match {
                form: *form,
                generated: *generated,
                scrut: Box::new(self.expr(scrut)),
                eqbind: eqbind.clone(),
                motive: motive.as_ref().map(|m| Box::new(self.expr(m))),
                arms: arms.iter().map(|a| self.arm(a, eqbind.as_ref())).collect(),
            },
            ExprKind::MatchCode { scrut, motive, arms } => ExprKind::MatchCode {
                scrut: Box::new(self.expr(scrut)),
                motive: motive.clone(),
                arms: arms.iter().map(|a| self.arm(a, None)).collect(),
            },
            ExprKind::Dot { recv, name, tyargs, args, named } => ExprKind::Dot {
                recv: Box::new(self.expr(recv)),
                name: name.clone(),
                tyargs: tyargs.clone(),
                args: args.as_ref().map(|xs| xs.iter().map(|x| self.expr(x)).collect()),
                named: self.named(named),
            },
            ExprKind::Index { recv, idx } => {
                ExprKind::Index { recv: Box::new(self.expr(recv)), idx: Box::new(self.expr(idx)) }
            }
            ExprKind::RecordLit { name, tyargs, fields } => ExprKind::RecordLit {
                name: name.clone(),
                tyargs: tyargs.clone(),
                fields: self.fields(fields),
            },
            ExprKind::RecordUpdate { base, fields } => ExprKind::RecordUpdate {
                base: Box::new(self.expr(base)),
                fields: self.fields(fields),
            },
            ExprKind::Block(b) => ExprKind::Block(Box::new(self.block(b))),
            ExprKind::Quote(x) => ExprKind::Quote(Box::new(self.expr(x))),
            ExprKind::Splice(x) => ExprKind::Splice(Box::new(self.expr(x))),
            ExprKind::J { proof, motive, case } => ExprKind::J {
                proof: Box::new(self.expr(proof)),
                motive: Box::new(self.expr(motive)),
                case: Box::new(self.expr(case)),
            },
            other @ (ExprKind::OpSymbol { .. }
            | ExprKind::Univ { .. }
            | ExprKind::Num(_)
            | ExprKind::Scaled(_)
            | ExprKind::Char(_)
            | ExprKind::Str(_)
            | ExprKind::ArgSlot(_)
            | ExprKind::TyLit(_)
            | ExprKind::Refl
            | ExprKind::AutoRefl
            | ExprKind::Hole(_)) => other.clone(),
        };
        Expr { kind, span }
    }
}

/// An error the recursion raised, in the members' terms: at a rewritten call,
/// the generated recursion and its two parameters are the callee and its
/// index and recursive parameters; elsewhere, the group.
fn reword(g: &Group, e: ElabError) -> ElabError {
    let ElabError::Elab { msg, span } = e else {
        return e;
    };
    let rec = format!("`{}`", rec_name(&g.first().name));
    let sites = g.sites.borrow();
    let site = sites
        .iter()
        .filter(|(s, _)| s.start <= span.start && span.end <= s.end)
        .min_by_key(|(s, _)| s.end - s.start);
    let msg = match site {
        Some(&(_, at)) => {
            let r = &g.recs[at];
            msg.replace(&rec, &format!("`{}`", r.base()))
                .replace("`#z`", &format!("`{}`", r.scrut_name()))
                .replace("`#j`", &r.index_name().map_or("its member".to_string(), |n| format!("`{n}`")))
        }
        None => msg.replace(&rec, &format!("the group {}", g.describe())),
    };
    ElabError::Elab { msg, span }
}

/// An arm's binders as one name per field (`_` for none), in field order:
/// positional binders first, then `field := x`. A deep pattern in a
/// descending `match` is refused, as the structural guard refuses it for a
/// single declaration: its arm binders are what a recursive call's argument
/// is matched against.
fn binder_names(
    c: &crate::inductive::Ctor,
    a: &Arm,
    r: &Rec,
    is_ctor: &dyn Fn(&str) -> bool,
) -> R<Vec<String>> {
    let deep = |span: Span| {
        err(
            format!(
                "a deep pattern is not available in this `match`: it descends on `{}`, a \
                 parameter of `{}`, so its arm binders are what the termination guard matches \
                 a recursive call's argument against. Match the field in a nested `match` \
                 inside the arm instead (docs/nested-match-patterns-design.md §6)",
                r.scrut_name(),
                r.base()
            ),
            span,
        )
    };
    let mut names = vec!["_".to_string(); c.fields.len()];
    let mut next = 0;
    for p in &a.binders {
        match p {
            Pat::Var { name, span } if is_ctor(name) => return deep(*span),
            Pat::Var { name, .. } => {
                if next >= names.len() {
                    return err(
                        format!("`{}` has {} field(s), and the arm binds more", c.name, c.fields.len()),
                        a.span,
                    );
                }
                names[next] = name.clone();
                next += 1;
            }
            Pat::Named { field, pat, span } => {
                let Pat::Var { name, .. } = &**pat else {
                    return deep(*span);
                };
                if is_ctor(name) {
                    return deep(*span);
                }
                let Some(at) = c.fields.iter().position(|(f, _)| f.as_deref() == Some(field)) else {
                    return err(format!("`{}` has no field `{field}`", c.name), *span);
                };
                names[at] = name.clone();
            }
            Pat::Ctor { span, .. } => return deep(*span),
        }
    }
    if next != names.len() && !a.binders.iter().any(|p| matches!(p, Pat::Named { .. })) {
        return err(
            format!("`{}` has {} field(s), and the arm binds {next}", c.name, c.fields.len()),
            a.span,
        );
    }
    Ok(names)
}

fn var(name: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Var(name.to_string()), span }
}

fn app(head: Expr, args: Vec<Expr>, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App { head: Box::new(head), args, named: Vec::new(), explicit: false, goal_oriented: false },
        span,
    }
}

/// `head<ā>`, or `head` itself for no arguments.
fn tyapp(head: Expr, args: Vec<Ty>, span: Span) -> Expr {
    if args.is_empty() {
        return head;
    }
    Expr { kind: ExprKind::TyApp { head: Box::new(head), args }, span }
}

fn pvar(name: &str, span: Span) -> Pat {
    Pat::Var { name: name.to_string(), span }
}

fn binder(name: &str, span: Span) -> LamBinder {
    LamBinder { name: name.to_string(), ty: None, implicit: false, span }
}

fn lam_named(name: &str, body: Expr, span: Span) -> Expr {
    Expr { kind: ExprKind::Lam { binders: vec![binder(name, span)], body: Box::new(body) }, span }
}

/// `λ x̄ => body`, or `body` for no binders.
fn lam(params: &[&Param], body: Expr, span: Span) -> Expr {
    if params.is_empty() {
        return body;
    }
    Expr {
        kind: ExprKind::Lam {
            binders: params.iter().map(|p| binder(&p.name, span)).collect(),
            body: Box::new(body),
        },
        span,
    }
}

fn let_(name: &str, ty: Option<Ty>, expr: Expr, span: Span) -> Stmt {
    Stmt::Let { name: name.to_string(), ty, expr, span, opaque: false }
}

/// `(x̄) -> cod`.
fn pi_over<'p>(params: impl DoubleEndedIterator<Item = &'p Param>, cod: Ty, span: Span) -> Ty {
    let mut ty = cod;
    for p in params.rev() {
        ty = Ty {
            kind: TyKind::Fn {
                binder: Some(p.name.clone()),
                implicit: false,
                dom: Box::new(p.ty.clone()),
                cod: Box::new(ty),
            },
            span,
        };
    }
    ty
}

fn param(name: &str, ty: Ty, span: Span) -> Param {
    Param {
        name: name.to_string(),
        ty,
        implicit: false,
        is_self: false,
        solver: None,
        default: None,
        origin: ParamOrigin::Written,
        symbol: None,
        span,
    }
}
