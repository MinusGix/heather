//! A definition's own equations, one per branch
//! (issues/definition-branch-equations.md).
//!
//! A `fn` whose body is a test (`if P`, `if h: P`, `match b`, `match h: b` on
//! a `Bool`, after any `let`s) gets one theorem per branch: the call equals
//! that branch, under the branch's condition as a hypothesis in the form the
//! source wrote it (`P`, or `¬P` for the `else`; `b = True`/`b = False` for a
//! `Bool`). A branch that is itself a test is split again, so every leaf of
//! the tests at the body's head has its equation, under every condition on
//! the way to it.
//!
//! The equation is named by the arms it takes: `f::True` and `f::False` for
//! one test (an `if` is a match on its condition's bit), `f::False::True` for
//! the `then` of an `if` in the `else`. Minted `f#True`, `f#False#True` and
//! designated as `f::ext` is, so that no name a module may declare is taken.
//!
//! Each is proved by choosing the arm at the hypothesis, one test at a time
//! (`Bool::convoy_true` where the test carries an equation, `Bool::picked_true`
//! where it does not), so a branch is stated exactly as the body spells it:
//! the `let`s before a test are kept, and a found proof is the body's own.
//! The checker sees every generated declaration, so nothing here is trusted;
//! one it refuses is skipped and the reason recorded.

use heather_syntax::ast::{Arm, Block, Decl, DeclKind, Expr, ExprKind, Param, ParamOrigin, Pat, Stmt, Ty, TyKind};

use crate::measure::{app, arrow, block, companion_ref, eq_ty, lam, subst, subst_surface_ty, var};
use crate::surface::lowered_condition;

/// More leaves than this and no equation is generated: a body that branches
/// that much is a table, and its equations are better asked for than built.
const MAX_LEAVES: usize = 16;

/// How a lowered `if` condition (`decide_bit<c>()`) is read: as the
/// proposition its `Decide` instance decides, or — where that does not
/// elaborate — as the `Bool` its expression is (`if b`, `if xs.is_empty()`),
/// which the elaborator tries second (`elab_condition`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Reading {
    Proposition,
    Bool,
}

/// One branch's equation: the designed spelling and the declaration, minted.
pub(crate) struct BranchEquation {
    pub(crate) designed: String,
    pub(crate) decl: Decl,
}

/// `f#True`, `f#False#True`: the minted name of the equation at `path`.
pub(crate) fn minted_name(name: &str, path: &[&str]) -> String {
    format!("{name}#{}", path.join("#"))
}

/// `f::True`, `f::False::True`: the designed spelling.
pub(crate) fn designed_name(name: &str, path: &[&str]) -> String {
    format!("{name}::{}", path.join("::"))
}

/// One test on the way to a leaf: the statements in force before it, the
/// arm's name (`True`, `Succ`), the parameters taking it (a constructor's
/// fields, then the hypothesis), and the proof that the test is that arm.
#[derive(Clone)]
struct Step {
    lets: Vec<Stmt>,
    arm: String,
    params: Vec<(String, Ty)>,
    chosen: Expr,
}

/// What a constructor's fields are, at the scrutinee's written type: the
/// elaborator's answer (`DeclarationsMut::elab_branch_equations`), `None`
/// where it cannot say.
pub(crate) type FieldTypes<'a> = &'a dyn Fn(&Ty, &str) -> Option<Vec<(Option<String>, Ty)>>;

/// A `Bool` test at the head of an expression.
struct Test<'a> {
    scrut: &'a Expr,
    convoy: Option<&'a String>,
    yes: &'a Expr,
    no: &'a Expr,
}

fn bool_test(e: &Expr) -> Option<Test<'_>> {
    let ExprKind::Match { scrut, eqbind, motive: None, arms, .. } = &e.kind else { return None };
    let [a, b] = arms.as_slice() else { return None };
    let named = |arm: &Arm, ctor: &str| arm.ctor == ctor && !arm.default && arm.binders.is_empty();
    let (yes, no) = if named(a, "True") && (named(b, "False") || b.default) {
        (a, b)
    } else if named(a, "False") && (named(b, "True") || b.default) {
        (b, a)
    } else {
        return None;
    };
    Some(Test { scrut, convoy: eqbind.as_ref(), yes: &yes.body, no: &no.body })
}

/// Every name the declaration binds or reads, so that a hypothesis's name
/// captures nothing where the bit's equation is substituted.
fn taken_names(decl: &Decl) -> Vec<String> {
    let mut out: Vec<String> = decl.params.iter().map(|p| p.name.clone()).collect();
    let body = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span: decl.body.span };
    crate::surface::walk_expr(&body, &mut |x: &Expr| match &x.kind {
        ExprKind::Var(n) => out.push(n.clone()),
        ExprKind::Lam { binders, .. } => out.extend(binders.iter().map(|b| b.name.clone())),
        ExprKind::Match { eqbind, arms, .. } => {
            out.extend(eqbind.iter().cloned());
            for a in arms {
                for p in &a.binders {
                    crate::measure::pat_names(p, &mut out);
                }
            }
        }
        ExprKind::Block(b) => {
            for st in &b.stmts {
                match st {
                    Stmt::Let { name, .. } | Stmt::LetCode { name, .. } => out.push(name.clone()),
                    Stmt::LetRecord { fields, .. } => {
                        for f in fields {
                            crate::measure::pat_names(&f.pat, &mut out);
                        }
                    }
                }
            }
        }
        _ => {}
    });
    out
}

fn is_evidence(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::App { head, .. } if matches!(&head.kind, ExprKind::TyApp { head, .. }
        if matches!(&head.kind, ExprKind::Var(v) if v == "decide_true" || v == "decide_false")))
}

/// The name an `if h: P` arm gives its evidence (`let h = decide_true<P>(e)`).
fn evidence_name(arm: &Expr) -> Option<&str> {
    let ExprKind::Block(b) = &arm.kind else { return None };
    match b.stmts.first() {
        Some(Stmt::Let { name, expr, .. }) if is_evidence(expr) => Some(name),
        _ => None,
    }
}

fn not_ty(p: Ty) -> Ty {
    let span = p.span;
    arrow(None, p, Ty { kind: TyKind::Named { name: "False".into(), args: Vec::new() }, span }, span)
}

fn ty_app_call(name: &str, ty: Ty, args: Vec<Expr>, span: heather_syntax::Span) -> Expr {
    let head = Expr { kind: ExprKind::TyApp { head: Box::new(var(name, span)), args: vec![ty] }, span };
    app(head, args, span)
}

fn with_lets(lets: &[Stmt], e: Expr) -> Expr {
    if lets.is_empty() {
        return e;
    }
    let span = e.span;
    Expr { kind: ExprKind::Block(Box::new(Block { stmts: lets.to_vec(), result: Box::new(e), ons: Vec::new(), span })), span }
}

/// The condition with the `let`s it reads replaced by their values, so that
/// it can be stated outside them; `None` where it reads a name no value
/// stands for (a destructured record, a `have`, code).
fn inline_ty(lets: &[Stmt], ty: &Ty) -> Option<Ty> {
    let mut ty = ty.clone();
    for st in lets.iter().rev() {
        match st {
            Stmt::Let { name, expr, opaque: false, .. } => {
                if crate::inductive::ty_mentions(&ty, name) {
                    ty = subst_surface_ty(&ty, name, expr);
                }
            }
            Stmt::Let { name, .. } | Stmt::LetCode { name, .. } => {
                if crate::inductive::ty_mentions(&ty, name) {
                    return None;
                }
            }
            Stmt::LetRecord { fields, .. } => {
                let mut names = Vec::new();
                for f in fields {
                    crate::measure::pat_names(&f.pat, &mut names);
                }
                if names.iter().any(|n| crate::inductive::ty_mentions(&ty, n)) {
                    return None;
                }
            }
        }
    }
    Some(ty)
}

fn inline_expr(lets: &[Stmt], e: &Expr) -> Option<Expr> {
    let span = e.span;
    let ty = inline_ty(lets, &Ty { kind: TyKind::OfExpr(Box::new(e.clone())), span })?;
    match ty.kind {
        TyKind::OfExpr(e) => Some(*e),
        _ => None,
    }
}

struct Walk<'a> {
    decl: &'a Decl,
    reading: Reading,
    fields: FieldTypes<'a>,
    /// The name the arm is checked at the result type under, `result`.
    result_name: String,
    taken: Vec<String>,
    /// Each leaf: the tests on the way, the statements in force, the leaf.
    leaves: Vec<(Vec<Step>, Vec<Stmt>, Expr)>,
    too_many: bool,
}

impl Walk<'_> {
    fn fresh(&mut self, want: &str) -> String {
        // A numbered name and not a primed one: a tactic that writes its
        // hypotheses into generated source (`omega`) reads `h'` as a
        // character literal.
        let mut n = want.to_string();
        let mut k = 1;
        while self.taken.contains(&n) {
            k += 1;
            n = format!("{want}{k}");
        }
        self.taken.push(n.clone());
        n
    }

    /// `name : R`, the declaration's result type: an equation's sides are
    /// inferred, so a literal arm (`0` of a `u64`) would otherwise take its
    /// default carrier.
    fn at_result(&self, e: Expr) -> Expr {
        let span = e.span;
        let stated = Stmt::Let { name: self.result_name.clone(), ty: Some(self.decl.result.clone()), expr: e, span, opaque: false };
        with_lets(&[stated], var(&self.result_name, span))
    }

    fn chooser(&self, name: &str) -> Expr {
        let span = self.decl.body.span;
        Expr { kind: ExprKind::TyApp { head: Box::new(var(name, span)), args: vec![self.decl.result.clone()] }, span }
    }

    /// A field binder's name as an equation's parameter: the written one
    /// unless a parameter, a `let` on the way or an earlier binder has it.
    fn binder_name(&mut self, want: &str, lets: &[Stmt], path: &[Step]) -> String {
        let want = if want == "_" { "x" } else { want };
        let clashes = |n: &str| {
            self.decl.params.iter().any(|p| p.name == n)
                || lets.iter().any(|st| matches!(st, Stmt::Let { name, .. } | Stmt::LetCode { name, .. } if name == n))
                || path.iter().any(|s| s.params.iter().any(|(p, _)| p == n))
                || n == self.result_name
        };
        let mut n = want.to_string();
        let mut k = 1;
        while clashes(&n) {
            k += 1;
            n = format!("{want}{k}");
        }
        self.taken.push(n.clone());
        n
    }

    /// The hypothesis an arm is taken under, and the bit's equation over it;
    /// `None` where the condition cannot be stated before the test.
    fn hypothesis(&mut self, lets: &[Stmt], t: &Test<'_>, truth: bool) -> Option<(String, Ty, Expr, Expr)> {
        let span = t.scrut.span;
        let arm = if truth { t.yes } else { t.no };
        if let Some(cond) = lowered_condition(t.scrut)
            && cond.head == "decide_bit"
        {
            let bool_reading = self.reading == Reading::Bool && cond.expr.is_some();
            if bool_reading && t.convoy.is_none() {
                // `if b`: the match is on `b` itself.
                let b = inline_expr(lets, cond.expr.as_ref()?)?;
                let name = self.fresh("h");
                let ty = eq_ty(b.clone(), var(if truth { "True" } else { "False" }, span), span);
                return Some((name.clone(), ty, var(&name, span), cond.expr.clone()?));
            }
            // `if P`/`if h: P` (and `if h: b`, read as `b.IsTrue()`).
            let prop = if bool_reading {
                let e = cond.expr.as_ref()?;
                Ty { kind: TyKind::OfExpr(Box::new(crate::surface::is_true_of(e))), span: e.span }
            } else {
                cond.ty.clone()
            };
            let stated = inline_ty(lets, &prop)?;
            let name = self.fresh(evidence_name(arm).unwrap_or("h"));
            let ty = if truth { stated.clone() } else { not_ty(stated.clone()) };
            let lemma = if truth { "bool::decide_bit_of" } else { "bool::decide_bit_of_not" };
            let bit_eq = ty_app_call(lemma, stated, vec![var(&name, span)], span);
            return Some((name, ty, bit_eq, (*t.scrut).clone()));
        }
        // A `match` on a `Bool`.
        let b = inline_expr(lets, t.scrut)?;
        let name = self.fresh(t.convoy.map(String::as_str).unwrap_or("h"));
        let ty = eq_ty(b, var(if truth { "True" } else { "False" }, span), span);
        Some((name.clone(), ty, var(&name, span), (*t.scrut).clone()))
    }

    fn walk(&mut self, e: &Expr, mut lets: Vec<Stmt>, path: Vec<Step>) {
        let mut e = e;
        while let ExprKind::Block(b) = &e.kind {
            if !b.ons.is_empty() {
                break;
            }
            lets.extend(b.stmts.iter().cloned());
            e = &b.result;
        }
        if self.too_many {
            return;
        }
        let leaf = |this: &mut Self, path: Vec<Step>, lets: Vec<Stmt>| {
            if !path.is_empty() {
                this.leaves.push((path, lets, e.clone()));
                this.too_many |= this.leaves.len() > MAX_LEAVES;
            }
        };
        let arms = match bool_test(e) {
            Some(t) => self.bool_arms(&lets, &t),
            None => self.ctor_arms(e, &lets, &path),
        };
        let Some(arms) = arms else {
            return leaf(self, path, lets);
        };
        for (arm, params, chosen, taken) in arms {
            let mut next = path.clone();
            next.push(Step { lets: lets.clone(), arm, params, chosen });
            self.walk(&taken, lets.clone(), next);
        }
    }

    /// The two arms of a `Bool` test: each one's hypothesis, the proof that
    /// the test is that arm, and the arm with the test's equation given.
    fn bool_arms(&mut self, lets: &[Stmt], t: &Test<'_>) -> Option<Vec<(String, Vec<(String, Ty)>, Expr, Expr)>> {
        let span = t.scrut.span;
        let mut hyps = Vec::new();
        for truth in [true, false] {
            hyps.push(self.hypothesis(lets, t, truth)?);
        }
        let mut out = Vec::new();
        for (truth, (hyp_name, hyp_ty, bit_eq, scrut)) in [true, false].into_iter().zip(hyps) {
            let arm = if truth { t.yes } else { t.no };
            let chosen = match t.convoy {
                Some(eq) => {
                    let chooser = if truth { "bool::Bool::convoy_true" } else { "bool::Bool::convoy_false" };
                    app(self.chooser(chooser), vec![scrut, lam(&[eq.as_str()], t.yes.clone(), span), lam(&[eq.as_str()], t.no.clone(), span), bit_eq.clone()], span)
                }
                None => {
                    let chooser = if truth { "bool::Bool::picked_true" } else { "bool::Bool::picked_false" };
                    app(self.chooser(chooser), vec![scrut, t.yes.clone(), t.no.clone(), bit_eq.clone()], span)
                }
            };
            let taken = match t.convoy {
                Some(eq) => subst(arm, &[(eq.as_str(), &bit_eq)], &mut Vec::new()),
                None => arm.clone(),
            };
            out.push((if truth { "True" } else { "False" }.to_string(), vec![(hyp_name, hyp_ty)], chosen, taken));
        }
        Some(out)
    }

    /// The arms of a `match` on a parameter of an inductive type, one per
    /// constructor written: its fields as parameters, typed from the
    /// declaration at the parameter's written type, and `h: x = C(ȳ)`. The
    /// proof rewrites the scrutinee to the constructor, where the `match`
    /// computes (`j`). A `_` arm has no equation: its condition is every
    /// other constructor's failure.
    fn ctor_arms(&mut self, e: &Expr, lets: &[Stmt], path: &[Step]) -> Option<Vec<(String, Vec<(String, Ty)>, Expr, Expr)>> {
        let ExprKind::Match { scrut, eqbind: None, motive: None, arms, .. } = &e.kind else { return None };
        let ExprKind::Var(x) = &scrut.kind else { return None };
        let rebound = lets.iter().any(|st| match st {
            Stmt::Let { name, .. } | Stmt::LetCode { name, .. } => name == x,
            Stmt::LetRecord { .. } => true,
        });
        let param = self.decl.params.iter().find(|p| &p.name == x)?;
        if rebound || path.iter().any(|s| s.params.iter().any(|(p, _)| p == x)) {
            return None;
        }
        let scrut_ty = param.ty.clone();
        let span = e.span;
        let c = self.fresh("c");
        let mut motive_match = e.clone();
        if let ExprKind::Match { scrut, motive, .. } = &mut motive_match.kind {
            *scrut = Box::new(var(&c, span));
            let r = Expr { kind: ExprKind::TyLit(Box::new(self.decl.result.clone())), span };
            *motive = Some(Box::new(lam(&["_"], r, span)));
        }
        let mut out = Vec::new();
        for arm in arms.iter().filter(|a| !a.default) {
            let fields = (self.fields)(&scrut_ty, &arm.ctor)?;
            if fields.len() != arm.binders.len() {
                return None;
            }
            let mut params = Vec::new();
            let mut renames: Vec<(String, Expr)> = Vec::new();
            let mut field_names: Vec<(String, Expr)> = Vec::new();
            for (binder, (field, ty)) in arm.binders.iter().zip(&fields) {
                let Pat::Var { name, .. } = binder else { return None };
                let mut all = path.to_vec();
                all.push(Step { lets: Vec::new(), arm: String::new(), params: params.clone(), chosen: var("_", span) });
                let fresh = self.binder_name(name, lets, &all);
                let mut ty = ty.clone();
                for (f, v) in &field_names {
                    ty = subst_surface_ty(&ty, f, v);
                }
                if let Some(f) = field {
                    field_names.push((f.clone(), var(&fresh, span)));
                }
                if name != "_" && &fresh != name {
                    renames.push((name.clone(), var(&fresh, span)));
                }
                params.push((fresh, ty));
            }
            let value = app(var(&arm.ctor, span), params.iter().map(|(n, _)| var(n, span)).collect(), span);
            let value = if params.is_empty() { var(&arm.ctor, span) } else { value };
            let h = self.fresh("h");
            params.push((h.clone(), eq_ty((**scrut).clone(), value, span)));
            let map: Vec<(&str, &Expr)> = renames.iter().map(|(a, b)| (a.as_str(), b)).collect();
            let taken = subst(&arm.body, &map, &mut Vec::new());
            let motive = lam(&[c.as_str(), "_"], Expr { kind: ExprKind::Eq(Box::new(motive_match.clone()), Box::new(self.at_result(taken.clone()))), span }, span);
            let back = app(var("sym", span), vec![var(&h, span)], span);
            let chosen = Expr { kind: ExprKind::J { proof: Box::new(back), motive: Box::new(motive), case: Box::new(Expr { kind: ExprKind::Refl, span }) }, span };
            out.push((arm.ctor.rsplit("::").next().unwrap_or(&arm.ctor).to_string(), params, chosen, taken));
        }
        if out.is_empty() { None } else { Some(out) }
    }
}

/// Does the body call the declaration again? Its equations are then its
/// unfolding's (`f::step`, `f::done` for a `decreases` loop), not these.
fn recursive(decl: &Decl, self_name: &str) -> bool {
    let base = self_name.rsplit("::").next().unwrap_or(self_name);
    let body = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span: decl.body.span };
    let mut found = false;
    crate::surface::walk_expr(&body, &mut |x: &Expr| match &x.kind {
        ExprKind::Var(n) if n == &decl.name || n == self_name => found = true,
        ExprKind::Dot { name, .. } if name == base => found = true,
        _ => {}
    });
    found
}

/// Whether `decl` is one whose branches get equations at all: a `fn` with
/// value parameters whose body is a test, not a recursion and not a tactic.
pub(crate) fn candidate(decl: &Decl) -> bool {
    if decl.kind != DeclKind::Fn || decl.is_meta || decl.value || decl.is_evidence || decl.is_interface {
        return false;
    }
    let mut e = &*decl.body.result;
    let mut ons = !decl.body.ons.is_empty();
    while let ExprKind::Block(b) = &e.kind {
        ons |= !b.ons.is_empty();
        e = &b.result;
    }
    !ons && matches!(&e.kind, ExprKind::Match { motive: None, .. })
}

/// The designed names a reference may expect of `decl`'s first test, under
/// which a refusal is recorded: `f::True`/`f::False`, or `f::C` per arm.
pub(crate) fn head_names(decl: &Decl) -> Vec<String> {
    let mut e = &*decl.body.result;
    while let ExprKind::Block(b) = &e.kind {
        e = &b.result;
    }
    if bool_test(e).is_some() {
        return vec![designed_name(&decl.name, &["True"]), designed_name(&decl.name, &["False"])];
    }
    match &e.kind {
        ExprKind::Match { arms, .. } => arms
            .iter()
            .filter(|a| !a.default)
            .map(|a| designed_name(&decl.name, &[a.ctor.rsplit("::").next().unwrap_or(&a.ctor)]))
            .collect(),
        _ => Vec::new(),
    }
}

/// The equations of `decl`'s branches, at `reading`. `Err` says why there
/// are none.
pub(crate) fn branch_equations(decl: &Decl, self_name: &str, reading: Reading, fields: FieldTypes<'_>) -> Result<Vec<BranchEquation>, String> {
    if recursive(decl, self_name) {
        return Err("the body calls the function again".into());
    }
    let span = decl.body.span;
    let mut taken = taken_names(decl);
    let result_name = ["result", "result2", "result3"].into_iter().find(|n| !taken.iter().any(|t| t == n)).unwrap_or("result_").to_string();
    taken.push(result_name.clone());
    let mut w = Walk { decl, reading, fields, result_name, taken, leaves: Vec::new(), too_many: false };
    let top = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span };
    w.walk(&top, Vec::new(), Vec::new());
    if w.too_many {
        return Err(format!("the body has more than {MAX_LEAVES} branches"));
    }
    if w.leaves.is_empty() {
        return Err("the body is not a test whose condition can be stated before it".into());
    }
    let decl = w.decl;
    let explicit = decl.params.iter().any(|p| p.implicit);
    let call = |head: Expr, args: Vec<Expr>| Expr {
        kind: ExprKind::App { head: Box::new(head), args, named: Vec::new(), explicit, goal_oriented: false },
        span,
    };
    let args: Vec<Expr> = decl.params.iter().map(|p| var(&p.name, span)).collect();
    let lhs = call(companion_ref(decl, &decl.name, span), args);
    let mut out = Vec::new();
    for (path, lets, leaf) in std::mem::take(&mut w.leaves) {
        let names: Vec<&str> = path.iter().map(|s| s.arm.as_str()).collect();
        // The leaf is stated under every statement on the way to it, at the
        // declaration's result type.
        let rhs = with_lets(&lets, w.at_result(leaf));
        let mut proof: Option<Expr> = None;
        for s in path.iter().rev() {
            let step = with_lets(&s.lets, s.chosen.clone());
            proof = Some(match proof {
                None => step,
                Some(rest) => app(var("trans", span), vec![step, rest], span),
            });
        }
        let mut params = decl.params.clone();
        for (name, ty) in path.iter().flat_map(|s| s.params.iter()) {
            params.push(Param {
                name: name.clone(),
                ty: ty.clone(),
                implicit: false,
                is_self: false,
                solver: None,
                default: None,
                origin: ParamOrigin::Written,
                symbol: None,
                span,
            });
        }
        out.push(BranchEquation {
            designed: designed_name(&decl.name, &names),
            decl: Decl {
                kind: DeclKind::Theorem,
                is_meta: false,
                is_evidence: false,
                is_interface: false,
                partial: None,
                value: false,
                elaborates: None,
                name: minted_name(&decl.name, &names),
                tyvars: decl.tyvars.clone(),
                params,
                result: eq_ty(lhs.clone(), rhs, span),
                decreases: None,
                unfolding: Vec::new(),
                body: block(proof.expect("a leaf is under at least one test"), span),
                span: decl.span,
            },
        });
    }
    Ok(out)
}
