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
//! A `match` on a parameter of an inductive type is a test too, and so is
//! one on any other term of one, a call's result above all, its type the
//! elaborator's (`Walk::result_arms`; `o.and_then(λ v => …)`, `o.map(…)`, a
//! postfix `?` and `b.guard(o)` read as the `match` they are,
//! `Walk::pipeline_arms`): an arm's equation is under its fields and
//! `h: g(ā) = C(ȳ)` (issues/induct-through-result-matches.md).
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
    /// The tests on the way to the leaf, the `let`s in force at it, and the
    /// leaf as the body spells it: what an induction principle that follows
    /// the body is built from (`function_induction`).
    pub(crate) path: Vec<PathStep>,
    pub(crate) lets: Vec<Stmt>,
    pub(crate) leaf: Expr,
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
    test: PathTest,
}

/// How a proof that follows the body decides one test on the way to a leaf
/// (`function_induction`): what to match on, and how the arm's hypothesis
/// is read off the match's equation.
#[derive(Clone)]
pub(crate) enum PathTest {
    /// A match on a `Bool`: `scrut` (stated outside the `let`s), and where
    /// the test decides a proposition `P`, `P` itself, whose evidence is
    /// `decide_true<P>(e)`/`decide_false<P>(e)` at the equation `e`; where it
    /// does not, the equation `scrut = True` is the hypothesis. `written`
    /// is the hypothesis's name in the body (`if h: P`'s `h`) where the
    /// equation had to number it apart (`h2`), so a proof that follows the
    /// body binds it under the name the body's `on` clauses use.
    Bool { scrut: Expr, prop: Option<Ty>, written: Option<String> },
    /// A `match` on the parameter `param`, at the arm `ctor`.
    Ctor { param: String, ctor: String },
    /// A `match` on any other term of an inductive type, a call's result
    /// above all (`match first.emits(p) { None => …, Some(c) => … }`), at
    /// the arm `ctor`: `scrut` stated outside the `let`s, the arm's fields
    /// and then `h: scrut = C(ȳ)` its parameters. `written` is the name a
    /// `match h:` gave the equation where the equations numbered it apart,
    /// as for a `Bool` test.
    Result { scrut: Expr, ctor: String, written: Option<String> },
}

/// One test on the way to an equation's leaf, as `function_induction` reads
/// it: the arm's name, the parameters taking it (a constructor's fields,
/// then the hypothesis), and the test.
#[derive(Clone)]
pub(crate) struct PathStep {
    pub(crate) arm: String,
    pub(crate) params: Vec<(String, Ty)>,
    pub(crate) test: PathTest,
}

/// How `f` itself reaches its body, which decides the first step of every
/// equation's proof.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Recursion {
    /// Not recursive: `f(x̄)` unfolds to its body by definition.
    None,
    /// A `decreases` recursion: `f_unfold(x̄)` states `f(x̄)` as its body.
    Measure,
    /// A structural recursion on a parameter the body's first test matches:
    /// `f` at that parameter's constructor computes to the arm.
    Structural,
}

/// What a constructor's fields are, at the scrutinee's written type: the
/// elaborator's answer (`DeclarationsMut::elab_branch_equations`), `None`
/// where it cannot say.
pub(crate) type FieldTypes<'a> = &'a dyn Fn(&Ty, &str) -> Option<Vec<(Option<String>, Ty)>>;

/// The surface type of a term the body matches on that is not a parameter
/// (`first.emits(p, names)`), over the parameters and the binders on the
/// way to it, in order: the elaborator's answer, checked, or `None`.
pub(crate) type ScrutTypes<'a> = &'a dyn Fn(&Expr, &[(String, Ty)]) -> Option<Ty>;

/// What a test's arms are, as the walk builds them: each arm's name, the
/// parameters taking it, the proof that the test is that arm, the arm with
/// the test's evidence given, and the test.
type Arms = Vec<(String, Vec<(String, Ty)>, Expr, Expr, PathTest)>;

/// A `Bool` test at the head of an expression.
struct Test<'a> {
    scrut: &'a Expr,
    convoy: Option<&'a String>,
    /// The name an `if h:` gave its test (`ExprKind::Match::test`).
    written: Option<&'a String>,
    yes: &'a Expr,
    no: &'a Expr,
}

fn bool_test(e: &Expr) -> Option<Test<'_>> {
    let ExprKind::Match { scrut, eqbind, motive: None, arms, test, .. } = &e.kind else { return None };
    let [a, b] = arms.as_slice() else { return None };
    let named = |arm: &Arm, ctor: &str| arm.ctor == ctor && !arm.default && arm.binders.is_empty();
    let (yes, no) = if named(a, "True") && (named(b, "False") || b.default) {
        (a, b)
    } else if named(a, "False") && (named(b, "True") || b.default) {
        (b, a)
    } else {
        return None;
    };
    Some(Test { scrut, convoy: eqbind.as_ref(), written: test.as_ref(), yes: &yes.body, no: &no.body })
}

/// A pipeline step written as a call (`o.and_then(λ v => k)`, `o.map(…)`,
/// `b.guard(o)`, or the same as `Option::and_then(o, …)`): the subject, the
/// method, and the arguments after the subject. Read as the `match` the
/// callee is (`Walk::pipeline_arms`).
fn pipeline_call(e: &Expr) -> Option<(&Expr, &str, &[Expr])> {
    let (subject, method, rest) = match &e.kind {
        ExprKind::Dot { recv, name, args: Some(args), named, .. } if named.is_empty() => (&**recv, name.as_str(), args.as_slice()),
        ExprKind::App { head, args, named, .. } if named.is_empty() && !args.is_empty() => {
            let ExprKind::Var(n) = &head.kind else { return None };
            let mut parts = n.rsplit("::");
            let method = parts.next()?;
            if !matches!(parts.next(), Some("Option" | "Result" | "Bool")) {
                return None;
            }
            (&args[0], method, &args[1..])
        }
        _ => return None,
    };
    matches!(method, "and_then" | "map" | "guard").then_some((subject, method, rest))
}

/// The arm names a pipeline step may take, by its method alone: a superset,
/// since `and_then` on an `Option` and on a `Result` read alike.
fn pipeline_arm_names(method: &str) -> &'static [&'static str] {
    match method {
        "guard" => &["True", "False"],
        _ => &["Some", "None", "Ok", "Err"],
    }
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
    arrow(None, p, Ty { kind: TyKind::Named { name: "logic::False".into(), args: Vec::new() }, span }, span)
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
                    // An expression is inlined sharing a value it reads more
                    // than once: the lets run backwards here, so `r := r
                    // with { a = r.a + i }` repeated `k` times would
                    // otherwise spell `r`'s first value 2^k times
                    // (issues/word-loop-body-exponential.md).
                    ty = match &ty.kind {
                        TyKind::OfExpr(e) => Ty {
                            kind: TyKind::OfExpr(Box::new(crate::measure::subst_shared(e, &[(name.as_str(), expr)]))),
                            span: ty.span,
                        },
                        _ => subst_surface_ty(&ty, name, expr),
                    };
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

pub(crate) fn inline_expr(lets: &[Stmt], e: &Expr) -> Option<Expr> {
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
    /// Where a `match` on a call's result is a test (`result_arms`): `None`
    /// reads such a match as a leaf, as before.
    results: Option<ScrutTypes<'a>>,
    /// Whether some leaf's path went through a `match` on a result.
    read_results: bool,
    /// The name the arm is checked at the result type under, `result`.
    result_name: String,
    taken: Vec<String>,
    recursion: Recursion,
    /// `f(x̄)`, the equations' left side: a structural recursion's first
    /// test is proved at it rather than at the body.
    lhs: Expr,
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
    fn hypothesis(&mut self, lets: &[Stmt], t: &Test<'_>, truth: bool) -> Option<(String, Ty, Expr, Expr, PathTest)> {
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
                let test = PathTest::Bool { scrut: b, prop: None, written: None };
                return Some((name.clone(), ty, var(&name, span), cond.expr.clone()?, test));
            }
            // `if P`/`if h: P` (and `if h: b`, read as `b.IsTrue()`).
            let prop = if bool_reading {
                let e = cond.expr.as_ref()?;
                Ty { kind: TyKind::OfExpr(Box::new(crate::surface::is_true_of(e))), span: e.span }
            } else {
                cond.ty.clone()
            };
            let stated = inline_ty(lets, &prop)?;
            // The name `if less:` gives, read off whichever branch binds it:
            // a branch that never uses it binds none.
            // A branch that never uses it binds none; the match keeps the
            // name as written either way.
            let written = evidence_name(arm)
                .or_else(|| evidence_name(if truth { t.no } else { t.yes }))
                .or(t.written.map(String::as_str))
                .map(str::to_string);
            let name = self.fresh(evidence_name(arm).unwrap_or("h"));
            let ty = if truth { stated.clone() } else { not_ty(stated.clone()) };
            let lemma = if truth { "bool::decide_bit_of" } else { "bool::decide_bit_of_not" };
            let bit_eq = ty_app_call(lemma, stated.clone(), vec![var(&name, span)], span);
            let written = written.filter(|w| *w != name);
            let test = PathTest::Bool { scrut: (*t.scrut).clone(), prop: Some(stated), written };
            return Some((name, ty, bit_eq, (*t.scrut).clone(), test));
        }
        // A `match` on a `Bool`.
        let b = inline_expr(lets, t.scrut)?;
        let name = self.fresh(t.convoy.map(String::as_str).unwrap_or("h"));
        let ty = eq_ty(b.clone(), var(if truth { "True" } else { "False" }, span), span);
        Some((name.clone(), ty, var(&name, span), (*t.scrut).clone(), PathTest::Bool { scrut: b, prop: None, written: None }))
    }

    fn walk(&mut self, e: &Expr, mut lets: Vec<Stmt>, path: Vec<Step>) {
        let mut e = e;
        while let ExprKind::Block(b) = &e.kind {
            if !b.ons.is_empty() {
                break;
            }
            // A claimed call (`let below = s.byte_within(…)` in a `mut
            // self` body is `\0mutated(…)`) spelled as the two `let`s it
            // binds, so a test that reads `below` states the value, which a
            // hypothesis outside the block can elaborate.
            match crate::measure::rebind_marked(&b.stmts, b.span, false) {
                Ok(stmts) => lets.extend(stmts),
                Err(_) => lets.extend(b.stmts.iter().cloned()),
            }
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
            None => self.ctor_arms(e, &lets, &path).or_else(|| self.result_arms(e, &lets, &path)).or_else(|| self.pipeline_arms(e, &lets, &path)),
        };
        let Some(arms) = arms else {
            return leaf(self, path, lets);
        };
        for (arm, params, chosen, taken, test) in arms {
            let mut next = path.clone();
            next.push(Step { lets: lets.clone(), arm, params, chosen, test });
            self.walk(&taken, lets.clone(), next);
        }
    }

    /// The two arms of a `Bool` test: each one's hypothesis, the proof that
    /// the test is that arm, and the arm with the test's equation given.
    fn bool_arms(&mut self, lets: &[Stmt], t: &Test<'_>) -> Option<Arms> {
        let span = t.scrut.span;
        let mut hyps = Vec::new();
        for truth in [true, false] {
            hyps.push(self.hypothesis(lets, t, truth)?);
        }
        let mut out = Vec::new();
        for (truth, (hyp_name, hyp_ty, bit_eq, scrut, test)) in [true, false].into_iter().zip(hyps) {
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
            out.push((if truth { "True" } else { "False" }.to_string(), vec![(hyp_name, hyp_ty)], chosen, taken, test));
        }
        Some(out)
    }

    /// The arms of a `match` on a parameter of an inductive type, one per
    /// constructor written: its fields as parameters, typed from the
    /// declaration at the parameter's written type, and `h: x = C(ȳ)`. The
    /// proof rewrites the scrutinee to the constructor, where the `match`
    /// computes (`j`). A `_` arm has no equation: its condition is every
    /// other constructor's failure.
    fn ctor_arms(&mut self, e: &Expr, lets: &[Stmt], path: &[Step]) -> Option<Arms> {
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
            let (mut params, renames, value) = self.arm_fields(arm, &scrut_ty, lets, path, span)?;
            let h = self.fresh("h");
            params.push((h.clone(), eq_ty((**scrut).clone(), value, span)));
            let map: Vec<(&str, &Expr)> = renames.iter().map(|(a, b)| (a.as_str(), b)).collect();
            let taken = subst(&arm.body, &map, &mut Vec::new());
            // A structural recursion's first test is proved at `f` itself:
            // `f` at the constructor computes to the arm, where its body as
            // a `match` on a neutral parameter is not `f` by definition.
            let lhs = if self.recursion == Recursion::Structural && path.is_empty() {
                let at = var(&c, span);
                let both = |e: &Expr| subst(e, &[(x.as_str(), &at)], &mut Vec::new());
                Expr { kind: ExprKind::Eq(Box::new(both(&self.lhs)), Box::new(self.at_result(both(&taken)))), span }
            } else {
                Expr { kind: ExprKind::Eq(Box::new(motive_match.clone()), Box::new(self.at_result(taken.clone()))), span }
            };
            let motive = lam(&[c.as_str(), "_"], lhs, span);
            let back = app(var("sym", span), vec![var(&h, span)], span);
            let chosen = Expr { kind: ExprKind::J { proof: Box::new(back), motive: Box::new(motive), case: Box::new(Expr { kind: ExprKind::Refl, span }) }, span };
            let test = PathTest::Ctor { param: x.clone(), ctor: arm.ctor.clone() };
            out.push((arm.ctor.rsplit("::").next().unwrap_or(&arm.ctor).to_string(), params, chosen, taken, test));
        }
        if out.is_empty() { None } else { Some(out) }
    }

    /// An arm's fields as an equation's parameters, typed at the
    /// scrutinee's type `scrut_ty` (a later field's type over the earlier
    /// ones as bound), named as the arm binds them unless that clashes; the
    /// renames the arm's body then needs; and the constructor at them.
    fn arm_fields(&mut self, arm: &Arm, scrut_ty: &Ty, lets: &[Stmt], path: &[Step], span: heather_syntax::Span) -> Option<(Vec<(String, Ty)>, Vec<(String, Expr)>, Expr)> {
        let fields = (self.fields)(scrut_ty, &arm.ctor)?;
        if fields.len() != arm.binders.len() {
            return None;
        }
        let mut params = Vec::new();
        let mut renames: Vec<(String, Expr)> = Vec::new();
        let mut field_names: Vec<(String, Expr)> = Vec::new();
        for (binder, (field, ty)) in arm.binders.iter().zip(&fields) {
            let Pat::Var { name, .. } = binder else { return None };
            let mut all = path.to_vec();
            all.push(Step { lets: Vec::new(), arm: String::new(), params: params.clone(), chosen: var("_", span), test: PathTest::Ctor { param: String::new(), ctor: String::new() } });
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
        Some((params, renames, value))
    }

    /// The arms of a `match` on a term that is not a parameter, a call's
    /// result above all (`match first.emits(p) { None => …, Some(c) => … }`):
    /// one per constructor written, its fields as parameters and
    /// `h: g(ā) = C(ȳ)` (under the name a `match h:` gives it), with `g(ā)`
    /// stated outside the `let`s. The term's type is the elaborator's
    /// (`results`); a `_` arm, whose condition is every other constructor's
    /// failure, leaves the `match` a leaf.
    ///
    /// The proof rewrites along `h` itself, as `Bool::taken_true` does: at
    /// `w := g(ā)` the two sides are the one `match`, and at `w := C(ȳ)` the
    /// right one computes to the arm, the convoy's equation given as `h`.
    fn result_arms(&mut self, e: &Expr, lets: &[Stmt], path: &[Step]) -> Option<Arms> {
        let ExprKind::Match { scrut, eqbind, motive: None, arms, .. } = &e.kind else { return None };
        if arms.is_empty() || arms.iter().any(|a| a.default) {
            return None;
        }
        // A parameter is `ctor_arms`'s, which declined it.
        let stated = inline_expr(lets, scrut)?;
        if matches!(&stated.kind, ExprKind::Var(x) if self.decl.params.iter().any(|p| &p.name == x)) {
            return None;
        }
        let scrut_ty = self.scrut_type(&stated, path)?;
        let span = e.span;
        let w = self.fresh("w");
        let c = self.fresh("c");
        let result = self.decl.result.clone();
        // The right side: the same `match` at `w`, the convoy's equation
        // passed as `q`.
        let mut at_w = e.clone();
        if let ExprKind::Match { scrut: s, eqbind: eb, motive, arms: wa, .. } = &mut at_w.kind {
            *s = Box::new(var(&w, span));
            match eqbind {
                Some(h) => {
                    *eb = None;
                    let eq = arrow(None, eq_ty((**scrut).clone(), var(&c, span), span), result.clone(), span);
                    *motive = Some(Box::new(lam(&[c.as_str()], Expr { kind: ExprKind::TyLit(Box::new(eq)), span }, span)));
                    for a in wa.iter_mut() {
                        a.body = lam(&[h.as_str()], a.body.clone(), span);
                    }
                }
                None => *motive = Some(Box::new(lam(&["_"], Expr { kind: ExprKind::TyLit(Box::new(result)), span }, span))),
            }
        }
        self.tested_arms(e, &w, at_w, &stated, &scrut_ty, eqbind.as_ref(), arms, lets, path)
    }

    /// A pipeline step written as a call rather than a `match`
    /// (issues/induct-through-result-matches.md item 4), read as the
    /// `match` the callee is: `o.and_then(λ v => k)` and `o.map(λ v => k)`
    /// on an `Option` or a `Result` (a postfix `?` lowers to the latter's),
    /// and `b.guard(o)` on a `Bool`. Named by the constructors as a `match`
    /// is (`Some`, `None`; `Ok`, `Err`; `True`, `False`). Read by name
    /// only: the equation is proved by the callee computing at the
    /// constructor, so a function of that name that does something else is
    /// refused by the checker, and the body is then read as before.
    fn pipeline_arms(&mut self, e: &Expr, lets: &[Stmt], path: &[Step]) -> Option<Arms> {
        let (subject, method, rest) = pipeline_call(e)?;
        // The step at `w`: the subject replaced.
        let at_w = |w: Expr| {
            let mut e = e.clone();
            match &mut e.kind {
                ExprKind::Dot { recv, .. } => *recv = Box::new(w),
                ExprKind::App { args, .. } => args[0] = w,
                _ => {}
            }
            e
        };
        let stated = inline_expr(lets, subject)?;
        let scrut_ty = self.scrut_type(&stated, path)?;
        let TyKind::Named { name: ty_name, .. } = &scrut_ty.kind else { return None };
        let kind = ty_name.rsplit("::").next().unwrap_or(ty_name);
        let span = e.span;
        let ctor = |c: &str| var(&format!("{ty_name}::{c}"), span);
        let arm = |c: &str, binders: Vec<&str>, body: Expr| Arm {
            ctor: c.to_string(),
            default: false,
            binders: binders.into_iter().map(|n| Pat::Var { name: n.to_string(), span }).collect(),
            body,
            span,
        };
        // `λ v => k`: the continuation's binder and body.
        let continuation = || -> Option<(String, Expr)> {
            let [f] = rest else { return None };
            let ExprKind::Lam { binders, body } = &f.kind else { return None };
            let [b] = binders.as_slice() else { return None };
            // A postfix `?`'s slot (`#try0`) is no name a case can bind.
            if b.name.starts_with('#') {
                let value = var("value", b.span);
                return Some(("value".to_string(), subst(body, &[(b.name.as_str(), &value)], &mut Vec::new())));
            }
            Some((b.name.clone(), (**body).clone()))
        };
        let arms = match (kind, method) {
            ("Option", "and_then") => {
                let (v, k) = continuation()?;
                vec![arm("None", vec![], ctor("None")), arm("Some", vec![&v], k)]
            }
            ("Option", "map") => {
                let (v, k) = continuation()?;
                vec![arm("None", vec![], ctor("None")), arm("Some", vec![&v], app(ctor("Some"), vec![k], span))]
            }
            ("Result", "and_then" | "map") => {
                let (v, k) = continuation()?;
                let x = self.fresh("x");
                let ok = if method == "map" { app(ctor("Ok"), vec![k], span) } else { k };
                vec![arm("Ok", vec![&v], ok), arm("Err", vec![&x], app(ctor("Err"), vec![var(&x, span)], span))]
            }
            ("Bool", "guard") => {
                let [o] = rest else { return None };
                vec![arm("False", vec![], var("None", span)), arm("True", vec![], o.clone())]
            }
            _ => return None,
        };
        let w = self.fresh("w");
        let rhs = at_w(var(&w, span));
        self.tested_arms(e, &w, rhs, &stated, &scrut_ty, None, &arms, lets, path)
    }

    /// The type of a matched term: a binder's own on the way, else the
    /// elaborator's (`results`).
    fn scrut_type(&self, stated: &Expr, path: &[Step]) -> Option<Ty> {
        let types = self.results?;
        let known: Vec<(String, Ty)> = self.decl.params.iter().map(|p| (p.name.clone(), p.ty.clone()))
            .chain(path.iter().flat_map(|s| s.params.iter().cloned()))
            .collect();
        match &stated.kind {
            ExprKind::Var(x) => known.iter().rev().find(|(n, _)| n == x).map(|(_, t)| t.clone()).or_else(|| types(stated, &known)),
            _ => types(stated, &known),
        }
    }

    /// The arms of a test on the term `stated` (of type `scrut_ty`), which
    /// `whole` (the `match`, or the call that is one) tests and `at_w` is at
    /// `w`: each arm's fields and `h: stated = C(ȳ)` as parameters, and the
    /// proof along `h` that `whole` is the arm (`j`, the motive's `q` the
    /// convoy's equation where `at_w` takes one).
    #[allow(clippy::too_many_arguments)]
    fn tested_arms(&mut self, whole: &Expr, w: &str, at_w: Expr, stated: &Expr, scrut_ty: &Ty, eqbind: Option<&String>, arms: &[Arm], lets: &[Stmt], path: &[Step]) -> Option<Arms> {
        let span = whole.span;
        let q = self.fresh("q");
        let rhs = match eqbind {
            Some(_) => app(at_w, vec![var(&q, span)], span),
            None => at_w,
        };
        let motive = lam(&[w, q.as_str()], Expr { kind: ExprKind::Eq(Box::new(self.at_result(whole.clone())), Box::new(self.at_result(rhs))), span }, span);
        let mut out = Vec::new();
        for arm in arms {
            let (mut params, mut renames, value) = self.arm_fields(arm, scrut_ty, lets, path, span)?;
            // Named as the arm's fields are, apart only from what is in
            // scope at the equation, so a case reads `h` and not a name
            // numbered past every test of the body.
            let mut all = path.to_vec();
            all.push(Step { lets: Vec::new(), arm: String::new(), params: params.clone(), chosen: var("_", span), test: PathTest::Ctor { param: String::new(), ctor: String::new() } });
            let h = self.binder_name(eqbind.map(String::as_str).unwrap_or("h"), lets, &all);
            if let Some(written) = eqbind
                && *written != h
            {
                renames.push((written.clone(), var(&h, span)));
            }
            params.push((h.clone(), eq_ty(stated.clone(), value, span)));
            let map: Vec<(&str, &Expr)> = renames.iter().map(|(a, b)| (a.as_str(), b)).collect();
            let taken = subst(&arm.body, &map, &mut Vec::new());
            let chosen = Expr { kind: ExprKind::J { proof: Box::new(var(&h, span)), motive: Box::new(motive.clone()), case: Box::new(Expr { kind: ExprKind::Refl, span }) }, span };
            let written = eqbind.cloned().filter(|n| *n != h);
            let test = PathTest::Result { scrut: stated.clone(), ctor: arm.ctor.clone(), written };
            out.push((arm.ctor.rsplit("::").next().unwrap_or(&arm.ctor).to_string(), params, chosen, taken, test));
        }
        self.read_results = true;
        Some(out)
    }
}

/// Does the body call the declaration again? Its equations are then its
/// unfolding's (`f::step`, `f::done` for a `decreases` loop), not these.
pub(crate) fn recursive(decl: &Decl, self_name: &str) -> bool {
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
    // A measured body's own `on`s discharge its obligations, which are no
    // part of its equations, as they are none of `f_unfold`'s.
    let mut ons = decl.decreases.is_none() && !decl.body.ons.is_empty();
    while let ExprKind::Block(b) = &e.kind {
        ons |= !b.ons.is_empty();
        e = &b.result;
    }
    !ons && (matches!(&e.kind, ExprKind::Match { motive: None, .. }) || pipeline_call(e).is_some())
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
        _ => match pipeline_call(e) {
            Some((_, method, _)) => pipeline_arm_names(method).iter().map(|a| designed_name(&decl.name, &[a])).collect(),
            None => Vec::new(),
        },
    }
}

/// Every path of arms through the tests at the head of a definition's
/// `body`, as it spells them (`["False", "True"]`), at any depth: where an equation may
/// be minted. A superset of the paths [`branch_equations`] names, which
/// also stops at a test it cannot state or a `match` that is not on a
/// parameter; never more than the body's own tests, so a reader looking
/// equations up by name tries exactly these (`simp_only(f)`, which before
/// tried every path six tests deep and so missed a seventh test). The
/// paths come in the order a reader should try them: below.
pub(crate) fn test_paths(body: &Expr) -> Vec<Vec<String>> {
    fn head(e: &Expr) -> &Expr {
        let mut e = e;
        while let ExprKind::Block(b) = &e.kind {
            e = &b.result;
        }
        e
    }
    /// Each arm's name and body, `None` for a pipeline step's arm that
    /// ends there (`None`, `Err`, `False`).
    fn arms(e: &Expr) -> Vec<(&str, Option<&Expr>)> {
        match bool_test(e) {
            Some(t) => vec![("True", Some(t.yes)), ("False", Some(t.no))],
            None => match &e.kind {
                ExprKind::Match { motive: None, arms, .. } => arms
                    .iter()
                    .filter(|a| !a.default)
                    .map(|a| (a.ctor.rsplit("::").next().unwrap_or(&a.ctor), Some(&a.body)))
                    .collect(),
                // A pipeline step: the continuation's body (the `λ`'s, or
                // the guarded value) at the arm that continues.
                _ => match pipeline_call(e) {
                    Some((_, method, rest)) => {
                        let body = match rest.first().map(|f| &f.kind) {
                            Some(ExprKind::Lam { body, .. }) => &**body,
                            Some(_) => &rest[0],
                            None => return Vec::new(),
                        };
                        pipeline_arm_names(method).iter().map(|a| (*a, matches!(*a, "Some" | "Ok" | "True").then_some(body))).collect()
                    }
                    None => Vec::new(),
                },
            },
        }
    }
    fn leaves(e: Option<&Expr>) -> usize {
        let arms = e.map(|e| arms(head(e))).unwrap_or_default();
        if arms.is_empty() { 1 } else { arms.iter().map(|(_, body)| leaves(*body)).sum() }
    }
    fn walk(e: &Expr, path: &mut Vec<String>, out: &mut Vec<Vec<String>>) {
        let e = head(e);
        if !path.is_empty() {
            out.push(path.clone());
        }
        // The arm with the most leaves first, the last of equals first: a
        // reader tries the equations in this order, so a test is asked
        // first as the arm most of them take, and its other arm is then
        // asked only where that failed. A body's main line (the recursion
        // under `if 0 < n`, the long tail of an `else if` chain) is then
        // asked first, and only a call that leaves it pays a failed side
        // condition.
        let mut arms: Vec<(usize, &str, Option<&Expr>)> = arms(e).into_iter().map(|(arm, body)| (leaves(body), arm, body)).collect();
        arms.reverse();
        arms.sort_by(|a, b| b.0.cmp(&a.0));
        for (_, arm, body) in arms {
            path.push(arm.to_string());
            match body {
                Some(body) => walk(body, path, out),
                None => out.push(path.clone()),
            }
            path.pop();
        }
    }
    let mut out = Vec::new();
    walk(body, &mut Vec::new(), &mut out);
    out
}

/// The equations of `decl`'s branches, at `reading`. `Err` says why there
/// are none. `recursion` says how `f` reaches its body: a definition by
/// unfolding, a `decreases` recursion through `f_unfold`, a structural one
/// by computing at the constructor its first test matches.
/// `results` reads a `match` on a call's result as a test (`result_arms`);
/// where that makes more than [`MAX_LEAVES`] leaves, the body is read
/// without it, as before, so no function loses the equations it had.
pub(crate) fn branch_equations(decl: &Decl, self_name: &str, reading: Reading, fields: FieldTypes<'_>, results: Option<ScrutTypes<'_>>, recursion: Recursion) -> Result<Vec<BranchEquation>, String> {
    if recursion == Recursion::None && recursive(decl, self_name) {
        return Err("the body calls the function again".into());
    }
    let span = decl.body.span;
    // A recursion's own calls are spelled by its full name, as `f_unfold`
    // spells them, so that an equation's leaf is the unfolding's.
    let qualified;
    let decl = if recursion != Recursion::None && decl.name != self_name {
        let mut d = decl.clone();
        let full = var(&decl.name, span);
        let body = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span };
        let ExprKind::Block(b) = subst(&body, &[(self_name, &full)], &mut Vec::new()).kind else { unreachable!("a block substitutes to a block") };
        d.body = *b;
        qualified = d;
        &qualified
    } else {
        decl
    };
    let mut taken = taken_names(decl);
    let result_name = ["result", "result2", "result3"].into_iter().find(|n| !taken.iter().any(|t| t == n)).unwrap_or("result_").to_string();
    taken.push(result_name.clone());
    let explicit = decl.params.iter().any(|p| p.implicit);
    let call = |head: Expr, args: Vec<Expr>| Expr {
        kind: ExprKind::App { head: Box::new(head), args, named: Vec::new(), explicit, goal_oriented: false },
        span,
    };
    let args: Vec<Expr> = decl.params.iter().map(|p| var(&p.name, span)).collect();
    let lhs = call(companion_ref(decl, &decl.name, span), args.clone());
    // A measured body's `on`s discharge its obligations, which are no part
    // of its equations (`candidate`).
    let ons = if decl.decreases.is_some() { Vec::new() } else { decl.body.ons.clone() };
    let top = Expr { kind: ExprKind::Block(Box::new(Block { ons, ..decl.body.clone() })), span };
    let mut w = Walk { decl, reading, fields, results, read_results: false, result_name: result_name.clone(), taken: taken.clone(), recursion, lhs: lhs.clone(), leaves: Vec::new(), too_many: false };
    w.walk(&top, Vec::new(), Vec::new());
    if w.too_many && w.read_results {
        w = Walk { decl, reading, fields, results: None, read_results: false, result_name, taken, recursion, lhs: lhs.clone(), leaves: Vec::new(), too_many: false };
        w.walk(&top, Vec::new(), Vec::new());
    }
    if w.too_many {
        return Err(format!("the body has more than {MAX_LEAVES} branches"));
    }
    if w.leaves.is_empty() {
        return Err("the body is not a test whose condition can be stated before it".into());
    }
    if recursion == Recursion::Structural && w.leaves.iter().any(|(path, _, _)| !matches!(path[0].test, PathTest::Ctor { .. })) {
        return Err("the body's first test is not a `match` on a parameter, at whose constructors the recursion computes".into());
    }
    // `f_unfold(x̄)` takes `f(x̄)` to the body, where the tests are chosen.
    let unfold = (recursion == Recursion::Measure).then(|| call(companion_ref(decl, &crate::measure::unfold_name(&decl.name), span), args));
    let mut out = Vec::new();
    for (path, lets, leaf) in std::mem::take(&mut w.leaves) {
        let names: Vec<&str> = path.iter().map(|s| s.arm.as_str()).collect();
        // The leaf is stated under every statement on the way to it, at the
        // declaration's result type.
        let rhs = with_lets(&lets, w.at_result(leaf.clone()));
        let mut proof: Option<Expr> = None;
        for s in path.iter().rev() {
            let step = with_lets(&s.lets, s.chosen.clone());
            proof = Some(match proof {
                None => step,
                Some(rest) => app(var("trans", span), vec![step, rest], span),
            });
        }
        let proof = proof.expect("a leaf is under at least one test");
        let proof = match &unfold {
            Some(unfold) => app(var("trans", span), vec![unfold.clone(), proof], span),
            None => proof,
        };
        let steps: Vec<PathStep> = path.iter().map(|s| PathStep { arm: s.arm.clone(), params: s.params.clone(), test: s.test.clone() }).collect();
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
                depth: None,
                unfolding: Vec::new(),
                body: block(proof, span),
                span: decl.span,
            },
            path: steps,
            lets,
            leaf,
        });
    }
    Ok(out)
}
