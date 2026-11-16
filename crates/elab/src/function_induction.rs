//! Induction that follows a function's own recursion: `f::induct`
//! (docs/tactics/functional-induction-design.md).
//!
//! A recursive `fn` whose branch equations exist (`branch_equations`, with
//! `Recursion::Measure` or `Recursion::Structural`) gets one more theorem,
//! minted `f#induct` and designated `f::induct`:
//!
//! ```text
//! theorem f::induct(fixed, motive: (varying) → Type,
//!     case_True:  (varying) → (h: P) → (eq: f(x̄) = leaf) → (ih: motive(args)) → motive(x̄),
//!     case_False: …,
//!     varying): motive(varying)
//! ```
//!
//! one case per leaf of the tests the body is, in the order of the branch
//! equations and named by the same path (`case_True`, `case_False_True`,
//! `case_Cons`). A case quantifies the parameters the recursion changes, the
//! fields and hypotheses on the way to its leaf, the leaf's own equation
//! (so a proof by cases needs nothing but the principle), and an induction
//! hypothesis at each recursive call the leaf makes. A parameter every call
//! passes unchanged is *fixed*: a parameter of the principle, not of the
//! motive. A parameter a test matches on is replaced in its case by the
//! constructor, as an induction on it would.
//!
//! It is proved by the same recursion as `f`, `decreases` or structural: the
//! proof is the tree of `f`'s own tests, each leaf the case applied to the
//! branch equation and to the principle at the recursive calls' arguments.
//! The checker sees it as any declaration, so nothing here is trusted; a
//! principle it refuses is skipped with the reason recorded.

use heather_syntax::ast::{Arm, Block, Decl, DeclKind, Expr, ExprKind, MatchForm, Param, ParamOrigin, Pat, Stmt, Ty, TyKind};
use heather_syntax::Span;

use crate::branch_equations::{BranchEquation, PathTest, Recursion};
use crate::measure::{app, arrow, block, companion_ref, subst, subst_surface_ty, var};

/// `f#induct`, spelled `f::induct`.
pub(crate) fn induct_name(name: &str) -> String {
    format!("{name}#induct")
}

/// A case parameter's name: `case_` and the path the leaf takes, `_`-joined.
pub(crate) const CASE_PREFIX: &str = "case_";

/// The name of the case at `path` (`case_False_True`).
pub(crate) fn case_name(path: &[&str]) -> String {
    format!("{CASE_PREFIX}{}", path.join("_"))
}

/// A recursive call in a leaf: its argument at each parameter, `None` where
/// the call leaves an implicit one to unification.
struct Call {
    args: Vec<Option<Expr>>,
}

/// The parameters a call's positional arguments fill: all of them under `@`,
/// the explicit ones otherwise.
fn call_args(decl: &Decl, e: &Expr, names: &[&str]) -> Option<Option<Call>> {
    let ExprKind::App { head, args, named, explicit, .. } = &e.kind else { return None };
    let callee = match &head.kind {
        ExprKind::TyApp { head, .. } => head,
        _ => head,
    };
    let ExprKind::Var(n) = &callee.kind else { return None };
    if !names.contains(&n.as_str()) {
        return None;
    }
    if !named.is_empty() {
        return Some(None);
    }
    let positions: Vec<usize> = (0..decl.params.len()).filter(|&i| *explicit || !decl.params[i].implicit).collect();
    if positions.len() != args.len() {
        return Some(None);
    }
    let mut out = vec![None; decl.params.len()];
    for (i, a) in positions.into_iter().zip(args) {
        out[i] = Some(a.clone());
    }
    Some(Some(Call { args: out }))
}

/// Every call of the function in `e`.
fn calls_in(decl: &Decl, e: &Expr, names: &[&str]) -> Result<Vec<(Span, Call)>, String> {
    let mut out = Vec::new();
    let mut bad = false;
    crate::surface::walk_expr(e, &mut |x: &Expr| match call_args(decl, x, names) {
        Some(Some(c)) => out.push((x.span, c)),
        Some(None) => bad = true,
        None => {}
    });
    if bad {
        return Err("a recursive call names an argument or leaves an explicit one out".into());
    }
    Ok(out)
}

/// The names bound anywhere inside `e`, and the spans under which a call is
/// conditional (a `match` arm, a `λ`): a call there is no induction
/// hypothesis of the leaf.
fn inner_scopes(e: &Expr) -> (Vec<String>, Vec<Span>) {
    let mut bound = Vec::new();
    let mut under = Vec::new();
    crate::surface::walk_expr(e, &mut |x: &Expr| match &x.kind {
        ExprKind::Lam { binders, body } => {
            bound.extend(binders.iter().map(|b| b.name.clone()));
            under.push(body.span);
        }
        ExprKind::Match { eqbind, arms, .. } => {
            bound.extend(eqbind.iter().cloned());
            for a in arms {
                for p in &a.binders {
                    crate::measure::pat_names(p, &mut bound);
                }
                under.push(a.body.span);
            }
        }
        ExprKind::Block(b) => {
            for st in &b.stmts {
                match st {
                    Stmt::Let { name, .. } | Stmt::LetCode { name, .. } => bound.push(name.clone()),
                    Stmt::LetRecord { fields, .. } => {
                        for f in fields {
                            crate::measure::pat_names(&f.pat, &mut bound);
                        }
                    }
                }
            }
        }
        _ => {}
    });
    (bound, under)
}

/// The `let`s with each claimed `mut self` call (`let p = \0mutated(x.m(a))`,
/// the statement `x.m(a);`) spelled as what it binds: `x` rebound to the
/// receiver after the call and `p` to its value
/// ([`heather_syntax::MUTATED_AFTER`], [`heather_syntax::MUTATED_VALUE`]), so
/// that an argument read after it is stated as the statement elaborates it.
fn threaded_lets(lets: &[Stmt]) -> Vec<Stmt> {
    let mut out = Vec::new();
    for st in lets {
        if let Stmt::Let { name, expr, span, .. } = st
            && let ExprKind::App { head, args, .. } = &expr.kind
            && matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::MUTATED)
            && let [inner] = args.as_slice()
            && let ExprKind::Dot { recv, .. } = &inner.kind
            && let ExprKind::Var(x) = &recv.kind
        {
            let marked = |m: &str| app(var(m, *span), vec![inner.clone()], *span);
            out.push(Stmt::Let { name: name.clone(), ty: None, expr: marked(heather_syntax::MUTATED_VALUE), span: *span, opaque: false });
            out.push(Stmt::Let { name: x.clone(), ty: None, expr: marked(heather_syntax::MUTATED_AFTER), span: *span, opaque: false });
            continue;
        }
        out.push(st.clone());
    }
    out
}

fn within(inner: Span, outer: Span) -> bool {
    outer.start <= inner.start && inner.end <= outer.end && outer != inner
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

fn of_expr(e: Expr) -> Ty {
    let span = e.span;
    Ty { kind: TyKind::OfExpr(Box::new(e)), span }
}

fn subst_ty_all(ty: &Ty, sigma: &[(String, Expr)]) -> Ty {
    let mut ty = ty.clone();
    for (x, v) in sigma {
        ty = subst_surface_ty(&ty, x, v);
    }
    ty
}

fn subst_all(e: &Expr, sigma: &[(String, Expr)]) -> Expr {
    let map: Vec<(&str, &Expr)> = sigma.iter().map(|(x, v)| (x.as_str(), v)).collect();
    subst(e, &map, &mut Vec::new())
}

/// One case of the principle, as the proof and the statement both read it.
struct Case {
    name: String,
    /// The case's binders in order, with their types.
    binders: Vec<(String, Ty)>,
    /// Each binder's value at the leaf of the proof, in the same order.
    values: Vec<Expr>,
    /// The motive's arguments the case concludes at.
    at: Vec<Expr>,
}

/// The parameters of `f::induct` and its proof. `decl` is the declaration
/// the branch equations were generated from (`self_name` its base name,
/// how its body calls it), `eqs` those equations.
pub(crate) fn induct(decl: &Decl, self_name: &str, eqs: &[BranchEquation], recursion: Recursion) -> Result<Decl, String> {
    if decl.kind != DeclKind::Fn || recursion == Recursion::None {
        return Err("only a recursive `fn` has an induction principle".into());
    }
    let span = decl.body.span;
    let names = [decl.name.as_str(), self_name];
    let body = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span };
    let all_calls = calls_in(decl, &body, &names)?;
    if all_calls.is_empty() {
        return Err("the body makes no recursive call".into());
    }
    // A parameter is fixed where every call passes it unchanged and no test
    // matches on it; one a call leaves to unification is taken as fixed, and
    // a principle wrong about that is refused by the checker.
    let matched: Vec<&str> = eqs.iter()
        .flat_map(|e| e.path.iter())
        .filter_map(|s| match &s.test { PathTest::Ctor { param, .. } => Some(param.as_str()), _ => None })
        .collect();
    let fixed: Vec<bool> = decl.params.iter().enumerate().map(|(i, p)| {
        !matched.contains(&p.name.as_str())
            && all_calls.iter().all(|(_, c)| match &c.args[i] {
                Some(a) => matches!(&a.kind, ExprKind::Var(n) if n == &p.name),
                None => true,
            })
    }).collect();
    let varying: Vec<usize> = (0..decl.params.len()).filter(|&i| !fixed[i]).collect();
    if varying.is_empty() {
        return Err("every recursive call passes every parameter unchanged".into());
    }

    let mut taken: Vec<String> = decl.params.iter().map(|p| p.name.clone()).collect();
    crate::surface::walk_expr(&body, &mut |x: &Expr| if let ExprKind::Var(n) = &x.kind { taken.push(n.clone()) });
    for e in eqs {
        taken.extend(e.decl.params.iter().map(|p| p.name.clone()));
    }
    let fresh = |want: &str, taken: &mut Vec<String>| {
        let mut n = want.to_string();
        let mut k = 1;
        while taken.contains(&n) {
            k += 1;
            n = format!("{want}{k}");
        }
        taken.push(n.clone());
        n
    };
    let motive = fresh("motive", &mut taken);
    let case_names: Vec<String> = eqs.iter().map(|e| {
        let path: Vec<&str> = e.path.iter().map(|s| s.arm.as_str()).collect();
        fresh(&case_name(&path), &mut taken)
    }).collect();

    let explicit = decl.params.iter().any(|p| p.implicit);
    let call = |head: Expr, args: Vec<Expr>| Expr {
        kind: ExprKind::App { head: Box::new(head), args, named: Vec::new(), explicit, goal_oriented: false },
        span,
    };
    let induct_self = induct_name(self_name);
    // The principle at the varying arguments `at`, every other parameter
    // passed as itself: an induction hypothesis's proof.
    let recurse = |at: Vec<Expr>| -> Expr {
        let mut args: Vec<Expr> = (0..decl.params.len()).filter(|&i| fixed[i]).map(|i| var(&decl.params[i].name, span)).collect();
        args.push(var(&motive, span));
        args.extend(case_names.iter().map(|c| var(c, span)));
        args.extend(at);
        app(companion_ref(decl, &induct_self, span), args, span)
    };
    let motive_at = |at: Vec<Expr>| of_expr(app(var(&motive, span), at, span));

    let mut cases: Vec<Case> = Vec::new();
    for (k, eq) in eqs.iter().enumerate() {
        // Each parameter a test matches is its constructor from that test on.
        let mut sigma: Vec<(String, Expr)> = Vec::new();
        let mut binders: Vec<(String, Ty)> = Vec::new();
        let mut values: Vec<Expr> = Vec::new();
        for &i in &varying {
            let p = &decl.params[i];
            if !matched.contains(&p.name.as_str()) || !eq.path.iter().any(|s| matches!(&s.test, PathTest::Ctor { param, .. } if param == &p.name)) {
                binders.push((p.name.clone(), p.ty.clone()));
                values.push(var(&p.name, span));
            }
        }
        // The equation's own hypotheses: a constructor's `x = C(ȳ)` is
        // `refl` once `x` is `C(ȳ)`.
        let mut eq_extra: Vec<Expr> = Vec::new();
        // Every name the equation's statement reads or binds.
        let mut eq_names: Vec<String> = Vec::new();
        if let TyKind::Eq(a, b) = &eq.decl.result.kind {
            for side in [a, b] {
                crate::surface::walk_expr(side, &mut |x: &Expr| if let ExprKind::Var(v) = &x.kind { eq_names.push(v.clone()) });
                eq_names.extend(inner_scopes(side).0);
            }
        }
        for (at, step) in eq.path.iter().enumerate() {
            match &step.test {
                PathTest::Ctor { param: x, ctor } => {
                    let (fields, h) = step.params.split_at(step.params.len() - 1);
                    for (n, t) in fields {
                        binders.push((n.clone(), subst_ty_all(t, &sigma)));
                        values.push(var(n, span));
                        eq_extra.push(var(n, span));
                    }
                    let value = if fields.is_empty() {
                        var(ctor, span)
                    } else {
                        app(var(ctor, span), fields.iter().map(|(n, _)| var(n, span)).collect(), span)
                    };
                    let _ = h;
                    eq_extra.push(Expr { kind: ExprKind::Refl, span });
                    if binders.iter().any(|(_, t)| crate::inductive::ty_mentions(t, x)) {
                        return Err(format!("a test before the `match` on `{x}` reads `{x}`"));
                    }
                    sigma.push((x.clone(), value));
                }
                PathTest::Bool { written, .. } | PathTest::Result { written, .. } => {
                    for (n, t) in &step.params {
                        // The case states the hypothesis under the name the
                        // body wrote (`if less: …` gives `less`, where the
                        // equations number it `less2`), so an arm of
                        // `induct` reads as the body does; later binders
                        // and the equation see it renamed.
                        let is_hyp = n == &step.params.last().expect("a test has its hypothesis").0;
                        // A hypothesis the body left unnamed is `h`, `h2`, …
                        // in the order the case binds them, not numbered
                        // past every test of the body as the equations'
                        // are: the constructor tests' own vanish here.
                        let generated = n == "h" || n.strip_prefix('h').is_some_and(|k| !k.is_empty() && k.bytes().all(|b| b.is_ascii_digit()));
                        let free = |c: &str| {
                            !binders.iter().any(|(b, _)| b == c)
                                && !decl.params.iter().any(|p| p.name == c)
                                && !eq.path[at..].iter().flat_map(|st| {
                                    // The tests from this one on (the
                                    // earlier are bound above, renamed); a
                                    // constructor test's own hypothesis is
                                    // no binder of the case.
                                    let kept = if matches!(st.test, PathTest::Ctor { .. }) { st.params.len() - 1 } else { st.params.len() };
                                    st.params[..kept].iter()
                                }).any(|(pn, pt)| (pn == c && pn != n) || crate::inductive::ty_mentions(pt, c))
                                // Renaming into the equation could be
                                // captured by a binder of the leaf (an
                                // `if h:` arm's own `let h`), where the
                                // equation mentions the hypothesis at all.
                                && !(eq_names.iter().any(|v| v == n) && eq_names.iter().any(|v| v == c))
                        };
                        let name = match written {
                            Some(w) if is_hyp && !binders.iter().any(|(b, _)| b == w) && !decl.params.iter().any(|p| &p.name == w) => w.clone(),
                            None if is_hyp && generated => {
                                let mut k = 1;
                                let mut c = "h".to_string();
                                while c != *n && !free(&c) {
                                    k += 1;
                                    c = format!("h{k}");
                                }
                                c
                            }
                            _ => n.clone(),
                        };
                        binders.push((name.clone(), subst_ty_all(t, &sigma)));
                        if name != *n {
                            sigma.push((n.clone(), var(&name, span)));
                        }
                        values.push(var(n, span));
                        eq_extra.push(var(n, span));
                    }
                }
            }
        }
        // The leaf's equation, at the constructors.
        let eq_ty = subst_ty_all(&eq.decl.result, &sigma);
        let mut eq_args: Vec<Expr> = decl.params.iter().map(|p| subst_all(&var(&p.name, span), &sigma)).collect();
        eq_args.extend(eq_extra);
        let eq_proof = call(companion_ref(decl, &eq.decl.name, span), eq_args);
        let eq_name = fresh("eq", &mut binders.iter().map(|(n, _)| n.clone()).chain(taken.iter().cloned()).collect());
        binders.push((eq_name, eq_ty));
        values.push(eq_proof);
        // An induction hypothesis at each call the leaf makes outright: not
        // under a `λ` or a `match` arm, and over no name the leaf binds;
        // first at each call a `match` on the way tests the result of
        // (`first.emits(p)` of `match first.emits(p) { … }`), stated as
        // the test states it, outside the `let`s.
        let threaded = threaded_lets(&eq.lets);
        let mut sites: Vec<(Vec<Stmt>, Vec<String>, Vec<(Span, Call)>)> = Vec::new();
        for step in &eq.path {
            if let PathTest::Result { scrut, .. } = &step.test {
                let (bound, under) = inner_scopes(scrut);
                let calls = calls_in(decl, scrut, &names)?.into_iter().filter(|(at, _)| !under.iter().any(|&u| within(*at, u))).collect();
                sites.push((Vec::new(), bound, calls));
            }
        }
        let (bound, under) = inner_scopes(&eq.leaf);
        let calls = calls_in(decl, &eq.leaf, &names)?.into_iter().filter(|(at, _)| !under.iter().any(|&u| within(*at, u))).collect();
        sites.push((threaded, bound, calls));
        let mut seen: Vec<String> = Vec::new();
        let mut ih_count = 0;
        for (threaded, bound, c) in sites.iter().flat_map(|(t, b, cs)| cs.iter().map(move |(_, c)| (t, b, c))) {
            let mut args = Vec::new();
            let mut ok = true;
            for &i in &varying {
                let Some(a) = &c.args[i] else { ok = false; break };
                if bound.iter().any(|b| crate::inductive::expr_mentions(a, b)) {
                    ok = false;
                    break;
                }
                match crate::branch_equations::inline_expr(threaded, a) {
                    Some(a) => args.push(subst_all(&a, &sigma)),
                    None => { ok = false; break; }
                }
            }
            if !ok {
                continue;
            }
            let key = format!("{args:?}");
            if seen.contains(&key) {
                continue;
            }
            seen.push(key);
            ih_count += 1;
            let ih = if ih_count == 1 { "ih".to_string() } else { format!("ih{ih_count}") };
            let ih = fresh(&ih, &mut binders.iter().map(|(n, _)| n.clone()).chain(taken.iter().cloned()).collect());
            binders.push((ih, motive_at(args.clone())));
            values.push(recurse(args));
        }
        let at: Vec<Expr> = varying.iter().map(|&i| subst_all(&var(&decl.params[i].name, span), &sigma)).collect();
        cases.push(Case { name: case_names[k].clone(), binders, values, at });
    }

    // -- the statement --------------------------------------------------------
    let mut motive_ty = Ty { kind: TyKind::Univ { level: 0 }, span };
    for &i in varying.iter().rev() {
        let p = &decl.params[i];
        motive_ty = arrow(Some(p.name.clone()), p.ty.clone(), motive_ty, span);
    }
    let mut params: Vec<Param> = (0..decl.params.len()).filter(|&i| fixed[i]).map(|i| param(&decl.params[i].name, decl.params[i].ty.clone(), span)).collect();
    params.push(param(&motive, motive_ty, span));
    for c in &cases {
        let mut ty = motive_at(c.at.clone());
        for (n, t) in c.binders.iter().rev() {
            ty = arrow(Some(n.clone()), t.clone(), ty, span);
        }
        params.push(param(&c.name, ty, span));
    }
    for &i in &varying {
        params.push(param(&decl.params[i].name, decl.params[i].ty.clone(), span));
    }
    let result = motive_at(varying.iter().map(|&i| var(&decl.params[i].name, span)).collect());

    // -- the proof: `f`'s tests, each leaf its case ---------------------------
    let all: Vec<usize> = (0..eqs.len()).collect();
    let mut bits = 0usize;
    let proof = tree(eqs, &cases, &all, 0, &[], &mut bits, span)?;
    let mut body = block(proof, span);
    // A measured principle recurses where `f` does, in the same order, so
    // its calls owe `f`'s decrease obligations: the `on ?decN` clauses that
    // discharged them in `f` discharge them here, under the same names
    // (each test's hypothesis is bound under its own name in `tree`, and a
    // leaf's `let`s are inlined, as the obligation's statement is). One the
    // principle's context cannot check is a refusal of the principle, as
    // before.
    if recursion == Recursion::Measure {
        body.ons = decl.body.ons.iter()
            .filter(|o| matches!(&o.target, heather_syntax::ast::OnTarget::Name(n) if n.strip_prefix("dec").is_some_and(|k| !k.is_empty() && k.bytes().all(|b| b.is_ascii_digit()))))
            .cloned()
            .collect();
    }
    Ok(Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        is_evidence: false,
        is_interface: false,
        partial: None,
        value: false,
        elaborates: None,
        name: induct_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params,
        result,
        decreases: if recursion == Recursion::Measure { decl.decreases.clone() } else { None },
        unfolding: Vec::new(),
        body,
        span: decl.span,
    })
}

/// The proof at the tests `group` (equation indices) share down to `depth`:
/// the leaf's case where one equation is left at its end, else the test at
/// `depth` with one arm per arm the group's equations take, in order.
fn tree(eqs: &[BranchEquation], cases: &[Case], group: &[usize], depth: usize, sigma: &[(String, Expr)], bits: &mut usize, span: Span) -> Result<Expr, String> {
    if let [k] = group
        && eqs[*k].path.len() == depth
    {
        let c = &cases[*k];
        return Ok(app(var(&c.name, span), c.values.clone(), span));
    }
    if group.iter().any(|&k| eqs[k].path.len() <= depth) {
        return Err("two branches share a path".into());
    }
    let first = &eqs[group[0]].path[depth];
    let mut arms_order: Vec<String> = Vec::new();
    for &k in group {
        let a = &eqs[k].path[depth].arm;
        if !arms_order.contains(a) {
            arms_order.push(a.clone());
        }
    }
    let sub = |arm: &str| -> Vec<usize> { group.iter().copied().filter(|&k| eqs[k].path[depth].arm == arm).collect() };
    match &first.test {
        PathTest::Bool { scrut, prop, .. } => {
            *bits += 1;
            // A lexable name, as the parser's `if h:` gives its bit's
            // equation where a branch leaves `h` unnamed: the hypothesis
            // `h` is a `let` over it, and a lifted decrease obligation whose
            // `on` names `h` quantifies `h` and what it is defined from,
            // which a `#` name cannot be (`measure::Rewrite`'s scope).
            let e = format!("__induct_bit{bits}");
            let mut arms = Vec::new();
            for arm in ["True", "False"] {
                let ks = sub(arm);
                if ks.is_empty() {
                    return Err(format!("the `{arm}` arm of a test has no leaf"));
                }
                let step = &eqs[ks[0]].path[depth];
                let evidence = match prop {
                    Some(p) => {
                        let p = subst_ty_all(p, sigma);
                        let side = if arm == "True" { "decide_true" } else { "decide_false" };
                        let head = Expr { kind: ExprKind::TyApp { head: Box::new(var(side, p.span)), args: vec![p.clone()] }, span: p.span };
                        app(head, vec![var(&e, span)], span)
                    }
                    None => var(&e, span),
                };
                let inner = tree(eqs, cases, &ks, depth + 1, sigma, bits, span)?;
                // Typed as the case states it, so a lifted decrease
                // obligation whose `on` names `h` can quantify it: the
                // walk's binder types are read off `f`'s own elaboration,
                // which this `let` is not part of.
                let (h, h_ty) = step.params.first().ok_or("a test without its hypothesis")?;
                let h_ty = prop.as_ref().map(|_| subst_ty_all(h_ty, sigma));
                let mut stmts = vec![Stmt::Let { name: h.clone(), ty: h_ty.clone(), expr: evidence, span, opaque: false }];
                // Also under the body's own name, which `f`'s `on ?decN`
                // clauses (carried over to the principle) use.
                if let PathTest::Bool { written: Some(w), .. } = &step.test {
                    stmts.push(Stmt::Let { name: w.clone(), ty: h_ty, expr: var(h, span), span, opaque: false });
                }
                let body = Expr {
                    kind: ExprKind::Block(Box::new(Block {
                        stmts,
                        result: Box::new(inner),
                        ons: Vec::new(),
                        span,
                    })),
                    span,
                };
                arms.push(Arm { ctor: arm.into(), default: false, binders: Vec::new(), body, span });
            }
            let scrut = match prop {
                // The lowered `if h: P`: the condition's span on the call's
                // head marks it as a condition (`surface::lowered_condition`).
                Some(p) => {
                    let p = subst_ty_all(p, sigma);
                    let head = Expr { kind: ExprKind::TyApp { head: Box::new(var("decide_bit", p.span)), args: vec![p.clone()] }, span: p.span };
                    app(head, Vec::new(), p.span)
                }
                None => subst_all(scrut, sigma),
            };
            Ok(Expr {
                kind: ExprKind::Match { form: MatchForm::Match, generated: false, scrut: Box::new(scrut), eqbind: Some(e), motive: None, arms },
                span,
            })
        }
        PathTest::Result { scrut, .. } => {
            // `match e: g(ā) { C(ȳ) => { let h = e; … } }`: each arm binds
            // the fields under the case's names and the equation under the
            // name the case gives it (and the body's own, for `on` clauses).
            *bits += 1;
            let e = format!("__induct_bit{bits}");
            let mut arms = Vec::new();
            for arm in &arms_order {
                let ks = sub(arm);
                let step = &eqs[ks[0]].path[depth];
                let PathTest::Result { ctor, written, .. } = &step.test else { return Err("a test's arms disagree".into()) };
                let (h, fields) = step.params.split_last().ok_or("a test without its hypothesis")?;
                let inner = tree(eqs, cases, &ks, depth + 1, sigma, bits, span)?;
                let mut stmts = vec![Stmt::Let { name: h.0.clone(), ty: Some(subst_ty_all(&h.1, sigma)), expr: var(&e, span), span, opaque: false }];
                if let Some(w) = written {
                    stmts.push(Stmt::Let { name: w.clone(), ty: Some(subst_ty_all(&h.1, sigma)), expr: var(&h.0, span), span, opaque: false });
                }
                let body = Expr { kind: ExprKind::Block(Box::new(Block { stmts, result: Box::new(inner), ons: Vec::new(), span })), span };
                arms.push(Arm {
                    ctor: ctor.clone(),
                    default: false,
                    binders: fields.iter().map(|(n, _)| Pat::Var { name: n.clone(), span }).collect(),
                    body,
                    span,
                });
            }
            Ok(Expr {
                kind: ExprKind::Match { form: MatchForm::Match, generated: false, scrut: Box::new(subst_all(scrut, sigma)), eqbind: Some(e), motive: None, arms },
                span,
            })
        }
        PathTest::Ctor { param: x, .. } => {
            let mut arms = Vec::new();
            for arm in &arms_order {
                let ks = sub(arm);
                let step = &eqs[ks[0]].path[depth];
                let PathTest::Ctor { ctor, .. } = &step.test else { return Err("a test's arms disagree".into()) };
                let fields = &step.params[..step.params.len() - 1];
                let value = if fields.is_empty() {
                    var(ctor, span)
                } else {
                    app(var(ctor, span), fields.iter().map(|(n, _)| var(n, span)).collect(), span)
                };
                let mut sigma = sigma.to_vec();
                sigma.push((x.clone(), value));
                let inner = tree(eqs, cases, &ks, depth + 1, &sigma, bits, span)?;
                arms.push(Arm {
                    ctor: ctor.clone(),
                    default: false,
                    binders: fields.iter().map(|(n, _)| Pat::Var { name: n.clone(), span }).collect(),
                    body: inner,
                    span,
                });
            }
            Ok(Expr {
                kind: ExprKind::Match { form: MatchForm::Match, generated: false, scrut: Box::new(var(x, span)), eqbind: None, motive: None, arms },
                span,
            })
        }
    }
}

// -- the `induct` step ---------------------------------------------------------
//
// `induct f(ā); all_goals { body }` at a goal `G`, where the arguments the
// recursion changes are local variables: the call is abstracted out of `G`
// and the locals after the first of those variables (the hypotheses about
// them, and anything declared later) are reverted, so the goal is
// `goal(ā, f(ā))` for `goal = λ x̄ r. Π R̄. G[ā := x̄, f(ā) := r]`, an alias
// the elaborator builds. The motive is `λ x̄ => goal(x̄, f(x̄))`; in each case
// the leaf's equation turns `goal(x̄ₖ, f(x̄ₖ))` into `goal(x̄ₖ, leaf)` (by
// `j`, so no occurrence has to be found again), the reverted locals are
// introduced under their own names, and the block is checked there with
// each induction hypothesis specialised: its premises proved by the block
// where it proves them, its statement in the goal's own spelling.

use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{Term, Type};

use crate::context::{Alias, Cx};
use crate::{Elaborator, R, err};

/// The leaf of one case: the block, then the case's induction hypotheses by
/// name. `INDUCT_LEAF_ALL` proves their premises with the block; `INDUCT_LEAF`
/// (an arm of its own) only restates them.
pub(crate) const INDUCT_LEAF_ALL: &str = "\0induct-leaf-all";
pub(crate) const INDUCT_LEAF: &str = "\0induct-leaf";
/// The leaf of a case the arms leave out: the case's name (a string), then
/// the case's induction hypotheses. Their premises and the goal are proved
/// by `known` (a hypothesis, a side of a conjunction, then `omega` and
/// `bv_omega`), so arms are written only for the cases that need thought.
pub(crate) const INDUCT_LEAF_DEFAULT: &str = "\0induct-leaf-default";
const GOAL_ALIAS: &str = "#induct_goal";

/// One case binder of `f::induct`, read off its surface statement.
struct CaseShape {
    name: String,
    binders: Vec<String>,
    /// The binder that is the leaf's equation, and those that are
    /// induction hypotheses.
    eq: Option<usize>,
    ihs: Vec<usize>,
    at: Vec<Expr>,
}

fn case_shapes(principle: &Decl, motive: &str) -> Vec<CaseShape> {
    principle.params.iter().filter(|p| p.name.starts_with(CASE_PREFIX)).filter_map(|p| {
        let mut binders = Vec::new();
        let mut ihs = Vec::new();
        let mut doms = Vec::new();
        let mut ty = &p.ty;
        while let TyKind::Fn { binder, dom, cod, .. } = &ty.kind {
            binders.push(binder.clone().unwrap_or_else(|| "_".into()));
            doms.push(dom.as_ref());
            ty = cod;
        }
        let is_motive = |t: &Ty| matches!(&t.kind, TyKind::OfExpr(e)
            if matches!(&e.kind, ExprKind::App { head, .. } if matches!(&head.kind, ExprKind::Var(m) if m == motive)));
        for (i, d) in doms.iter().enumerate() {
            if is_motive(d) {
                ihs.push(i);
            }
        }
        let eq = match ihs.first() {
            Some(&0) => None,
            Some(&i) => Some(i - 1),
            None => binders.len().checked_sub(1),
        };
        let TyKind::OfExpr(e) = &ty.kind else { return None };
        let ExprKind::App { args, .. } = &e.kind else { return None };
        Some(CaseShape { name: p.name.clone(), binders, eq, ihs, at: args.clone() })
    }).collect()
}

fn marker(head: &str, args: Vec<Expr>, span: Span) -> Expr {
    app(var(head, span), args, span)
}

/// The β-redexes and codes of a hypothesis's type contracted: what the
/// principle states as `motive(args)` read as the goal it stands for.
fn normal(ty: &Type) -> Type {
    let ty = match ty {
        Type::El { level, tm } => Type::El { level: level.clone(), tm: Rc::new(crate::goal_combinators::beta_below(tm)) },
        other => other.clone(),
    };
    crate::inductive::decode_deep(&ty).unwrap_or(ty)
}

/// `(Term, Type, Level)` of local `name`, innermost binding, in `cx`.
fn local(cx: &Cx, name: &str) -> Option<(u32, Type, Level)> {
    let m = cx.gamma.entries.len();
    let p = (0..cx.names.len()).rev().find(|&p| cx.names[p] == *name)?;
    let entry = cx.gamma.entries.get(p)?;
    Some(((m - 1 - p) as u32, entry.ty.shift_local((m - p) as u32), entry.level.clone()))
}

/// The `induct` step's view of the elaborator (crates/elab/CLAUDE.md).
pub(crate) struct FunctionInduction<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for FunctionInduction<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl FunctionInduction<'_> {
    /// `induct f(ā); …` (`body` is `Ok(block)`) or `induct f(ā) { … }`
    /// (`Err(arms)`): the expression to check at `expected`, in the context
    /// it is to be checked in.
    pub(crate) fn induct_step(&self, cx: &Cx, call: &Expr, body: Result<&Expr, &[Arm]>, expected: &Type, lvl: &Level, span: Span) -> R<(Expr, Cx)> {
        let Some((head, args, explicit)) = call.as_named() else {
            return err("`induct` takes a call of a recursive function: `induct f(x, y)`", call.span);
        };
        let head = head.to_string();
        let designed = format!("{head}::induct");
        let lookup = crate::name_lookup::NameLookup(self);
        let principle = lookup
            .key_of_kinds(&designed, crate::names::ANY_KIND)
            .and_then(|key| crate::names::split_qual(&key).map(|(m, b)| (m.to_string(), b.to_string())))
            .and_then(|(m, b)| self.names.surface_decl_in(&m, &b).cloned());
        let Some(principle) = principle else {
            let why = self.pass.unfold_refusals.borrow().get(&designed).cloned()
                .unwrap_or_else(|| format!("`{head}` is not a recursive function with one"));
            return err(format!("`induct {head}(…)` needs the induction principle `{designed}`: {why}"), call.span);
        };
        let function = lookup
            .key_of_kinds(&head, crate::names::ANY_KIND)
            .and_then(|key| crate::names::split_qual(&key).map(|(m, b)| (m.to_string(), b.to_string())))
            .and_then(|(m, b)| self.names.surface_decl_in(&m, &b).cloned());
        let Some(function) = function else {
            return err(format!("`induct`: `{head}` is not a declared function"), call.span);
        };
        let positions: Vec<usize> = (0..function.params.len()).filter(|&i| explicit || !function.params[i].implicit).collect();
        if positions.len() != args.len() {
            return err(format!(
                "`induct {head}(…)` takes {} argument(s){}",
                positions.len(),
                if function.params.iter().any(|p| p.implicit) { "; write `@` to pass the implicit ones" } else { "" }
            ), call.span);
        }
        if positions.len() != function.params.len() {
            return err(format!("`induct {head}(…)`: pass every argument, the implicit ones too, as `@{head}(…)`"), call.span);
        }
        // The principle's parameters: the fixed ones, the motive, the cases,
        // the varying ones; the varying ones are those named after the
        // function's parameters past the cases.
        let motive_at = principle.params.iter().position(|p| matches!(&p.ty.kind, TyKind::Fn { .. }) && !p.name.starts_with(CASE_PREFIX)
            && { let mut t = &p.ty; while let TyKind::Fn { cod, .. } = &t.kind { t = cod; } matches!(t.kind, TyKind::Univ { .. }) });
        let Some(motive_at) = motive_at else {
            return err(format!("`{designed}` is not an induction principle"), call.span);
        };
        let motive_name = principle.params[motive_at].name.clone();
        let fixed: Vec<String> = principle.params[..motive_at].iter().map(|p| p.name.clone()).collect();
        let cases = case_shapes(&principle, &motive_name);
        let varying: Vec<String> = principle.params[motive_at + 1 + cases.len()..].iter().map(|p| p.name.clone()).collect();
        let at = |name: &str| function.params.iter().position(|p| p.name == name);

        // The varying arguments are distinct local variables.
        let mut var_positions: Vec<usize> = Vec::new();
        let mut var_names: Vec<String> = Vec::new();
        let m = cx.gamma.entries.len();
        for v in &varying {
            let Some(i) = at(v) else { return err(format!("`{designed}` does not match `{head}`"), call.span) };
            let a = &args[i];
            let ExprKind::Var(name) = &a.kind else {
                return err(format!("`induct` needs a local variable at `{v}`, which the recursion changes: state the claim for a variable there and instantiate it"), a.span);
            };
            let (t, _, _) = self.elab_infer(cx, a)?;
            let Term::Var(ix) = t else {
                return err(format!("`induct` needs a local variable at `{v}`, which the recursion changes; `{name}` is not one"), a.span);
            };
            let p = m - 1 - ix.0 as usize;
            if var_positions.contains(&p) {
                return err(format!("`induct` needs distinct variables at the arguments the recursion changes; `{name}` is passed twice"), a.span);
            }
            var_positions.push(p);
            var_names.push(name.clone());
        }
        // Reverted: every local after the first varying one, so a
        // hypothesis about the arguments and whatever it mentions (the list
        // a counter indexes) are generalized with them, except what a fixed
        // argument names and what that local's own type needs: those stay,
        // since the principle passes them unchanged.
        let first = *var_positions.iter().min().expect("a principle has a varying parameter");
        let mut kept: Vec<usize> = Vec::new();
        for f in &fixed {
            let Some(i) = at(f) else { return err(format!("`{designed}` does not match `{head}`"), call.span) };
            for q in first + 1..m {
                let name = &cx.names[q];
                let visible = !(q + 1..m).any(|r| cx.names[r] == *name);
                if visible && !var_positions.contains(&q) && crate::inductive::expr_mentions(&args[i], name) && !kept.contains(&q) {
                    kept.push(q);
                }
            }
        }
        let mut k = 0;
        while k < kept.len() {
            let q = kept[k];
            for p in first + 1..q {
                if !var_positions.contains(&p) && !kept.contains(&p) && crate::generalize::mentions_binder(cx, q, p) {
                    kept.push(p);
                }
            }
            k += 1;
        }
        let reverted: Vec<usize> = (first + 1..m).filter(|q| !var_positions.contains(q) && !kept.contains(q)).collect();
        let reverted_names: Vec<String> = reverted.iter().map(|&p| cx.names[p].to_string()).collect();
        for f in &fixed {
            let Some(i) = at(f) else { return err(format!("`{designed}` does not match `{head}`"), call.span) };
            let through = kept.iter().find(|&&q| var_positions.iter().any(|&p| p < q && crate::generalize::mentions_binder(cx, q, p)));
            if let Some(&q) = through {
                return err(format!("`induct`: the argument at `{f}`, which the recursion passes unchanged, needs `{}`, whose type mentions an argument the induction generalizes", &cx.names[q]), args[i].span);
            }
            if let Some(n) = var_names.iter().find(|n| crate::inductive::expr_mentions(&args[i], n)) {
                return err(format!("`induct`: the argument at `{f}`, which the recursion passes unchanged, mentions `{n}`, which the induction generalizes"), args[i].span);
            }
        }

        // goal = λ x̄ r. Π R̄. G[f(ā) := r]
        let (call_term, call_ty, call_level) = self.elab_infer(cx, call)?;
        let (closed, closed_level) = crate::generalize::Generalize(self).generalize_expected(cx, &reverted, expected, lvl);
        let abstracted = closed.abstract_local(&call_term).unwrap_or_else(|| closed.shift_local(1));
        let with_r = Type::Pi { dom_level: call_level.clone(), cod_level: closed_level.clone(), dom: Rc::new(call_ty), cod: Rc::new(abstracted) };
        let with_r_level = Level::max(call_level, closed_level.clone());
        let (whole, _) = crate::generalize::Generalize(self).generalize_expected(cx, &var_positions, &with_r, &with_r_level);
        // Peel the m + 1 Π into λ, and code what is left.
        let mut binders: Vec<(Level, Rc<Type>)> = Vec::new();
        let mut ty = whole;
        for _ in 0..=var_positions.len() {
            let Type::Pi { dom_level, dom, cod, .. } = ty else { unreachable!("built with one Π per binder") };
            binders.push((dom_level, dom));
            ty = (*cod).clone();
        }
        let Some(code) = crate::code::code_of(&ty) else {
            return err("`induct`: the goal has no code in the universe a motive ranges over", span);
        };
        let mut term = code;
        let mut alias_ty = Type::Ty(closed_level.clone());
        let mut level = Level::succ(closed_level);
        for (dom_level, dom) in binders.into_iter().rev() {
            term = Term::Lam { dom_level: dom_level.clone(), cod_level: level.clone(), dom: Rc::clone(&dom), body: Rc::new(term) };
            alias_ty = Type::Pi { dom_level: dom_level.clone(), cod_level: level.clone(), dom, cod: Rc::new(alias_ty) };
            level = Level::max(dom_level, level);
        }
        let mut inner = cx.clone();
        inner.aliases.push(Rc::new(Alias {
            name: GOAL_ALIAS.into(),
            depth: cx.names.len(),
            term: Rc::new(term),
            ty: alias_ty,
            level,
            skel: None,
            spliced: None,
            shifted: Default::default(),
        }));

        // The motive: λ x̄ => goal(x̄, f(… x̄ …)).
        let fresh: Vec<String> = (0..varying.len()).map(|i| format!("#induct_x{i}")).collect();
        let mut at_call = call.clone();
        if let ExprKind::App { args: call_args, .. } = &mut at_call.kind {
            for (k, v) in varying.iter().enumerate() {
                let i = at(v).expect("checked above");
                call_args[i] = var(&fresh[k], span);
            }
        }
        let mut goal_args: Vec<Expr> = fresh.iter().map(|x| var(x, span)).collect();
        goal_args.push(at_call);
        let motive = crate::measure::lam(&fresh.iter().map(String::as_str).collect::<Vec<_>>(), app(var(GOAL_ALIAS, span), goal_args, span), span);

        // The cases.
        let arms: Option<&[Arm]> = body.err();
        if let Some(arms) = arms {
            for a in arms {
                let want = format!("{CASE_PREFIX}{}", a.ctor.replace("::", "_"));
                if a.default || !a.binders.is_empty() || !cases.iter().any(|c| c.name == want) {
                    let names: Vec<String> = cases.iter().map(|c| c.name[CASE_PREFIX.len()..].replace('_', "::")).collect();
                    return err(format!("`induct {head}(…)` has the cases {}; an arm is one of them with no binders", names.join(", ")), a.span);
                }
            }
        }
        let renamed = |n: &str| -> String {
            match varying.iter().position(|v| v == n) {
                Some(k) => var_names[k].clone(),
                None => n.to_string(),
            }
        };
        let mut case_exprs = Vec::new();
        for c in &cases {
            // Binders named after a varying parameter take the caller's
            // name for it; any other that would hide a reverted local or a
            // caller's variable is renamed.
            let users: Vec<&String> = var_names.iter().chain(&reverted_names).collect();
            let mut names: Vec<String> = Vec::new();
            for b in &c.binders {
                let mut n = renamed(b);
                if !varying.contains(b) {
                    let base = n.clone();
                    let mut k = 1;
                    while users.contains(&&n) || names.contains(&n) {
                        k += 1;
                        n = format!("{base}{k}");
                    }
                }
                names.push(n);
            }
            let map: Vec<(String, Expr)> = c.binders.iter().zip(&names).map(|(b, n)| (b.clone(), var(n, span))).collect();
            let at_k: Vec<Expr> = c.at.iter().map(|e| subst_all(e, &map)).collect();
            // An arm's block, the block for all goals, or, for a case the
            // arms leave out, `known` on its premises and goal.
            let (leaf_head, leaf_body) = match body {
                Ok(b) => (INDUCT_LEAF_ALL, b.clone()),
                Err(arms) => {
                    let want = &c.name[CASE_PREFIX.len()..];
                    match arms.iter().find(|a| a.ctor.replace("::", "_") == want) {
                        Some(a) => (INDUCT_LEAF, a.body.clone()),
                        None => (INDUCT_LEAF_DEFAULT, Expr { kind: ExprKind::Str(want.replace('_', "::")), span }),
                    }
                }
            };
            let mut leaf_args = vec![leaf_body];
            leaf_args.extend(c.ihs.iter().map(|&i| var(&names[i], span)));
            let leaf = marker(leaf_head, leaf_args, span);
            let leaf = if reverted_names.is_empty() {
                leaf
            } else {
                crate::measure::lam(&reverted_names.iter().map(String::as_str).collect::<Vec<_>>(), leaf, span)
            };
            // goal(x̄ₖ, f(x̄ₖ)) from goal(x̄ₖ, leaf), along the equation.
            let proof = match c.eq {
                Some(e) => {
                    let mut hole_args = at_k.clone();
                    hole_args.push(var("#induct_v", span));
                    let jm = crate::measure::lam(&["#induct_v", "_"], app(var(GOAL_ALIAS, span), hole_args, span), span);
                    let back = app(var("sym", span), vec![var(&names[e], span)], span);
                    Expr { kind: ExprKind::J { proof: Box::new(back), motive: Box::new(jm), case: Box::new(leaf) }, span }
                }
                None => leaf,
            };
            case_exprs.push(crate::measure::lam(&names.iter().map(String::as_str).collect::<Vec<_>>(), proof, span));
        }

        let mut principle_args: Vec<Expr> = fixed.iter().map(|f| args[at(f).expect("checked above")].clone()).collect();
        principle_args.push(motive);
        principle_args.extend(case_exprs);
        principle_args.extend(var_names.iter().map(|n| var(n, span)));
        let mut out = app(var(&designed, span), principle_args, span);
        if !reverted_names.is_empty() {
            out = app(out, reverted_names.iter().map(|n| var(n, span)).collect(), span);
        }
        Ok((out, inner))
    }

    /// A case's leaf: each induction hypothesis restated in the goal's
    /// spelling, after its premises where `discharge` proves them with the
    /// block, then the block at the goal.
    pub(crate) fn induct_leaf(&self, cx: &Cx, args: &[Expr], discharge: bool, expected: &Type, lvl: &Level, span: Span) -> R<Term> {
        let [body, ihs @ ..] = args else {
            return err("internal `induct` leaf has the wrong arity", span);
        };
        // A case the arms leave out (`INDUCT_LEAF_DEFAULT`): `known`, and a
        // refusal names the case.
        let (case, known);
        let body = match &body.kind {
            ExprKind::Str(name) => {
                case = Some(name.clone());
                known = Expr { kind: ExprKind::Var(crate::tested::KNOWN.to_string()), span };
                &known
            }
            _ => {
                case = None;
                body
            }
        };
        let out = self.induct_leaf_with(cx, body, ihs, discharge, expected, lvl, span);
        match (case, out) {
            (Some(case), Err(crate::ElabError::Elab { msg, span })) => err(
                format!("`induct`: no arm for the case `{case}`, and its default did not close it: {msg}; write an arm `{case} => …`"),
                span,
            ),
            (_, out) => out,
        }
    }

    fn induct_leaf_with(&self, cx: &Cx, body: &Expr, ihs: &[Expr], discharge: bool, expected: &Type, lvl: &Level, span: Span) -> R<Term> {
        let mut cur = cx.clone();
        // (dom, level, value) of each restated hypothesis, outermost first.
        let mut bound: Vec<(Type, Level, Term)> = Vec::new();
        for ih in ihs {
            let ExprKind::Var(name) = &ih.kind else { continue };
            let Some((ix, ty, level)) = local(&cur, name) else { continue };
            let mut term = Term::Var(heather_kernel::term::LocalVar(ix));
            let mut ty = normal(&ty);
            let mut level = level;
            while discharge {
                let Type::Pi { dom_level, cod_level, dom, cod } = &ty else { break };
                let premise = normal(dom);
                let mark = crate::resolve::SearchMark::of(self);
                match self.elab_check(&cur, body, &premise, dom_level) {
                    Ok(p) => {
                        let p = Rc::new(p);
                        let next = normal(&cod.inst_top(0, &p));
                        term = crate::spelling::checked_app(Rc::new(term), dom_level.clone(), cod_level.clone(), Rc::clone(dom), Rc::clone(cod), p);
                        level = cod_level.clone();
                        ty = next;
                    }
                    Err(_) => {
                        mark.rollback(self);
                        break;
                    }
                }
            }
            cur.push(name.clone(), ty.clone(), level.clone());
            bound.push((ty, level, term));
        }
        let n = bound.len() as u32;
        let goal = normal(&expected.shift_local(n));
        let mut out = self.elab_check(&cur, body, &goal, lvl)?;
        // λ ih. out, applied to its value, innermost first.
        let mut cod = expected.shift_local(n);
        for (k, (dom, level, value)) in bound.into_iter().enumerate().rev() {
            let lam = Term::Lam { dom_level: level.clone(), cod_level: lvl.clone(), dom: Rc::new(dom.clone()), body: Rc::new(out) };
            let outer_cod = expected.shift_local(k as u32);
            out = Term::App { fun: Rc::new(lam), dom_level: level, cod_level: lvl.clone(), dom: Rc::new(dom), cod: Rc::new(cod), arg: Rc::new(value) };
            cod = outer_cod;
        }
        Ok(out)
    }
}
