//! State carried while elaborating structurally recursive matches.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalVar, Term, Type};
use heather_syntax::{Expr, ExprKind, Span, Stmt, Ty, TyKind};

use crate::application::{self, ExplicitArgElab, ParamMeta};
use crate::{Cx, R, err, matching};

/// Semantic capabilities needed by guarded self-call lowering.
///
/// This module owns termination-guard interpretation and selection of the
/// induction hypothesis. The root elaborator retains recursive expression
/// inference and callable metadata, while explicit spill application reuses
/// the ordinary application engine.
pub(crate) trait SelfCallElab: ExplicitArgElab {
    fn infer_self_call_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)>;
    fn self_call_application_params(&self, name: &str) -> Rc<Vec<ParamMeta>>;
    /// The declaration `name`'s [`RecursionPlan::Misplaced`], if it has one.
    fn misplaced_recursion(&self, name: &str) -> Option<(usize, String)>;
}

/// Is `scrut` (already elaborated) exactly one of the enclosing declaration's
/// parameters? Returns its parameter index — the argument position the
/// recursion descends on.
pub(crate) fn descends_on_param(cx: &Cx, scrut: &Term) -> Option<usize> {
    let s = cx.selfref.as_ref()?;
    let Term::Var(LocalVar(i)) = scrut else {
        return None;
    };
    let pos = cx.names.len() - 1 - *i as usize;
    (pos < s.params.len()).then_some(pos)
}

/// Does a self-call in `arms` pass, at parameter `dec`'s position, anything
/// but that parameter itself? That is what makes a `match` on `dec` the
/// recursion rather than a branch on a parameter passed along unchanged
/// (`match b { … f(k, b) … }` inside the recursion on `n`). Syntactic, so it
/// answers the same on every speculative re-elaboration of the arms.
pub(crate) fn recurses_on(self_ref: &SelfRef, arms: &[heather_syntax::Arm], dec: usize) -> bool {
    let own = &self_ref.params[dec].0;
    let mut found = false;
    for arm in arms {
        crate::surface::walk_expr(&arm.body, &mut |e| {
            let Some((args, explicit)) = surface_self_call(self_ref, e) else { return };
            // The written slots skip value implicits unless `@`-marked.
            let slot = (self_ref.n_tyvars..self_ref.params.len())
                .filter(|&p| explicit || !self_ref.params[p].1)
                .position(|p| p == dec);
            if let Some(slot) = slot
                && let Some(arg) = args.get(slot)
                && !matches!(&arg.kind, ExprKind::Var(v) if v == own)
            {
                found = true;
            }
        });
    }
    found
}

/// The parameters other than `dec` that a self-call in `arms` passes at
/// anything but the parameter itself — the ones ih generalization quantifies
/// (`generalize`), and indices an indexed `match` rebinds. Syntactic, like
/// [`recurses_on`].
fn varied_params(self_ref: &SelfRef, arms: &[heather_syntax::Arm], dec: usize) -> Vec<usize> {
    let mut varied = Vec::new();
    for arm in arms {
        crate::surface::walk_expr(&arm.body, &mut |e| {
            let Some((args, explicit)) = surface_self_call(self_ref, e) else { return };
            let positions = (self_ref.n_tyvars..self_ref.params.len())
                .filter(|&p| explicit || !self_ref.params[p].1);
            for (slot, position) in positions.enumerate() {
                let Some(arg) = args.get(slot) else { break };
                let own = &self_ref.params[position].0;
                if position != dec
                    && !matches!(&arg.kind, ExprKind::Var(v) if v == own)
                    && !varied.contains(&position)
                {
                    varied.push(position);
                }
            }
        });
    }
    varied
}

/// How a `fn` without `decreases` is lowered
/// (issues/fn-recursion-means-the-function.md).
///
/// The structural lowering compiles the recursion at the `match`: a self-call
/// becomes the eliminator's hypothesis, which is *the `match` at the smaller
/// value*, and everything outside the `match` is evaluated once, by the top
/// call. That is the function exactly when the recursive `match` is the
/// body's result, under no branch that depends on its parameter, and its arms
/// do not read the parameter from outside. The plan is decided on the
/// **surface**, before anything is elaborated, because it picks the lowering.
pub(crate) enum RecursionPlan {
    /// The structural lowering means what the source means.
    Structural,
    /// A recursive `match` on parameter `dec` reads `dec`, or a name bound
    /// from it above the `match`, inside its arms (first at `read`, through
    /// `name`, bound from parameter `from`). Or it reads a name bound above
    /// it from a parameter `from` its self-calls pass a *different* value
    /// (issues/recursion-let-reads-changing-parameter.md): the ih
    /// generalizes `from` itself, but not a value computed from it outside
    /// the `match`. The structural lowering would see the top call's value
    /// there; a measure on `dec` sees this level's, so that is the lowering.
    ByMeasure { dec: usize, read: Span, name: String, from: usize },
    /// A recursive `match` on `dec` is somewhere the structural lowering
    /// cannot put the recursion, and the measure lowering has no unfolding
    /// equation for (docs/decreases-unfolding-design.md §3). Refused with
    /// `msg`, but only at a self-call the elaborator actually lowers under a
    /// guard on `dec`: the syntax cannot tell `contents.size()` on another
    /// type's member from a self-call.
    Misplaced { dec: usize, msg: String },
}

/// A name in scope during [`plan`]: the parameters its value depends on, and
/// which parameter it *is*, if it is one. `stale`: inside a recursive
/// `match`'s arms, the name was bound above the `match` from a parameter its
/// self-calls vary, so it holds the top call's value (the varied parameter).
#[derive(Clone)]
struct Bound {
    name: String,
    deps: Vec<usize>,
    param: Option<usize>,
    stale: Option<usize>,
}

fn lookup<'a>(scope: &'a [Bound], name: &str) -> Option<&'a Bound> {
    scope.iter().rev().find(|b| b.name == name)
}

fn bind_names(scope: &mut Vec<Bound>, names: impl IntoIterator<Item = String>) {
    scope.extend(names.into_iter().filter(|n| n != "_").map(|name| Bound {
        name,
        deps: Vec::new(),
        param: None,
        stale: None,
    }));
}

fn pattern_names(pat: &heather_syntax::Pat, out: &mut Vec<String>) {
    use heather_syntax::Pat;
    match pat {
        Pat::Var { name, .. } => out.push(name.clone()),
        Pat::Ctor { args, .. } => args.iter().for_each(|p| pattern_names(p, out)),
        Pat::Named { pat, .. } => pattern_names(pat, out),
    }
}

fn arm_names(arm: &heather_syntax::Arm) -> Vec<String> {
    let mut out = Vec::new();
    arm.binders.iter().for_each(|p| pattern_names(p, &mut out));
    out
}

/// Every free name `e` reads, with its binding in `scope` and its span —
/// binder-aware for `λ`, `match` arms and block statements.
fn reads(e: &Expr, scope: &[Bound], out: &mut dyn FnMut(&Bound, Span)) {
    match &e.kind {
        ExprKind::Var(name) => {
            if let Some(b) = lookup(scope, name) {
                out(b, e.span);
            }
        }
        ExprKind::Lam { binders, body } => {
            let mut inner = scope.to_vec();
            bind_names(&mut inner, binders.iter().map(|b| b.name.clone()));
            reads(body, &inner, out);
        }
        ExprKind::Match { scrut, arms, .. } => {
            reads(scrut, scope, out);
            for arm in arms {
                let mut inner = scope.to_vec();
                bind_names(&mut inner, arm_names(arm));
                reads(&arm.body, &inner, out);
            }
        }
        ExprKind::Block(block) => {
            let mut inner = scope.to_vec();
            for statement in &block.stmts {
                bind_statement(statement, &mut inner, &mut |e, scope| reads(e, scope, out));
            }
            reads(&block.result, &inner, out);
            block.ons.iter().for_each(|o| reads(&o.expr, &inner, out));
        }
        _ => crate::surface::for_each_child(e, &mut |c| reads(c, scope, out)),
    }
}

/// The parameters `e`'s value depends on.
fn deps(e: &Expr, scope: &[Bound]) -> Vec<usize> {
    let mut out = Vec::new();
    reads(e, scope, &mut |b, _| {
        for &p in &b.deps {
            if !out.contains(&p) {
                out.push(p);
            }
        }
    });
    out
}

/// Visit a block statement's right-hand side, then bind what it binds.
fn bind_statement(
    statement: &Stmt,
    scope: &mut Vec<Bound>,
    visit: &mut dyn FnMut(&Expr, &[Bound]),
) {
    match statement {
        Stmt::Let { name, expr, .. } => {
            visit(expr, scope);
            let deps = deps(expr, scope);
            scope.push(Bound { name: name.clone(), deps, param: None, stale: None });
        }
        Stmt::LetRecord { fields, expr, .. } => {
            visit(expr, scope);
            let deps = deps(expr, scope);
            let mut names = Vec::new();
            fields.iter().for_each(|f| pattern_names(&f.pat, &mut names));
            scope.extend(names.into_iter().filter(|n| n != "_").map(|name| Bound {
                name,
                deps: deps.clone(),
                param: None,
                stale: None,
            }));
        }
        Stmt::LetCode { .. } => {}
    }
}

struct Planner<'a> {
    self_ref: &'a SelfRef,
    misplaced: Option<(usize, String)>,
    read: Option<(usize, Span, String, usize)>,
}

impl Planner<'_> {
    /// `tail`: `e` is the body's result, reached only through block results
    /// and `match` arms. `spine`: the parameters an enclosing tail `match`'s
    /// scrutinee depends on.
    fn walk(&mut self, e: &Expr, tail: bool, scope: &[Bound], spine: &[usize]) {
        match &e.kind {
            ExprKind::Block(block) => {
                let mut inner = scope.to_vec();
                for statement in &block.stmts {
                    bind_statement(statement, &mut inner, &mut |e, scope| {
                        self.walk(e, false, scope, spine)
                    });
                }
                self.walk(&block.result, tail, &inner, spine);
                for on in &block.ons {
                    self.walk(&on.expr, false, &inner, spine);
                }
            }
            ExprKind::Match { scrut, arms, .. } => {
                let dec = match &scrut.kind {
                    ExprKind::Var(name) => lookup(scope, name).and_then(|b| b.param),
                    _ => None,
                };
                if let Some(dec) = dec
                    && recurses_on(self.self_ref, arms, dec)
                {
                    self.recursive_match(dec, arms, tail, scope, spine);
                }
                self.walk(scrut, false, scope, spine);
                let mut spine = spine.to_vec();
                for p in deps(scrut, scope) {
                    if !spine.contains(&p) {
                        spine.push(p);
                    }
                }
                for arm in arms {
                    let mut inner = scope.to_vec();
                    bind_names(&mut inner, arm_names(arm));
                    self.walk(&arm.body, tail, &inner, &spine);
                }
            }
            ExprKind::Lam { binders, body } => {
                let mut inner = scope.to_vec();
                bind_names(&mut inner, binders.iter().map(|b| b.name.clone()));
                self.walk(body, false, &inner, spine);
            }
            _ => crate::surface::for_each_child(e, &mut |c| self.walk(c, false, scope, spine)),
        }
    }

    fn recursive_match(
        &mut self,
        dec: usize,
        arms: &[heather_syntax::Arm],
        tail: bool,
        scope: &[Bound],
        spine: &[usize],
    ) {
        let name = &self.self_ref.name;
        let param = &self.self_ref.params[dec].0;
        let why = "the recursion is compiled at the `match`, so a recursive call in its \
                   arms means the `match` alone at the smaller value";
        let refusal = if !tail {
            Some(format!(
                "this recursive `match` on `{param}` is not the result of `{name}`: {why}, \
                 without the code around it. Make the `match` the body's result and move \
                 the surrounding code into each arm \
                 (issues/fn-recursion-means-the-function.md)"
            ))
        } else if spine.contains(&dec) {
            Some(format!(
                "this recursive `match` on `{param}` sits under a branch that depends on \
                 `{param}`: {why}, so the branch is decided once, by the top call. Branch \
                 inside the arms instead (issues/fn-recursion-means-the-function.md)"
            ))
        } else {
            None
        };
        if let Some(msg) = refusal {
            self.misplaced.get_or_insert((dec, msg));
            return;
        }
        // A name bound above the `match` from a parameter the self-calls
        // vary is evaluated once, at the top call's value of it; the varied
        // parameter itself is the ih's generalized binder, so reading *it*
        // is this level's value (issues/recursion-let-reads-changing-parameter.md).
        let varied = varied_params(self.self_ref, arms, dec);
        let above: Vec<Bound> = scope
            .iter()
            .map(|b| Bound {
                stale: b
                    .param
                    .is_none()
                    .then(|| b.deps.iter().copied().find(|p| varied.contains(p)))
                    .flatten(),
                ..b.clone()
            })
            .collect();
        for arm in arms {
            let mut inner = above.clone();
            bind_names(&mut inner, arm_names(arm));
            reads(&arm.body, &inner, &mut |b, span| {
                if self.read.is_some() {
                    return;
                }
                if b.deps.contains(&dec) {
                    self.read = Some((dec, span, b.name.clone(), dec));
                } else if let Some(from) = b.stale {
                    self.read = Some((dec, span, b.name.clone(), from));
                }
            });
        }
    }
}

/// Decide how a `fn` without `decreases` is lowered ([`RecursionPlan`]).
pub(crate) fn plan(self_ref: &SelfRef, body: &heather_syntax::Block) -> RecursionPlan {
    let scope: Vec<Bound> = self_ref
        .params
        .iter()
        .enumerate()
        .map(|(i, (name, _))| Bound { name: name.clone(), deps: vec![i], param: Some(i), stale: None })
        .collect();
    let mut planner = Planner { self_ref, misplaced: None, read: None };
    let body = Expr {
        kind: ExprKind::Block(Box::new(body.clone())),
        span: body.span,
    };
    planner.walk(&body, true, &scope, &[]);
    match (planner.misplaced, planner.read) {
        (Some((dec, msg)), _) => RecursionPlan::Misplaced { dec, msg },
        (None, Some((dec, read, name, from))) => RecursionPlan::ByMeasure { dec, read, name, from },
        (None, None) => RecursionPlan::Structural,
    }
}

/// Validate the written type arguments of a self-call
/// (issues/recursive-self-call-type-arguments.md).
///
/// A self-call is always at the declaration's own type parameters: the
/// recursion becomes an eliminator whose type parameters are bound outside
/// it, so there is no place for a second instantiation.
pub(crate) fn check_self_tyargs(cx: &Cx, tyargs: &[Ty], span: Span) -> R<()> {
    let s = cx.selfref.as_ref().expect("checked by the caller");
    let name = &s.name;
    let own: Vec<&str> = s.params[..s.n_tyvars]
        .iter()
        .map(|(n, _)| n.as_str())
        .collect();
    if tyargs.len() != s.n_tyvars {
        return err(
            if s.n_tyvars == 0 {
                format!("`{name}` has no type parameters, so a recursive call takes none")
            } else {
                format!(
                    "the recursive call to `{name}` writes {} type argument(s), and \
                     `{name}` has {} (`{}`)",
                    tyargs.len(),
                    s.n_tyvars,
                    own.join(", ")
                )
            },
            span,
        );
    }
    for (a, want) in tyargs.iter().zip(&own) {
        let is_own = matches!(&a.kind, TyKind::Named { name, args }
            if args.is_empty() && name == want);
        if !is_own {
            return err(
                format!(
                    "a recursive call to `{name}` is always at `{name}`'s own type \
                     parameter(s) `{}`, and `{}` is not `{want}`: recursing at a \
                     *different* instantiation is polymorphic recursion, which this \
                     lowering cannot express — the recursion becomes an `elim` whose \
                     type parameters are bound outside it, so there is nowhere for a \
                     second instantiation to go (issues/match-recursion.md). Writing \
                     `{}` is the same call and so is dropping the type arguments \
                     entirely",
                    own.join(", "),
                    crate::traits::render_ty(a),
                    own.join(", ")
                ),
                a.span,
            );
        }
    }
    Ok(())
}

/// Lower a call to the enclosing declaration's own name to the induction
/// hypothesis supplied by its structurally recursive match.
///
/// The decreasing argument is checked first because indexed guards discover
/// the descendant before they can validate a rebound index. Every remaining
/// declared parameter must be passed unchanged. Arguments beyond the
/// declaration's arity are applied to the induction hypothesis's result by
/// the ordinary explicit-application engine.
pub(crate) fn elab_self_call(
    elab: &impl SelfCallElab,
    cx: &Cx,
    args: &[Expr],
    explicit: bool,
    span: Span,
) -> R<(Term, Type, Level)> {
    let self_ref = Rc::clone(
        cx.selfref
            .as_ref()
            .expect("self-call outside a declaration"),
    );
    let name = &self_ref.name;
    let Some(guard) = cx.guard.clone() else {
        if let Some(codata) = &cx.codata_match {
            return err(
                format!(
                    "recursive call to `{name}` under a `match` on the codata `{codata}`: codata \
                     has no structural order, so a function out of it cannot recurse on it — \
                     recurse on a `Nat` fuel parameter beside it instead \
                     (docs/codata-elaborator-design.md §4)"
                ),
                span,
            );
        }
        return err(
            format!(
                "recursive call to `{name}` is not structurally guarded: it must occur \
                 inside a `match` on one of `{name}`'s own parameters"
            ),
            span,
        );
    };

    // Which parameter each written value argument fills. Leading type
    // parameters are never passed here; value implicits are omitted unless
    // the call is `@`-marked.
    let positions: Vec<usize> = (self_ref.n_tyvars..self_ref.params.len())
        .filter(|&position| explicit || !self_ref.params[position].1)
        .collect();
    if !positions.contains(&guard.dec) {
        return err(
            format!(
                "`{name}` recurses on its implicit parameter `{}`; pass it explicitly \
                 (`@{name}(…)`) to make the recursive call",
                self_ref.params[guard.dec].0
            ),
            span,
        );
    }
    if args.len() < positions.len() {
        return err(
            format!(
                "recursive call to `{name}` must pass all {} argument(s), found {}",
                positions.len(),
                args.len()
            ),
            span,
        );
    }

    let (args, spill) = args.split_at(positions.len());
    // A generalized parameter that the call cannot pass — an implicit one at
    // a call without `@` — has no argument to apply the ih to.
    if let Some(generalized) = &guard.generalized
        && let Some(&missing) = generalized.iter().find(|p| !positions.contains(p))
    {
        return err(
            format!(
                "`{name}` recurses at a varying value of its implicit parameter `{}`; \
                 pass it explicitly (`@{name}(…)`) to make the recursive call",
                self_ref.params[missing].0
            ),
            span,
        );
    }
    let mut descendant = 0usize;
    let mut cov_at = 0usize;
    // A descent through a recursive function field: which field, and the
    // argument the field was applied to.
    let mut through_fn: Option<(usize, Rc<Term>)> = None;
    // Arguments at generalized positions, in position order: applied to the
    // ih below, and checked there against its Π domains.
    let mut varied: Vec<&Expr> = Vec::new();
    let order = {
        let mut order: Vec<usize> = (0..args.len()).collect();
        if let Some(decreasing) = positions.iter().position(|&position| position == guard.dec) {
            order.swap(0, decreasing);
        }
        order
    };
    for (argument, position) in order.iter().map(|&index| (&args[index], positions[index])) {
        if position != guard.dec && guard.generalized.as_ref().is_some_and(|g| g.contains(&position)) {
            varied.push(argument);
            continue;
        }
        // Compare by binder for Nat and by term for Wf. Names are diagnostic
        // data only and cannot fake structural descent through shadowing.
        let (argument_term, _, _) = elab.infer_self_call_argument(cx, argument)?;
        let accepted = match (&guard.kind, position == guard.dec) {
            (GuardKind::Nat { preds, comps, .. }, true) => match argument_term {
                Term::Var(LocalVar(index)) => {
                    let absolute = cx.names.len() - 1 - index as usize;
                    match preds
                        .iter()
                        .position(|&predecessor| predecessor == absolute)
                    {
                        Some(depth) if depth < comps.len() => {
                            cov_at = depth;
                            true
                        }
                        _ => false,
                    }
                }
                _ => false,
            },
            (
                GuardKind::Wf {
                    depth,
                    children,
                    cov,
                    fn_children,
                    ..
                },
                true,
            ) => {
                let shift = (cx.names.len() - depth) as u32;
                // With a window, the chain is what a call may descend to —
                // `chain[0]` is the arm's own child, so the ordinary one-step
                // call is the `i = 0` case of the same lookup.
                match cov {
                    Some(window) => match window
                        .chain
                        .iter()
                        .position(|subterm| subterm.shift_local(shift) == argument_term)
                    {
                        Some(at) if at < window.comps.len() => {
                            cov_at = at;
                            true
                        }
                        _ => false,
                    },
                    None => match children
                        .iter()
                        .position(|(child, ..)| child.shift_local(shift) == argument_term)
                    {
                        Some(index) => {
                            descendant = index;
                            true
                        }
                        // Through a recursive function field: `k e` at any
                        // `e`, matched by the application's head term.
                        None => match fn_call(fn_children, shift, &argument_term) {
                            Some(hit) => {
                                through_fn = Some(hit);
                                true
                            }
                            None => false,
                        },
                    },
                }
            }
            (_, false) => {
                let is_original_binder = |absolute: usize| {
                    matches!(argument_term, Term::Var(LocalVar(index))
                        if cx.names.len() - 1 - index as usize == absolute)
                };
                is_original_binder(position)
                    || guard.rebind.as_ref().is_some_and(|(rebound, terms)| {
                        let (depth, fn_children) = match &guard.kind {
                            GuardKind::Wf { depth, fn_children, .. } => (*depth, fn_children),
                            GuardKind::Nat { .. } => return false,
                        };
                        let shift = (cx.names.len() - depth) as u32;
                        if *rebound != position {
                            return false;
                        }
                        // Through a function child, the index is the one
                        // written for it, at the argument the call passed.
                        if let Some((at, arg)) = &through_fn {
                            return fn_children[*at].rebind.as_ref().is_some_and(|term| {
                                term.shift_local_above(shift, 1).inst_top(0, arg) == argument_term
                            });
                        }
                        terms
                            .get(descendant)
                            .is_some_and(|term| term.shift_local(shift) == argument_term)
                    })
            }
        };
        if accepted {
            continue;
        }
        return if position == guard.dec {
            let (what, why) = match &guard.kind {
                GuardKind::Nat { preds, comps, .. } => {
                    let usable = preds.len().min(comps.len());
                    let names: Vec<String> = preds[..usable]
                        .iter()
                        .map(|predecessor| format!("`{}`", &cx.names[*predecessor]))
                        .collect();
                    if usable == 1 {
                        (
                            format!("{}, the predecessor bound by", names[0]),
                            format!(
                                ". A deeper subterm is refused too, even though it is \
                                 genuinely smaller: this `match` compiles to a recursor \
                                 whose induction hypothesis is the value at {} and at \
                                 nothing else, so a call anywhere else has no term to \
                                 elaborate to. Reaching further needs the recursion to \
                                 carry its earlier values \
                                 (issues/recursion-at-deeper-subterms.md), which happens \
                                 only where an arm scrutinizes its own predecessor",
                                names[0]
                            ),
                        )
                    } else {
                        (
                            format!("one of {}, the predecessors bound by", names.join(", ")),
                            format!(
                                ". The recursion carries its last {usable} values, so \
                                 those are the subterms it can descend to; anything else \
                                 has no term to elaborate to, even when it is genuinely \
                                 smaller (issues/recursion-at-deeper-subterms.md)"
                            ),
                        )
                    }
                }
                // Tier 2: the subtrees are the plain child and `k` applied
                // to anything (docs/inductive-tier2-w-lowering.md §8).
                GuardKind::Wf { fn_children, .. } if !fn_children.is_empty() => (
                    "a recursive field, or the function field applied to an argument, \
                     bound by"
                        .to_string(),
                    ". Through a function field `k` every `k(e)` is a subtree, \
                     whatever `e` is; a value built *around* one is not, so it has no \
                     induction hypothesis to elaborate to \
                     (docs/inductive-tier2-w-lowering.md §8)"
                        .to_string(),
                ),
                GuardKind::Wf { cov, .. } => match cov {
                    // The window exists, so the rule is not "the immediate
                    // field": it is "within the chain the recursion carries".
                    Some(window) => {
                        let usable = window.chain.len().min(window.comps.len());
                        (
                            format!(
                                "the recursive field bound by, or one of the {} \
                                 subterm(s) below it reached by",
                                usable.saturating_sub(1)
                            ),
                            format!(
                                ". The recursion carries its last {} value(s) down the \
                                 recursive field, so those are the subterms it can \
                                 descend to; anything else has no term to elaborate to, \
                                 even when it is genuinely smaller. The chain reaches \
                                 one further at each arm that scrutinizes its own \
                                 recursive field again, and no further than that \
                                 (docs/list-course-of-values-design.md §4)",
                                window.comps.len()
                            ),
                        )
                    }
                    None => (
                        "one of the recursive fields bound by".to_string(),
                        ". A deeper subterm is refused too, even though it is genuinely \
                         smaller: the induction hypothesis this `match` binds is the \
                         value at each recursive field and at nothing else, so a call \
                         anywhere else has no term to elaborate to. A window of earlier \
                         values exists for **chain-shaped** declarations — every \
                         constructor with at most one recursive field and no container \
                         (docs/list-course-of-values-design.md §1) — and this one is \
                         not: a branching constructor has no chain to walk, only a tree \
                         of children, and a container field is a group of children that \
                         a self-call maps over rather than descends into"
                            .to_string(),
                    ),
                },
            };
            err(
                format!(
                    "recursive call to `{name}` must descend: argument `{}` has to be \
                     {what} the enclosing `match`{why}",
                    self_ref.params[position].0
                ),
                argument.span,
            )
        } else {
            err(
                format!(
                    "recursive call to `{name}` must pass `{}` unchanged: the induction \
                     hypothesis fixes every non-decreasing parameter. A parameter is \
                     generalized into the motive — so that a recursive call may vary it \
                     — only when the `match` is checked against a known result type \
                     and the varying call is visible in its arms \
                     (docs/ih-generalization-design.md); here it was not",
                    self_ref.params[position].0
                ),
                argument.span,
            )
        };
    }

    let (term, ty, level) = match &guard.kind {
        GuardKind::Nat {
            tuple,
            comps,
            mlvl,
            depth,
            ..
        } => {
            let shift = (cx.names.len() - depth) as u32;
            let term = matching::cov_proj(comps, mlvl, tuple.clone(), cov_at);
            (
                term.shift_local(shift),
                comps[cov_at].shift_local(shift),
                mlvl.clone(),
            )
        }
        GuardKind::Wf {
            depth,
            children,
            cov,
            ..
        } => {
            let shift = (cx.names.len() - depth) as u32;
            match cov {
                Some(window) => {
                    let term = matching::cov_proj(
                        &window.comps,
                        &window.mlvl,
                        window.tuple.clone(),
                        cov_at,
                    );
                    (
                        term.shift_local(shift),
                        window.comps[cov_at].shift_local(shift),
                        window.mlvl.clone(),
                    )
                }
                None => match (&through_fn, &guard.kind) {
                    (Some((at, arg)), GuardKind::Wf { fn_children, .. }) => {
                        // `(λy. ih' y (c y)) e`, at `M[k e]`: the ih's Π
                        // instantiated at the argument the call wrote.
                        let field = &fn_children[*at];
                        let Type::Pi {
                            dom_level,
                            cod_level,
                            dom,
                            cod,
                        } = field.ih_ty.shift_local(shift)
                        else {
                            return err("internal: a function child's ih is not a `Π`", span);
                        };
                        let ty = cod.apply_local(
                            &crate::embed(&cx.gamma, 0).extended(Rc::clone(arg)),
                        );
                        let term = crate::spelling::checked_app(
                            Rc::new(field.ih.shift_local(shift)),
                            dom_level,
                            cod_level.clone(),
                            dom,
                            cod,
                            Rc::clone(arg),
                        );
                        (term, ty, cod_level)
                    }
                    _ => {
                        let (_, ih, ty, level) = &children[descendant];
                        (
                            (**ih).shift_local(shift),
                            ty.shift_local(shift),
                            level.clone(),
                        )
                    }
                },
            }
        }
    };
    // The call is the recursion's: a `match` the plan found misplaced is now
    // refused, here where the call is (issues/fn-recursion-means-the-function.md).
    if let Some((dec, msg)) = elab.misplaced_recursion(name)
        && dec == guard.dec
    {
        return err(msg, span);
    }
    // The ih is a Π over the generalized parameters (in position order, which
    // is `varied`'s order); the ordinary application engine checks each
    // argument against its domain, so a varied argument at the wrong type is
    // refused where it is written.
    let (term, ty, level) = if varied.is_empty() {
        (term, ty, level)
    } else {
        let generalized = guard.generalized.as_ref().expect("varied only fills at a generalized position");
        let metas: Vec<ParamMeta> = generalized
            .iter()
            .map(|&p| ParamMeta {
                name: self_ref.params[p].0.clone(),
                implicit: self_ref.params[p].1,
                is_type: false,
                is_self: false,
                skel: None,
                solver: None,
                default: None,
            })
            .collect();
        let varied: Vec<Expr> = varied.into_iter().cloned().collect();
        application::apply_explicit(elab, cx, Some(name), Rc::new(metas), 0, term, ty, level, &varied)?
    };
    if spill.is_empty() {
        return Ok((term, ty, level));
    }
    application::apply_explicit(
        elab,
        cx,
        Some(name),
        elab.self_call_application_params(name),
        self_ref.params.len(),
        term,
        ty,
        level,
        spill,
    )
}

/// A self-call's decreasing argument read as `k e`, for `k` one of an arm's
/// recursive function fields (docs/inductive-tier2-w-lowering.md §8): the
/// field it goes through and `e`. By **term**, never by name, like every
/// other descent: the application's head has to be the field binder's own
/// term, so a shadowing name cannot fake it.
fn fn_call(fields: &[FnChildIh], shift: u32, argument: &Term) -> Option<(usize, Rc<Term>)> {
    let (fun, arg) = match argument {
        Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => (fun, arg),
        _ => return None,
    };
    let at = fields.iter().position(|f| f.fun.shift_local(shift) == **fun)?;
    Some((at, Rc::clone(arg)))
}

/// The enclosing declaration, in scope throughout its own body so that a
/// structurally guarded self-call can lower to the induction hypothesis
/// (issues/match-recursion.md). Nothing else can reference it: neither self
/// spelling is registered as a global until the declaration is checked.
pub(crate) struct SelfRef {
    /// The base spelling used by the recursion machinery and diagnostics.
    pub(crate) name: String,
    /// The declaration head exactly as written. For an ordinary declaration
    /// this equals `name`; for a member it is the qualified spelling
    /// (`List::nth`). Both spellings denote this same in-progress
    /// self-reference, without publishing a provisional global.
    pub(crate) written_name: String,
    /// `(parameter name, implicit?)` in declaration order. Parameter `j` is
    /// bound at position `j` of the body's `Cx` (the telescope goes first).
    pub(crate) params: Vec<(String, bool)>,
    /// How many leading entries of [`Self::params`] are `<A, …>` type
    /// parameters. They are never passed at a call site — neither implicitly
    /// nor under `@`, which now controls only the *value* implicits
    /// (issues/at-and-type-arguments.md) — so they are skipped wholesale
    /// rather than filtered by implicitness.
    pub(crate) n_tyvars: usize,
    /// Where receiver syntax inserts its subject in the written explicit
    /// argument list. The declaration is not a committed global while its
    /// body is checked, so ordinary callable metadata cannot answer this for
    /// a recursive method call.
    pub(crate) receiver_slot: usize,
}

impl SelfRef {
    /// The enclosing declaration's self-reference, from its syntax.
    pub(crate) fn of_decl(decl: &heather_syntax::Decl) -> SelfRef {
        SelfRef {
            // A member's base name is its canonical recursion name, and
            // `SelfRef::matches` also accepts the declaration's qualified
            // spelling. Both are checked before globals, so neither path
            // publishes or calls a provisional global.
            name: decl.name.rsplit("::").next().unwrap_or(&decl.name).to_string(),
            written_name: decl.name.clone(),
            // Type parameters participate in guarded-call bookkeeping as
            // implicit parameters (docs/surface-polymorphism.md §6.1).
            params: decl
                .tyvars
                .iter()
                .map(|t| (t.name.clone(), true))
                .chain(decl.params.iter().map(|p| (p.name.clone(), p.implicit)))
                .collect(),
            n_tyvars: decl.tyvars.len(),
            receiver_slot: decl
                .params
                .iter()
                .filter(|p| !p.implicit)
                .position(|p| p.is_self)
                .unwrap_or(0),
        }
    }

    pub(crate) fn matches(&self, name: &str) -> bool {
        self.name == name || self.written_name == name
    }
}

/// Read a written self-call in either of its surface spellings.
///
/// Direct calls already carry declaration-order arguments. A receiver call
/// is normalized to that same order by inserting its receiver at the current
/// declaration's `self` slot. This is analysis only: guarded-call lowering
/// still checks binders and the kernel still checks the emitted eliminator.
pub(crate) fn surface_self_call<'a>(
    self_ref: &SelfRef,
    expression: &'a Expr,
) -> Option<(Vec<&'a Expr>, bool)> {
    match &expression.kind {
        ExprKind::App {
            head,
            args,
            explicit,
            ..
        } => {
            let head = match &head.kind {
                ExprKind::TyApp { head, .. } => head,
                _ => head,
            };
            matches!(&head.kind, ExprKind::Var(name) if self_ref.matches(name))
                .then(|| (args.iter().collect(), *explicit))
        }
        ExprKind::Dot {
            recv,
            name,
            args: Some(args),
            ..
        } if self_ref.matches(name) => {
            let at = self_ref.receiver_slot.min(args.len());
            let mut ordered = Vec::with_capacity(args.len() + 1);
            ordered.extend(args[..at].iter());
            ordered.push(recv.as_ref());
            ordered.extend(args[at..].iter());
            Some((ordered, false))
        }
        _ => None,
    }
}

/// What a guarded self-call must look like inside a `match` arm, and what it
/// lowers to (issues/match-recursion.md).
pub(crate) struct Guard {
    /// Index of the parameter the recursion descends on.
    pub(crate) dec: usize,
    pub(crate) kind: GuardKind,
    /// An indexed `match`'s index parameter, *rebound* by the arm
    /// (docs/inductive-indexed-lowering.md §6): a self-call must pass the
    /// arm's pattern variable there, not the original parameter.
    ///
    /// `(parameter position, one index term per descendant)` — parallel to
    /// [`GuardKind::Wf`]'s `children` and scoped at the same `depth`, because
    /// a branching index constructor gives each recursive field its *own*
    /// pattern variable (`Bal(SNode(l, r))`), and the ih at descendant `t`
    /// lives at exactly that one. `None` for every non-indexed guard.
    pub(crate) rebind: Option<(usize, Vec<Rc<Term>>)>,
    /// The parameters this recursion's motive **generalizes**, ascending
    /// (`generalize.rs`; issues/ih-generalization.md). At each of them a
    /// self-call may pass anything: the ih is a Π over these, in this order,
    /// and the call applies it to the written arguments. `None` when nothing
    /// is generalized, which is every recursion written before this existed.
    pub(crate) generalized: Option<Rc<Vec<usize>>>,
}

/// The two arm shapes a self-call can sit in. They differ in how many
/// descendants an arm has — one for `Nat`, `mᵢ` for a branching constructor —
/// and correspondingly in whether the ih is a variable or a function of the
/// index (`docs/inductive-tier1-wf-lowering.md` §6.4).
pub(crate) enum GuardKind {
    /// A `Succ(k)` arm. Positions are *absolute* (indices into `cx.names`,
    /// outermost first) so they stay valid as inner binders are pushed.
    Nat {
        /// The chain of predecessors this arm makes available, outermost
        /// first: `preds[0]` is the `k` the arm itself binds, `preds[1]` the
        /// `l` a nested `match k` binds, and so on
        /// (issues/recursion-at-deeper-subterms.md). A self-call descending to
        /// `preds[i]` lowers to the `i`-th component of [`Self::tuple`].
        ///
        /// One entry for the ordinary one-step recursion; the chain grows only
        /// where the arm's own body scrutinizes the predecessor again, and
        /// only by being convoyed through that `match`
        /// (docs/course-of-values-recursion-design.md §5).
        preds: Vec<usize>,
        /// The window of past values in scope: the ih binder itself for the
        /// ordinary recursion, a Σ-tuple of the last `comps.len()` values
        /// above that. Scoped at [`Self::depth`] binders, like
        /// [`GuardKind::Wf`]'s `children`, so a call from deeper inside the
        /// arm shifts it by the difference.
        tuple: Term,
        /// Its component types, at the same scope. `comps.len()` is the depth
        /// the recursion was *elaborated* for: a call below the chain's end
        /// but within it is what a nested `match` unlocks, and a call below
        /// `comps.len()` has no component to become — the refusal
        /// `elab_self_call` reports.
        comps: Vec<Type>,
        /// The level every component lives at.
        mlvl: Level,
        /// Binder count at the arm's ih — the scope [`Self::tuple`] lives in.
        depth: usize,
        /// The recursion's motive, scoped in ([`Self::gamma`], z), kept so a
        /// nested `match` can rebuild the window's type at *its* scrutinee.
        /// The pair travels together because reindexing a family needs the
        /// context it was written in, which a shift cannot recover.
        motive: Rc<Type>,
        gamma: LocalCtx,
    },
    /// A `Wf` arm: one entry per recursive field, as
    /// `(the child's term, `ih' ι_t`, its type, that type's level)`. All four
    /// are scoped at `depth` binders, so a call from deeper inside the arm
    /// shifts them by the difference.
    ///
    /// The match is on the *term*, not the name: an arm binder is an alias
    /// (tier 0 §5.1), not a kernel binder, so there is no position to compare,
    /// and comparing terms is what keeps shadowing from faking a guarded call.
    Wf {
        depth: usize,
        children: Vec<(Rc<Term>, Rc<Term>, Type, Level)>,
        /// The course-of-values window, where the recursion carries one
        /// (`docs/list-course-of-values-design.md` §3). `None` for every
        /// ordinary one-step recursion — which is every `Wf` recursion
        /// written before this existed, and which therefore still emits the
        /// term it always did.
        ///
        /// An *extension* rather than a third kind: a `Wf` arm's ih and its
        /// aliases are unchanged by the window, and only what a self-call at
        /// a **deeper** subterm lowers to is new.
        cov: Option<Rc<WfCov>>,
        /// The arm's *container* field, if it has one
        /// (`docs/container-fields.md` §4.2). A container is a group of
        /// children rather than one, so a self-call over it maps rather than
        /// descends — and the thing it maps to is the ih *tabulated* over the
        /// container's index range.
        container: Option<ContainerIh>,
        /// The arm's recursive **function** fields — a tier-2 arm's `k : A ->
        /// D` (docs/inductive-tier2-w-lowering.md §8). Empty for every `Wf`
        /// arm. A self-call descends through one at *any* argument: its
        /// decreasing argument is `k e`, matched by the application's head.
        fn_children: Vec<FnChildIh>,
    },
}

/// What a self-call through a recursive function field needs
/// (docs/inductive-tier2-w-lowering.md §8), scoped like the rest of
/// [`GuardKind::Wf`], at `depth` binders.
pub(crate) struct FnChildIh {
    /// The field binder's own term, `λy. ⟨f' y, c y⟩`: a call's decreasing
    /// argument must be an application *of this term*.
    pub(crate) fun: Rc<Term>,
    /// The ih as a function of the argument, `λy. ih' y (c y)`.
    pub(crate) ih: Rc<Term>,
    /// Its type, `Π(y : A). M[k y]`, kept whole so that a call site shifts it
    /// like any other type and reads the codomain under its own binder.
    pub(crate) ih_ty: Type,
    /// In an indexed family (docs/iwf-infinitary-design.md §8), the child's
    /// written index as a term under the field's one binder `y`, scoped like
    /// the rest at `depth + 1`: what a self-call through `k e` must pass at
    /// [`Guard::rebind`]'s parameter, instantiated at its `e`. `None` on
    /// tier 2, which has no index.
    pub(crate) rebind: Option<Rc<Term>>,
}

/// The window of past values a course-of-values `Wf` arm carries
/// (`docs/list-course-of-values-design.md` §3), field for field the twin of
/// [`GuardKind::Nat`]'s — with `pred` replaced by the recursive-field
/// projection, and the chain followed by **term** rather than by binder
/// position, because a `Wf` arm binder is an alias and has no position.
///
/// Everything here is scoped at [`GuardKind::Wf`]'s `depth`, so a call from
/// deeper inside the arm shifts it by the difference — except `motive`,
/// `gamma` and `tail`, which travel as they were written so that a nested
/// `match` can reindex them at *its* scrutinee.
pub(crate) struct WfCov {
    /// The chain this arm makes available, outermost first: `chain[0]` is the
    /// arm's own child, `chain[1]` the child a nested `match chain[0]` binds,
    /// and so on. A self-call descending to `chain[i]` lowers to the `i`-th
    /// component of [`Self::tuple`].
    ///
    /// One entry for the arm itself; the chain grows only where the arm's own
    /// body scrutinizes the child again, and only by being convoyed through
    /// that `match` (§4).
    pub(crate) chain: Vec<Rc<Term>>,
    /// The window: the ih tuple at `chain[0]` in the arm itself, the convoy
    /// binder inside a nested `match`.
    pub(crate) tuple: Term,
    /// Its component types. `comps.len()` is the depth the recursion was
    /// *elaborated* for: a call below `chain`'s end but within `comps` is what
    /// a nested `match` unlocks, and a call below `comps.len()` has no
    /// component to become.
    pub(crate) comps: Vec<Type>,
    pub(crate) mlvl: Level,
    /// The recursion's motive as written, over `(gamma, z : ⟦D⟧)`, with the
    /// context it was written in: reindexing a family needs that context, and
    /// a shift cannot recover it.
    pub(crate) motive: Rc<Type>,
    pub(crate) gamma: LocalCtx,
    /// `tail_D`, over `(gamma, z : ⟦D⟧)` — carried rather than rebuilt,
    /// because building one runs the whole `elim_Wf` lowering.
    pub(crate) tail: Rc<Term>,
    /// Where the window's **anchor** sits, as a function of this arm's chain
    /// end: `λ y. Cⱼ(payload, … C(…, y))`, the constructors of the arms
    /// *below* the recursion's own rebuilt around `y`, so that
    /// `window(chain-end)` is `chain[0]`. `λ y. y` in the arm the recursion's
    /// own `match` binds, which is the `Nat` design's "the first nesting
    /// lifts by nothing".
    ///
    /// A *function* and not an open term because its body mentions the
    /// enclosing arms' payload binders, which are not ambient: as a λ it
    /// shifts like any other term in the arm. It is applied by substitution,
    /// so no β-redex reaches an annotation.
    pub(crate) window: Rc<Term>,
    /// Where the **goal** sits, the same way: `λ y. C₀(payload, … C(…, y))`,
    /// now including the recursion's own arm, so that `goal(chain-end)` is
    /// the value that arm stands for and `M[goal(y)]` is the arm's obligation
    /// refined at `y`.
    ///
    /// Two anchors and not one because they differ by exactly that outermost
    /// constructor: the window is anchored at `chain[0]`, the goal one
    /// constructor above it. `Nat`'s convoy needs only the first, and gets
    /// the second from motive synthesis (`Succ k` has `k` as a subterm); a
    /// `Wf` arm's value has its child under a `nth`, not as a subterm, so
    /// synthesis cannot recover it and the goal is rebuilt here instead.
    pub(crate) goal: Rc<Term>,
}

/// What a self-call over a container binder needs, gathered at the arm and
/// scoped like the rest of [`GuardKind::Wf`], at `depth` binders.
#[derive(Clone)]
pub(crate) struct ContainerIh {
    /// The container binder's own term (`snd^m cs`), matched against the
    /// call's elaborated argument exactly as a plain child's term is.
    pub(crate) term: Rc<Term>,
    /// Its length.
    pub(crate) len: Rc<Term>,
    /// The ih function `Π(i : Fin (Succ^m len)). M`, as a term.
    pub(crate) ih: Rc<Term>,
    /// `m`: how many plain children precede the container, and so how far the
    /// container's indices are offset inside `Fin (Succ^m len)`.
    pub(crate) plain: usize,
    /// The motive, *strengthened* — a self-call over a container maps to a
    /// `Vec` of results, which requires a motive independent of the scrutinee
    /// (`docs/container-fields.md` §4.3). `None` when it depends, in which case
    /// [`ContainerIh::eq`] decides whether this is phase 3 or a diagnostic.
    pub(crate) result: Option<Type>,
    /// The motive read as an **equation**, when it is one — phase 3
    /// (`docs/container-proofs.md` §5). Set only when `result` is `None`: a
    /// dependent motive `Id^l(A; lhs(z); rhs(z))` whose *type* `A` does not
    /// mention `z` still relates the two children vectors pointwise, which is
    /// what `vec::tab_cong` turns into an equation between them.
    pub(crate) eq: Option<EqSplit>,
    /// The ih's own Π type, so a call site annotates its application with the
    /// codomain the eliminator actually gave rather than rebuilding it — the
    /// rebuild is only correct for a strengthened motive, and phase 3's is not.
    pub(crate) ih_ty: Type,
    /// `⟦D⟧`, the container's element type, for `nth` at the call site.
    pub(crate) elem: Type,
    /// `l`: the declaration's level, which is `⟦D⟧`'s. Not `mlvl`, which is the
    /// motive's — `nth` and the endpoint applications need this one.
    pub(crate) level: Level,
    pub(crate) mlvl: Level,
}

/// A dependent motive that is an equation, split into its two endpoints
/// (`docs/container-proofs.md` §5).
#[derive(Clone)]
pub(crate) struct EqSplit {
    /// The level `Id^l` is at, which is `A`'s.
    pub(crate) level: Level,
    /// `A`, the type the equation is at — strengthened, so it may not mention
    /// the scrutinee. A heterogeneous motive is out of scope and diagnosed
    /// (`issues/dependent-field-injectivity.md` holds the transport question).
    pub(crate) ty: Type,
    /// `λ(z : ⟦D⟧). lhs` and `λ(z : ⟦D⟧). rhs`. Kept as *functions* rather than
    /// as open terms so that a call site can shift them like any other term and
    /// apply them to a child; the β-redex this leaves is what conversion is for.
    pub(crate) lhs: Rc<Term>,
    pub(crate) rhs: Rc<Term>,
}

#[cfg(test)]
mod tests {
    use super::*;

    struct FakeSelfCall;

    impl ExplicitArgElab for FakeSelfCall {
        fn whnf_for_application(&self, _cx: &Cx, ty: &Type, _span: Span) -> R<Type> {
            Ok(ty.clone())
        }

        fn check_explicit_argument(
            &self,
            cx: &Cx,
            argument: &Expr,
            _expected: &Type,
            _level: &Level,
            _hint: Option<(&str, &str)>,
            _skeleton: Option<&crate::Skel>,
        ) -> R<Term> {
            Ok(self.infer_self_call_argument(cx, argument)?.0)
        }
    }

    impl SelfCallElab for FakeSelfCall {
        fn infer_self_call_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)> {
            let term = match &argument.kind {
                heather_syntax::ExprKind::Var(name) => {
                    let position = cx
                        .names
                        .iter()
                        .rposition(|candidate| candidate == name)
                        .ok_or_else(|| crate::ElabError::Elab {
                            msg: format!("unknown test local `{name}`"),
                            span: argument.span,
                        })?;
                    Term::Var(LocalVar((cx.names.len() - 1 - position) as u32))
                }
                heather_syntax::ExprKind::Num(__n) if __n.as_u64() == Some(0) => Term::Zero,
                _ => return err("unsupported test expression", argument.span),
            };
            Ok((term, Type::Nat, Level::Zero))
        }

        fn self_call_application_params(&self, _name: &str) -> Rc<Vec<ParamMeta>> {
            Rc::new(Vec::new())
        }

        fn misplaced_recursion(&self, _name: &str) -> Option<(usize, String)> {
            None
        }
    }

    const SPAN: Span = Span { start: 0, end: 1 };

    fn nat_guarded_context(component: Type) -> Cx {
        let mut cx = Cx::empty();
        cx.push("n".into(), Type::Nat, Level::Zero);
        cx.push("predecessor".into(), Type::Nat, Level::Zero);
        cx.selfref = Some(Rc::new(SelfRef {
            name: "f".into(),
            written_name: "f".into(),
            params: vec![("n".into(), false)],
            n_tyvars: 0,
            receiver_slot: 0,
        }));
        cx.guard = Some(Rc::new(Guard {
            dec: 0,
            rebind: None,
            generalized: None,
            kind: GuardKind::Nat {
                preds: vec![1],
                tuple: Term::Var(LocalVar(0)),
                comps: vec![component],
                mlvl: Level::Zero,
                depth: 2,
                motive: Rc::new(Type::Nat),
                gamma: LocalCtx::nil(),
            },
        }));
        cx
    }

    #[test]
    fn descent_is_parameter_identity_not_a_shadowing_name() {
        let mut cx = Cx::empty();
        cx.push("n".into(), Type::Nat, Level::Zero);
        cx.selfref = Some(Rc::new(SelfRef {
            name: "f".into(),
            written_name: "f".into(),
            params: vec![("n".into(), false)],
            n_tyvars: 0,
            receiver_slot: 0,
        }));
        assert_eq!(descends_on_param(&cx, &Term::Var(LocalVar(0))), Some(0));

        cx.push("n".into(), Type::Nat, Level::Zero);
        assert_eq!(descends_on_param(&cx, &Term::Var(LocalVar(0))), None);
        assert_eq!(descends_on_param(&cx, &Term::Var(LocalVar(1))), Some(0));
    }

    #[test]
    fn guarded_self_call_selects_the_ih_without_an_elaborator() {
        let cx = nat_guarded_context(Type::Nat);
        let predecessor = Expr {
            kind: heather_syntax::ExprKind::Var("predecessor".into()),
            span: SPAN,
        };
        let (term, ty, level) = elab_self_call(
            &FakeSelfCall,
            &cx,
            std::slice::from_ref(&predecessor),
            false,
            SPAN,
        )
        .expect("guarded call");
        assert_eq!(term, Term::Var(LocalVar(0)));
        assert_eq!(ty, Type::Nat);
        assert_eq!(level, Level::Zero);
    }

    #[test]
    fn self_call_spill_reuses_explicit_application() {
        let result = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Nat),
        };
        let cx = nat_guarded_context(result);
        let args = [
            Expr {
                kind: heather_syntax::ExprKind::Var("predecessor".into()),
                span: SPAN,
            },
            Expr {
                kind: heather_syntax::ExprKind::Num(0u64.into()),
                span: SPAN,
            },
        ];
        let (term, ty, level) =
            elab_self_call(&FakeSelfCall, &cx, &args, false, SPAN).expect("spilled call");
        assert!(matches!(term, Term::App { .. }));
        assert_eq!(ty, Type::Nat);
        assert_eq!(level, Level::Zero);
    }
}
