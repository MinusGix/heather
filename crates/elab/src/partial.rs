//! `partial fn f(x: A) → B { body }` (docs/language/partial-functions-design.md §4.2,
//! issues/partial-fn-surface.md): a function that may not return.
//!
//! The body is a block over the carrier of `f`'s own calls,
//! `CoTree<B>(Events::sum(Events::calls(A, B), E))`: each self-call `f(e)` is
//! the call event `CoTree::call(E, e)`, bound with `let r <- f(e);` or in
//! tail position, and a value leaves with `Pointed::ret(v)`. The declaration
//! is then the family
//!
//! ```text
//! fn f#body(x: A) → CoTree<B>(Events::sum(Events::calls(A, B), E)) { body[f(e) := CoTree::call(E, e)] }
//! fn f(x: A) → Partial(B) { CoTree::rec(Events::calls(A, B), E, λ (x: A) => f#body(x), x) }
//! theorem f_unfold(x: A): f(x) = CoTree::rec(…) { refl }
//! ```
//!
//! with `f#body` designated `f::body`, so that `CoTree::rec_sound` reads
//! `f::body` as its body and `f::body`'s own safety is what a proof shows.
//! Several parameters are one argument, nested in the prelude's pair
//! (`Mutated(x₁, Mutated(x₂, x₃))`), which the body reads back. `partial(E)
//! fn` gives the computation the events `E` and `f` the type
//! `A → CoTree<B>(E)`; without it `E` is `Events::none()` and the result is
//! `Partial(B)`.
//!
//! **The tail case** (§4.2, issues/partial-fn-tail-iter.md). When every
//! self-call is in tail position, no call waits for an answer, and `f` is a
//! loop: one `CoTree::iter` of a pass over the argument, the shape a native
//! loop has. The body is then a pass,
//!
//! ```text
//! fn f#body(x: A) → CoTree<Step<A, B>>(E) { body[f(e) := CRet(Continue(e)), leaf v := Break(v)] }
//! fn f(x: A) → Partial(B) { CoTree::iter(E, λ (x: A) => f#body(x), x) }
//! ```
//!
//! each tail self-call a `Continue` of its argument and each other tail leaf
//! the same computation with its value wrapped in `Break`: `Pointed::ret(v)`
//! and `CRet(v)` directly, anything else through `CoTree::map`. A proof
//! reads it with `CoTree::iter_sound`, an invariant on states the pass keeps.
//! A body with a bound call (`let r <- f(e);`) goes through `CoTree::rec`
//! as above, and so does a tail body this walk cannot place (a bind whose
//! continuation is not a `λ`, a `match` with a written motive), which still
//! has `rec`'s meaning.
//!
//! Nothing here is trusted: each part is an ordinary declaration checked
//! the ordinary way.
//!
//! A call used where `B` is expected (`fn g(n: Nat) → Nat { f(n) }`) is
//! refused by the gate as a mismatch between `Partial(B)` and `B`; the
//! elaborator records the call's head, and when the gate refuses and the
//! head is a partial function ([`Partial::is_partial_fn`]) the refusal
//! names it ([`Partial::partial_use_note`], §4.2's refusal).

use heather_syntax::{Block, Decl, DeclKind, Expr, ExprKind, LamBinder, Param, ParamOrigin, Span, Stmt, Ty, TyKind};

use heather_kernel::rc::Rc;

use heather_kernel::term::Type;

use crate::{Cx, Elaborator, R, err};

pub(crate) struct Family {
    pub(crate) parts: Vec<Decl>,
    /// `f_unfold`, attempted after the family; a refusal is recorded, never
    /// a reason to refuse `f`.
    pub(crate) unfold: Decl,
    pub(crate) designations: Vec<(String, String)>,
}

fn var(name: &str, span: Span) -> Expr { Expr { kind: ExprKind::Var(name.into()), span } }

fn call(head: Expr, args: Vec<Expr>, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App { head: Box::new(head), args, named: vec![], explicit: false, goal_oriented: false },
        span,
    }
}

fn ty_lit(t: &Ty) -> Expr { Expr { kind: ExprKind::TyLit(Box::new(t.clone())), span: t.span } }

fn of_expr(e: Expr) -> Ty { Ty { span: e.span, kind: TyKind::OfExpr(Box::new(e)) } }

fn named_ty(name: &str, args: Vec<Ty>, span: Span) -> Ty { Ty { kind: TyKind::Named { name: name.into(), args }, span } }

/// `CoTree<B>(events)`.
fn cotree_ty(b: &Ty, events: Expr, span: Span) -> Ty {
    let head = Expr { kind: ExprKind::TyApp { head: Box::new(var("CoTree", span)), args: vec![b.clone()] }, span };
    of_expr(call(head, vec![events], span))
}

fn param(name: &str, ty: Ty, span: Span) -> Param {
    Param {
        name: name.into(),
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

/// The argument a call passes: the one parameter, or the parameters nested
/// in `Mutated` pairs.
fn bundle(mut args: Vec<Expr>, span: Span) -> Expr {
    if args.len() == 1 {
        return args.pop().expect("one argument");
    }
    let first = args.remove(0);
    call(var("Mutated", span), vec![first, bundle(args, span)], span)
}

fn bundle_ty(mut tys: Vec<Ty>, span: Span) -> Ty {
    if tys.len() == 1 {
        return tys.pop().expect("one type");
    }
    let first = tys.remove(0);
    named_ty("Mutated", vec![first, bundle_ty(tys, span)], span)
}

/// The parameters read back from a bundle `a`.
fn unbundle(a: &str, names: &[String], span: Span) -> Vec<Stmt> {
    let mut out = Vec::with_capacity(names.len());
    let mut at = var(a, span);
    let dot = |recv: Expr, name: &str| Expr {
        kind: ExprKind::Dot { recv: Box::new(recv), name: name.into(), tyargs: vec![], args: None, named: vec![] },
        span,
    };
    for (i, n) in names.iter().enumerate() {
        let read = if i + 1 == names.len() { at.clone() } else { dot(at.clone(), "after") };
        out.push(Stmt::Let { name: n.clone(), ty: None, expr: read, span, opaque: false });
        at = dot(at, "value");
    }
    out
}

struct Calls<'a> {
    names: [&'a str; 2],
    arity: usize,
    /// `CoTree::call<A, B>(E, ·)`'s head and events.
    head: Expr,
    events: Expr,
    found: usize,
    /// Self-calls bound with `let r <- f(e);`: any makes the body general.
    bound: usize,
    /// The tail case's walk (module docs): a tail self-call is `Continue`,
    /// a tail leaf `Break`. Only run on a body the general walk accepted
    /// with no bound call.
    iter: Option<Iter>,
}

/// What the tail case's walk needs, and whether it met a shape it cannot
/// place (then the body is lowered the general way).
struct Iter {
    /// `CoTree::map<B, Step<A, B>>`, `E`.
    map: Expr,
    events: Expr,
    unplaced: bool,
}

impl Calls<'_> {
    fn is_self(&self, e: &Expr) -> bool { matches!(&e.kind, ExprKind::Var(n) if self.names.contains(&n.as_str())) }

    /// The call event a self-call `f(ē)` is, its arguments rewritten.
    fn call_event(&mut self, args: Vec<Expr>, span: Span) -> R<Expr> {
        if args.len() != self.arity {
            return err(
                format!("`{}` takes {} argument(s) here, and this call passes {}", self.names[0], self.arity, args.len()),
                span,
            );
        }
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            out.push(self.rewrite(a, false)?);
        }
        self.found += 1;
        if self.iter.is_some() {
            let next = call(var("Continue", span), vec![bundle(out, span)], span);
            return Ok(call(var("CRet", span), vec![next], span));
        }
        Ok(call(self.head.clone(), vec![self.events.clone(), bundle(out, span)], span))
    }

    /// A tail leaf of the tail case: the same computation, its value a
    /// `Break`.
    fn leaf(&self, e: Expr) -> Expr {
        let span = e.span;
        let Some(it) = &self.iter else { return e };
        match e.kind {
            ExprKind::App { head, mut args, named, explicit: false, goal_oriented }
                if named.is_empty()
                    && args.len() == 1
                    && matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::POINTED_RET || n == "CRet") =>
            {
                let v = args.pop().expect("one argument");
                let v = call(var("Break", span), vec![v], span);
                Expr { kind: ExprKind::App { head, args: vec![v], named, explicit: false, goal_oriented }, span }
            }
            kind => {
                let brk = Expr {
                    kind: ExprKind::Lam {
                        binders: vec![LamBinder { name: "#v".into(), ty: None, implicit: false, span }],
                        body: Box::new(call(var("Break", span), vec![var("#v", span)], span)),
                    },
                    span,
                };
                call(it.map.clone(), vec![it.events.clone(), Expr { kind, span }, brk], span)
            }
        }
    }

    fn unplaced(&mut self) {
        if let Some(it) = &mut self.iter {
            it.unplaced = true;
        }
    }

    /// Rewrite every self-call in `e`, which is in tail position when `tail`.
    fn rewrite(&mut self, e: Expr, tail: bool) -> R<Expr> {
        let span = e.span;
        match e.kind {
            ExprKind::App { head, args, named, explicit, goal_oriented } if self.is_self(&head) => {
                if !named.is_empty() || explicit {
                    return err(format!("a call of the partial `{}` passes its arguments by position", self.names[0]), span);
                }
                let _ = goal_oriented;
                if !tail {
                    return err(
                        format!(
                            "`{0}` is partial, so a call to it is a computation that may not return: bind it \
                             with `let r <- {0}(…);`, or make it the body's result. Outside its body, \
                             `CoTree::get` reads a result once a proof says the call returns",
                            self.names[0]
                        ),
                        span,
                    );
                }
                self.call_event(args, span)
            }
            ExprKind::Var(n) if self.names.contains(&n.as_str()) => err(
                format!("the partial `{n}` is called in its own body, not passed: a self-call is a call event"),
                span,
            ),
            // `let r <- f(e); rest`: the bound expression may be a call.
            ExprKind::App { head, mut args, named, explicit, goal_oriented }
                if matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::BIND_SEQ) && args.len() == 2 =>
            {
                let k = args.pop().expect("a continuation");
                let m = args.pop().expect("a bound expression");
                let m = match m.kind {
                    ExprKind::App { head: h, args: a, named: na, .. } if self.is_self(&h) && na.is_empty() => {
                        self.bound += 1;
                        self.call_event(a, m.span)?
                    }
                    kind => self.rewrite(Expr { kind, span: m.span }, false)?,
                };
                let k = self.continuation(k, tail)?;
                Ok(Expr { kind: ExprKind::App { head, args: vec![m, k], named, explicit, goal_oriented }, span })
            }
            // A `while` with no measure and the rest of its block: the rest
            // is in the position the loop is.
            ExprKind::App { head, mut args, named, explicit, goal_oriented }
                if matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::ITERATE_THEN) && args.len() == 3 =>
            {
                let k = args.pop().expect("a continuation");
                let mut out = Vec::with_capacity(3);
                for a in args {
                    out.push(self.rewrite(a, false)?);
                }
                out.push(self.continuation(k, tail)?);
                Ok(Expr { kind: ExprKind::App { head, args: out, named, explicit, goal_oriented }, span })
            }
            ExprKind::Block(mut b) => {
                let mut stmts = Vec::with_capacity(b.stmts.len());
                for s in std::mem::take(&mut b.stmts) {
                    stmts.push(match s {
                        Stmt::Let { name, ty, expr, span, opaque } => {
                            Stmt::Let { name, ty, expr: self.rewrite(expr, false)?, span, opaque }
                        }
                        other => other,
                    });
                }
                b.stmts = stmts;
                let result = std::mem::replace(&mut *b.result, var("", span));
                *b.result = self.rewrite(result, tail)?;
                Ok(Expr { kind: ExprKind::Block(b), span })
            }
            ExprKind::Match { form, generated, scrut, eqbind, motive, arms } => {
                if tail && motive.is_some() {
                    self.unplaced();
                }
                let scrut = Box::new(self.rewrite(*scrut, false)?);
                let mut out = Vec::with_capacity(arms.len());
                for mut arm in arms {
                    arm.body = self.rewrite(arm.body, tail)?;
                    out.push(arm);
                }
                Ok(Expr { kind: ExprKind::Match { form, generated, scrut, eqbind, motive, arms: out }, span })
            }
            kind => {
                let mut e = Expr { kind, span };
                let mut failed = None;
                heather_syntax::expr_children_mut(&mut e, &mut |c| {
                    if failed.is_some() {
                        return;
                    }
                    let taken = std::mem::replace(c, var("", c.span));
                    match self.rewrite(taken, false) {
                        Ok(x) => *c = x,
                        Err(error) => failed = Some(error),
                    }
                });
                match failed {
                    Some(error) => Err(error),
                    None if tail => Ok(self.leaf(e)),
                    None => Ok(e),
                }
            }
        }
    }

    /// A bind's continuation `λ x => rest`: `rest` is in the bind's position.
    fn continuation(&mut self, k: Expr, tail: bool) -> R<Expr> {
        let span = k.span;
        match k.kind {
            ExprKind::Lam { binders, body } => {
                Ok(Expr { kind: ExprKind::Lam { binders, body: Box::new(self.rewrite(*body, tail)?) }, span })
            }
            kind => {
                if tail {
                    self.unplaced();
                }
                self.rewrite(Expr { kind, span }, false)
            }
        }
    }
}

/// Lower a `partial fn` (module docs).
pub(crate) fn lower(decl: &Decl) -> R<Family> {
    let spec = decl.partial.as_ref().expect("a partial declaration");
    let span = decl.span;
    if decl.kind != DeclKind::Fn || decl.is_meta || decl.value {
        return err("`partial` marks a `fn`", spec.span);
    }
    if decl.is_interface {
        return err("a `partial fn` cannot be an `interface fn` yet: its body is already reached only through `f::body`", spec.span);
    }
    if let Some(p) = decl.params.iter().find(|p| p.implicit || p.solver.is_some() || p.default.is_some()) {
        return err(
            format!(
                "a `partial fn`'s parameters are its calls' argument, so each is explicit: `{}` is \
                 implicit, searched for or defaulted, which is not supported yet",
                p.name
            ),
            p.span,
        );
    }
    if decl.params.is_empty() {
        return err("a `partial fn` takes at least one parameter: its calls' argument", span);
    }
    let names: Vec<String> = decl.params.iter().map(|p| p.name.clone()).collect();
    for (i, p) in decl.params.iter().enumerate() {
        if names[..i].iter().any(|n| crate::measure::mentions_ty(&p.ty, n)) {
            return err(
                format!(
                    "`{}`'s type mentions an earlier parameter: a `partial fn`'s parameters are one \
                     argument of a fixed type, so they cannot depend on each other yet",
                    p.name
                ),
                p.span,
            );
        }
    }
    let a = bundle_ty(decl.params.iter().map(|p| p.ty.clone()).collect(), span);
    let b = decl.result.clone();
    let events = spec.events.clone().unwrap_or_else(|| call(var("Events::none", span), vec![], span));
    let calls = call(var("Events::calls", span), vec![ty_lit(&a), ty_lit(&b)], span);
    let sum = call(var("Events::sum", span), vec![calls.clone(), events.clone()], span);
    let last = decl.name.rsplit_once("::").map_or(decl.name.as_str(), |(_, l)| l);
    let mut rewriter = Calls {
        names: [decl.name.as_str(), last],
        arity: decl.params.len(),
        head: Expr {
            kind: ExprKind::TyApp { head: Box::new(var("CoTree::call", span)), args: vec![a.clone(), b.clone()] },
            span,
        },
        events: events.clone(),
        found: 0,
        bound: 0,
        iter: None,
    };
    let whole = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span: decl.body.span };
    let mut rewritten = rewriter.rewrite(whole.clone(), true)?;
    if rewriter.found == 0 {
        return err(
            format!("`{}` never calls itself, so it always returns: write it as a plain `fn`", decl.name),
            spec.span,
        );
    }
    // The tail case: no call waits for an answer, so `f` is a loop.
    let step_ty = named_ty("Step", vec![a.clone(), b.clone()], span);
    let mut tail_only = false;
    if rewriter.bound == 0 {
        rewriter.iter = Some(Iter {
            map: Expr {
                kind: ExprKind::TyApp { head: Box::new(var("CoTree::map", span)), args: vec![b.clone(), step_ty.clone()] },
                span,
            },
            events: events.clone(),
            unplaced: false,
        });
        let pass = rewriter.rewrite(whole, true)?;
        if !rewriter.iter.as_ref().is_some_and(|it| it.unplaced) {
            rewritten = pass;
            tail_only = true;
        }
    }
    let ExprKind::Block(body) = rewritten.kind else { unreachable!("a block rewrites to a block") };
    let mut body = *body;
    let minted = format!("{}#body", decl.name);
    let designed = format!("{}::body", decl.name);
    let (body_params, a_name) = if names.len() == 1 {
        (decl.params.clone(), names[0].clone())
    } else {
        let reads = unbundle("#args", &names, span);
        body.stmts.splice(0..0, reads);
        (vec![param("#args", a.clone(), span)], "#args".to_string())
    };
    let tyargs: Vec<Ty> = decl.tyvars.iter().map(|t| named_ty(&t.name, vec![], span)).collect();
    let body_decl = Decl {
        kind: DeclKind::Fn,
        is_meta: false,
        is_evidence: false,
        is_interface: false,
        partial: None,
        value: false,
        elaborates: None,
        name: minted.clone(),
        tyvars: decl.tyvars.clone(),
        params: body_params,
        result: if tail_only { cotree_ty(&step_ty, events.clone(), span) } else { cotree_ty(&b, sum, span) },
        decreases: None,
        depth: None,
        unfolding: decl.unfolding.clone(),
        body,
        span,
    };
    // `CoTree::rec(Events::calls(A, B), E, λ (a: A) => f#body(a), ⟨x̄⟩)`, or
    // `CoTree::iter(E, λ (a: A) => f#body(a), ⟨x̄⟩)` in the tail case.
    let mut body_head = var(&minted, span);
    if !tyargs.is_empty() {
        body_head = Expr { kind: ExprKind::TyApp { head: Box::new(body_head), args: tyargs.clone() }, span };
    }
    let step = Expr {
        kind: ExprKind::Lam {
            binders: vec![LamBinder { name: a_name.clone(), ty: Some(a.clone()), implicit: false, span }],
            body: Box::new(call(body_head, vec![var(&a_name, span)], span)),
        },
        span,
    };
    let argument = bundle(names.iter().map(|n| var(n, span)).collect(), span);
    let rec = if tail_only {
        call(var("CoTree::iter", span), vec![events, step, argument], span)
    } else {
        call(var("CoTree::rec", span), vec![calls, events, step, argument], span)
    };
    let result = match &spec.events {
        None => of_expr(call(var("Partial", span), vec![ty_lit(&b)], span)),
        Some(e) => cotree_ty(&b, e.clone(), span),
    };
    let wrapper = Decl {
        kind: DeclKind::Fn,
        is_meta: false,
        is_evidence: false,
        is_interface: false,
        partial: None,
        value: false,
        elaborates: None,
        name: decl.name.clone(),
        tyvars: decl.tyvars.clone(),
        params: decl.params.clone(),
        result,
        decreases: None,
        depth: None,
        unfolding: Vec::new(),
        body: Block { stmts: vec![], result: Box::new(rec.clone()), ons: vec![], span },
        span,
    };
    // `f_unfold(x̄): f(x̄) = CoTree::rec(…)`, by `refl`.
    let mut head = var(&decl.name, span);
    if !tyargs.is_empty() {
        head = Expr { kind: ExprKind::TyApp { head: Box::new(head), args: tyargs } , span };
    }
    let lhs = Expr {
        kind: ExprKind::App {
            head: Box::new(head),
            args: names.iter().map(|n| var(n, span)).collect(),
            named: vec![],
            explicit: true,
            goal_oriented: false,
        },
        span,
    };
    let unfold = Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        is_evidence: false,
        is_interface: false,
        partial: None,
        value: false,
        elaborates: None,
        name: crate::measure::unfold_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params: decl.params.clone(),
        result: Ty { kind: TyKind::Eq(Box::new(lhs), Box::new(rec)), span },
        decreases: None,
        depth: None,
        unfolding: Vec::new(),
        body: Block { stmts: vec![], result: Box::new(Expr { kind: ExprKind::Refl, span }), ons: vec![], span },
        span,
    };
    Ok(Family { parts: vec![body_decl, wrapper], unfold, designations: vec![(designed, minted)] })
}

/// Partial functions' part of the elaborator.
pub(crate) struct Partial<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Partial<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Partial<'_> {
    /// Whether `name`, the head of a call written in `cx`, is a `partial
    /// fn`. Partial is read off what the lowering left, which a module image
    /// carries, so an imported function is recognised as a local one is: the
    /// global `f#body`, designated `f::body`. A measure's family
    /// (`docs/language/recursion/decreases-unfolding-design.md` §11) designates `f::body` too,
    /// but always beside `f::rec`, which a partial function never has.
    pub(crate) fn is_partial_fn(&self, cx: &Cx, name: &str) -> bool {
        if cx.names.contains(name) || cx.aliases.iter_inner().any(|alias| alias.name == *name) {
            return false;
        }
        let Some(key) = self.key_of(name) else { return false };
        let base = key.split_once("::").map_or(key.as_str(), |(_, base)| base);
        let minted = format!("{base}#body");
        self.names.global(&format!("{key}#body")).is_some()
            && self.access_alias(&format!("{base}::body")) == Some(minted.as_str())
            && self.access_alias(&format!("{base}::rec")).is_none()
    }

    /// The refusal of a call to `f` where something other than a
    /// computation is expected (docs/language/partial-functions-design.md §4.2): `f`
    /// is named, with the two ways out. `None` when `f` is not a `partial
    /// fn`, when the call's type is not a `CoTree` or the expected one is (a
    /// mismatch between two computations is the ordinary one), or when either
    /// type does not spell.
    pub(crate) fn partial_use_note(&self, cx: &Cx, f: &str, got: &Type, expected: &Type) -> Option<String> {
        if !self.is_partial_fn(cx, f) {
            return None;
        }
        let tree = |ty: &Type| {
            crate::goal_combinators::type_inductive(self, cx, ty).is_some_and(|i| i.codata && i.name == "CoTree")
        };
        if !tree(got) || tree(expected) {
            return None;
        }
        let g = self.partial_display(cx, got)?;
        let w = self.display_type_clean(cx, expected)?;
        Some(format!(
            "`{f}` is partial, so a call to it is a computation that may not return: this one has \
             type `{g}`, but `{w}` is expected here; bind it with `let r <- {f}(…);` inside a \
             computation, or use `CoTree::get` with a termination proof"
        ))
    }

    /// A call's type as `Partial(B)` when it is `CoTree<B>(none)`, the
    /// type a `partial fn` without events was declared with (`Partial` is
    /// a `def`, expanded where it is read: issues/type-name-display-respelling.md).
    /// Otherwise its ordinary display.
    fn partial_display(&self, cx: &Cx, got: &Type) -> Option<String> {
        let shown = self.display_type_clean(cx, got)?;
        let result = || {
            let decoded = crate::inductive::decoded(got);
            let Type::M { sig, index } = &*decoded else { return None };
            let Type::El { tm, .. } = sig.shape_at(index) else { return None };
            let (crate::gendefs::GenDef::MShape(_), args) = self.gen_app_of(&tm)? else { return None };
            let b = Type::El { level: heather_kernel::level::Level::Zero, tm: Rc::clone(args.first()?) };
            self.display_type_clean(cx, &b)
        };
        Some(match result() {
            Some(b) if shown == format!("CoTree<{b}>(none)") => format!("Partial({b})"),
            _ => shown,
        })
    }
}
