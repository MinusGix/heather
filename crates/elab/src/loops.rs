//! `for x in xs { body }` in pure code (docs/sequencing-surface-design.md
//! §5.2): the loop's body becomes a **named step** over a fold.
//!
//! The parser has already threaded the `let mut` locals the body assigns
//! ([`heather_syntax::LOOP`]): a loop arrives as
//!
//! ```text
//! let #forN = \0loop(xs, λ x => { body; \0state(v̄) }, v̄);
//! let vᵢ: TypeOf(vᵢ) = \0proj(#forN, vᵢ);          // one per local
//! ```
//!
//! and this pass, before the declaration is elaborated, turns it into a
//! family of ordinary declarations, each checked the ordinary way:
//!
//! - with one local `v: T`, `fn f#step(c̄, v: T, x: E) → T { body; v }`;
//! - with several, `record f#State { v₁: T₁, … }` and
//!   `fn f#step(c̄, #s: f#State, x: E) → f#State { let vᵢ = #s.vᵢ; …; body;
//!   f#State(v̄) }`;
//! - and `f` itself, with the loop replaced by `xs.foldl(λ #s x =>
//!   f#step(c̄, #s, x), v)` (or `f#State(v̄)`) and each `\0proj` by the state
//!   or its field.
//!
//! `c̄` are the captures: the locals in scope at the loop that the body
//! mentions, at the types the [`BinderTys`] oracle recovers, after every
//! solver parameter of `f` (a body's operators may resolve through them).
//! The step and state are designated `f::step` and `f::State` (with several
//! loops, `f::loop1_step`, …; §5.4), the spellings proofs cite.
//!
//! Nothing here is trusted: a wrong capture or type is refused by the
//! checker at the generated declaration.

use heather_syntax::{
    Arm, Block, CtorDecl, Decl, DeclKind, Expr, ExprKind, FieldDecl, InductiveDecl, LamBinder, Param,
    ParamOrigin, Span, Stmt, Ty, TyKind,
};

use crate::measure::{self, Binder, BinderTys};
use crate::{R, err};

/// What a declaration with loops lowers to, in elaboration order.
pub(crate) enum Part {
    State(InductiveDecl),
    Decl(Decl),
}

/// The lowered family, and the designed spellings to install after it.
pub(crate) struct Family {
    pub(crate) parts: Vec<Part>,
    /// `f_unfold : f(x̄) = <the lowered body>` by `refl` (§7.1), attempted
    /// after the family and skipped, with its reason recorded, if refused.
    pub(crate) unfold: Decl,
    pub(crate) designations: Vec<(String, String)>,
}

fn loop_parts(e: &Expr) -> Option<(&Expr, &LamBinder, &Block, Vec<&str>)> {
    let ExprKind::App { head, args, .. } = &e.kind else { return None };
    if args.len() < 3 || !matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::LOOP) {
        return None;
    }
    let ExprKind::Lam { binders, body } = &args[1].kind else { return None };
    let ExprKind::Block(b) = &body.kind else { return None };
    let vars = args[2..]
        .iter()
        .map(|a| match &a.kind {
            ExprKind::Var(n) => Some(n.as_str()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some((&args[0], binders.first()?, b, vars))
}

/// Does the declaration's body hold a lowered loop?
pub(crate) fn has_loop(decl: &Decl) -> bool {
    let e = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span: decl.body.span };
    let mut found = false;
    crate::surface::walk_expr(&e, &mut |x| {
        found |= loop_parts(x).is_some();
    });
    found
}

fn count_loops(b: &Block) -> usize {
    let e = Expr { kind: ExprKind::Block(Box::new(b.clone())), span: b.span };
    let mut n = 0;
    crate::surface::walk_expr(&e, &mut |x| {
        if let Some((_, _, body, _)) = loop_parts(x) {
            // A nested loop is the step's, counted when the step is lowered.
            n += 1;
            n -= count_loops(body);
        }
    });
    n
}

fn var(name: &str, span: Span) -> Expr { Expr { kind: ExprKind::Var(name.into()), span } }

fn call(head: Expr, args: Vec<Expr>, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App { head: Box::new(head), args, named: vec![], explicit: false, goal_oriented: false },
        span,
    }
}

fn named_ty(name: &str, args: Vec<Ty>, span: Span) -> Ty { Ty { kind: TyKind::Named { name: name.into(), args }, span } }

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

struct Lift<'a> {
    decl: &'a Decl,
    tys: &'a dyn BinderTys,
    loops: usize,
    next: usize,
    parts: Vec<Part>,
    designations: Vec<(String, String)>,
}

/// A local in scope: its name, and its type once one is needed.
#[derive(Clone)]
struct Local {
    name: String,
    written: Option<Ty>,
    value: Option<Expr>,
}

impl<'a> Lift<'a> {
    /// The scope's surface types, in order, inferring each local's from its
    /// value under the ones before it. `None` where the oracle declines.
    fn typed(&self, scope: &[Local]) -> Vec<Binder> {
        let mut out: Vec<Binder> = Vec::new();
        for l in scope {
            let ty = match &l.written {
                // `x := e` annotates its alias with the type of `x` before it.
                Some(Ty { kind: TyKind::TypeOf(e), .. }) => match &e.kind {
                    ExprKind::Var(n) if *n == l.name => out.iter().rev().find(|b| b.name == l.name).and_then(|b| b.ty.clone()),
                    _ => self.infer(&out, e),
                },
                Some(t) => Some(t.clone()),
                None => l.value.as_ref().and_then(|v| self.infer(&out, v)),
            };
            out.push(Binder { name: l.name.clone(), ty, value: None });
        }
        out
    }

    /// `e`'s surface type under the part of `scope` it reads: the locals it
    /// mentions and those their types mention, each at its last binding.
    /// `None` where one of them is untyped or the oracle declines.
    fn infer(&self, scope: &[Binder], e: &Expr) -> Option<Ty> {
        let mut keep = vec![false; scope.len()];
        let mut changed = true;
        let live = |i: usize| !scope[i + 1..].iter().any(|c| c.name == scope[i].name);
        for i in 0..scope.len() {
            keep[i] = live(i) && measure::mentions_context(e, &scope[i].name);
        }
        while changed {
            changed = false;
            for i in 0..scope.len() {
                if keep[i] || !live(i) {
                    continue;
                }
                let needed = (0..scope.len()).any(|j| keep[j] && scope[j].ty.as_ref().is_some_and(|t| measure::mentions_ty(t, &scope[i].name)));
                if needed {
                    keep[i] = true;
                    changed = true;
                }
            }
        }
        let selected: Vec<Binder> = scope.iter().zip(&keep).filter(|(_, k)| **k).map(|(b, _)| b.clone()).collect();
        if selected.iter().any(|b| b.ty.is_none()) {
            return None;
        }
        self.tys.infer_local(self.decl, &[], &selected, e)
    }

    fn names(&mut self) -> (String, String, String, String) {
        self.next += 1;
        let (step, state) = if self.loops == 1 {
            ("step".to_string(), "State".to_string())
        } else {
            (format!("loop{}_step", self.next), format!("loop{}_State", self.next))
        };
        (
            format!("{}#{step}", self.decl.name),
            format!("{}#{state}", self.decl.name),
            format!("{}::{step}", self.decl.name),
            format!("{}::{state}", self.decl.name),
        )
    }

    /// One block: its statements in order, with the scope they extend.
    fn block(&mut self, mut b: Block, scope: &mut Vec<Local>) -> R<Block> {
        let mut stmts = Vec::with_capacity(b.stmts.len());
        // A loop's name, the number of locals in its state, for its `\0proj`s.
        let mut results: Vec<(String, bool)> = Vec::new();
        let all = std::mem::take(&mut b.stmts);
        // Whether a loop follows statement `i`, which then needs every local
        // before it typed.
        let later: Vec<bool> = (0..all.len())
            .map(|i| all[i + 1..].iter().any(|s| matches!(s, Stmt::Let { expr, .. } if contains_loop(expr))) || contains_loop(&b.result))
            .collect();
        for (i, s) in all.into_iter().enumerate() {
            match s {
                Stmt::Let { name, ty, expr, span, opaque } => {
                    let expr = if let Some(read) = self.proj(&expr, &results) {
                        read
                    } else if loop_parts(&expr).is_some() {
                        let (lowered, single) = self.lift(&expr, scope)?;
                        results.push((name.clone(), single));
                        lowered
                    } else {
                        self.expr(expr, scope)?
                    };
                    scope.push(Local { name: name.clone(), written: ty.clone(), value: Some(expr.clone()) });
                    stmts.push(Stmt::Let { name, ty, expr, span, opaque });
                }
                other => {
                    if let Stmt::LetRecord { span, .. } | Stmt::LetCode { span, .. } = &other
                        && later[i]
                    {
                        return err("a `for` after a destructuring `let` is not supported yet: bind the record whole", *span);
                    }
                    stmts.push(other);
                }
            }
        }
        b.stmts = stmts;
        let result = std::mem::replace(&mut *b.result, var("", b.span));
        *b.result = self.expr(result, scope)?;
        Ok(b)
    }

    /// `\0proj(#forN, v)`: the loop's state, or its field `v`.
    fn proj(&self, e: &Expr, results: &[(String, bool)]) -> Option<Expr> {
        let ExprKind::App { head, args, .. } = &e.kind else { return None };
        if args.len() != 2 || !matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::PROJ) {
            return None;
        }
        let (ExprKind::Var(l), ExprKind::Var(v)) = (&args[0].kind, &args[1].kind) else { return None };
        let (_, single) = results.iter().rev().find(|(n, _)| n == l)?;
        let state = var(l, e.span);
        Some(if *single {
            state
        } else {
            Expr { kind: ExprKind::Dot { recv: Box::new(state), name: v.clone(), tyargs: vec![], args: None, named: vec![] }, span: e.span }
        })
    }

    /// The forms a loop may sit under: blocks, and the bodies of a
    /// statement form's joins.
    fn expr(&mut self, e: Expr, scope: &mut Vec<Local>) -> R<Expr> {
        if !contains_loop(&e) {
            return Ok(e);
        }
        let span = e.span;
        match e.kind {
            ExprKind::Block(b) => {
                let mut inner = scope.clone();
                Ok(Expr { kind: ExprKind::Block(Box::new(self.block(*b, &mut inner)?)), span })
            }
            ExprKind::Match { form, generated, scrut, eqbind, motive, arms } => {
                let mut out: Vec<Arm> = Vec::with_capacity(arms.len());
                for mut arm in arms {
                    if contains_loop(&arm.body) && (!arm.binders.is_empty() || eqbind.is_some()) {
                        return err(
                            "a `for` under a `match` arm that binds is not supported yet: move the loop \
                             out of the arm, or into a function of its own",
                            arm.body.span,
                        );
                    }
                    let mut inner = scope.clone();
                    arm.body = self.expr(arm.body, &mut inner)?;
                    out.push(arm);
                }
                Ok(Expr { kind: ExprKind::Match { form, generated, scrut, eqbind, motive, arms: out }, span })
            }
            _ => err("a `for` here is not supported yet: write it as a statement of the function's body", span),
        }
    }

    /// Lift one loop (module docs): returns its replacement and whether its
    /// state is a single local.
    fn lift(&mut self, e: &Expr, scope: &[Local]) -> R<(Expr, bool)> {
        let (iter, x, body, vars) = loop_parts(e).expect("a loop");
        let span = e.span;
        let typed = self.typed(scope);
        let ty_of = |n: &str| typed.iter().rev().find(|b| b.name == n);
        // The element type: a `for` iterates a `List` this round.
        let iter_ty = self.infer(&typed, iter);
        let elem = match iter_ty.as_ref().map(|t| &t.kind) {
            Some(TyKind::Named { name, args }) if (name == "List" || name.ends_with("::List")) && args.len() == 1 => {
                args[0].clone()
            }
            Some(_) => {
                return err("a `for` iterates a `List` for now (§5.2's other owners are not built yet)", iter.span);
            }
            None => {
                return err(
                    "the type of this `for`'s list could not be recovered, so its step cannot be named: \
                     annotate the locals it reads (`let xs: List<T> = …;`)",
                    iter.span,
                );
            }
        };
        let mut state_tys = Vec::new();
        for v in &vars {
            match ty_of(v).and_then(|b| b.ty.clone()) {
                Some(t) => state_tys.push(t),
                None => {
                    return err(
                        format!("the type of `{v}`, which this `for` assigns, could not be recovered: annotate \
                                 it, `let mut {v}: T = …;`"),
                        span,
                    );
                }
            }
        }
        // Captures, in scope order: the last binding of each name the body
        // mentions, neither the element nor the state.
        let whole = Expr { kind: ExprKind::Block(Box::new(body.clone())), span: body.span };
        let mut captures: Vec<(String, Ty)> = Vec::new();
        for (i, b) in typed.iter().enumerate() {
            if typed[i + 1..].iter().any(|c| c.name == b.name)
                || b.name == x.name
                || vars.contains(&b.name.as_str())
                || b.name.starts_with('#')
                || !measure::mentions_context(&whole, &b.name)
            {
                continue;
            }
            let Some(t) = b.ty.clone() else {
                return err(
                    format!("the type of `{}`, which this `for` reads, could not be recovered: annotate its \
                             `let`", b.name),
                    span,
                );
            };
            captures.push((b.name.clone(), t));
        }
        let (step, state, step_designed, state_designed) = self.names();
        let tyargs: Vec<Ty> = self.decl.tyvars.iter().map(|t| named_ty(&t.name, vec![], span)).collect();
        let single = vars.len() == 1;
        let state_ty = if single { state_tys[0].clone() } else { named_ty(&state, tyargs.clone(), span) };
        let s = "#s";
        // The step's telescope: the declaration's solver parameters, the
        // captures, the state, the element.
        let mut params: Vec<Param> = self.decl.params.iter().filter(|p| p.solver.is_some()).cloned().collect();
        params.extend(captures.iter().map(|(n, t)| param(n, t.clone(), span)));
        let mut body = body.clone();
        let end = body.result.span;
        if single {
            params.push(param(vars[0], state_ty.clone(), span));
            *body.result = var(vars[0], end);
        } else {
            params.push(param(s, state_ty.clone(), span));
            let reads: Vec<Stmt> = vars
                .iter()
                .map(|v| Stmt::Let {
                    name: v.to_string(),
                    ty: None,
                    expr: Expr {
                        kind: ExprKind::Dot { recv: Box::new(var(s, span)), name: v.to_string(), tyargs: vec![], args: None, named: vec![] },
                        span,
                    },
                    span,
                    opaque: false,
                })
                .collect();
            body.stmts.splice(0..0, reads);
            *body.result = call(var(&state, end), vars.iter().map(|v| var(v, end)).collect(), end);
            self.parts.push(Part::State(InductiveDecl {
                name: state.clone(),
                params: self.decl.tyvars.iter().map(|t| t.name.clone()).collect(),
                valparams: vec![],
                varies: None,
                ctors: vec![CtorDecl {
                    name: state.clone(),
                    fields: vars
                        .iter()
                        .zip(&state_tys)
                        .map(|(v, t)| FieldDecl { name: Some(v.to_string()), ty: t.clone(), default: None, span })
                        .collect(),
                    result: None,
                    span,
                }],
                is_record: true,
                is_codata: false,
                index: None,
                span,
            }));
            self.designations.push((state_designed, state.clone()));
        }
        params.push(param(&x.name, elem.clone(), span));
        self.parts.push(Part::Decl(Decl {
            kind: DeclKind::Fn,
            is_meta: false,
            is_evidence: false,
            value: false,
            elaborates: None,
            name: step.clone(),
            tyvars: self.decl.tyvars.clone(),
            params,
            result: state_ty.clone(),
            decreases: None,
            body,
            span,
        }));
        self.designations.push((step_designed, step.clone()));
        // `xs.foldl(λ (#s: S) (x: E) => f#step(c̄, #s, x), init)`.
        let mut args: Vec<Expr> = captures.iter().map(|(n, _)| var(n, span)).collect();
        args.push(var(s, span));
        args.push(var("#x", span));
        let lam = Expr {
            kind: ExprKind::Lam {
                binders: vec![
                    LamBinder { name: s.into(), ty: Some(state_ty.clone()), implicit: false, span },
                    LamBinder { name: "#x".into(), ty: Some(elem), implicit: false, span },
                ],
                body: Box::new(call(var(&step, span), args, span)),
            },
            span,
        };
        let init = if single { var(vars[0], span) } else { call(var(&state, span), vars.iter().map(|v| var(v, span)).collect(), span) };
        let fold = Expr {
            kind: ExprKind::Dot { recv: Box::new(iter.clone()), name: "foldl".into(), tyargs: vec![], args: Some(vec![lam, init]), named: vec![] },
            span,
        };
        Ok((fold, single))
    }
}

fn contains_loop(e: &Expr) -> bool {
    let mut found = false;
    crate::surface::walk_expr(e, &mut |x| found |= loop_parts(x).is_some());
    found
}

/// Lower a declaration whose body holds loops (module docs).
pub(crate) fn lower(decl: &Decl, tys: &dyn BinderTys) -> R<Family> {
    if decl.decreases.is_some() {
        return err("a `for` in a `decreases` function is not supported yet: lift the loop into a function of its own", decl.span);
    }
    let mut lift = Lift {
        decl,
        tys,
        loops: count_loops(&decl.body),
        next: 0,
        parts: Vec::new(),
        designations: Vec::new(),
    };
    let mut scope: Vec<Local> =
        decl.params.iter().map(|p| Local { name: p.name.clone(), written: Some(p.ty.clone()), value: None }).collect();
    let body = lift.block(decl.body.clone(), &mut scope)?;
    let mut parts = std::mem::take(&mut lift.parts);
    let span = decl.span;
    let mut head = var(&decl.name, span);
    if !decl.tyvars.is_empty() {
        head = Expr {
            kind: ExprKind::TyApp {
                head: Box::new(head),
                args: decl.tyvars.iter().map(|t| named_ty(&t.name, vec![], span)).collect(),
            },
            span,
        };
    }
    let lhs = Expr {
        kind: ExprKind::App {
            head: Box::new(head),
            args: decl.params.iter().map(|p| var(&p.name, span)).collect(),
            named: vec![],
            explicit: true,
            goal_oriented: false,
        },
        span,
    };
    let rhs = Expr { kind: ExprKind::Block(Box::new(body.clone())), span: body.span };
    let unfold = Decl {
        kind: DeclKind::Theorem,
        is_meta: false,
        is_evidence: false,
        value: false,
        elaborates: None,
        name: measure::unfold_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params: decl.params.clone(),
        result: Ty { kind: TyKind::Eq(Box::new(lhs), Box::new(rhs)), span },
        decreases: None,
        body: Block { stmts: vec![], result: Box::new(Expr { kind: ExprKind::Refl, span }), ons: vec![], span },
        span,
    };
    parts.push(Part::Decl(Decl { body, ..decl.clone() }));
    Ok(Family { parts, unfold, designations: lift.designations })
}
