//! `for x in xs { body }` in pure code (docs/language/sequencing-surface-design.md
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
//! A `while c decreases m { body }` arrives as the same marker over the
//! header `\0while(decide_bit<c>(), m)` and lifts to `fn f#run(c̄, v̄) → S
//! decreases m`, the body hoisted above `match h: decide_bit<c>() { True =>
//! f#run(c̄, v̄'), False => v̄ }` in SSA form ([`crate::alpha::ssa`]), and the
//! loop to `f#run(c̄, v̄)`; designated `f::run` and `f::run_unfold` (§5.3).
//!
//! Nothing here is trusted: a wrong capture or type is refused by the
//! checker at the generated declaration.

use heather_syntax::{
    Arm, Block, CtorDecl, Decl, DeclKind, Expr, ExprKind, FieldDecl, InductiveDecl, LamBinder, MatchForm, Param,
    ParamOrigin, Pat, Span, Stmt, Ty, TyKind,
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
    /// The counted loops lifted as `mut self` methods of the declaration's
    /// receiver type (minted names, in the order they are elaborated): a
    /// prefix generator over the declaration runs over each of them too.
    pub(crate) methods: Vec<String>,
    /// `f_unfold : f(x̄) = <the lowered body>` by `refl` (§7.1), attempted
    /// after the family and skipped, with its reason recorded, if refused.
    /// None for a `decreases` function, whose equation the measure
    /// lowering writes.
    pub(crate) unfold: Option<Decl>,
    pub(crate) designations: Vec<(String, String)>,
}

fn loop_parts(e: &Expr) -> Option<(&Expr, &LamBinder, &Block, Vec<&str>)> {
    let ExprKind::App { head, args, .. } = &e.kind else { return None };
    if args.len() < 2 || !matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::LOOP) {
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

/// Does the declaration's body hold a `for` over a range of numerals?
pub(crate) fn has_numeral_range(decl: &Decl) -> bool {
    let e = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span: decl.body.span };
    let mut found = false;
    crate::surface::walk_expr(&e, &mut |x| {
        if let Some((iter, ..)) = loop_parts(x)
            && let Some((lo, hi)) = range_parts(iter)
        {
            found |= matches!(lo.kind, ExprKind::Num(_)) && matches!(hi.kind, ExprKind::Num(_));
        }
    });
    found
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

/// A declaration's name past its type's qualifier, `f` of `T::f`.
fn base_name(name: &str) -> &str { name.rsplit("::").next().unwrap_or(name) }

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
    /// Whether a range of numerals counts words (`u64`) rather than
    /// listing `Nat`s ([`Ranges`]).
    ranges: Ranges,
    /// The counted loops lifted as `mut self` methods, by minted name.
    methods: Vec<String>,
    /// Counted loops lifted so far, for their tests' private names.
    next_if: usize,
    loops: usize,
    next: usize,
    parts: Vec<Part>,
    designations: Vec<(String, String)>,
}

/// How a loop's result holds its state, for the `\0proj`s after it: the
/// one local itself, a field of `f#State` per local, or a `Mutated` whose
/// `after` is the receiver of a `mut self` method and whose `value` is the
/// one other local beside it.
#[derive(Clone)]
enum Shape {
    Single,
    Record,
    Mutated { receiver: String },
}

impl Shape {
    fn of(single: bool) -> Shape { if single { Shape::Single } else { Shape::Record } }
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

    /// The declaration's solver parameters, which a lifted loop takes
    /// first: a body's operators may resolve through them.
    fn solver_params(&self) -> Vec<Param> { self.decl.params.iter().filter(|p| p.solver.is_some()).cloned().collect() }

    /// The declaration's implicit parameters that the types of a loop's
    /// captures or state mention (`{n: u64}` of a receiver at `Bytes(n)`),
    /// captured too, first: a lifted loop takes them as it takes any
    /// capture, so its calls and its own recursion pass them.
    fn implicit_captures<'t>(&self, captures: &mut Vec<(String, Ty)>, tys: impl Iterator<Item = &'t Ty>) {
        let tys: Vec<Ty> = tys.cloned().chain(captures.iter().map(|(_, t)| t.clone())).collect();
        let found: Vec<(String, Ty)> = self
            .decl
            .params
            .iter()
            .filter(|p| p.implicit && p.solver.is_none() && p.default.is_none())
            .filter(|p| !captures.iter().any(|(n, _)| *n == p.name))
            .filter(|p| tys.iter().any(|t| measure::mentions_ty(t, &p.name)))
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect();
        captures.splice(0..0, found);
    }

    /// The receiver of a `mut self` method when it is among a loop's state
    /// with at most one other local beside it (the position of that local
    /// in `vars`): such a loop is lifted as a `mut self` method of the
    /// receiver's type, which returns the other local
    /// (docs/language/sequencing-surface-design.md §22).
    fn receiver_in(&self, vars: &[&str]) -> Option<(Param, Option<usize>)> {
        if !matches!(&self.decl.result.kind, TyKind::Named { name, .. } if name == heather_syntax::MUTATED_RECORD) {
            return None;
        }
        let r = self.decl.params.iter().find(|p| p.is_self)?;
        let at = vars.iter().position(|v| *v == r.name)?;
        match vars.len() {
            1 => Some((r.clone(), None)),
            2 => Some((r.clone(), Some(1 - at))),
            _ => None,
        }
    }

    /// The name of a loop lifted as a method of the receiver's type,
    /// `T::f_loop`, or `T::f_loop2`, … where `f` has several.
    fn method_name(&self) -> String {
        if self.loops == 1 { format!("{}_loop", self.decl.name) } else { format!("{}_loop{}", self.decl.name, self.next) }
    }

    /// The minted and designed names of the next loop's function (`step`
    /// for a `for`, `run` for a `while`) and state record (§5.4).
    fn names(&mut self, word: &str) -> (String, String, String, String) {
        self.next += 1;
        let (step, state) = if self.loops == 1 {
            (word.to_string(), "State".to_string())
        } else {
            (format!("loop{}_{word}", self.next), format!("loop{}_State", self.next))
        };
        (
            format!("{}#{step}", self.decl.name),
            format!("{}#{state}", self.decl.name),
            format!("{}::{step}", self.decl.name),
            format!("{}::{state}", self.decl.name),
        )
    }

    /// One block: its statements in order, with the scope they extend.
    fn block(&mut self, b: Block, scope: &mut Vec<Local>) -> R<Block> {
        self.block_after(b, scope, Vec::new())
    }

    /// [`Self::block`] with the loops before it already lowered: `results`
    /// names them for the `\0proj`s in `b` (the rest of a body after a loop
    /// that may `return`, which the parser nests in `\0after`).
    fn block_after(&mut self, mut b: Block, scope: &mut Vec<Local>, mut results: Vec<(String, Shape)>) -> R<Block> {
        let mut stmts = Vec::with_capacity(b.stmts.len());
        // `results`: a loop's name, whether its state is a single local, for
        // its `\0proj`s. With an early exit, the state is read through
        // `#forN#s := #forN.state(init)`, bound once right after the loop.
        let all = std::mem::take(&mut b.stmts);
        // Whether a loop follows statement `i`, which then needs every local
        // before it typed.
        let later: Vec<bool> = (0..all.len())
            .map(|i| all[i + 1..].iter().any(|s| matches!(s, Stmt::Let { expr, .. } if contains_loop(expr))) || contains_loop(&b.result))
            .collect();
        for (i, s) in all.into_iter().enumerate() {
            match s {
                Stmt::Let { name, ty, expr, span, opaque } => {
                    let mut alias = None;
                    let expr = if let Some(read) = self.proj(&expr, &results) {
                        read
                    } else if loop_parts(&expr).is_some() {
                        let (lowered, shape, exit_init) = self.lift(&expr, scope)?;
                        match exit_init {
                            Some(init) => {
                                let s = format!("{name}#s");
                                results.push((s.clone(), shape));
                                alias = Some((s, init));
                            }
                            None => results.push((name.clone(), shape)),
                        }
                        lowered
                    } else {
                        self.expr(expr, scope)?
                    };
                    scope.push(Local { name: name.clone(), written: ty.clone(), value: Some(expr.clone()) });
                    stmts.push(Stmt::Let { name: name.clone(), ty, expr, span, opaque });
                    if let Some((s, init)) = alias {
                        let read = Expr {
                            kind: ExprKind::Dot { recv: Box::new(var(&name, span)), name: "state".into(), tyargs: vec![], args: Some(vec![init]), named: vec![] },
                            span,
                        };
                        scope.push(Local { name: s.clone(), written: None, value: Some(read.clone()) });
                        stmts.push(Stmt::Let { name: s, ty: None, expr: read, span, opaque: false });
                    }
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
        *b.result = match after_parts(&result) {
            // The loop's `Return` is the function's value; anything else
            // runs the rest of the body.
            Some((l, rest)) => {
                let span = result.span;
                let rest = match &rest.kind {
                    ExprKind::Block(rb) => {
                        let mut inner = scope.clone();
                        let rb = self.block_after((**rb).clone(), &mut inner, results.clone())?;
                        Expr { span: rest.span, kind: ExprKind::Block(Box::new(rb)) }
                    }
                    _ => self.expr(rest.clone(), scope)?,
                };
                Expr {
                    kind: ExprKind::Match {
                        form: MatchForm::Match,
                        generated: true,
                        scrut: Box::new(var(&l, span)),
                        eqbind: None,
                        motive: None,
                        arms: vec![
                            Arm { ctor: "Return".into(), default: false, binders: vec![Pat::Var { name: "#r".into(), span }], body: var("#r", span), span },
                            Arm { ctor: "_".into(), default: true, binders: vec![], body: rest, span },
                        ],
                    },
                    span,
                }
            }
            None => self.expr(result, scope)?,
        };
        Ok(b)
    }

    /// `\0proj(#forN, v)`: the loop's state, or its field `v`.
    fn proj(&self, e: &Expr, results: &[(String, Shape)]) -> Option<Expr> {
        let ExprKind::App { head, args, .. } = &e.kind else { return None };
        if args.len() != 2 || !matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::PROJ) {
            return None;
        }
        let (ExprKind::Var(l), ExprKind::Var(v)) = (&args[0].kind, &args[1].kind) else { return None };
        let (found, shape) = results.iter().rev().find(|(n, _)| n == l || *n == format!("{l}#s"))?;
        let state = var(found, e.span);
        let field = |name: &str| Expr {
            kind: ExprKind::Dot { recv: Box::new(state.clone()), name: name.to_string(), tyargs: vec![], args: None, named: vec![] },
            span: e.span,
        };
        Some(match shape {
            Shape::Single => state.clone(),
            Shape::Record => field(v),
            Shape::Mutated { receiver } => field(if v == receiver { "after" } else { "value" }),
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
                    // A test's own equation, which a lifted loop's `if` binds
                    // under a private name, is read by no source.
                    let private = eqbind.as_deref().is_some_and(|n| n.starts_with("__"));
                    if contains_loop(&arm.body) && (!arm.binders.is_empty() || (eqbind.is_some() && !private)) {
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
    fn lift(&mut self, e: &Expr, scope: &[Local]) -> R<(Expr, Shape, Option<Expr>)> {
        let (iter, x, body, vars) = loop_parts(e).expect("a loop");
        if let Some((cond, measure, invariant)) = while_parts(iter) {
            return self.lift_while(e, scope, cond, measure, invariant);
        }
        if let Some((lo, hi)) = range_parts(iter) {
            let typed = self.typed(scope);
            if let Some(word) = self.word_range(&typed, &lo, &hi) {
                return self.lift_counted(e, scope, lo, hi, word);
            }
        }
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
        self.implicit_captures(&mut captures, state_tys.iter());
        let (step, state, step_designed, state_designed) = self.names("step");
        let tyargs: Vec<Ty> = self.decl.tyvars.iter().map(|t| named_ty(&t.name, vec![], span)).collect();
        let single = vars.len() == 1;
        let state_ty = if single { state_tys[0].clone() } else { named_ty(&state, tyargs.clone(), span) };
        let s = "#s";
        // The step's telescope: the declaration's solver parameters, the
        // captures, the state, the element.
        let mut params: Vec<Param> = self.solver_params();
        params.extend(captures.iter().map(|(n, t)| param(n, t.clone(), span)));
        let mut body = body.clone();
        let end = body.result.span;
        // A body that exits early ends in a tree of `\0next`/`\0brk`/`\0ret`
        // leaves (the parser's tail lowering): the step returns `ForStep`.
        let exits = has_leaf(&body.result, &[heather_syntax::NEXT, heather_syntax::BRK, heather_syntax::RET]);
        let returns = has_leaf(&body.result, &[heather_syntax::RET]);
        // No locals (a stateless search that `return`s): the state is the
        // record with no fields, its one value the constructor itself.
        let state_of = |args: Vec<Expr>, at: Span| if single { args.into_iter().next().expect("one local") } else if args.is_empty() { var(&state, at) } else { call(var(&state, at), args, at) };
        if exits {
            let result = std::mem::replace(&mut *body.result, var("", end));
            *body.result = leaves(result, &|m, args, at| {
                let ctor = match m {
                    _ if m == heather_syntax::NEXT => "ForStep::Next",
                    _ if m == heather_syntax::BRK => "ForStep::Break",
                    _ => return call(var("ForStep::Return", at), args, at),
                };
                call(var(ctor, at), vec![state_of(args, at)], at)
            });
        }
        if single {
            params.push(param(vars[0], state_ty.clone(), span));
            if !exits {
                *body.result = var(vars[0], end);
            }
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
            if !exits {
                *body.result = call(var(&state, end), vars.iter().map(|v| var(v, end)).collect(), end);
            }
            self.push_state(&state, &vars, &state_tys, span);
            self.designations.push((state_designed, state.clone()));
        }
        params.push(param(&x.name, elem.clone(), span));
        // `ForStep<S, R>`: `R` is the function's result where the body may
        // `return`, and otherwise never built, so the state's own type.
        let step_ty = if exits {
            let r = if returns { self.decl.result.clone() } else { state_ty.clone() };
            named_ty("ForStep", vec![state_ty.clone(), r], span)
        } else {
            state_ty.clone()
        };
        self.parts.push(Part::Decl(Decl {
            kind: DeclKind::Fn,
            is_meta: false,
            is_evidence: false,
            is_interface: false, partial: None,
            value: false,
            elaborates: None,
            name: step.clone(),
            tyvars: self.decl.tyvars.clone(),
            params,
            result: step_ty,
            decreases: None,
            unfolding: Vec::new(),
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
        let init = state_of(vars.iter().map(|v| var(v, span)).collect(), span);
        let member = if exits { "for_in" } else { "foldl" };
        let fold = Expr {
            kind: ExprKind::Dot { recv: Box::new(iter.clone()), name: member.into(), tyargs: vec![], args: Some(vec![lam, init.clone()]), named: vec![] },
            span,
        };
        Ok((fold, Shape::of(single), exits.then_some(init)))
    }
}

impl Lift<'_> {
    /// Lift one `while c decreases m { body }` (§5.3): the recursive
    /// `f#run(c̄, v̄) → S decreases m { match __while_h: decide_bit<c>() { True =>
    /// { body; f#run(c̄, v̄) }, False => v̄ } }`, the state as separate
    /// parameters so the measure obligation reads them plainly, its result
    /// the state as a `for`'s step returns it. The match's equation is what
    /// the obligation's `omega` reads the condition from.
    fn lift_while(&mut self, e: &Expr, scope: &[Local], cond: &Expr, measure: &Expr, invariant: Option<&Expr>) -> R<(Expr, Shape, Option<Expr>)> {
        let (_, x, body, vars) = loop_parts(e).expect("a loop");
        let span = e.span;
        let typed = self.typed(scope);
        let ty_of = |n: &str| typed.iter().rev().find(|b| b.name == n);
        let mut state_tys = Vec::new();
        for v in &vars {
            match ty_of(v).and_then(|b| b.ty.clone()) {
                Some(t) => state_tys.push(t),
                None => {
                    return err(
                        format!("the type of `{v}`, which this `while` assigns, could not be recovered: annotate \
                                 it, `let mut {v}: T = …;`"),
                        span,
                    );
                }
            }
        }
        // Captures: what the body, the condition or the measure reads.
        let whole = Expr { kind: ExprKind::Block(Box::new(body.clone())), span: body.span };
        let mut captures: Vec<(String, Ty)> = Vec::new();
        for (i, b) in typed.iter().enumerate() {
            if typed[i + 1..].iter().any(|c| c.name == b.name)
                || b.name == x.name
                || vars.contains(&b.name.as_str())
                || b.name.starts_with('#')
                || !(measure::mentions_context(&whole, &b.name)
                    || measure::mentions_context(cond, &b.name)
                    || measure::mentions_context(measure, &b.name)
                    || invariant.is_some_and(|p| measure::mentions_context(p, &b.name)))
            {
                continue;
            }
            let Some(t) = b.ty.clone() else {
                return err(
                    format!("the type of `{}`, which this `while` reads, could not be recovered: annotate its \
                             `let`", b.name),
                    span,
                );
            };
            captures.push((b.name.clone(), t));
        }
        self.implicit_captures(&mut captures, state_tys.iter());
        // The invariant's facts: parameters `__invN_k: ∥P_k∥` after the
        // state, each found (`bv_omega`) where the loop starts and where a
        // round recurs, and assumed in the body (a search for a condition
        // releases them). Squashed, so two proofs of one are one, as the
        // companions of a `decreases` function need.
        self.next_if += 1;
        let facts: Vec<Param> = invariant_facts(invariant)
            .into_iter()
            .enumerate()
            .map(|(k, p)| param(&format!("__inv{}_{k}", self.next_if), Ty { span: p.span, kind: TyKind::Squash(Box::new(p)) }, span))
            .collect();
        let found = |at: Span| -> Vec<Expr> { facts.iter().map(|_| var("bv_omega", at)).collect() };
        // At a `mut self` receiver with one other local, the loop is a
        // method of the receiver's type returning that local.
        if let Some((r, Some(k))) = self.receiver_in(&vars) {
            return self.lift_while_method(span, body, captures, r, (vars[k], state_tys[k].clone()), cond, measure, facts);
        }
        let (run, state, run_designed, state_designed) = self.names("run");
        let tyargs: Vec<Ty> = self.decl.tyvars.iter().map(|t| named_ty(&t.name, vec![], span)).collect();
        let single = vars.len() == 1;
        let state_ty = if single { state_tys[0].clone() } else { named_ty(&state, tyargs, span) };
        let state_of = |at: Span| {
            let args: Vec<Expr> = vars.iter().map(|v| var(v, at)).collect();
            if single { args.into_iter().next().expect("one local") } else { call(var(&state, at), args, at) }
        };
        if !single {
            self.push_state(&state, &vars, &state_tys, span);
            self.designations.push((state_designed, state.clone()));
        }
        let mut params: Vec<Param> = self.solver_params();
        params.extend(captures.iter().map(|(n, t)| param(n, t.clone(), span)));
        params.extend(vars.iter().zip(&state_tys).map(|(v, t)| param(v, t.clone(), span)));
        params.extend(facts.iter().cloned());
        let args = |at: Span| -> Vec<Expr> {
            captures.iter().map(|(n, _)| var(n, at)).chain(vars.iter().map(|v| var(v, at))).chain(found(at)).collect()
        };
        // The body runs before the condition's match, in SSA form, so the
        // condition placed after its `let`s still reads the parameters (the
        // `decreases` lowering deshadows on its own, `alpha::deshadow`). Hoisted
        // above the match, the lets are what every arm sees; the `False` arm
        // ignores them (the body is pure), and the match's equation is about
        // the parameters, which the obligation compares.
        let mut again = body.clone();
        let end = again.result.span;
        // The self-call by its base name: a member recurses under it, and a
        // qualified one is not yet in scope while the member is checked.
        *again.result = call(var(base_name(&run), end), args(end), end);
        let telescope: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
        crate::alpha::ssa(&mut again, &telescope);
        let next = std::mem::replace(&mut *again.result, var("", end));
        *again.result = self.tested(cond, next, &|| state_of(span), span);
        self.parts.push(Part::Decl(Decl {
            kind: DeclKind::Fn,
            is_meta: false,
            is_interface: false, partial: None,
            unfolding: Vec::new(),
            is_evidence: false,
            value: false,
            elaborates: None,
            name: run.clone(),
            tyvars: self.decl.tyvars.clone(),
            params,
            result: state_ty,
            decreases: Some(measure.clone()),
            body: again,
            span,
        }));
        // A prefix generator over the declaration runs over the loop too, so
        // a `runtime fn`'s loop is compiled and its call can be; by its
        // designed name, which a lookup resolves (a minted one has a `#`).
        self.methods.push(run_designed.clone());
        // A `decreases` function's equation, `f#run_unfold`, is a member
        // proofs cite too (§7.3).
        self.designations.push((measure::unfold_name(&run_designed), measure::unfold_name(&run)));
        self.designations.push((run_designed, run.clone()));
        Ok((call(var(&run, span), args(span), span), Shape::of(single), None))
    }

    /// A `while` whose state is the receiver `r` of a `mut self` method and
    /// one other local `o`: the method `T::f_loop(mut self r, c̄, o) →
    /// Mutated<T, O> decreases m { if c { body; r.f_loop(c̄, o′) } else {
    /// Mutated(r, o) } }`, the body under the test (not hoisted above it,
    /// as a pure `while`'s is: a store into the receiver may not run where
    /// the condition fails), and the loop the `Mutated` its call returns.
    /// The test is spelled as a `for` over words spells its own, so a search
    /// in the body reads the condition.
    #[allow(clippy::too_many_arguments)]
    fn lift_while_method(
        &mut self,
        span: Span,
        body: &Block,
        mut captures: Vec<(String, Ty)>,
        r: Param,
        (o, o_ty): (&str, Ty),
        cond: &Expr,
        measure: &Expr,
        facts: Vec<Param>,
    ) -> R<(Expr, Shape, Option<Expr>)> {
        let _ = self.names("run");
        let run = self.method_name();
        let method = run.rsplit("::").next().unwrap_or(&run).to_string();
        let mut params: Vec<Param> = self.solver_params();
        // The receiver first, as a function over a span takes its span,
        // after only the captures its type names (`n` of `Bytes(n)`).
        let named = named_first(&mut captures, &r.ty);
        params.extend(captures[..named].iter().map(|(n, t)| param(n, t.clone(), span)));
        params.push(Param { is_self: true, ..param(&r.name, r.ty.clone(), span) });
        params.extend(captures[named..].iter().map(|(n, t)| param(n, t.clone(), span)));
        params.push(param(o, o_ty.clone(), span));
        params.extend(facts.iter().cloned());
        let dot = |args: Vec<Expr>, at: Span| Expr {
            kind: ExprKind::Dot { recv: Box::new(var(&r.name, at)), name: method.clone(), tyargs: vec![], args: Some(args), named: vec![] },
            span: at,
        };
        let args = |at: Span| -> Vec<Expr> {
            captures
                .iter()
                .map(|(n, _)| var(n, at))
                .chain(std::iter::once(var(o, at)))
                .chain(facts.iter().map(|_| var("bv_omega", at)))
                .collect()
        };
        // At the recursion, each invariant fact is a `let` of its own at the
        // end of the body, proved once there and passed by name: a search
        // left in the call's arguments runs again at each of the call's
        // elaborations.
        let next_facts: Vec<String> = (0..facts.len()).map(|k| format!("__inv_next{}_{k}", self.next_if)).collect();
        let recur_args = |at: Span| -> Vec<Expr> {
            captures
                .iter()
                .map(|(n, _)| var(n, at))
                .chain(std::iter::once(var(o, at)))
                .chain(next_facts.iter().map(|f| var(f, at)))
                .collect()
        };
        let mut again = body.clone();
        let end = again.result.span;
        *again.result = marked(heather_syntax::MUTATED_WHOLE, dot(recur_args(end), end), end);
        // The body's claimed method calls on the receiver rebind it as plain
        // `let`s, and every rebinding gets a fresh name (SSA): the
        // condition's equation, which reads the receiver the method is
        // called with, then names no binder the body shadows.
        again.stmts = measure::rebind_marked(&again.stmts, end, false).map_err(|m| crate::ElabError::Elab { msg: m, span })?;
        let telescope: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
        let bound_at: Vec<(usize, String)> = again
            .stmts
            .iter()
            .enumerate()
            .filter_map(|(i, st)| match st {
                Stmt::Let { name, .. } if name == &r.name || name == o => Some((i, name.clone())),
                _ => None,
            })
            .collect();
        crate::alpha::ssa(&mut again, &telescope);
        // The state's names at the end of the body, after SSA.
        let mut latest: Vec<(String, String)> = vec![(r.name.clone(), r.name.clone()), (o.to_string(), o.to_string())];
        for (i, was) in bound_at {
            if let Stmt::Let { name, .. } = &again.stmts[i]
                && let Some(entry) = latest.iter_mut().find(|(w, _)| *w == was)
            {
                entry.1 = name.clone();
            }
        }
        for (fact, next) in facts.iter().zip(&next_facts) {
            let ty = latest.iter().fold(fact.ty.clone(), |t, (was, now)| {
                if was == now { t } else { measure::subst_surface_ty(&t, was, &var(now, end)) }
            });
            let inner = match &ty.kind { TyKind::Squash(p) => (**p).clone(), _ => ty.clone() };
            let head = Expr { kind: ExprKind::TyApp { head: Box::new(var("bitvec_omega::found_fact", end)), args: vec![inner] }, span: end };
            let found = call(head, vec![], end);
            again.stmts.push(Stmt::Let { name: next.clone(), ty: Some(ty), expr: found, span: end, opaque: false });
        }
        let done = || call(var(heather_syntax::MUTATED_RECORD, span), vec![var(&r.name, span), var(o, span)], span);
        let branch = self.tested(cond, Expr { kind: ExprKind::Block(Box::new(again)), span: body.span }, &done, span);
        let result = Ty { kind: TyKind::Named { name: heather_syntax::MUTATED_RECORD.into(), args: vec![r.ty.clone(), o_ty] }, span };
        self.parts.push(Part::Decl(Decl {
            kind: DeclKind::Fn,
            is_meta: false,
            is_interface: false,
            partial: None,
            unfolding: Vec::new(),
            is_evidence: false,
            value: false,
            elaborates: None,
            name: run.clone(),
            tyvars: self.decl.tyvars.clone(),
            params,
            result,
            decreases: Some(measure.clone()),
            body: Block { stmts: vec![], result: Box::new(branch), ons: vec![], span },
            span,
        }));
        self.methods.push(run);
        Ok((marked(heather_syntax::MUTATED_WHOLE, dot(args(span), span), span), Shape::Mutated { receiver: r.name.clone() }, None))
    }

    /// `match __while_hN: c₁ { True => match … cₖ { True => then, False
    /// => otherwise }, False => otherwise }`: a `while`'s condition tested
    /// conjunct by conjunct ([`tests_of`]), each match's equation in scope
    /// for the tests after it and for the body.
    fn tested(&mut self, cond: &Expr, then: Expr, otherwise: &dyn Fn() -> Expr, span: Span) -> Expr {
        let mut out = then;
        for mut test in tests_of(cond).into_iter().rev() {
            // An element read in the test (`key < s[j - 1]`) is bound by a
            // `let` just before it: in the proposition it would be part of
            // a type, whose found proof every copy of that type searches
            // for again.
            let mut reads = Vec::new();
            if let ExprKind::App { head, .. } = &mut test.kind
                && let ExprKind::TyApp { args: tys, .. } = &mut head.kind
                && let [Ty { kind: TyKind::OfExpr(prop), .. }] = tys.as_mut_slice()
            {
                crate::alpha::walk_expr_mut(prop, &mut |x| {
                    if !matches!(x.kind, ExprKind::Index { .. }) {
                        return false;
                    }
                    self.next_if += 1;
                    let name = format!("__while_read{}", self.next_if);
                    let read = std::mem::replace(x, var(&name, x.span));
                    reads.push(Stmt::Let { name, ty: None, expr: read, span, opaque: false });
                    true
                });
            }
            self.next_if += 1;
            out = Expr {
                kind: ExprKind::Match {
                    form: MatchForm::Match,
                    generated: true,
                    scrut: Box::new(test),
                    eqbind: Some(format!("__while_h{}", self.next_if)),
                    motive: None,
                    arms: vec![
                        Arm { ctor: "True".into(), default: false, binders: vec![], body: out, span },
                        Arm { ctor: "False".into(), default: false, binders: vec![], body: otherwise(), span },
                    ],
                },
                span,
            };
            if !reads.is_empty() {
                out = Expr { kind: ExprKind::Block(Box::new(Block { stmts: reads, result: Box::new(out), ons: vec![], span })), span };
            }
        }
        out
    }

    /// `record f#State { v₁: T₁, … }`, the state of a loop with several locals.
    fn push_state(&mut self, state: &str, vars: &[&str], tys: &[Ty], span: Span) {
        self.parts.push(Part::State(InductiveDecl {
            name: state.to_string(),
            params: self.decl.tyvars.iter().map(|t| t.name.clone()).collect(),
            valparams: vec![],
            varies: None,
            ctors: vec![CtorDecl {
                name: state.to_string(),
                fields: vars
                    .iter()
                    .zip(tys)
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
    }
}

/// How a `for` over a range of numerals, `for i in 0..n`, counts: through
/// a list of `Nat`s (§17), or as a word (§21). A range whose bounds are
/// words counts words either way.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Ranges {
    Lists,
    Words,
}

/// `a..b` as the parser writes it in a `for` header (§17): `List::range(b)`
/// for `0..b`, `List::range_from(a, b - a)` otherwise. The bounds.
fn range_parts(e: &Expr) -> Option<(Expr, Expr)> {
    let ExprKind::App { head, args, named, .. } = &e.kind else { return None };
    let ExprKind::Var(f) = &head.kind else { return None };
    if !named.is_empty() {
        return None;
    }
    match (f.as_str(), args.as_slice()) {
        ("List::range", [hi]) => Some((Expr { kind: ExprKind::Num(heather_numeral::Numeral::ZERO), span: e.span }, hi.clone())),
        ("List::range_from", [lo, len]) => {
            let ExprKind::App { head: minus, args: diff, .. } = &len.kind else { return None };
            if !matches!(&minus.kind, ExprKind::OpSymbol { symbol, .. } if symbol == "-") {
                return None;
            }
            match diff.as_slice() {
                [hi, lo2] if lo2.span == lo.span && format!("{lo2:?}") == format!("{lo:?}") => Some((lo.clone(), hi.clone())),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Is `t` a fixed-width word, `u64` or `BitVec(w)`?
fn is_word_ty(t: &Ty) -> bool {
    match &t.kind {
        TyKind::Named { name, args } => {
            let base = name.rsplit("::").next().unwrap_or(name);
            (args.is_empty() && matches!(base, "u8" | "u16" | "u32" | "u64")) || base == "BitVec"
        }
        TyKind::OfExpr(e) => match &e.kind {
            ExprKind::App { head, .. } => matches!(&head.kind, ExprKind::Var(n) if n.rsplit("::").next() == Some("BitVec")),
            ExprKind::Var(n) => matches!(n.rsplit("::").next(), Some("u8" | "u16" | "u32" | "u64")),
            _ => false,
        },
        _ => false,
    }
}

fn op(sym: &str, args: Vec<Expr>, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App {
            head: Box::new(Expr { kind: ExprKind::OpSymbol { symbol: sym.into(), fixity: heather_syntax::OpFixity::Infix }, span }),
            args,
            named: vec![],
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

fn num(n: u64, span: Span) -> Expr { Expr { kind: ExprKind::Num(heather_numeral::Numeral::from_u64(n)), span } }

fn marked(marker: &str, e: Expr, span: Span) -> Expr { call(var(marker, span), vec![e], span) }

impl Lift<'_> {
    /// The word type a range over `lo..hi` counts, if it counts one: a
    /// bound's own type where it is a word, and `u64` for numerals under
    /// [`Ranges::Words`].
    fn word_range(&self, typed: &[Binder], lo: &Expr, hi: &Expr) -> Option<Ty> {
        let numeral = |e: &Expr| matches!(e.kind, ExprKind::Num(_));
        let mut found: Option<Ty> = None;
        for b in [lo, hi] {
            if numeral(b) {
                continue;
            }
            let t = self.infer(typed, b)?;
            if !is_word_ty(&t) {
                return None;
            }
            found.get_or_insert(t);
        }
        match found {
            Some(t) => Some(t),
            None if self.ranges == Ranges::Words => Some(named_ty("u64", vec![], lo.span)),
            None => None,
        }
    }

    /// Lift one `for i in lo..hi` over words (§21): a recursion that counts
    /// `i` from `lo` up to `hi`, its body under the test `i < hi`, so a proof
    /// the body needs about `i` (an index inside an array) is found from it.
    ///
    /// Where the loop's state is the receiver of a `mut self` method, the
    /// recursion is a `mut self` method of the receiver's type,
    /// `T::f#run(mut self x: T, c̄, i: W) → W decreases (hi - i).toNat() {
    /// if i < hi { body; x.f#run(c̄, i + 1) } else { i } }`, the shape a
    /// `runtime fn` of a laid record compiles as a loop; otherwise
    /// `f#run(c̄, v̄, i: W) → S`, returning the state.
    fn lift_counted(&mut self, e: &Expr, scope: &[Local], lo: Expr, hi: Expr, word: Ty) -> R<(Expr, Shape, Option<Expr>)> {
        let (_, x, body, vars) = loop_parts(e).expect("a loop");
        let span = e.span;
        if has_leaf(&body.result, &[heather_syntax::NEXT, heather_syntax::BRK, heather_syntax::RET]) {
            return err("a `for` over words has no `break`, `continue` or `return` yet", span);
        }
        let typed = self.typed(scope);
        let ty_of = |n: &str| typed.iter().rev().find(|b| b.name == n);
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
        // Captures: what the body or the upper bound reads.
        let whole = Expr { kind: ExprKind::Block(Box::new(body.clone())), span: body.span };
        let mut captures: Vec<(String, Ty)> = Vec::new();
        for (i, b) in typed.iter().enumerate() {
            if typed[i + 1..].iter().any(|c| c.name == b.name)
                || b.name == x.name
                || vars.contains(&b.name.as_str())
                || b.name.starts_with('#')
                || !(measure::mentions_context(&whole, &b.name) || measure::mentions_context(&hi, &b.name))
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
        self.implicit_captures(&mut captures, state_tys.iter());
        // The receiver of a `mut self` method among the state, with at most
        // one other local beside it.
        let receiver = self.receiver_in(&vars);
        let named = match &receiver {
            Some((r, _)) => named_first(&mut captures, &r.ty),
            None => 0,
        };
        let (mut run, state, run_designed, state_designed) = self.names("run");
        // A method of the receiver's type is a member under a name of its
        // own, `T::f_loop` (`T::f_loop2` for a second loop): a generator
        // over it, and a proof about it, name it as they name `T::f`.
        if receiver.is_some() {
            run = self.method_name();
        }
        let tyargs: Vec<Ty> = self.decl.tyvars.iter().map(|t| named_ty(&t.name, vec![], span)).collect();
        let single = vars.len() == 1;
        let state_ty = if single { state_tys[0].clone() } else { named_ty(&state, tyargs, span) };
        if !single && receiver.is_none() {
            self.push_state(&state, &vars, &state_tys, span);
            self.designations.push((state_designed, state.clone()));
        }
        let i = var(&x.name, span);
        let mut params: Vec<Param> = self.solver_params();
        let mut again = body.clone();
        let end = again.result.span;
        let next = op("+", vec![i.clone(), num(1, end)], end);
        let capture_args = |at: Span| -> Vec<Expr> { captures.iter().map(|(n, _)| var(n, at)).collect() };
        let (result, recur, done, entry, shape) = match &receiver {
            Some((r, other)) => {
                // The receiver first, after only the captures its type names.
                params.extend(captures[..named].iter().map(|(n, t)| param(n, t.clone(), span)));
                params.push(Param { is_self: true, ..param(&r.name, r.ty.clone(), span) });
                params.extend(captures[named..].iter().map(|(n, t)| param(n, t.clone(), span)));
                let other = other.map(|k| (vars[k], state_tys[k].clone()));
                if let Some((o, t)) = &other {
                    params.push(param(o, t.clone(), span));
                }
                params.push(param(&x.name, word.clone(), span));
                // `x.f#run(c̄, o, i + 1)`, as a `mut self` method's own call
                // that ends its body (§19.3).
                let method = run.rsplit("::").next().unwrap_or(&run).to_string();
                let dot = |args: Vec<Expr>, at: Span| Expr {
                    kind: ExprKind::Dot { recv: Box::new(var(&r.name, at)), name: method.clone(), tyargs: vec![], args: Some(args), named: vec![] },
                    span: at,
                };
                let mut on = capture_args(end);
                on.extend(other.iter().map(|(o, _)| var(o, end)));
                on.push(next);
                let recur = marked(heather_syntax::MUTATED_WHOLE, dot(on, end), end);
                // The loop's value: the other local where there is one,
                // otherwise the count where it stopped.
                let (value, value_ty) = match &other {
                    Some((o, t)) => (var(o, span), t.clone()),
                    None => (i.clone(), word.clone()),
                };
                let done = call(var(heather_syntax::MUTATED_RECORD, span), vec![var(&r.name, span), value], span);
                let mut first = capture_args(span);
                first.extend(other.iter().map(|(o, _)| var(o, span)));
                first.push(lo.clone());
                // With the receiver alone, the loop is the receiver after
                // the call; with another local, the `Mutated` the call
                // returns, read back by its fields.
                let (entry, shape) = match &other {
                    None => (marked(heather_syntax::MUTATED_AFTER, dot(first, span), span), Shape::Single),
                    Some(_) => (marked(heather_syntax::MUTATED_WHOLE, dot(first, span), span), Shape::Mutated { receiver: r.name.clone() }),
                };
                let result = Ty { kind: TyKind::Named { name: heather_syntax::MUTATED_RECORD.into(), args: vec![r.ty.clone(), value_ty] }, span };
                self.methods.push(run.clone());
                (result, recur, done, entry, shape)
            }
            None => {
                params.extend(captures.iter().map(|(n, t)| param(n, t.clone(), span)));
                params.extend(vars.iter().zip(&state_tys).map(|(v, t)| param(v, t.clone(), span)));
                params.push(param(&x.name, word.clone(), span));
                let state_of = |at: Span| {
                    let args: Vec<Expr> = vars.iter().map(|v| var(v, at)).collect();
                    if single { args.into_iter().next().expect("one local") } else { call(var(&state, at), args, at) }
                };
                let mut on = capture_args(end);
                on.extend(vars.iter().map(|v| var(v, end)));
                on.push(next);
                let recur = call(var(base_name(&run), end), on, end);
                let mut first = capture_args(span);
                first.extend(vars.iter().map(|v| var(v, span)));
                first.push(lo.clone());
                self.methods.push(run_designed.clone());
                (state_ty.clone(), recur, state_of(span), call(var(&run, span), first, span), Shape::of(single))
            }
        };
        *again.result = recur;
        // `if i < hi { body; again } else { done }`, spelled as the parser
        // spells an `if` whose branches do not name its evidence: a match on
        // the comparison's bit with the bit's equation bound, which a search
        // in the body reads as the test (an index inside an array).
        let test = op("<", vec![i.clone(), hi.clone()], span);
        let proposition = Ty { kind: TyKind::OfExpr(Box::new(test.clone())), span };
        let bit = Expr {
            kind: ExprKind::App {
                head: Box::new(Expr {
                    kind: ExprKind::TyApp { head: Box::new(var("decide_bit", span)), args: vec![proposition] },
                    span,
                }),
                args: vec![],
                named: vec![],
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        self.next_if += 1;
        let branch = Expr {
            kind: ExprKind::Match {
                form: MatchForm::If,
                generated: false,
                scrut: Box::new(bit),
                eqbind: Some(format!("__if_bit_for{}", self.next_if)),
                motive: None,
                arms: vec![
                    Arm { ctor: "True".into(), default: false, binders: vec![], body: Expr { kind: ExprKind::Block(Box::new(again)), span: body.span }, span },
                    Arm { ctor: "False".into(), default: false, binders: vec![], body: done, span },
                ],
            },
            span,
        };
        let measure = Expr {
            kind: ExprKind::Dot { recv: Box::new(op("-", vec![hi.clone(), i.clone()], span)), name: "toNat".into(), tyargs: vec![], args: Some(vec![]), named: vec![] },
            span,
        };
        self.parts.push(Part::Decl(Decl {
            kind: DeclKind::Fn,
            is_meta: false,
            is_interface: false,
            partial: None,
            unfolding: Vec::new(),
            is_evidence: false,
            value: false,
            elaborates: None,
            name: run.clone(),
            tyvars: self.decl.tyvars.clone(),
            params,
            result,
            decreases: Some(measure),
            body: Block { stmts: vec![], result: Box::new(branch), ons: vec![], span },
            span,
        }));
        if receiver.is_none() {
            self.designations.push((measure::unfold_name(&run_designed), measure::unfold_name(&run)));
            self.designations.push((run_designed, run.clone()));
        }
        Ok((entry, shape, None))
    }
}

/// `\0while(cond, measure)`: a `while`'s header in a loop marker's list.
fn while_parts(e: &Expr) -> Option<(&Expr, &Expr, Option<&Expr>)> {
    let ExprKind::App { head, args, .. } = &e.kind else { return None };
    if !(2..=3).contains(&args.len()) || !matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::WHILE) {
        return None;
    }
    Some((&args[0], &args[1], args.get(2)))
}

/// Moves the captures `ty` names to the front, keeping each group's order,
/// and answers how many there are.
fn named_first(captures: &mut Vec<(String, Ty)>, ty: &Ty) -> usize {
    let (mut named, rest): (Vec<_>, Vec<_>) = std::mem::take(captures).into_iter().partition(|(n, _)| measure::mentions_ty(ty, n));
    let count = named.len();
    named.extend(rest);
    *captures = named;
    count
}

/// The conjuncts of a proposition `P ∧ (Q ∧ …)`, each its own.
fn conjuncts(t: &Ty) -> Vec<Ty> {
    match &t.kind {
        TyKind::Named { name, args } if args.len() == 2 && name.rsplit("::").next() == Some("And") => {
            let mut out = conjuncts(&args[0]);
            out.extend(conjuncts(&args[1]));
            out
        }
        _ => vec![t.clone()],
    }
}

/// A condition `decide_bit<P ∧ Q>()` as its tests in order,
/// `[decide_bit<P>(), decide_bit<Q>()]`: tested one after the other, each
/// under the ones before, so `0 < j ∧ s[j - 1] < key` reads `s[j - 1]`
/// where `0 < j` is known (Rust's `&&`). Any other condition is one test.
fn tests_of(cond: &Expr) -> Vec<Expr> {
    if let ExprKind::App { head, args, .. } = &cond.kind
        && args.is_empty()
        && let ExprKind::TyApp { head: bit, args: tys } = &head.kind
        && matches!(&bit.kind, ExprKind::Var(n) if n == "decide_bit")
        && let [t] = tys.as_slice()
    {
        // `a && b` (a `Bool`, its relations already decided): each operand
        // its own test, the first `&&` operand first.
        if let TyKind::OfExpr(inner) = &t.kind
            && let ExprKind::App { head: op, args: sides, .. } = &inner.kind
            && matches!(&op.kind, ExprKind::OpSymbol { symbol, .. } if symbol == "&&")
            && sides.len() == 2
        {
            return sides.iter().flat_map(|side| tests_of(side)).collect();
        }
        let parts = conjuncts(t);
        if parts.len() > 1 {
            return parts
                .into_iter()
                .map(|p| Expr {
                    kind: ExprKind::App {
                        head: Box::new(Expr { kind: ExprKind::TyApp { head: bit.clone(), args: vec![p] }, span: head.span }),
                        args: vec![],
                        named: vec![],
                        explicit: false,
                        goal_oriented: false,
                    },
                    span: cond.span,
                })
                .collect();
        }
    }
    vec![cond.clone()]
}

/// The invariant's facts, one squashed parameter each.
fn invariant_facts(invariant: Option<&Expr>) -> Vec<Ty> {
    match invariant.map(|e| &e.kind) {
        Some(ExprKind::TyLit(t)) => conjuncts(t),
        _ => vec![],
    }
}

/// `\0after(#forN, rest)`: the loop's name and the rest of the body.
fn after_parts(e: &Expr) -> Option<(String, &Expr)> {
    let ExprKind::App { head, args, .. } = &e.kind else { return None };
    if args.len() != 2 || !matches!(&head.kind, ExprKind::Var(n) if n == heather_syntax::AFTER) {
        return None;
    }
    let ExprKind::Var(l) = &args[0].kind else { return None };
    Some((l.clone(), &args[1]))
}

/// The marker of a leaf call `\0next(…)` and the like.
fn leaf_of<'e>(e: &'e Expr, markers: &[&str]) -> Option<(&'e str, &'e [Expr])> {
    let ExprKind::App { head, args, .. } = &e.kind else { return None };
    let ExprKind::Var(n) = &head.kind else { return None };
    markers.contains(&n.as_str()).then_some((n.as_str(), args.as_slice()))
}

fn has_leaf(e: &Expr, markers: &[&str]) -> bool {
    let mut found = false;
    crate::surface::walk_expr(e, &mut |x| found |= leaf_of(x, markers).is_some());
    found
}

/// Rewrite the leaves of a tail-lowered body: they sit in the result of a
/// block or of a `match` arm, and nowhere else.
fn leaves(e: Expr, f: &dyn Fn(&str, Vec<Expr>, Span) -> Expr) -> Expr {
    let markers = [heather_syntax::NEXT, heather_syntax::BRK, heather_syntax::RET];
    if let Some((m, args)) = leaf_of(&e, &markers) {
        return f(m, args.to_vec(), e.span);
    }
    let span = e.span;
    match e.kind {
        ExprKind::Block(mut b) => {
            let r = std::mem::replace(&mut *b.result, var("", span));
            *b.result = leaves(r, f);
            Expr { kind: ExprKind::Block(b), span }
        }
        ExprKind::Match { form, generated, scrut, eqbind, motive, arms } => {
            let arms = arms.into_iter().map(|mut a| { a.body = leaves(a.body, f); a }).collect();
            Expr { kind: ExprKind::Match { form, generated, scrut, eqbind, motive, arms }, span }
        }
        kind => Expr { kind, span },
    }
}

fn contains_loop(e: &Expr) -> bool {
    let mut found = false;
    crate::surface::walk_expr(e, &mut |x| found |= loop_parts(x).is_some());
    found
}

/// Lower a declaration whose body holds loops (module docs).
pub(crate) fn lower(decl: &Decl, tys: &dyn BinderTys, ranges: Ranges) -> R<Family> {
    // A `decreases` function's loops are lifted as any are (a loop nested
    // in a loop is one, in the function the outer loop lifts to); its
    // equation is the measure lowering's own `f_unfold`, not §7.1's.
    let measured = decl.decreases.is_some();
    let mut lift = Lift {
        decl,
        tys,
        ranges,
        methods: Vec::new(),
        next_if: 0,
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
        is_interface: false, partial: None,
        value: false,
        elaborates: None,
        name: measure::unfold_name(&decl.name),
        tyvars: decl.tyvars.clone(),
        params: decl.params.clone(),
        result: Ty { kind: TyKind::Eq(Box::new(lhs), Box::new(rhs)), span },
        decreases: None,
        unfolding: Vec::new(),
        body: Block { stmts: vec![], result: Box::new(Expr { kind: ExprKind::Refl, span }), ons: vec![], span },
        span,
    };
    parts.push(Part::Decl(Decl { body, ..decl.clone() }));
    Ok(Family { parts, methods: lift.methods, unfold: (!measured).then_some(unfold), designations: lift.designations })
}
