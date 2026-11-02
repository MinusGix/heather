//! Local state in pure code: `let mut`, `:=` and statement `if`/`match`
//! (docs/sequencing-surface-design.md §4, §5.1), lowered to ordinary
//! `let`s. No new kernel form, and no new AST node: the parser writes the
//! statements as `let`s whose right side is a private marker call, and this
//! module rewrites each block when it closes, before its binds are lowered
//! ([`crate::try_lower::binds_in_block`]).
//!
//! - `let mut x = e;` is `let x = e;`, with `x` recorded as mutable in the
//!   block.
//! - `x := e;` is `let x: typeof(x) = e;`: a new alias shadowing the old one,
//!   checked at the declared type, which therefore never changes (§4).
//! - A statement `if`/`match` whose bodies assign `x̄` joins **per
//!   variable** (§5.1): for each `x`, `let x: typeof(x) = match c { P => {
//!   body; x }, … };`, with an `else` that assigns nothing reading `x`
//!   unchanged. The annotation puts the match in checking position, which
//!   is why a join needs no motive.
//!
//! The bodies of a statement form belong to the scope around them, so an
//! inner block cannot tell, when it closes, whether an assignment in it is
//! its enclosing scope's. It leaves an assignment to a name it did not
//! declare `mut` as it is, a *residual*, and the block that declared the name
//! rewrites the statement form that holds it. A residual left once the
//! declaration is parsed assigned a name no enclosing statement scope
//! declared `mut` ([`reject_residue`]), or reached it through a λ or a block
//! in value position.
use crate::ast::*;
use crate::parser::ParseError;
type R<T> = Result<T, ParseError>;

/// `let mut x = e;`: the marker around `e`.
pub(crate) const MUT: &str = "\0mut";
/// `x := e;`: the marker around `e`, at a `let` named `x`.
pub(crate) const ASSIGN: &str = "\0assign";
/// A statement `if`/`match`, at a `let` with a private name.
pub(crate) const STMT: &str = "\0stmt";
/// The result of a statement body, which has none.
pub(crate) const UNIT: &str = "\0unit";
/// `for x in e { body }`: `\0for(e, λ x => body)`, at a private name.
pub(crate) const FOR: &str = "\0for";
/// A `for` once its body is lowered: `\0loop(e, λ x => { body; \0state(v̄) },
/// v̄)` over the `let mut` locals `v̄` the body assigns, for the elaborator
/// to lift into a named step over a fold (§5.2).
pub const LOOP: &str = "\0loop";
/// The state a lowered loop body ends in: `\0state(v̄)`.
pub const STATE: &str = "\0state";
/// After a loop, a local's value out of its result: `\0proj(#forN, v)`.
pub const PROJ: &str = "\0proj";
/// `break;`, `continue;` and `return e;` as statements, at a private name.
pub(crate) const BREAK: &str = "\0break";
pub(crate) const CONTINUE: &str = "\0continue";
pub(crate) const RETURN: &str = "\0return";
/// The leaves of a loop body that exits early (§5.2): go on with the state
/// `\0next(v̄)`, stop with it `\0brk(v̄)`, or leave the function with a
/// value `\0ret(e)`. The elaborator spells them `ForStep`'s constructors.
pub const NEXT: &str = "\0next";
pub const BRK: &str = "\0brk";
pub const RET: &str = "\0ret";
/// A function body after a loop that may `return`: `\0after(#forN, { rest })`,
/// the loop's `Return` value or else the rest.
pub const AFTER: &str = "\0after";

fn fail<T>(span: Span, msg: impl Into<String>) -> R<T> { Err(ParseError { span, msg: msg.into() }) }

fn var(name: &str, span: Span) -> Expr { Expr { kind: ExprKind::Var(name.into()), span } }

pub(crate) fn marked(marker: &str, input: Expr, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App {
            head: Box::new(var(marker, span)),
            args: vec![input],
            named: vec![],
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

/// The input of a marker call `marker(e)`.
fn unmark<'e>(e: &'e Expr, marker: &str) -> Option<&'e Expr> {
    match &e.kind {
        ExprKind::App { head, args, .. } if args.len() == 1 && matches!(&head.kind, ExprKind::Var(n) if n == marker) => {
            Some(&args[0])
        }
        _ => None,
    }
}

pub(crate) fn unit(span: Span) -> Expr { var(UNIT, span) }

fn is_unit(e: &Expr) -> bool { matches!(&e.kind, ExprKind::Var(n) if n == UNIT) }

/// The type annotation an assignment checks at: the type of the local's
/// current value.
fn type_of(name: &str, span: Span) -> Ty { Ty { kind: TyKind::TypeOf(Box::new(var(name, span))), span } }

/// Does this block hold layer-2 statements at all? The cheap test that
/// keeps every ordinary block on the path it had.
fn has_markers(b: &Block) -> bool {
    b.stmts.iter().any(|s| matches!(s, Stmt::Let { expr, .. }
        if unmark(expr, MUT).is_some() || unmark(expr, ASSIGN).is_some() || unmark(expr, STMT).is_some()
            || unmark_for(expr).is_some()))
        || is_unit(&b.result)
}

/// The iterable, binder and body of a `\0for(e, λ x => body)`.
fn unmark_for(e: &Expr) -> Option<(&Expr, &LamBinder, &Block)> {
    let ExprKind::App { head, args, .. } = &e.kind else { return None };
    if args.len() != 2 || !matches!(&head.kind, ExprKind::Var(n) if n == FOR) { return None; }
    let ExprKind::Lam { binders, body } = &args[1].kind else { return None };
    let ExprKind::Block(b) = &body.kind else { return None };
    Some((&args[0], binders.first()?, b))
}

/// An exit statement: its marker, and `return`'s value.
fn exit_of(s: &Stmt) -> Option<(&'static str, Option<&Expr>, Span)> {
    let Stmt::Let { expr, span, .. } = s else { return None };
    let ExprKind::App { head, args, .. } = &expr.kind else { return None };
    let ExprKind::Var(n) = &head.kind else { return None };
    for m in [BREAK, CONTINUE, RETURN] {
        if n == m { return Some((m, args.first(), *span)); }
    }
    None
}

/// Does a loop body exit early: an exit statement in it, or in a statement
/// form's body inside it — not in a nested loop's, whose exits are its own.
fn has_exit(b: &Block) -> bool {
    b.stmts.iter().any(|s| exit_of(s).is_some() || matches!(s, Stmt::Let { expr, .. } if unmark(expr, STMT).is_some_and(form_has_exit)))
}

fn form_has_exit(form: &Expr) -> bool {
    matches!(&form.kind, ExprKind::Match { arms, .. }
        if arms.iter().any(|a| matches!(&a.body.kind, ExprKind::Block(b) if has_exit(b))))
}

/// Does a loop body `return` (a [`has_exit`] whose exit is a `return`)?
fn body_returns(b: &Block) -> bool {
    b.stmts.iter().any(|s| matches!(exit_of(s), Some((m, _, _)) if m == RETURN)
        || matches!(s, Stmt::Let { expr, .. } if unmark(expr, STMT).is_some_and(|form| matches!(&form.kind,
            ExprKind::Match { arms, .. } if arms.iter().any(|a| matches!(&a.body.kind, ExprKind::Block(b) if body_returns(b)))))))
}

fn is_exit_stmt(s: &Stmt) -> bool {
    exit_of(s).is_some() || matches!(s, Stmt::Let { expr, .. } if unmark(expr, STMT).is_some_and(form_has_exit))
}

/// Does a lowered loop body hold a `\0ret` leaf?
fn returns(e: &Expr) -> bool {
    let mut found = false;
    let mut go = |x: &Expr| {
        if matches!(&x.kind, ExprKind::App { head, .. } if matches!(&head.kind, ExprKind::Var(n) if n == RET)) {
            found = true;
        }
    };
    walk(e, &mut go);
    found
}

fn walk(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    crate::try_lower::visit_children(e, &mut |x| walk(x, f));
}

/// A loop body that exits early, lowered **in tail position** (§5.2): a
/// statement form that exits takes the rest of the body into each of its
/// arms, so the body is one expression whose leaves are `\0next(v̄)`,
/// `\0brk(v̄)` and `\0ret(e)`. An arm that exits drops the rest. The rest is
/// copied into every arm that falls through, which is linear when, as
/// usual, one arm does.
fn tail(mut stmts: Vec<Stmt>, env: &[String], vars: &[String], end: Span, next: &mut usize) -> R<Block> {
    let leaf = |m: &str, span: Span| call(m, vars.iter().map(|v| var(v, span)).collect(), span);
    let Some(i) = stmts.iter().position(is_exit_stmt) else {
        let (mut b, _) = lower_in_env(Block { stmts, result: Box::new(unit(end)), ons: Vec::new(), span: end }, env, next)?;
        b.result = Box::new(leaf(NEXT, end));
        return Ok(b);
    };
    let rest = stmts.split_off(i);
    let (mut pre, env) = lower_in_env(Block { stmts, result: Box::new(unit(end)), ons: Vec::new(), span: end }, env, next)?;
    let head = &rest[0];
    let after = &rest[1..];
    if let Some((m, value, span)) = exit_of(head) {
        pre.result = Box::new(match m {
            BREAK => leaf(BRK, span),
            CONTINUE => leaf(NEXT, span),
            _ => call(RET, vec![value.expect("`return` has a value").clone()], span),
        });
        return Ok(pre);
    }
    let Stmt::Let { expr, .. } = head else { unreachable!("an exit statement is a `let`") };
    let mut form = unmark(expr, STMT).expect("a statement form").clone();
    let ExprKind::Match { arms, .. } = &mut form.kind else {
        return fail(form.span, "a statement form is an `if` or a `match`");
    };
    for arm in arms {
        let ExprKind::Block(body) = &arm.body.kind else {
            return fail(arm.body.span, "a statement `match` arm is a braced block of statements: `P => { x := e }`");
        };
        let mut spliced = if body.stmts.is_empty() && matches!(body.result.kind, ExprKind::AutoRefl) { Vec::new() } else { body.stmts.clone() };
        spliced.extend(after.iter().cloned());
        let lowered = tail(spliced, &env, vars, body.span, next)?;
        arm.body = Expr { span: arm.body.span, kind: ExprKind::Block(Box::new(lowered)) };
    }
    pre.result = Box::new(form);
    Ok(pre)
}

/// No statement follows an exit in the block that holds it.
fn check_unreachable(b: &Block) -> R<()> {
    for (i, s) in b.stmts.iter().enumerate() {
        if let Some((m, _, span)) = exit_of(s)
            && i + 1 < b.stmts.len()
        {
            let word = match m { BREAK => "break", CONTINUE => "continue", _ => "return" };
            return fail(span, format!("nothing after `{word}` runs: it ends the block"));
        }
    }
    Ok(())
}

fn call(head: &str, args: Vec<Expr>, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App { head: Box::new(var(head, span)), args, named: vec![], explicit: false, goal_oriented: false },
        span,
    }
}

/// The names a statement body assigns and leaves to its scope: its residual
/// assignments, and those of the statement forms inside it, in first-written
/// order.
fn assigned(b: &Block, out: &mut Vec<String>) {
    for s in &b.stmts {
        let Stmt::Let { name, expr, .. } = s else { continue };
        if unmark(expr, ASSIGN).is_some() {
            if !out.contains(name) { out.push(name.clone()); }
        } else if let Some(form) = unmark(expr, STMT) {
            assigned_by_form(form, out);
        }
    }
}

fn assigned_by_form(form: &Expr, out: &mut Vec<String>) {
    if let ExprKind::Match { arms, .. } = &form.kind {
        for arm in arms {
            if let ExprKind::Block(b) = &arm.body.kind { assigned(b, out); }
        }
    }
}

/// Lower one block's layer-2 statements (module docs). `outer` is the set
/// of mutable names a caller rewriting a statement body passes in: the
/// enclosing scope's.
pub(crate) fn lower_block(b: Block, next: &mut usize) -> R<Block> {
    if !has_markers(&b) { return Ok(b); }
    lower_in(b, &[], next)
}

fn lower_in(b: Block, outer: &[String], next: &mut usize) -> R<Block> {
    Ok(lower_in_env(b, outer, next)?.0)
}

/// [`lower_in`], and the mutable locals in scope at the block's end.
fn lower_in_env(mut b: Block, outer: &[String], next: &mut usize) -> R<(Block, Vec<String>)> {
    check_unreachable(&b)?;
    let mut env: Vec<String> = outer.to_vec();
    let mut stmts = Vec::with_capacity(b.stmts.len());
    for s in std::mem::take(&mut b.stmts) {
        match s {
            Stmt::Let { name, ty, expr, span, opaque } => {
                if let Some(value) = unmark(&expr, MUT) {
                    if opaque { return fail(span, "`have` binds a proposition's proof: it cannot be `mut`"); }
                    env.retain(|n| *n != name);
                    env.push(name.clone());
                    stmts.push(Stmt::Let { name, ty, expr: value.clone(), span, opaque });
                } else if let Some(value) = unmark(&expr, ASSIGN) {
                    if env.contains(&name) {
                        let ty = Some(type_of(&name, span));
                        stmts.push(Stmt::Let { name, ty, expr: value.clone(), span, opaque });
                    } else {
                        // Not this scope's: a residual for the scope that
                        // declared it (module docs).
                        stmts.push(Stmt::Let { name, ty, expr, span, opaque });
                    }
                } else if let Some((iter, x, body)) = unmark_for(&expr) {
                    // The loop's state is the `let mut` locals its body
                    // assigns (§5.2), threaded as the STMT joins are: the
                    // body lowered with them mutable, each read back after
                    // the loop, and a residual for a local this block did
                    // not declare.
                    let mut vars = Vec::new();
                    assigned(body, &mut vars);
                    // The state in declaration order, so `f::State(v̄)` reads
                    // as the locals were written; a residual's last.
                    vars.sort_by_key(|v| env.iter().position(|e| e == v).unwrap_or(usize::MAX));
                    // A loop that may `return` computes its exit even
                    // with no state (a search).
                    if vars.is_empty() && !body_returns(body) {
                        return fail(span,
                            "this `for` assigns no `let mut` local, so it computes nothing: in pure code \
                             a loop only reassigns locals or `return`s");
                    }
                    let mut inner = env.clone();
                    for v in &vars {
                        if !inner.contains(v) { inner.push(v.clone()); }
                    }
                    let lowered = if has_exit(body) {
                        tail(body.stmts.clone(), &inner, &vars, body.result.span, next)?
                    } else {
                        let mut lowered = lower_in(body.clone(), &inner, next)?;
                        let end = lowered.result.span;
                        lowered.result = Box::new(call(STATE, vars.iter().map(|v| var(v, end)).collect(), end));
                        lowered
                    };
                    let lam = Expr {
                        kind: ExprKind::Lam {
                            binders: vec![x.clone()],
                            body: Box::new(Expr { span: lowered.span, kind: ExprKind::Block(Box::new(lowered)) }),
                        },
                        span,
                    };
                    let mut args = vec![iter.clone(), lam];
                    args.extend(vars.iter().map(|v| var(v, span)));
                    stmts.push(Stmt::Let { name: name.clone(), ty: None, expr: call(LOOP, args, span), span, opaque });
                    for v in vars {
                        let read = call(PROJ, vec![var(&name, span), var(&v, span)], span);
                        let mine = env.contains(&v);
                        stmts.push(Stmt::Let {
                            name: v.clone(),
                            ty: if mine { Some(type_of(&v, span)) } else { None },
                            expr: if mine { read } else { marked(ASSIGN, read, span) },
                            span,
                            opaque: false,
                        });
                    }
                } else if unmark(&expr, STMT).is_some_and(form_has_exit) || exit_of(&Stmt::Let { name: name.clone(), ty: None, expr: expr.clone(), span, opaque }).is_some() {
                    // An exit, or a form holding one, is the enclosing loop's
                    // to lower in tail position ([`tail`]).
                    stmts.push(Stmt::Let { name, ty, expr, span, opaque });
                } else if let Some(form) = unmark(&expr, STMT) {
                    let mut vars = Vec::new();
                    assigned_by_form(form, &mut vars);
                    if vars.is_empty() {
                        return fail(form.span,
                            "this statement `if`/`match` assigns no `let mut` local, so it does nothing: \
                             in pure code a statement form only reassigns locals");
                    }
                    // The bodies are lowered with every local the form
                    // assigns taken as mutable; a local this block did not
                    // declare `mut` gets its join as a residual assignment,
                    // `x := match c { … { body; x } }`, for the scope that
                    // did (module docs) — or for `reject_residue`.
                    let mut inner = env.clone();
                    for v in &vars {
                        if !inner.contains(v) { inner.push(v.clone()); }
                    }
                    // Every copy of the form reads the locals as they were
                    // before it: with several, each join lands in a private
                    // name first, and the locals are rebound after the last.
                    let staged = vars.len() > 1;
                    let mut values = Vec::with_capacity(vars.len());
                    for v in &vars {
                        let joined = join(form, v, &inner, next)?;
                        if staged {
                            let tmp = format!("#stage{}", *next);
                            *next += 1;
                            stmts.push(Stmt::Let {
                                name: tmp.clone(),
                                ty: Some(type_of(v, form.span)),
                                expr: joined,
                                span: form.span,
                                opaque: false,
                            });
                            values.push(var(&tmp, form.span));
                        } else {
                            values.push(joined);
                        }
                    }
                    for (v, joined) in vars.into_iter().zip(values) {
                        let mine = env.contains(&v);
                        stmts.push(Stmt::Let {
                            name: v.clone(),
                            ty: if mine { Some(type_of(&v, form.span)) } else { None },
                            expr: if mine { joined } else { marked(ASSIGN, joined, form.span) },
                            span: form.span,
                            opaque: false,
                        });
                    }
                } else {
                    // A plain `let` of the same name shadows the mutable local.
                    env.retain(|n| *n != name);
                    stmts.push(Stmt::Let { name, ty, expr, span, opaque });
                }
            }
            other => stmts.push(other),
        }
    }
    b.stmts = stmts;
    Ok((b, env))
}

/// `form` with each body rewritten to end in `v`'s value after it: one copy
/// of the condition per assigned local (§5.1).
fn join(form: &Expr, v: &str, env: &[String], next: &mut usize) -> R<Expr> {
    let mut form = form.clone();
    let ExprKind::Match { arms, .. } = &mut form.kind else {
        return fail(form.span, "a statement form is an `if` or a `match`");
    };
    for arm in arms {
        let ExprKind::Block(body) = &arm.body.kind else {
            return fail(arm.body.span, "a statement `match` arm is a braced block of statements: `P => { x := e }`");
        };
        let empty = body.stmts.is_empty() && matches!(body.result.kind, ExprKind::AutoRefl);
        if !is_unit(&body.result) && !empty {
            return fail(body.result.span,
                "a statement body ends in a statement, not a value: this `if`/`match` assigns locals, \
                 so its branches have no result");
        }
        let mut lowered = lower_in((**body).clone(), env, next)?;
        let span = lowered.result.span;
        lowered.result = Box::new(var(v, span));
        arm.body = Expr { kind: ExprKind::Block(Box::new(lowered)), span: arm.body.span };
    }
    Ok(form)
}

/// A function body whose top-level loop may `return`: the rest of the body
/// after it becomes `\0after(#forN, { rest })` (§5.2), so the loop's
/// `Return` is the function's value. Run once on the declaration's body,
/// before [`reject_residue`]; a returning loop anywhere else is refused
/// there.
pub(crate) fn lower_returns(mut body: Block) -> Block {
    let Some(i) = body.stmts.iter().position(|s| matches!(s, Stmt::Let { expr, .. }
        if is_loop(expr) && returns(expr)))
    else {
        return body;
    };
    let rest: Vec<Stmt> = body.stmts.split_off(i + 1);
    let Stmt::Let { name, span, .. } = &body.stmts[i] else { unreachable!() };
    let (name, span) = (name.clone(), *span);
    let inner = lower_returns(Block {
        stmts: rest,
        result: std::mem::replace(&mut body.result, Box::new(unit(span))),
        ons: Vec::new(),
        span: body.span,
    });
    let inner = Expr { span: inner.span, kind: ExprKind::Block(Box::new(inner)) };
    body.result = Box::new(call(AFTER, vec![var(&name, span), inner], span));
    body
}

fn is_loop(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::App { head, .. } if matches!(&head.kind, ExprKind::Var(n) if n == LOOP))
}

/// A layer-2 marker left once a declaration is parsed: an assignment no
/// enclosing statement scope owned, or a statement body where a value was
/// needed.
pub(crate) fn reject_residue(body: &Block) -> R<()> {
    let e = Expr { kind: ExprKind::Block(Box::new(body.clone())), span: body.span };
    let mut error = None;
    find_residue(&e, &mut error);
    match error { Some(e) => Err(e), None => Ok(()) }
}

fn find_residue(e: &Expr, error: &mut Option<ParseError>) {
    if error.is_some() { return; }
    if let ExprKind::Block(b) = &e.kind {
        for s in &b.stmts {
            if let Stmt::Let { name, expr, span, .. } = s
                && unmark(expr, ASSIGN).is_some()
            {
                *error = Some(ParseError {
                    span: *span,
                    msg: format!(
                        "`{name}` is not mutable: declare it `let mut {name}` (an assignment reaches a \
                         `let mut` local of its own block or of a statement body inside it, never \
                         through a λ or a block in value position)"),
                });
                return;
            }
        }
        for s in &b.stmts {
            if let Some((m, _, span)) = exit_of(s) {
                let word = match m { BREAK => "break", CONTINUE => "continue", _ => "return" };
                *error = Some(ParseError {
                    span,
                    msg: if m == RETURN {
                        "`return` is supported inside a `for` for now, not elsewhere in a function".into()
                    } else {
                        format!("`{word}` is outside any loop")
                    },
                });
                return;
            }
            if let Stmt::Let { name, expr, span, .. } = s
                && is_loop(expr)
                && returns(expr)
                && !matches!(&b.result.kind, ExprKind::App { head, args, .. }
                    if matches!(&head.kind, ExprKind::Var(n) if n == AFTER)
                        && matches!(args.first().map(|a| &a.kind), Some(ExprKind::Var(l)) if l == name))
            {
                *error = Some(ParseError {
                    span: *span,
                    msg: "a `for` whose body may `return` is supported only as a statement of the function's \
                          own body for now, not inside another statement or loop".into(),
                });
                return;
            }
            if let Stmt::Let { expr, span, .. } = s
                && unmark_for(expr).is_some()
            {
                *error = Some(ParseError {
                    span: *span,
                    msg: "a `for` is a statement of a block that declares the `let mut` locals it \
                          assigns".into(),
                });
                return;
            }
        }
        if is_unit(&b.result) {
            *error = Some(ParseError {
                span: b.span,
                msg: "this block ends in a statement, so it has no value here: a block of statements is \
                      the body of a statement `if`/`match` that assigns a `let mut` local".into(),
            });
            return;
        }
    }
    crate::try_lower::visit_children(e, &mut |x| find_residue(x, error));
}
