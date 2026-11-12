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
/// A method call on a mutable local, `let p = x.m(a);` or `x.m(a);`
/// (§8.2): the parser's candidate, `\0mutcall(x.m(a))`, which the block
/// declaring `x` claims. A claimed call is `\0mutated(x.m(a))`: the
/// elaborator binds `p` to its value and `x` to the receiver after it when
/// the method returns `Mutated`, and reads it as an ordinary call when not.
/// An unclaimed candidate (its receiver is not mutable here: reached
/// through a λ, or shadowed) is an ordinary call.
pub const MUTCALL: &str = "\0mutcall";
pub const MUTATED: &str = "\0mutated";
/// The two parts of a claimed call `\0mutated(x.m(a))` as expressions, for
/// generated code that substitutes a block's statements into its result
/// (the `decreases` companions, `crates/elab/src/measure.rs`):
/// `\0mutated_after(x.m(a))` is `x` after the call (for a call on a field
/// path, `x.f.m(a)`, the field `x.f` after it, §20) and
/// `\0mutated_value(x.m(a))` the value `let p = x.m(a);` binds to `p`. Both
/// read the call as the statement does: the `Mutated` record's fields when
/// `m` is a `mut self` method, the receiver unchanged and the call itself
/// when not. The receiver may be any expression.
pub const MUTATED_AFTER: &str = "\0mutated_after";
pub const MUTATED_VALUE: &str = "\0mutated_value";
/// A `mut self` method's own call on its receiver, where it ends the body
/// (§19.3): `\0mutated_whole(x.m(a))` is the body's whole result, the
/// receiver after the call beside its value, which is the call itself. So
/// the recursion is a tail call, which a `decreases` function's companions
/// and a `runtime fn`'s loop both need. (Read at a method that turns out
/// not to return `Mutated`, a same-named one of another type, it is
/// `Mutated(x, x.m(a))`.)
pub const MUTATED_WHOLE: &str = "\0mutated_whole";
/// A function body after a loop that may `return`: `\0after(#forN, { rest })`,
/// the loop's `Return` value or else the rest.
pub const AFTER: &str = "\0after";
/// `\0while(decide_bit<c>(), m)`: a `while`'s header, in the place of a
/// `for`'s list (§5.3). The loop is otherwise a `for`'s, over a private
/// binder the body never reads.
pub const WHILE: &str = "\0while";
/// A `while` with no measure, once lowered (§18): `\0iterate(step, init)`,
/// always the input of a bind, which [`crate::try_lower`] writes as one call
/// `Iterate::then(init, step, k)` over the rest of the block `k`.
pub(crate) const ITERATE: &str = "\0iterate";

fn call_marked(marker: &str, input: Expr, span: Span) -> Expr { marked(marker, input, span) }

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

/// A statement body's result, which has none.
pub(crate) fn is_unit_result(e: &Expr) -> bool { is_unit(e) }

/// A statement body that ends in a method call on a mutable local, `{
/// x.m(a) }`: the call is the body's last statement, as `x.m(a);` would
/// be, and the body has no value.
fn statement_tail(b: &mut Block) {
    if !ends_in_method_call(b) { return; }
    let ExprKind::Var(n) = &b.result.kind else { return };
    let seq = format!("#seq{}", &n["#tail".len()..]);
    if let Some(Stmt::Let { name, .. }) = b.stmts.last_mut() { *name = seq; }
    b.result = Box::new(unit(b.result.span));
}

/// Does a block end in a method call on a mutable local, `{ …; x.m(a) }`
/// (the parser's `#tail` binding of it)? Such a block is a statement body
/// where one is wanted, and its value where a value is.
pub(crate) fn ends_in_method_call(b: &Block) -> bool {
    let ExprKind::Var(n) = &b.result.kind else { return false };
    n.starts_with("#tail")
        && matches!(b.stmts.last(), Some(Stmt::Let { name, expr, .. })
            if name == n && (unmark(expr, MUTCALL).is_some() || unmark(expr, MUTATED).is_some()))
}

/// The local a method-call candidate may update: its receiver, or the local
/// its receiver is a field path of (`x.f.g.m(a)` updates `x`,
/// docs/sequencing-surface-design.md §20).
pub(crate) fn mut_receiver(call: &Expr) -> Option<&str> {
    match &call.kind {
        ExprKind::Dot { recv, .. } => place_root(recv),
        _ => None,
    }
}

/// The local a place is a field path of: `x` for `x`, `x.f`, `x.f.g`.
pub fn place_root(place: &Expr) -> Option<&str> {
    match &place.kind {
        ExprKind::Var(x) => Some(x),
        ExprKind::Dot { recv, args: None, tyargs, named, .. } if tyargs.is_empty() && named.is_empty() => place_root(recv),
        _ => None,
    }
}

/// The local a place is a path of, and that local's value once the place
/// holds `value`: `(x, value)` for `x`, and `(x, x with { f = x.f with { g =
/// value } })` for `x.f.g` (§20). `None` where `place` is no field path.
pub fn place_update(place: &Expr, value: Expr) -> Option<(String, Expr)> {
    match &place.kind {
        ExprKind::Var(x) => Some((x.clone(), value)),
        ExprKind::Dot { recv, name, args: None, tyargs, named } if tyargs.is_empty() && named.is_empty() => {
            let span = place.span;
            let field = RecordLitField { name: name.clone(), expr: value, span };
            place_update(recv, Expr { kind: ExprKind::RecordUpdate { base: recv.clone(), fields: vec![field] }, span })
        }
        _ => None,
    }
}

/// The type annotation an assignment checks at: the type of the local's
/// current value.
fn type_of(name: &str, span: Span) -> Ty { Ty { kind: TyKind::TypeOf(Box::new(var(name, span))), span } }

/// Does this block hold layer-2 statements at all? The cheap test that
/// keeps every ordinary block on the path it had.
fn has_markers(b: &Block) -> bool {
    b.stmts.iter().any(|s| matches!(s, Stmt::Let { expr, .. }
        if unmark(expr, MUT).is_some() || unmark(expr, ASSIGN).is_some() || unmark(expr, STMT).is_some()
            || unmark_for(expr).is_some() || unmark(expr, MUTCALL).is_some()))
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

pub(crate) fn call_marker(head: &str, args: Vec<Expr>, span: Span) -> Expr { call(head, args, span) }

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
        } else if let Some(x) = unmark(expr, MUTCALL).or_else(|| unmark(expr, MUTATED)).and_then(mut_receiver) {
            // A method call on a mutable local may update it: the scope
            // threads it, whether or not the method turns out to (§8.2).
            if !out.iter().any(|n| n == x) { out.push(x.to_string()); }
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
    let (mut b, env) = lower_in_env(b, &[], next)?;
    claim_tail(&mut b.result, &env, next)?;
    Ok(b)
}

/// A block's result is the last thing it computes, so a branch there may
/// go on updating the block's mutable locals: nothing after it reads them
/// (§19.1). Each arm of a tail `if`/`match` is lowered again with those
/// locals in scope, which claims the residuals its own lowering left for
/// the scope that declared them (module docs), and so on through the arm's
/// own tail. A name the arm's pattern binds is the pattern's there.
fn claim_tail(e: &mut Expr, env: &[String], next: &mut usize) -> R<()> {
    if env.is_empty() { return Ok(()); }
    let ExprKind::Match { arms, eqbind, .. } = &mut e.kind else { return Ok(()) };
    for arm in arms {
        let ExprKind::Block(body) = &mut arm.body.kind else { continue };
        let mut bound = Vec::new();
        arm_names(arm.binders.as_slice(), eqbind.as_deref(), &mut bound);
        let inner: Vec<String> = env.iter().filter(|n| !bound.contains(n)).cloned().collect();
        let block = std::mem::replace(&mut **body, Block {
            stmts: Vec::new(),
            result: Box::new(unit(arm.body.span)),
            ons: Vec::new(),
            span: arm.body.span,
        });
        let (mut lowered, inner) = lower_in_env(block, &inner, next)?;
        claim_tail(&mut lowered.result, &inner, next)?;
        **body = lowered;
    }
    Ok(())
}

/// The names an arm binds: its pattern's variables and the equation's.
fn arm_names(pats: &[Pat], eqbind: Option<&str>, out: &mut Vec<String>) {
    fn go(p: &Pat, out: &mut Vec<String>) {
        match p {
            Pat::Var { name, .. } => out.push(name.clone()),
            Pat::Ctor { args, .. } => args.iter().for_each(|a| go(a, out)),
            Pat::Named { pat, .. } => go(pat, out),
        }
    }
    pats.iter().for_each(|p| go(p, out));
    out.extend(eqbind.map(str::to_string));
}

/// Does the tail of a `mut self` body, a branch with these arms, update the
/// receiver `x` in some arm (§19.2)? An arm updates it by a residual
/// assignment or a method-call candidate its own lowering left, in its
/// statements or its own tail; one that rebinds the name instead (a `let`,
/// a pattern variable) makes the answer no for the whole branch, since the
/// name at that arm's end would not be the receiver.
pub(crate) fn tail_updates(arms: &[Arm], eqbind: Option<&str>, x: &str) -> bool {
    matches!(touch_arms(arms, eqbind, x), Touch::Updates)
}

#[derive(Clone, Copy, PartialEq)]
enum Touch { No, Updates, Shadows }

impl Touch {
    fn and(self, other: Touch) -> Touch {
        match (self, other) {
            (Touch::Shadows, _) | (_, Touch::Shadows) => Touch::Shadows,
            (Touch::Updates, _) | (_, Touch::Updates) => Touch::Updates,
            _ => Touch::No,
        }
    }
}

fn touch_arms(arms: &[Arm], eqbind: Option<&str>, x: &str) -> Touch {
    let mut all = Touch::No;
    for arm in arms {
        let mut bound = Vec::new();
        arm_names(arm.binders.as_slice(), eqbind, &mut bound);
        all = all.and(if bound.iter().any(|n| n == x) { Touch::Shadows } else { touch(&arm.body, x) });
    }
    all
}

fn touch(e: &Expr, x: &str) -> Touch {
    match &e.kind {
        ExprKind::Block(b) => {
            let mut all = Touch::No;
            for s in &b.stmts {
                match s {
                    Stmt::Let { name, expr, .. } => {
                        if unmark(expr, MUTCALL).and_then(mut_receiver) == Some(x) {
                            all = Touch::Updates;
                        }
                        if name == x {
                            if unmark(expr, ASSIGN).is_none() { return Touch::Shadows; }
                            all = Touch::Updates;
                        }
                    }
                    Stmt::LetRecord { fields, .. } => {
                        let pats: Vec<Pat> = fields.iter().map(|f| f.pat.clone()).collect();
                        let mut bound = Vec::new();
                        arm_names(&pats, None, &mut bound);
                        if bound.iter().any(|n| n == x) { return Touch::Shadows; }
                    }
                    Stmt::LetCode { name, .. } => if name == x { return Touch::Shadows; },
                }
            }
            all.and(touch(&b.result, x))
        }
        ExprKind::Match { motive: None, arms, eqbind, .. } => touch_arms(arms, eqbind.as_deref(), x),
        _ if receiver_call(e, x) => Touch::Updates,
        _ => Touch::No,
    }
}

/// Is `e` a method call on the local `x` or on a field path of it,
/// `x.m(a)` or `x.f.m(a)`?
pub(crate) fn receiver_call(e: &Expr, x: &str) -> bool {
    matches!(&e.kind, ExprKind::Dot { args: Some(_), .. }) && mut_receiver(e) == Some(x)
}

/// Is `e` a method call on the local `x` itself, `x.m(a)`?
fn direct_call(e: &Expr, x: &str) -> bool {
    matches!(&e.kind, ExprKind::Dot { recv, args: Some(_), .. } if matches!(&recv.kind, ExprKind::Var(n) if n == x))
}

/// The method's own call on the receiver `x`, `x.method(a)`, where it ends
/// a `mut self` body or one of its tail arms, taken out of the block: the
/// parser's `#tail` binding of it ([`ends_in_method_call`]), or an arm that
/// is the bare call. What is left is the block's statements before it.
pub(crate) fn take_own_call(b: &mut Block, x: &str, method: &str) -> Option<Expr> {
    let own = |e: &Expr| direct_call(e, x) && matches!(&e.kind, ExprKind::Dot { name, .. } if name == method);
    if own(&b.result) {
        let span = b.result.span;
        return Some(std::mem::replace(&mut *b.result, unit(span)));
    }
    if !ends_in_method_call(b) { return None; }
    let Some(Stmt::Let { expr, .. }) = b.stmts.last() else { return None };
    let call = unmark(expr, MUTCALL).filter(|call| own(call))?.clone();
    b.stmts.pop();
    Some(call)
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
                    if vars.is_empty() && carrier_while(iter).is_some() {
                        return fail(span,
                            "this `while` assigns no `let mut` local, so its condition can never change: \
                             a loop with no measure threads the locals its body assigns (a loop that \
                             runs forever is `CoTree::spin`)");
                    }
                    if vars.is_empty() && !body_returns(body) {
                        return fail(span,
                            "this loop assigns no `let mut` local, so it computes nothing: in pure code \
                             a loop only reassigns locals or `return`s");
                    }
                    let is_while = matches!(&iter.kind, ExprKind::App { head, .. } if matches!(&head.kind, ExprKind::Var(n) if n == WHILE));
                    if is_while && has_exit(body) {
                        return fail(span,
                            "`break`, `continue` and `return` in a `while` are not built yet (§5.3): end the \
                             loop through its condition");
                    }
                    let mut inner = env.clone();
                    for v in &vars {
                        if !inner.contains(v) { inner.push(v.clone()); }
                    }
                    if let Some(cond) = carrier_while(iter) {
                        // A `while` with no measure: a loop of the block's
                        // carrier (§18), lowered here in full.
                        let step = carrier_step(cond, body, &inner, &vars, x, next)?;
                        let init = state_expr(&vars, span);
                        let looped = call(ITERATE, vec![step, init], span);
                        stmts.push(Stmt::Let {
                            name: name.clone(),
                            ty: None,
                            expr: crate::try_lower::bind_marker(looped, span),
                            span,
                            opaque,
                        });
                        for (v, read) in state_reads(&name, &vars, span) {
                            let mine = env.contains(&v);
                            stmts.push(Stmt::Let {
                                name: v.clone(),
                                ty: if mine { Some(type_of(&v, span)) } else { None },
                                expr: if mine { read } else { marked(ASSIGN, read, span) },
                                span,
                                opaque: false,
                            });
                        }
                        continue;
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
                } else if let Some(call) = unmark(&expr, MUTCALL)
                    && mut_receiver(call).is_some_and(|x| env.iter().any(|n| n == x))
                {
                    // This block's own mutable local: claimed (§8.2). The
                    // elaborator rebinds the receiver; a later `let` of the
                    // same name shadows it as usual.
                    let call = call.clone();
                    let mine = name.clone();
                    if mine != mut_receiver(&call).unwrap_or("") {
                        env.retain(|n| *n != mine);
                    }
                    if ty.is_some() {
                        // `let p: T = x.m(a);`: the call binds a private
                        // name, which the annotated `let` then reads, so the
                        // annotation is held to the answer, not the record.
                        let tmp = format!("#mutcall{}", *next);
                        *next += 1;
                        stmts.push(Stmt::Let { name: tmp.clone(), ty: None, expr: call_marked(MUTATED, call, span), span, opaque: false });
                        stmts.push(Stmt::Let { name, ty, expr: var(&tmp, span), span, opaque });
                    } else {
                        stmts.push(Stmt::Let { name, ty, expr: call_marked(MUTATED, call, span), span, opaque });
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
                    // One join for every local the form assigns: each arm
                    // ends in the state `Mutated(v₁, Mutated(v₂, …))` the
                    // loop lowering threads, bound once at a private name,
                    // and the locals are read out of it after. A join per
                    // local would copy each branch, its calls included, once
                    // per local (issues/statement-form-join-copies-calls.md).
                    let joined = join(form, &state_expr(&vars, form.span), &inner, next)?;
                    let reads = if vars.len() > 1 {
                        let tmp = format!("#stage{}", *next);
                        *next += 1;
                        stmts.push(Stmt::Let {
                            name: tmp.clone(),
                            ty: Some(state_type(&vars, form.span)),
                            expr: joined,
                            span: form.span,
                            opaque: false,
                        });
                        state_reads(&tmp, &vars, form.span)
                    } else {
                        vec![(vars[0].clone(), joined)]
                    };
                    for (v, joined) in reads {
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
fn join(form: &Expr, state: &Expr, env: &[String], next: &mut usize) -> R<Expr> {
    let mut form = form.clone();
    let ExprKind::Match { arms, .. } = &mut form.kind else {
        return fail(form.span, "a statement form is an `if` or a `match`");
    };
    for arm in arms {
        let ExprKind::Block(body) = &arm.body.kind else {
            return fail(arm.body.span, "a statement `match` arm is a braced block of statements: `P => { x := e }`");
        };
        let empty = body.stmts.is_empty() && matches!(body.result.kind, ExprKind::AutoRefl);
        let mut body = body.clone();
        statement_tail(&mut body);
        if !is_unit(&body.result) && !empty {
            return fail(body.result.span,
                "a statement body ends in a statement, not a value: this `if`/`match` assigns locals, \
                 so its branches have no result");
        }
        let mut lowered = lower_in(*body, env, next)?;
        let span = lowered.result.span;
        lowered.result = Box::new(Expr { span, ..state.clone() });
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

/// A `mut self` method's returns, after [`lower_returns`]: each `\0ret(e)`
/// leaf of a returning loop becomes `\0ret(Mutated(x, e))` over the
/// receiver `x`, so the loop's `Return` is the method's whole result. The
/// leaf reads `x` where it stands, which is the receiver as the body has
/// threaded it so far: the loop carries it as state when the body calls on
/// it or assigns it. A returning loop is a statement of the body, or of a
/// `\0after` rest below one; one anywhere else is refused after this by
/// [`reject_residue`], as in pure code.
pub(crate) fn return_receiver(body: &mut Block, receiver: &str, record: &str) {
    for s in &mut body.stmts {
        let Stmt::Let { expr, .. } = s else { continue };
        if !is_loop(expr) || !returns(expr) { continue; }
        let ExprKind::App { args, .. } = &mut expr.kind else { continue };
        let Some(ExprKind::Lam { body: lam, .. }) = args.get_mut(1).map(|a| &mut a.kind) else { continue };
        wrap_ret_leaves(lam, receiver, record);
    }
    if let ExprKind::App { head, args, .. } = &mut body.result.kind
        && matches!(&head.kind, ExprKind::Var(n) if n == AFTER)
        && let Some(ExprKind::Block(rest)) = args.get_mut(1).map(|a| &mut a.kind)
    {
        return_receiver(rest, receiver, record);
    }
}

/// The leaves of a tail-lowered loop body sit in the result of a block or
/// of a `match` arm, and nowhere else (the tree [`tail`] builds).
fn wrap_ret_leaves(e: &mut Expr, receiver: &str, record: &str) {
    match &mut e.kind {
        ExprKind::App { head, args, .. } if matches!(&head.kind, ExprKind::Var(n) if n == RET) && args.len() == 1 => {
            let span = args[0].span;
            let value = std::mem::replace(&mut args[0], unit(span));
            args[0] = call(record, vec![var(receiver, span), value], span);
        }
        ExprKind::Block(b) => wrap_ret_leaves(&mut b.result, receiver, record),
        ExprKind::Match { arms, .. } => {
            for a in arms { wrap_ret_leaves(&mut a.body, receiver, record); }
        }
        _ => {}
    }
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
                         `let mut` local of its own block, of a statement body inside it, or of a branch \
                         that ends it; never through a λ or another block in value position)"),
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

/// The condition of a `while` with no measure: its header is
/// `\0while(decide_bit<c>())` alone (a measured one also carries `m`).
fn carrier_while(header: &Expr) -> Option<&Expr> {
    match &header.kind {
        ExprKind::App { head, args, .. } if args.len() == 1 && matches!(&head.kind, ExprKind::Var(n) if n == WHILE) => {
            Some(&args[0])
        }
        _ => None,
    }
}

/// The state a carrier loop threads: the one local itself, or the locals
/// nested in the prelude's pair `Mutated(v₁, Mutated(v₂, …))`, which needs no
/// declaration the parser cannot write.
fn state_expr(vars: &[String], span: Span) -> Expr {
    match vars {
        [v] => var(v, span),
        [v, rest @ ..] => call("Mutated", vec![var(v, span), state_expr(rest, span)], span),
        [] => unreachable!("a carrier loop threads at least one local"),
    }
}

/// The type of [`state_expr`]'s state: `Mutated<TypeOf(v₁), …>`, each
/// local at its type before the form, which `:=` keeps.
fn state_type(vars: &[String], span: Span) -> Ty {
    match vars {
        [v] => type_of(v, span),
        [v, rest @ ..] => Ty {
            kind: TyKind::Named { name: "Mutated".into(), args: vec![type_of(v, span), state_type(rest, span)] },
            span,
        },
        [] => unreachable!("a statement form assigns at least one local"),
    }
}

/// Each local out of a state `s` that [`state_expr`] built.
fn state_reads(s: &str, vars: &[String], span: Span) -> Vec<(String, Expr)> {
    let mut out = Vec::with_capacity(vars.len());
    let mut at = var(s, span);
    let dot = |recv: Expr, name: &str| Expr {
        kind: ExprKind::Dot { recv: Box::new(recv), name: name.into(), tyargs: vec![], args: None, named: vec![] },
        span,
    };
    for (i, v) in vars.iter().enumerate() {
        if i + 1 == vars.len() {
            out.push((v.clone(), at));
            break;
        }
        out.push((v.clone(), dot(at.clone(), "after")));
        at = dot(at, "value");
    }
    out
}

/// The step of a `while c { body }` with no measure (§18):
///
/// ```text
/// λ (#s: TypeOf(v̄)) => { let vᵢ = #s…; match decide_bit<c>() {
///     True => { body; Pointed::ret(Step::Continue(v̄)) },
///     False => Pointed::ret(Step::Break(v̄)) } }
/// ```
///
/// The body's binds were left as markers when it closed and are lowered
/// here, in the `True` arm, so they run inside the step and after the
/// locals are read. The state's annotation is the locals' types before the
/// loop, which `:=` keeps.
fn carrier_step(cond: &Expr, body: &Block, env: &[String], vars: &[String], x: &LamBinder, next: &mut usize) -> R<Expr> {
    let span = body.span;
    let ret = |ctor: &str, at: Span| {
        call(crate::try_lower::POINTED_RET, vec![call(ctor, vec![state_expr(vars, at)], at)], at)
    };
    let mut lowered = lower_in(body.clone(), env, next)?;
    let end = lowered.result.span;
    lowered.result = Box::new(ret("Step::Continue", end));
    let lowered = crate::try_lower::binds_in_block(lowered, next)?;
    let arms = vec![
        Arm {
            ctor: "True".into(),
            default: false,
            binders: vec![],
            body: Expr { span: lowered.span, kind: ExprKind::Block(Box::new(lowered)) },
            span,
        },
        Arm { ctor: "False".into(), default: false, binders: vec![], body: ret("Step::Break", span), span },
    ];
    let decide = Expr {
        kind: ExprKind::Match { form: MatchForm::Match, generated: true, scrut: Box::new(cond.clone()), eqbind: None, motive: None, arms },
        span,
    };
    let s = format!("{}#s", x.name);
    let reads = if vars.len() == 1 {
        vec![Stmt::Let { name: vars[0].clone(), ty: None, expr: var(&s, span), span, opaque: false }]
    } else {
        state_reads(&s, vars, span)
            .into_iter()
            .map(|(v, e)| Stmt::Let { name: v, ty: None, expr: e, span, opaque: false })
            .collect()
    };
    let block = Block { stmts: reads, result: Box::new(decide), ons: Vec::new(), span };
    let annotation = Ty { kind: TyKind::TypeOf(Box::new(state_expr(vars, span))), span };
    Ok(Expr {
        kind: ExprKind::Lam {
            binders: vec![LamBinder { name: s, ty: Some(annotation), implicit: false, span: x.span }],
            body: Box::new(Expr { span, kind: ExprKind::Block(Box::new(block)) }),
        },
        span,
    })
}
