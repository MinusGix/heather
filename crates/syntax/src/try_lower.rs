//! Function-scoped Result propagation and nested binds, lowered to ordinary
//! surface calls and matches. No new kernel form or evaluation rule is
//! involved.
//!
//! One continuation-passing walk serves two protocols ([`Protocol`]):
//!
//! - **`e?`** (docs/result-propagation-design.md): `K[e?]` is
//!   `result::and_then(e, λ v => K[v])`, scoped to the nearest function or
//!   λ body. Written blocks and match arms are transparent.
//! - **`(<- e)` and `let x <- e;`** (docs/sequencing-surface-design.md §3):
//!   `K[(<- e)]` is `Bind::seq(e, λ v => K[v])`, at the carrier the
//!   elaborator finds for the call. A binding statement is the nested bind at
//!   a `let`'s right side (`let x <- e;` is `let x = (<- e);`), and the
//!   expression statement `e;` is the same at a private name. The scope is
//!   the nearest **block** or λ body: every block is lowered when it closes
//!   ([`binds_in_block`]), so an inner block in value position is a scope of
//!   its own with its own carrier, and the walk never sees a marker inside
//!   one. A nested bind in a non-tail match arm runs in that arm: the arm
//!   packages its value with `Pointed::ret` and the match is bound once.
use crate::ast::*;
use crate::parser::ParseError;
type R<T> = Result<T, ParseError>;
pub(crate) const TRY: &str = "\0result-propagate";
/// The marker of a nested bind `(<- e)`, the parser's private head.
pub(crate) const BIND: &str = "\0bind";
/// The prelude call a bind lowers to (`crates/elab/src/prelude.hthr`).
pub const BIND_SEQ: &str = "Bind::seq";
/// The prelude call a carrier block packages a value with.
pub const POINTED_RET: &str = "Pointed::ret";

/// Which propagation the walk lowers. The two differ only in their marker,
/// the call that continues, the wrapper that packages a local scope's value,
/// the slot prefix, and how a refusal names the form.
#[derive(Clone, Copy)]
struct Protocol {
    marker: &'static str,
    slot: &'static str,
    what: &'static str,
    /// `result::Ok` / `Pointed::ret`: the local scope's success value.
    wrap: &'static str,
    /// Whether a terminal wrapper may be stripped into a `map`.
    map: Option<&'static str>,
    and_then: &'static str,
}

const PROPAGATE: Protocol = Protocol {
    marker: TRY,
    slot: "#try",
    what: "postfix `?`",
    wrap: "result::Ok",
    map: Some("result::Result::map"),
    and_then: "result::Result::and_then",
};

const BINDING: Protocol = Protocol {
    marker: BIND,
    slot: "#bind",
    what: "a nested bind `(<- e)`",
    wrap: POINTED_RET,
    map: None,
    and_then: BIND_SEQ,
};

fn var(name: &str, span: Span) -> Expr { Expr { kind: ExprKind::Var(name.into()), span } }
fn call(name: &str, args: Vec<Expr>, span: Span) -> Expr {
    Expr { kind:ExprKind::App { head:Box::new(var(name,span)),args,named:vec![],explicit:false,goal_oriented:false },span }
}
/// `(<- e)`: the marker the parser writes for a nested bind.
pub(crate) fn bind_marker(input: Expr, span: Span) -> Expr {
    Expr { kind:ExprKind::App { head:Box::new(var(BIND,span)),args:vec![input],named:vec![],explicit:false,goal_oriented:false },span }
}
impl Protocol {
    fn bind(self, input: Expr, slot: &str, body: Expr, span: Span) -> Expr {
        // A continuation that only re-binds the slot under a written
        // annotation, `{ let x: T = slot; rest }`, gives the λ that
        // annotation, so that `let x: T <- e;` checks `e` at `M(T)`.
        let mut ty = None;
        if let ExprKind::Block(b) = &body.kind
            && let Some(Stmt::Let { ty: Some(t), expr, opaque: false, .. }) = b.stmts.first()
            && matches!(&expr.kind, ExprKind::Var(n) if n == slot)
            && self.marker == BIND
        {
            ty = Some(t.clone());
        }
        let continuation = Expr { kind:ExprKind::Lam {
            binders:vec![LamBinder { name:slot.into(),ty,implicit:false,span }],body:Box::new(body),
        },span };
        let mut continuation = continuation;
        let ExprKind::Lam { body,.. } = &mut continuation.kind else { unreachable!() };
        let name = match self.map {
            Some(map) => if let Some(value) = self.unreturn(body) {
                **body = value;
                map
            } else { self.and_then },
            None => self.and_then,
        };
        call(name,vec![input,continuation],span)
    }
    // A local success wrapper can use map, whose callback returns the plain
    // value. That lets domain-directed callback inference learn its result type.
    fn unreturn(self, e: &Expr) -> Option<Expr> {
        if e.named_args().is_empty()
            && let Some((name,[value],false)) = e.as_named()
            && name == self.wrap
        { return Some(value.clone()); }
        if let ExprKind::Block(b) = &e.kind {
            let mut b = b.clone();
            b.result = Box::new(self.unreturn(&b.result)?);
            return Some(Expr { kind:ExprKind::Block(b),span:e.span });
        }
        None
    }
    fn marker(self, e: &Expr) -> bool {
        matches!(&e.kind, ExprKind::App { head, .. } if matches!(&head.kind, ExprKind::Var(n) if n == self.marker))
    }
    fn contains(self, e: &Expr) -> bool {
        if self.marker(e) { return true; }
        let mut found = false;
        visit(e, &mut |x| found |= self.contains(x));
        found
    }
}
fn fail<T>(span: Span, msg: &str) -> R<T> { Err(ParseError { span, msg: msg.into() }) }

// Visit every expression child, including annotations. This is also used to
// reject propagation in positions which are not executable expressions.
fn ty_children(t: &mut Ty, f: &mut impl FnMut(&mut Expr)) {
    match &mut t.kind {
        TyKind::Eq(a,b) => { f(a); f(b); }
        TyKind::OfExpr(e) | TyKind::Fin(e) | TyKind::TypeOf(e) => f(e),
        TyKind::Named { args, .. } => for t in args { ty_children(t,f); },
        TyKind::Vec { elem, len } => { ty_children(elem,f); f(len); }
        TyKind::Squash(t) | TyKind::Code { ty: t, .. } => ty_children(t,f),
        TyKind::Fn { dom, cod, .. } => { ty_children(dom,f); ty_children(cod,f); }
        _ => {}
    }
}
fn children(e: &mut Expr, f: &mut impl FnMut(&mut Expr)) {
    match &mut e.kind {
        ExprKind::App { head, args, named, .. } => {
            f(head); for a in args { f(a); } for a in named { f(&mut a.expr); }
        }
        ExprKind::TyApp { head, args } => { f(head); for t in args { ty_children(t,f); } }
        ExprKind::Lam { binders, body } => {
            for b in binders { if let Some(t) = &mut b.ty { ty_children(t,f); } } f(body);
        }
        ExprKind::CollectionLit(xs) => for x in xs { f(x); },
        ExprKind::Eq(a,b) | ExprKind::Index { recv:a, idx:b } => { f(a); f(b); }
        ExprKind::TyLit(t) => ty_children(t,f),
        ExprKind::Match { scrut, motive, arms, .. } => {
            f(scrut); if let Some(m) = motive { f(m); } for a in arms { f(&mut a.body); }
        }
        ExprKind::MatchCode { scrut, motive, arms } => {
            f(scrut); ty_children(motive,f); for a in arms { f(&mut a.body); }
        }
        ExprKind::Dot { recv, tyargs, args, named, .. } => {
            f(recv); for t in tyargs { ty_children(t,f); }
            for a in args.iter_mut().flatten() { f(a); } for a in named { f(&mut a.expr); }
        }
        ExprKind::RecordLit { tyargs, fields, .. } => {
            for t in tyargs { ty_children(t,f); } for a in fields { f(&mut a.expr); }
        }
        ExprKind::Block(b) => {
            for s in &mut b.stmts {
                match s {
                    Stmt::Let { ty, expr, .. } => { if let Some(t) = ty { ty_children(t,f); } f(expr); }
                    Stmt::LetRecord { expr, .. } | Stmt::LetCode { expr, .. } => f(expr),
                }
            }
            f(&mut b.result);
            for o in &mut b.ons { f(&mut o.expr); if let OnTarget::Stmt(t) = &mut o.target { ty_children(t,f); } }
        }
        ExprKind::Quote(x) | ExprKind::Splice(x) => f(x),
        ExprKind::J { proof, motive, case } => { f(proof); f(motive); f(case); }
        _ => {}
    }
}
fn ty_visit(t: &Ty, f: &mut impl FnMut(&Expr)) {
    match & t.kind {
        TyKind::Eq(a,b) => { f(a); f(b); }
        TyKind::OfExpr(e) | TyKind::Fin(e) | TyKind::TypeOf(e) => f(e),
        TyKind::Named { args, .. } => for t in args { ty_visit(t,f); },
        TyKind::Vec { elem, len } => { ty_visit(elem,f); f(len); }
        TyKind::Squash(t) | TyKind::Code { ty: t, .. } => ty_visit(t,f),
        TyKind::Fn { dom, cod, .. } => { ty_visit(dom,f); ty_visit(cod,f); }
        _ => {}
    }
}
/// Every expression child of `e`, annotations included: the walk other
/// parser-side lowerings share.
pub(crate) fn visit_children(e: &Expr, f: &mut impl FnMut(&Expr)) { visit(e, f) }

fn visit(e: &Expr, f: &mut impl FnMut(&Expr)) {
    match & e.kind {
        ExprKind::App { head, args, named, .. } => {
            f(head); for a in args { f(a); } for a in named { f(&a.expr); }
        }
        ExprKind::TyApp { head, args } => { f(head); for t in args { ty_visit(t,f); } }
        ExprKind::Lam { binders, body } => {
            for b in binders { if let Some(t) = &b.ty { ty_visit(t,f); } } f(body);
        }
        ExprKind::CollectionLit(xs) => for x in xs { f(x); },
        ExprKind::Eq(a,b) | ExprKind::Index { recv:a, idx:b } => { f(a); f(b); }
        ExprKind::TyLit(t) => ty_visit(t,f),
        ExprKind::Match { scrut, motive, arms, .. } => {
            f(scrut); if let Some(m) = motive { f(m); } for a in arms { f(&a.body); }
        }
        ExprKind::MatchCode { scrut, motive, arms } => {
            f(scrut); ty_visit(motive,f); for a in arms { f(&a.body); }
        }
        ExprKind::Dot { recv, tyargs, args, named, .. } => {
            f(recv); for t in tyargs { ty_visit(t,f); }
            for a in args.iter().flatten() { f(a); } for a in named { f(&a.expr); }
        }
        ExprKind::RecordLit { tyargs, fields, .. } => {
            for t in tyargs { ty_visit(t,f); } for a in fields { f(&a.expr); }
        }
        ExprKind::Block(b) => {
            for s in & b.stmts {
                match s {
                    Stmt::Let { ty, expr, .. } => { if let Some(t) = ty { ty_visit(t,f); } f(expr); }
                    Stmt::LetRecord { expr, .. } | Stmt::LetCode { expr, .. } => f(expr),
                }
            }
            f(&b.result);
            for o in & b.ons { f(&o.expr); if let OnTarget::Stmt(t) = &o.target { ty_visit(t,f); } }
        }
        ExprKind::Quote(x) | ExprKind::Splice(x) => f(x),
        ExprKind::J { proof, motive, case } => { f(proof); f(motive); f(case); }
        _ => {}
    }
}
fn contains(e: &Expr) -> bool { PROPAGATE.contains(e) }
// Substitute only a private, globally fresh continuation slot. It is never a
// written binder, so this substitution needs no capture-avoidance convention.
fn plug(mut e: Expr, slot: &str, value: &Expr) -> Expr {
    if matches!(&e.kind, ExprKind::Var(n) if n == slot) { return value.clone(); }
    children(&mut e, &mut |x| *x = plug(x.clone(),slot,value));
    e
}

struct Lower { next: usize, p: Protocol }
impl Lower {
    fn fresh(&mut self, span: Span) -> Expr {
        let n = self.next; self.next += 1; var(&format!("{}{n}",self.p.slot),span)
    }
    fn identity(&mut self, span: Span) -> (String, Expr) {
        let v = self.fresh(span);
        let ExprKind::Var(n) = &v.kind else { unreachable!() };
        (n.clone(),v)
    }
    fn scope(&mut self, e: Expr) -> R<Expr> {
        let (slot,k) = self.identity(e.span);
        self.cps(e,&slot,k)
    }
    fn cps(&mut self, mut e: Expr, slot: &str, k: Expr) -> R<Expr> {
        let span = e.span;
        if let ExprKind::Lam { binders, body } = &mut e.kind {
            for binder in binders { if let Some(t) = &binder.ty { reject_type(t)?; } }
            **body = self.scope((**body).clone())?;
            return Ok(plug(k,slot,&e));
        }
        if !self.p.contains(&e) { return Ok(plug(k,slot,&e)); }
        match &e.kind {
            ExprKind::TyApp { args, .. } => for t in args { reject_type(t)?; },
            ExprKind::RecordLit { tyargs, .. } => for t in tyargs { reject_type(t)?; },
            _ => {}
        }
        if self.p.marker(&e) {
            let ExprKind::App { mut args, .. } = e.kind else { unreachable!() };
            let input = args.remove(0);
            let (input_slot,input_var) = self.identity(input.span);
            let m = self.p.bind(input_var,slot,k,span);
            return self.cps(input,&input_slot,m);
        }
        // A continuation remains outside written lexical scopes. Package
        // the scope's success value locally, then propagate that Result into
        // the outer continuation. This avoids guessing which bare patterns
        // bind names, and also preserves method/instance lookup scope.
        let identity = matches!(&k.kind,ExprKind::Var(n) if n == slot);
        let returning = k.named_args().is_empty() && matches!(k.as_named(),Some((wrap,args,false))
            if wrap == self.p.wrap && args.len() == 1 && matches!(&args[0].kind,ExprKind::Var(n) if n == slot));
        // A match whose arms bind nothing needs no packaging: only its
        // scrutinee is bound, before the match, and the continuation stays
        // around it (`Pure(match <- e { … })`).
        let arms_bind = match &e.kind {
            ExprKind::Match { arms, motive, .. } => arms.iter().any(|a| self.p.contains(&a.body))
                || motive.as_ref().is_some_and(|m| self.p.contains(m)),
            _ => true,
        };
        if matches!(e.kind,ExprKind::Block(_) | ExprKind::Match { .. }) && !identity && !returning && arms_bind {
            let (s,v) = self.identity(span);
            let success = call(self.p.wrap,vec![v],span);
            let local = self.cps(e,&s,success)?;
            return Ok(self.p.bind(local,slot,k,span));
        }
        match e.kind {
            ExprKind::Block(mut b) => {
                if !b.ons.is_empty() { return fail(span,&format!("{} is not supported in a block with `on` discharges",self.p.what)); }
                if b.stmts.is_empty() { return self.cps(*b.result,slot,k); }
                let first = b.stmts.remove(0);
                let rest = Expr { kind:ExprKind::Block(b),span };
                let rest = self.cps(rest,slot,k)?;
                let (s,v) = self.identity(span);
                let mut statement = first.clone();
                let input = match &mut statement {
                    Stmt::Let { ty, expr, .. } => {
                        if let Some(t) = ty {
                            let mut bad = false; ty_children(t,&mut |e| bad |= self.p.contains(e));
                            if bad { return fail(span,&format!("{} cannot occur in a type annotation",self.p.what)); }
                        }
                        std::mem::replace(expr,v)
                    }
                    Stmt::LetRecord { expr, .. } => std::mem::replace(expr,v),
                    Stmt::LetCode { .. } => return fail(span,&format!("{} cannot cross a `let code` binding",self.p.what)),
                };
                let cont = Expr { kind:ExprKind::Block(Box::new(Block { stmts:vec![statement],result:Box::new(rest),ons:vec![],span })),span };
                self.cps(input,&s,cont)
            }
            ExprKind::Match { form,generated,scrut,eqbind,motive,arms } if !arms_bind => {
                let (s,v) = self.identity(span);
                let matched = Expr { kind:ExprKind::Match { form,generated,scrut:Box::new(v),eqbind,motive,arms },span };
                self.cps(*scrut,&s,plug(k,slot,&matched))
            }
            ExprKind::Match { form,generated,scrut,eqbind,motive,mut arms } => {
                let identity = matches!(&k.kind,ExprKind::Var(n) if n == slot);
                if !identity && motive.is_some() { return fail(span,&format!("{} in a non-tail match with a written motive is not supported; move the match to a helper returning the carrier",self.p.what)); }
                for a in &mut arms {
                    a.body = self.cps(a.body.clone(),slot,k.clone())?;
                }
                let (s,v) = self.identity(span);
                let cont = Expr { kind:ExprKind::Match { form,generated,scrut:Box::new(v),eqbind,motive,arms },span };
                self.cps(*scrut,&s,cont)
            }
            ExprKind::App { .. } | ExprKind::Dot { .. } | ExprKind::Index { .. }
            | ExprKind::CollectionLit(_) | ExprKind::RecordLit { .. } | ExprKind::TyApp { .. } => {
                let mut e = e;
                // Extract expression children in written order, preserving the
                // original application (and its expected-type inference).
                let mut inputs = Vec::new();
                children(&mut e,&mut |x| {
                    if self.p.contains(x) {
                        let (s,v) = self.identity(x.span);
                        inputs.push((s,std::mem::replace(x,v)));
                    }
                });
                let mut out = plug(k,slot,&e);
                for (s,input) in inputs.into_iter().rev() { out = self.cps(input,&s,out)?; }
                Ok(out)
            }
            _ => fail(span,&format!("{} is supported in function/lambda value expressions, not in types, proofs, or quoted code",self.p.what)),
        }
    }
}

pub(crate) fn block(mut b: Block, next: &mut usize) -> R<Block> {
    let e = Expr { kind:ExprKind::Block(Box::new(b.clone())),span:b.span };
    if !contains(&e) { return Ok(b); }
    let ons = std::mem::take(&mut b.ons);
    for on in &ons {
        if contains(&on.expr) { return fail(on.span,"postfix `?` cannot occur in an `on` discharge"); }
        if let OnTarget::Stmt(t) = &on.target { reject_type(t)?; }
    }
    let e = Expr { kind:ExprKind::Block(Box::new(b.clone())),span:b.span };
    let mut lower = Lower { next:*next, p:PROPAGATE };
    let lowered = lower.scope(e);
    *next = lower.next;
    let lowered = lowered?;
    b.stmts.clear(); b.result = Box::new(lowered); b.ons = ons;
    Ok(b)
}


pub(crate) fn expression(e: Expr, next: &mut usize) -> R<Expr> {
    if !contains(&e) { return Ok(e); }
    let mut lower = Lower { next:*next, p:PROPAGATE };
    let out = lower.scope(e);
    *next = lower.next;
    out
}
pub(crate) fn reject_type(t: &Ty) -> R<()> {
    let mut bad = None;
    ty_visit(t,&mut |e| if contains(e) { bad = Some(e.span); });
    if let Some(span) = bad { fail(span,"postfix `?` cannot occur in a type; it returns from a function or lambda") }
    else { Ok(()) }
}

/// A block's binding statements and nested binds, lowered when the block
/// closes (module docs). Inner blocks and λ bodies were lowered when they
/// closed, so every marker the walk meets here is this block's own. The
/// block's `on` discharges stay on it: they are declaration-scoped.
pub(crate) fn binds_in_block(mut b: Block, next: &mut usize) -> R<Block> {
    let e = Expr { kind:ExprKind::Block(Box::new(b.clone())),span:b.span };
    if !BINDING.contains(&e) { return Ok(b); }
    let ons = std::mem::take(&mut b.ons);
    for on in &ons {
        if BINDING.contains(&on.expr) { return fail(on.span,"a bind cannot occur in an `on` discharge"); }
        if let OnTarget::Stmt(t) = &on.target { reject_bind_in_type(t)?; }
    }
    let e = Expr { kind:ExprKind::Block(Box::new(b.clone())),span:b.span };
    let mut lower = Lower { next:*next, p:BINDING };
    let lowered = lower.scope(e);
    *next = lower.next;
    let lowered = lowered?;
    b.stmts.clear(); b.result = Box::new(lowered); b.ons = ons;
    Ok(b)
}

/// A λ body's nested binds: a λ is a scope of its own
/// (docs/sequencing-surface-design.md §3.2), so a bind in its body never
/// leaves it.
pub(crate) fn binds_in_expression(e: Expr, next: &mut usize) -> R<Expr> {
    if !BINDING.contains(&e) { return Ok(e); }
    let mut lower = Lower { next:*next, p:BINDING };
    let out = lower.scope(e);
    *next = lower.next;
    out
}

/// A bind left where no block or λ body scopes it: a declaration's
/// signature, or a type.
pub(crate) fn reject_bind_in_type(t: &Ty) -> R<()> {
    let mut bad = None;
    ty_visit(t,&mut |e| if BINDING.contains(e) { bad = Some(e.span); });
    if let Some(span) = bad { fail(span,"a bind `<- e` cannot occur in a type: it runs inside a block over a carrier") }
    else { Ok(()) }
}

// Labels use an unspellable named-argument key so all existing surface
// traversals and Result lowering preserve their attachment to the call.
// They are consumed by measure lowering before application elaboration.
pub(crate) fn validate_decrease_labels(body: &Block, measured: bool) -> R<()> {
    fn walk(e: &Expr, measured: bool, labels: &mut Vec<String>, error: &mut Option<ParseError>) {
        if let ExprKind::App { named, .. } = &e.kind {
            let mut count = 0;
            for arg in named {
                if let Some(label) = arg.name.strip_prefix("#decreasing:") {
                    count += 1;
                    let message = if !measured { Some("a decrease label needs a declaration with `decreases`".into()) }
                        else if count > 1 { Some("a recursive call takes only one decrease label".into()) }
                        else if labels.iter().any(|n| n == label) { Some(format!("duplicate decrease label `{label}` in this declaration")) }
                        else { None };
                    if error.is_none() { *error = message.map(|msg| ParseError { msg, span: arg.name_span }); }
                    labels.push(label.into());
                }
            }
        }
        visit(e, &mut |e| walk(e, measured, labels, error));
    }
    if !measured && let Some(on) = body.ons.iter().find(|on|
        matches!(&on.target, OnTarget::Name(n) if n.starts_with("#decreasing:")))
    { return fail(on.span, "a named decrease discharge needs a declaration with `decreases`"); }
    let e = Expr { kind: ExprKind::Block(Box::new(body.clone())), span: body.span };
    let mut error = None;
    walk(&e, measured, &mut Vec::new(), &mut error);
    if let Some(error) = error { Err(error) } else { Ok(()) }
}

/// Remove call-site annotations for an isolated type query. The executable
/// source retains them until measure lowering consumes the corresponding call.
pub fn without_decrease_labels(e: &Expr) -> Expr {
    let mut e = e.clone();
    fn strip(e: &mut Expr) {
        if let ExprKind::App { named, .. } = &mut e.kind {
            named.retain(|a| !a.name.starts_with("#decreasing:"));
        }
        children(e, &mut strip);
    }
    strip(&mut e);
    e
}
