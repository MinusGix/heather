//! Function-scoped Result propagation, lowered to ordinary surface matches.
//! No new kernel form or evaluation rule is involved.
use crate::ast::*;
use crate::parser::ParseError;
type R<T> = Result<T, ParseError>;
pub(crate) const TRY: &str = "\0result-propagate";

fn var(name: &str, span: Span) -> Expr { Expr { kind: ExprKind::Var(name.into()), span } }
fn call(name: &str, args: Vec<Expr>, span: Span) -> Expr {
    Expr { kind:ExprKind::App { head:Box::new(var(name,span)),args,named:vec![],explicit:false,goal_oriented:false },span }
}
fn bind(input: Expr, slot: &str, body: Expr, span: Span) -> Expr {
    let continuation = Expr { kind:ExprKind::Lam {
        binders:vec![LamBinder { name:slot.into(),ty:None,implicit:false,span }],body:Box::new(body),
    },span };
    let mut continuation = continuation;
    let ExprKind::Lam { body,.. } = &mut continuation.kind else { unreachable!() };
    let name = if let Some(value) = unreturn(body) {
        **body = value;
        "result::map"
    } else { "result::and_then" };
    call(name,vec![input,continuation],span)
}
// A local success wrapper can use map, whose callback returns the plain
// value. That lets domain-directed callback inference learn its result type.
fn unreturn(e: &Expr) -> Option<Expr> {
    if e.named_args().is_empty()
        && let Some(("result::Ok",[value],false)) = e.as_named()
    { return Some(value.clone()); }
    if let ExprKind::Block(b) = &e.kind {
        let mut b = b.clone();
        b.result = Box::new(unreturn(&b.result)?);
        return Some(Expr { kind:ExprKind::Block(b),span:e.span });
    }
    None
}
fn fail<T>(span: Span, msg: &str) -> R<T> { Err(ParseError { span, msg: msg.into() }) }

// Visit every expression child, including annotations. This is also used to
// reject propagation in positions which are not executable expressions.
fn ty_children(t: &mut Ty, f: &mut impl FnMut(&mut Expr)) {
    match &mut t.kind {
        TyKind::Eq(a,b) => { f(a); f(b); }
        TyKind::OfExpr(e) | TyKind::Fin(e) => f(e),
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
        ExprKind::Dot { recv, args, named, .. } => {
            f(recv); for a in args.iter_mut().flatten() { f(a); } for a in named { f(&mut a.expr); }
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
        TyKind::OfExpr(e) | TyKind::Fin(e) => f(e),
        TyKind::Named { args, .. } => for t in args { ty_visit(t,f); },
        TyKind::Vec { elem, len } => { ty_visit(elem,f); f(len); }
        TyKind::Squash(t) | TyKind::Code { ty: t, .. } => ty_visit(t,f),
        TyKind::Fn { dom, cod, .. } => { ty_visit(dom,f); ty_visit(cod,f); }
        _ => {}
    }
}
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
        ExprKind::Dot { recv, args, named, .. } => {
            f(recv); for a in args.iter().flatten() { f(a); } for a in named { f(&a.expr); }
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
fn marker(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::App { head, .. } if matches!(&head.kind, ExprKind::Var(n) if n == TRY))
}
fn contains(e: &Expr) -> bool {
    if marker(e) { return true; }
    let mut found = false;
    visit(e, &mut |x| found |= contains(x));
    found
}
// Substitute only a private, globally fresh continuation slot. It is never a
// written binder, so this substitution needs no capture-avoidance convention.
fn plug(mut e: Expr, slot: &str, value: &Expr) -> Expr {
    if matches!(&e.kind, ExprKind::Var(n) if n == slot) { return value.clone(); }
    children(&mut e, &mut |x| *x = plug(x.clone(),slot,value));
    e
}

struct Lower { next: usize }
impl Lower {
    fn fresh(&mut self, span: Span) -> Expr {
        let n = self.next; self.next += 1; var(&format!("#try{n}"),span)
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
        if !contains(&e) { return Ok(plug(k,slot,&e)); }
        match &e.kind {
            ExprKind::TyApp { args, .. } => for t in args { reject_type(t)?; },
            ExprKind::RecordLit { tyargs, .. } => for t in tyargs { reject_type(t)?; },
            _ => {}
        }
        if marker(&e) {
            let ExprKind::App { mut args, .. } = e.kind else { unreachable!() };
            let input = args.remove(0);
            let (input_slot,input_var) = self.identity(input.span);
            let m = bind(input_var,slot,k,span);
            return self.cps(input,&input_slot,m);
        }
        // A continuation remains outside written lexical scopes. Package
        // the scope's success value locally, then propagate that Result into
        // the outer continuation. This avoids guessing which bare patterns
        // bind names, and also preserves method/instance lookup scope.
        let identity = matches!(&k.kind,ExprKind::Var(n) if n == slot);
        let returning = k.named_args().is_empty() && matches!(k.as_named(),Some(("result::Ok",args,false))
            if args.len() == 1 && matches!(&args[0].kind,ExprKind::Var(n) if n == slot));
        if matches!(e.kind,ExprKind::Block(_) | ExprKind::Match { .. }) && !identity && !returning {
            let (s,v) = self.identity(span);
            let success = call("result::Ok",vec![v],span);
            let local = self.cps(e,&s,success)?;
            return Ok(bind(local,slot,k,span));
        }
        match e.kind {
            ExprKind::Block(mut b) => {
                if !b.ons.is_empty() { return fail(span,"postfix `?` is not supported in a block with `on` discharges"); }
                if b.stmts.is_empty() { return self.cps(*b.result,slot,k); }
                let first = b.stmts.remove(0);
                let rest = Expr { kind:ExprKind::Block(b),span };
                let rest = self.cps(rest,slot,k)?;
                let (s,v) = self.identity(span);
                let mut statement = first.clone();
                let input = match &mut statement {
                    Stmt::Let { ty, expr, .. } => {
                        if let Some(t) = ty {
                            let mut bad = false; ty_children(t,&mut |e| bad |= contains(e));
                            if bad { return fail(span,"postfix `?` cannot occur in a type annotation"); }
                        }
                        std::mem::replace(expr,v)
                    }
                    Stmt::LetRecord { expr, .. } => std::mem::replace(expr,v),
                    Stmt::LetCode { .. } => return fail(span,"postfix `?` cannot cross a `let code` binding"),
                };
                let cont = Expr { kind:ExprKind::Block(Box::new(Block { stmts:vec![statement],result:Box::new(rest),ons:vec![],span })),span };
                self.cps(input,&s,cont)
            }
            ExprKind::Match { form,generated,scrut,eqbind,motive,mut arms } => {
                let identity = matches!(&k.kind,ExprKind::Var(n) if n == slot);
                if !identity && motive.is_some() { return fail(span,"postfix `?` in a non-tail match with a written motive is not supported; move the match to a Result-returning helper"); }
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
                    if contains(x) {
                        let (s,v) = self.identity(x.span);
                        inputs.push((s,std::mem::replace(x,v)));
                    }
                });
                let mut out = plug(k,slot,&e);
                for (s,input) in inputs.into_iter().rev() { out = self.cps(input,&s,out)?; }
                Ok(out)
            }
            _ => fail(span,"postfix `?` is supported in function/lambda value expressions, not in types, proofs, or quoted code"),
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
    let mut lower = Lower { next:*next };
    let lowered = lower.scope(e);
    *next = lower.next;
    let lowered = lowered?;
    b.stmts.clear(); b.result = Box::new(lowered); b.ons = ons;
    Ok(b)
}


pub(crate) fn expression(e: Expr, next: &mut usize) -> R<Expr> {
    if !contains(&e) { return Ok(e); }
    let mut lower = Lower { next:*next };
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
