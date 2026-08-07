//! Classes and instances, layer 1 (`docs/traits-layer1-design.md`).
//!
//! Nothing here reaches the kernel on its own. A `class` builds the
//! `InductiveDecl` that the equivalent `record` would have built and hands it
//! to `elab_inductive`; an `instance` builds `ast::Decl`s — one per block
//! member, one for the assembled value, one per synthesized canonical parent,
//! one per override-agreement certificate — and hands each to `elab_decl`.
//! Every artifact therefore passes the ordinary declaration gate, and the
//! trusted base is untouched (design §intro).
//!
//! The two tables this round adds are consumed by `extends` and by the
//! instance assembler only. Layer 2's resolver is the consumer they exist for.

use std::collections::HashMap;
use std::rc::Rc;

use heather_syntax::{
    Block, ClassDecl, ClassRef, CtorDecl, Decl, DeclKind, Expr, ExprKind, FieldDecl, InductiveDecl,
    InstanceBody, InstanceDecl, InstanceField, LamBinder, Param, RecordLitField, Span, Stmt, Ty,
    TyKind,
};

use crate::names::qkey;
use crate::{err, ElabError, Elaborator, R};

/// A declared class: the record it is, plus what `extends` and the instance
/// assembler need to know about it.
#[derive(Clone)]
pub(crate) struct ClassInfo {
    /// Unqualified name, as written.
    pub name: String,
    /// Type-parameter names, in order.
    pub params: Vec<String>,
    /// The **flattened** field list — ancestors first, in `ancestors` order,
    /// then the class's own — deduped by name (design §3). This is exactly the
    /// record's field list, so a field's index here is its projection index.
    pub fields: Vec<FieldDecl>,
    /// Every ancestor, transitively, deduped, in the deterministic order the
    /// flattening used. Each `ClassRef`'s arguments are written in terms of
    /// *this* class's parameters, so instantiating this class at `T⃗`
    /// instantiates its ancestors by the same substitution.
    pub ancestors: Vec<ClassRef>,
    /// Which class contributed each field, parallel to `fields`. `None` for
    /// the class's own fields. Used to phrase the collision diagnostic and to
    /// decide which ancestor an inherited field is filled from.
    pub owner: Vec<Option<String>>,
}

/// A registered instance: one canonical value per (class, carrier head)
/// (design §4.1).
#[derive(Clone)]
pub(crate) struct InstanceInfo {
    /// The global that *is* the instance — `Rat::Monoid`.
    pub global: String,
    /// The instance head as written, for diagnostics (`Monoid<Rat>`).
    pub written: String,
    /// `true` when the instance takes parameters (generic instance or
    /// `requires` binders), in which case it cannot be projected from by name
    /// alone — fill-by-reference is refused against it with a clear message.
    pub parameterized: bool,
}

/// The key an instance is registered under. Deliberately *not* the rendered
/// carrier: see design §4.1 and §7.1.
pub(crate) fn instance_key(class_key: &str, head: &str) -> (String, String) {
    (class_key.to_string(), head.to_string())
}

/// The head name of a surface type — the carrier's constructor, which is what
/// the canonical name is built from and what has to name a type in scope.
fn head_name(t: &Ty) -> Option<&str> {
    match &t.kind {
        TyKind::Nat => Some("Nat"),
        TyKind::Named { name, .. } => Some(name),
        _ => None,
    }
}

/// A surface type as written, for diagnostics and for the instance's display
/// name. Not a canonical encoding — nothing keys on it.
pub(crate) fn render_ty(t: &Ty) -> String {
    match &t.kind {
        TyKind::Nat => "Nat".into(),
        TyKind::Univ { level } => format!("Type<{level}>"),
        TyKind::Named { name, args } if args.is_empty() => name.clone(),
        TyKind::Named { name, args } => {
            format!("{name}<{}>", args.iter().map(render_ty).collect::<Vec<_>>().join(", "))
        }
        TyKind::Fn { dom, cod, .. } => format!("{} -> {}", render_ty(dom), render_ty(cod)),
        // A goal may be an ordinary proposition (`p: n = n := infer`), and
        // "`_`" for it would make the whole diagnostic unreadable.
        TyKind::Eq(a, b) => format!("{} = {}", render_expr(a), render_expr(b)),
        TyKind::Vec { elem, .. } => format!("[{}; _]", render_ty(elem)),
        TyKind::Fin(_) => "Fin(_)".into(),
        _ => "_".into(),
    }
}

/// The written form of the few expression shapes that appear inside a *type*
/// worth displaying — an equation's endpoints. Anything larger renders as
/// `_`: this is a diagnostic's display, and nothing keys on it.
fn render_expr(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Var(n) => n.clone(),
        ExprKind::Num(n) => n.to_string(),
        ExprKind::App { head, args, .. } => format!(
            "{}({})",
            render_expr(head),
            args.iter().map(render_expr).collect::<Vec<_>>().join(", ")
        ),
        ExprKind::Dot { recv, name, .. } => format!("{}.{name}", render_expr(recv)),
        _ => "_".into(),
    }
}

fn class_ref_written(r: &ClassRef) -> String {
    format!("{}<{}>", r.name, r.args.iter().map(render_ty).collect::<Vec<_>>().join(", "))
}

fn span_expr(kind: ExprKind, span: Span) -> Expr {
    Expr { kind, span }
}

fn var(name: &str, span: Span) -> Expr {
    span_expr(ExprKind::Var(name.to_string()), span)
}

// -- renaming a parent's type parameters ------------------------------------
//
// `extends` arguments are restricted to the child's own type parameters
// (design §3), so instantiating a parent's stored field declarations is a
// rename. The two walks below are mechanical and total: a missed variant would
// silently leave a parent's parameter name free, which the record's own
// lowering would then report as an unknown type — loud, but at the wrong
// place, so nothing here takes a wildcard shortcut.

type Ren = HashMap<String, String>;

fn ren(m: &Ren, n: &str) -> String {
    m.get(n).cloned().unwrap_or_else(|| n.to_string())
}

fn rename_ty(m: &Ren, t: &Ty) -> Ty {
    let kind = match &t.kind {
        TyKind::Nat => TyKind::Nat,
        TyKind::Univ { level } => TyKind::Univ { level: *level },
        TyKind::Ctx => TyKind::Ctx,
        TyKind::Eq(a, b) => {
            TyKind::Eq(Box::new(rename_expr(m, a)), Box::new(rename_expr(m, b)))
        }
        TyKind::OfExpr(e) => TyKind::OfExpr(Box::new(rename_expr(m, e))),
        TyKind::Named { name, args } => TyKind::Named {
            name: ren(m, name),
            args: args.iter().map(|a| rename_ty(m, a)).collect(),
        },
        TyKind::Vec { elem, len } => TyKind::Vec {
            elem: Box::new(rename_ty(m, elem)),
            len: Box::new(rename_expr(m, len)),
        },
        TyKind::Fin(e) => TyKind::Fin(Box::new(rename_expr(m, e))),
        TyKind::Fn { binder, implicit, dom, cod } => TyKind::Fn {
            binder: binder.clone(),
            implicit: *implicit,
            dom: Box::new(rename_ty(m, dom)),
            cod: Box::new(rename_ty(m, cod)),
        },
        TyKind::TyCode { ctx } => TyKind::TyCode { ctx: ctx.clone() },
        TyKind::Code { ctx, ty } => {
            TyKind::Code { ctx: ctx.clone(), ty: Box::new(rename_ty(m, ty)) }
        }
        TyKind::Splice { name } => TyKind::Splice { name: name.clone() },
    };
    Ty { kind, span: t.span }
}

fn rename_expr(m: &Ren, e: &Expr) -> Expr {
    use ExprKind::*;
    let kind = match &e.kind {
        Var(n) => Var(ren(m, n)),
        Univ { level } => Univ { level: *level },
        Num(n) => Num(*n),
        Refl => Refl,
        AutoRefl => AutoRefl,
        Hole(n) => Hole(n.clone()),
        App { head, args, explicit } => App {
            head: Box::new(rename_expr(m, head)),
            args: args.iter().map(|a| rename_expr(m, a)).collect(),
            explicit: *explicit,
        },
        TyApp { head, args } => TyApp {
            head: Box::new(rename_expr(m, head)),
            args: args.iter().map(|a| rename_ty(m, a)).collect(),
        },
        Lam { binders, body } => Lam {
            binders: binders
                .iter()
                .map(|b| LamBinder {
                    name: b.name.clone(),
                    ty: b.ty.as_ref().map(|t| rename_ty(m, t)),
                    implicit: b.implicit,
                    span: b.span,
                })
                .collect(),
            body: Box::new(rename_expr(m, body)),
        },
        VecLit(es) => VecLit(es.iter().map(|x| rename_expr(m, x)).collect()),
        Eq(a, b) => Eq(Box::new(rename_expr(m, a)), Box::new(rename_expr(m, b))),
        TyLit(t) => TyLit(Box::new(rename_ty(m, t))),
        Match { scrut, eqbind, motive, arms } => Match {
            scrut: Box::new(rename_expr(m, scrut)),
            eqbind: eqbind.clone(),
            motive: motive.as_ref().map(|x| Box::new(rename_expr(m, x))),
            arms: arms
                .iter()
                .map(|a| heather_syntax::Arm {
                    ctor: a.ctor.clone(),
                    default: a.default,
                    binders: a.binders.clone(),
                    body: rename_expr(m, &a.body),
                    span: a.span,
                })
                .collect(),
        },
        Dot { recv, name, args } => Dot {
            recv: Box::new(rename_expr(m, recv)),
            name: name.clone(),
            args: args.as_ref().map(|v| v.iter().map(|a| rename_expr(m, a)).collect()),
        },
        Index { recv, idx } => Index {
            recv: Box::new(rename_expr(m, recv)),
            idx: Box::new(rename_expr(m, idx)),
        },
        RecordLit { name, tyargs, fields } => RecordLit {
            name: ren(m, name),
            tyargs: tyargs.iter().map(|t| rename_ty(m, t)).collect(),
            fields: fields
                .iter()
                .map(|f| RecordLitField {
                    name: f.name.clone(),
                    expr: rename_expr(m, &f.expr),
                    span: f.span,
                })
                .collect(),
        },
        Block(b) => Block(Box::new(rename_block(m, b))),
        Quote(x) => Quote(Box::new(rename_expr(m, x))),
        Splice(x) => Splice(Box::new(rename_expr(m, x))),
        J { proof, motive, case } => J {
            proof: Box::new(rename_expr(m, proof)),
            motive: Box::new(rename_expr(m, motive)),
            case: Box::new(rename_expr(m, case)),
        },
    };
    Expr { kind, span: e.span }
}

fn rename_block(m: &Ren, b: &Block) -> Block {
    Block {
        stmts: b
            .stmts
            .iter()
            .map(|s| match s {
                Stmt::Let { name, ty, expr, span } => Stmt::Let {
                    name: name.clone(),
                    ty: ty.as_ref().map(|t| rename_ty(m, t)),
                    expr: rename_expr(m, expr),
                    span: *span,
                },
                Stmt::LetRecord { fields, expr, span } => Stmt::LetRecord {
                    fields: fields.clone(),
                    expr: rename_expr(m, expr),
                    span: *span,
                },
                Stmt::LetCode { name, expr, span } => Stmt::LetCode {
                    name: name.clone(),
                    expr: rename_expr(m, expr),
                    span: *span,
                },
            })
            .collect(),
        result: Box::new(rename_expr(m, &b.result)),
        ons: b
            .ons
            .iter()
            .map(|o| heather_syntax::OnStmt {
                target: match &o.target {
                    heather_syntax::OnTarget::Name(n) => {
                        heather_syntax::OnTarget::Name(n.clone())
                    }
                    heather_syntax::OnTarget::Stmt(t) => {
                        heather_syntax::OnTarget::Stmt(rename_ty(m, t))
                    }
                    heather_syntax::OnTarget::Ctor { ctor, binders, default } => {
                        heather_syntax::OnTarget::Ctor {
                            ctor: ctor.clone(),
                            binders: binders.clone(),
                            default: *default,
                        }
                    }
                },
                expr: rename_expr(m, &o.expr),
                span: o.span,
            })
            .collect(),
        span: b.span,
    }
}

/// The size of a written type: type constructors and variable occurrences,
/// counted the same way on both sides of the decrease check (§6). Only the
/// *comparison* is meaningful, so a coarse walk is the honest one — anything
/// finer would be a claim about which shapes shrink.
fn ty_size(t: &Ty) -> usize {
    match &t.kind {
        TyKind::Named { args, .. } => 1 + args.iter().map(ty_size).sum::<usize>(),
        TyKind::Vec { elem, .. } => 1 + ty_size(elem),
        TyKind::Fn { dom, cod, .. } => 1 + ty_size(dom) + ty_size(cod),
        _ => 1,
    }
}

/// How often `v` occurs as a bare name in `t` — the second half of Paterson's
/// condition, which is what refuses `C<A> requires C<Pair<A, A>>` even where
/// the sizes happen to agree.
fn ty_var_count(t: &Ty, v: &str) -> usize {
    match &t.kind {
        TyKind::Named { name, args } => {
            (name == v && args.is_empty()) as usize
                + args.iter().map(|a| ty_var_count(a, v)).sum::<usize>()
        }
        TyKind::Vec { elem, .. } => ty_var_count(elem, v),
        TyKind::Fn { dom, cod, .. } => ty_var_count(dom, v) + ty_var_count(cod, v),
        _ => 0,
    }
}

/// A block whose result is `e` and which binds nothing — every synthesized
/// declaration's body.
fn body_of(e: Expr) -> Block {
    let span = e.span;
    Block { stmts: Vec::new(), result: Box::new(e), ons: Vec::new(), span }
}

impl Elaborator {
    // -- classes ------------------------------------------------------------

    /// `class C<p⃗> extends … { f⃗ }` — the record, then the registry entry
    /// (design §2, §3).
    pub(crate) fn elab_class(&mut self, d: &ClassDecl) -> R<()> {
        for (i, p) in d.params.iter().enumerate() {
            if d.params[..i].contains(p) {
                return err(format!("duplicate type parameter `{p}`"), d.span);
            }
        }
        // Flatten: ancestors first, then own fields, deduped by name.
        let mut fields: Vec<FieldDecl> = Vec::new();
        let mut owner: Vec<Option<String>> = Vec::new();
        let mut ancestors: Vec<ClassRef> = Vec::new();
        for parent in &d.extends {
            let (pinfo, rename) = self.parent_view(d, parent)?;
            // The parent's own ancestors come with it, renamed the same way.
            for a in &pinfo.ancestors {
                let a = ClassRef {
                    name: a.name.clone(),
                    args: a.args.iter().map(|t| rename_ty(&rename, t)).collect(),
                    span: parent.span,
                };
                if !ancestors.iter().any(|x| x.name == a.name) {
                    ancestors.push(a);
                }
            }
            if !ancestors.iter().any(|x| x.name == parent.name) {
                ancestors.push(ClassRef {
                    name: parent.name.clone(),
                    args: parent.args.clone(),
                    span: parent.span,
                });
            }
            for (f, o) in pinfo.fields.iter().zip(pinfo.owner.iter()) {
                let from = o.clone().unwrap_or_else(|| pinfo.name.clone());
                let name = f.name.clone().unwrap_or_default();
                if let Some(prev) = fields.iter().position(|g| g.name == f.name) {
                    // A shared ancestor reached twice contributes once. Two
                    // *unrelated* classes contributing one name is a genuine
                    // collision and is refused.
                    let prev_from = owner[prev].clone().unwrap_or_default();
                    if prev_from != from {
                        return err(
                            format!(
                                "field `{name}` is inherited from both `{prev_from}` and \
                                 `{from}`, which are unrelated: flattening collapses a \
                                 shared ancestor reached by two paths, it does not merge \
                                 two different fields"
                            ),
                            parent.span,
                        );
                    }
                    continue;
                }
                fields.push(FieldDecl {
                    name: f.name.clone(),
                    ty: rename_ty(&rename, &f.ty),
                    span: parent.span,
                });
                owner.push(Some(from));
            }
        }
        for f in &d.fields {
            if let Some(prev) = fields.iter().position(|g| g.name == f.name) {
                let from = owner[prev].clone().unwrap_or_default();
                return err(
                    format!(
                        "`{}` already has a field `{}` inherited from `{from}`: a class \
                         does not redeclare an inherited field — an instance overrides it \
                         (and owes agreement)",
                        d.name,
                        f.name.clone().unwrap_or_default()
                    ),
                    f.span,
                );
            }
            fields.push(f.clone());
            owner.push(None);
        }
        // The record. One constructor named after the class, exactly as
        // `record` desugars (docs/surface-records.md §2.1).
        let ctor = CtorDecl {
            name: d.name.clone(),
            fields: fields.clone(),
            result: None,
            span: d.span,
        };
        let ind = InductiveDecl {
            name: d.name.clone(),
            params: d.params.clone(),
            valparams: Vec::new(),
            ctors: vec![ctor],
            is_record: true,
            index: None,
            span: d.span,
        };
        self.elab_inductive(&ind)?;
        // The cheap negative test receiver dispatch consults before it infers
        // anything (docs/traits-receiver-dispatch-design.md §3). Recorded here
        // and not in `elab_inductive`: a plain `record`'s fields are reachable
        // only through a receiver of that record's own type, and dispatch must
        // stay off every call that has nothing to do with a class.
        for f in &fields {
            if let Some(n) = &f.name {
                self.class_members.insert(n.clone());
            }
        }
        let info = ClassInfo {
            name: d.name.clone(),
            params: d.params.clone(),
            fields,
            ancestors,
            owner,
        };
        self.classes.insert(qkey(&self.scope.module, &d.name), Rc::new(info));
        Ok(())
    }

    /// A parent class reference, resolved, with the renaming that instantiates
    /// it at the child's arguments. Layer 1 restricts the arguments to the
    /// child's own type parameters, so instantiation is a rename (design §3).
    fn parent_view(&self, d: &ClassDecl, parent: &ClassRef) -> R<(Rc<ClassInfo>, Ren)> {
        let info = match self.lookup_class(&parent.name) {
            Some(i) => i,
            None => return Err(self.not_a_class(&parent.name, "extends", parent.span)),
        };
        if info.params.len() != parent.args.len() {
            return err(
                format!(
                    "`{}` takes {} type argument(s), {} given",
                    parent.name,
                    info.params.len(),
                    parent.args.len()
                ),
                parent.span,
            );
        }
        let mut rename = Ren::new();
        for (p, a) in info.params.iter().zip(parent.args.iter()) {
            let arg = match &a.kind {
                TyKind::Named { name, args } if args.is_empty() && d.params.contains(name) => {
                    name.clone()
                }
                _ => {
                    return err(
                        format!(
                            "an `extends` argument must be one of `{}`'s own type parameters \
                             (`{}`), and `{}` is not: instantiating a parent at a composite \
                             type is refused at layer 1 rather than half-supported \
                             (docs/traits-layer1-design.md §3)",
                            d.name,
                            d.params.join(", "),
                            render_ty(a)
                        ),
                        a.span,
                    )
                }
            };
            rename.insert(p.clone(), arg);
        }
        Ok((info, rename))
    }

    /// The diagnostic for a name in class position that is not a class. A
    /// *declared* type gets told what it is: `instance R<Z>` on a `record R`
    /// is the mistake this catches, and "unbound name" would be a lie.
    fn not_a_class(&self, name: &str, what: &str, span: Span) -> ElabError {
        if self.lookup_inductive(name).is_some() {
            return ElabError::Elab {
                msg: format!(
                    "`{name}` is not a class, so it has no instances and cannot be \
                     extended: `{what}` takes a `class`, and a plain `record` value is \
                     written as an ordinary `fn`"
                ),
                span,
            };
        }
        self.name_miss(name, format!("`{name}` is not a class in scope"), span)
    }

    pub(crate) fn lookup_class(&self, name: &str) -> Option<Rc<ClassInfo>> {
        self.classes.get(&self.key_of(name)?).cloned()
    }

    /// The colon in a type-parameter list carries two nouns — a **universe**
    /// (`<A: Type<n>>`, where `A` lives) and a **class** (`<A: Monoid>`, what
    /// `A` carries) — told apart by the head word alone
    /// (issues/requires-placement-syntax.md §R2-A). A word that is neither is
    /// the one place that reading can go wrong, so it is reported here, naming
    /// both readings, rather than falling out of the desugared type as
    /// "unknown type `Nat`" — a complaint about `Nat<A>`, which the user never
    /// wrote.
    ///
    /// Constraint parameters are recognized by their unspellable `#`-prefixed
    /// binder name, which is the parser's mark that this `Param` came from the
    /// inline form and not from a `requires` binder (whose type is checked by
    /// the ordinary class-reference path, with the user's own name to blame).
    pub(crate) fn check_constraint_param(&self, p: &Param) -> R<()> {
        if !p.name.starts_with("#constraint") {
            return Ok(());
        }
        let TyKind::Named { name, .. } = &p.ty.kind else { return Ok(()) };
        if self.lookup_class(name).is_some() {
            return Ok(());
        }
        err(
            format!(
                "`{name}` is not a class, so it cannot constrain a type parameter. \
                 After the colon in `<A: …>` there are two readings and this is \
                 neither: a UNIVERSE — `Type`, `Type<n>` — saying where `A` lives, or \
                 the name of a `class`, saying what `A` carries"
            ),
            p.span,
        )
    }

    // -- instances ----------------------------------------------------------

    /// `instance C<T⃗> { … }` (design §4).
    ///
    /// All-or-nothing, like every other declaration form: an instance emits
    /// several globals (its members, its value, its synthesized parents, its
    /// agreement certificates) and a failure at any of them must leave none of
    /// them behind. `Elaborator` is cheaply clonable exactly so that this kind
    /// of speculative work is expressible (`lib.rs`, the `Clone` note).
    pub(crate) fn elab_instance(&mut self, d: &InstanceDecl) -> R<()> {
        let snapshot = self.clone();
        let r = self.elab_instance_inner(d);
        if r.is_err() {
            *self = snapshot;
        }
        r
    }

    fn elab_instance_inner(&mut self, d: &InstanceDecl) -> R<()> {
        let class = match self.lookup_class(&d.class.name) {
            Some(c) => c,
            None => return Err(self.not_a_class(&d.class.name, "instance", d.class.span)),
        };
        let class_key = self
            .key_of(&d.class.name)
            .expect("a class that resolved has a key");
        if class.params.len() != d.class.args.len() {
            return err(
                format!(
                    "`{}` takes {} type argument(s), {} given",
                    d.class.name,
                    class.params.len(),
                    d.class.args.len()
                ),
                d.class.span,
            );
        }
        let carrier = &d.class.args[0];
        let Some(head) = head_name(carrier) else {
            return err(
                format!(
                    "the carrier `{}` has no head type name, so this instance has no \
                     canonical name (docs/traits-layer1-design.md §4.1)",
                    render_ty(carrier)
                ),
                carrier.span,
            );
        };
        let head = head.to_string();
        if !self.names_a_type(&head) {
            return err(
                format!(
                    "`{head}` is not a type in scope, so `{head}::{}` attaches to nothing",
                    d.class.name
                ),
                carrier.span,
            );
        }
        let prefix = format!("{head}::{}", class.name);
        let key = instance_key(&class_key, &head);
        if let Some(prev) = self.instances.get(&key) {
            return err(
                format!(
                    "`{}` already has an instance of `{}` (`{}`), declared as `{}`: at layer \
                     1 the canonical name is keyed on the carrier's *head*, so two carriers \
                     with the same head collide — this is refused rather than silently \
                     overwritten (docs/traits-layer1-design.md §4.1)",
                    head, class.name, prev.global, prev.written
                ),
                d.class.span,
            );
        }
        let parameterized = !d.tyvars.is_empty() || !d.requires.is_empty();
        let written = class_ref_written(&d.class);
        // Termination, checked here rather than detected when it hangs
        // (docs/traits-layer2-design.md §6).
        self.check_decrease(d, &written)?;

        // The class type as a surface type: `Monoid<Rat>`.
        let class_ty = Ty {
            kind: TyKind::Named { name: d.class.name.clone(), args: d.class.args.clone() },
            span: d.class.span,
        };

        // 1. Block members, in order, each a real global under the prefix.
        let mut member_names: Vec<String> = Vec::new();
        if let InstanceBody::Block(members) = &d.body {
            for m in members {
                if m.name.contains("::") {
                    return err(
                        format!(
                            "`{}` is a member of this instance's namespace and is written \
                             unqualified: the prefix `{prefix}` is the declaration's",
                            m.name
                        ),
                        m.span,
                    );
                }
                if class.fields.iter().all(|f| f.name.as_deref() != Some(m.name.as_str())) {
                    return err(
                        format!(
                            "`{}` is not a field of `{}`: an instance's members are its \
                             class's fields",
                            m.name, class.name
                        ),
                        m.span,
                    );
                }
                if member_names.iter().any(|n| n == &m.name) {
                    return err(format!("duplicate member `{}`", m.name), m.span);
                }
                // A `meta fn` is elaborator-held and never reaches Ψ, so it
                // cannot be a field's value; and an elaboration template's slot
                // is claimed program-wide, which an instance's namespace has no
                // business doing. Both are refused by name.
                if m.is_meta || m.elaborates.is_some() {
                    return err(
                        format!(
                            "`{}` cannot be a `meta fn`: an instance member is the value of \
                             a field, and a meta definition never reaches Ψ",
                            m.name
                        ),
                        m.span,
                    );
                }
                let full = format!("{prefix}::{}", m.name);
                let decl = Decl {
                    kind: m.kind,
                    is_meta: m.is_meta,
                    elaborates: m.elaborates.clone(),
                    name: full,
                    tyvars: d.tyvars.iter().cloned().chain(m.tyvars.iter().cloned()).collect(),
                    params: d.requires.iter().cloned().chain(m.params.iter().cloned()).collect(),
                    result: m.result.clone(),
                    body: m.body.clone(),
                    span: m.span,
                };
                self.elab_decl(&decl)?;
                // Only *after* it lands does the name become visible to the
                // members after it (design §4.2): a member cannot reference
                // itself or a later one by short name.
                member_names.push(m.name.clone());
                self.instance_scope.push((m.name.clone(), format!("{prefix}::{}", m.name)));
            }
        }
        // The scope is a block-local device and must not survive the block.
        // On the failure path the whole snapshot is restored, which clears it
        // too.
        let r = self.assemble_instance(d, &class, &head, &prefix, &class_ty, &written);
        self.instance_scope.clear();
        r?;
        self.instances.insert(
            key,
            InstanceInfo { global: prefix, written, parameterized },
        );
        Ok(())
    }

    /// Fields 2–4 of design §4.3, then the canonical parents (§4.4) and the
    /// override certificates (§4.5).
    #[allow(clippy::too_many_arguments)]
    fn assemble_instance(
        &mut self,
        d: &InstanceDecl,
        class: &ClassInfo,
        head: &str,
        prefix: &str,
        class_ty: &Ty,
        written: &str,
    ) -> R<()> {
        let span = d.class.span;
        // A reference to one of this instance's members no longer applies the
        // `requires` binders: they are **solver parameters**
        // (docs/traits-layer2-design.md §1, §9.3), so the reference leaves
        // them to resolution, which finds them where they are — as locals of
        // this very declaration, the first ascending scope. Layer 1 passed
        // them by hand, and that is exactly the rule this round retires.

        // The instance's own type parameters, as type arguments. They are
        // written *explicitly* rather than left implicit because the reference
        // is a partial application — the member still wants its own arguments
        // — and mixing partial application with implicit insertion is refused
        // by the applicator (docs/unifier-completeness-design.md §5.3). Under
        // `f<A, B>` the leading type parameters are consumed by the
        // `param_offset` route and the remainder may be a prefix — which at
        // layer 2 is exactly the solver parameters, filled by resolution from
        // this declaration's own binders (docs/traits-layer2-design.md §9.3).
        let tyargs: Vec<Ty> = d
            .tyvars
            .iter()
            .map(|t| Ty { kind: TyKind::Named { name: t.name.clone(), args: vec![] }, span })
            .collect();
        let member_ref = |name: &str| -> Expr {
            let full = format!("{prefix}::{name}");
            if tyargs.is_empty() {
                var(&full, span)
            } else {
                span_expr(
                    ExprKind::TyApp { head: Box::new(var(&full, span)), args: tyargs.clone() },
                    span,
                )
            }
        };

        // What the body says about each field, by name.
        let mut written_fields: HashMap<String, Expr> = HashMap::new();
        match &d.body {
            InstanceBody::Block(members) => {
                for m in members {
                    written_fields.insert(m.name.clone(), member_ref(&m.name));
                }
            }
            InstanceBody::Literal(fields) => {
                for InstanceField { name, expr, span: fspan } in fields {
                    if class.fields.iter().all(|f| f.name.as_deref() != Some(name.as_str())) {
                        return err(
                            format!("`{name}` is not a field of `{}`", class.name),
                            *fspan,
                        );
                    }
                    if written_fields.insert(name.clone(), expr.clone()).is_some() {
                        return err(format!("duplicate field `{name}`"), *fspan);
                    }
                }
            }
        }

        // An ancestor's arguments are written in terms of *the class's* type
        // parameters (design §3), so instantiating the class at `T⃗`
        // instantiates its ancestors by the same positional substitution. The
        // §3 restriction is what makes this a lookup rather than a walk.
        let anc_args = |a: &ClassRef| -> Vec<Ty> {
            a.args
                .iter()
                .map(|arg| match &arg.kind {
                    TyKind::Named { name, args } if args.is_empty() => class
                        .params
                        .iter()
                        .position(|p| p == name)
                        .map(|i| d.class.args[i].clone())
                        .unwrap_or_else(|| arg.clone()),
                    _ => arg.clone(),
                })
                .collect()
        };

        // Ancestors that already have a canonical instance at this carrier —
        // the fill-by-reference source (design §4.3 rule 3) and the agreement
        // partner (§4.5).
        let mut registered: Vec<(String, Rc<ClassInfo>, String)> = Vec::new();
        for a in &class.ancestors {
            let Some(akey) = self.key_of(&a.name) else { continue };
            let Some(inst) = self.instances.get(&instance_key(&akey, head)) else { continue };
            // A *parameterized* canonical parent (a generic instance, or one
            // with `requires` binders) offers neither fill-by-reference nor an
            // agreement partner at layer 1: its value is a function, and
            // deciding what to apply it to is resolution, which does not exist
            // yet. It is skipped rather than refused — the consequence is an
            // honest missing-field error if the child leaves the field out
            // (docs/traits-layer1-design.md §8).
            if inst.parameterized {
                continue;
            }
            let g = inst.global.clone();
            let Some(ainfo) = self.classes.get(&akey).cloned() else { continue };
            registered.push((a.name.clone(), ainfo, g));
        }

        // 2. The field values, in declaration order.
        let mut lit_fields: Vec<RecordLitField> = Vec::new();
        let mut agreements: Vec<(String, Expr, Expr, String)> = Vec::new();
        let mut missing: Vec<String> = Vec::new();
        for f in &class.fields {
            let Some(fname) = f.name.clone() else { continue };
            // The ancestor that canonically holds this field, if any.
            let from_parent = registered
                .iter()
                .find(|(_, info, _)| {
                    info.fields.iter().any(|g| g.name.as_deref() == Some(fname.as_str()))
                })
                .map(|(aname, _, g)| {
                    (
                        aname.clone(),
                        span_expr(
                            ExprKind::Dot {
                                recv: Box::new(var(g, span)),
                                name: fname.clone(),
                                args: None,
                            },
                            span,
                        ),
                    )
                });
            match (written_fields.get(&fname), from_parent) {
                (Some(e), Some((aname, pe))) => {
                    // An override of a field a canonical value already holds
                    // owes agreement (design §4.5).
                    agreements.push((fname.clone(), e.clone(), pe, aname));
                    lit_fields.push(RecordLitField { name: fname, expr: e.clone(), span });
                }
                (Some(e), None) => {
                    lit_fields.push(RecordLitField { name: fname, expr: e.clone(), span })
                }
                (None, Some((_, pe))) => {
                    lit_fields.push(RecordLitField { name: fname, expr: pe, span })
                }
                (None, None) => missing.push(fname),
            }
        }
        if !missing.is_empty() {
            return err(
                format!(
                    "`instance {written}` is missing {}: {}",
                    if missing.len() == 1 { "a field" } else { "fields" },
                    missing.join(", ")
                ),
                span,
            );
        }

        // 3. The value itself.
        let lit = span_expr(
            ExprKind::RecordLit {
                name: class.name.clone(),
                tyargs: d.class.args.clone(),
                fields: lit_fields.clone(),
            },
            span,
        );
        self.synth_decl(DeclKind::Fn, prefix, d, class_ty.clone(), lit, span)?;

        // 4. Override agreements — kernel-checked convertibility, as a real
        // certificate rather than a side-effect (design §4.5).
        for (fname, over, parent, aname) in agreements {
            let stmt = Ty { kind: TyKind::Eq(Box::new(over), Box::new(parent)), span };
            let name = format!("{prefix}::{fname}#agrees");
            let proof = span_expr(ExprKind::Refl, span);
            self.synth_decl(DeclKind::Theorem, &name, d, stmt, proof, span).map_err(|e| {
                ElabError::Elab {
                    msg: format!(
                        "`instance {written}` overrides `{fname}`, which the canonical \
                         `{aname}` at `{head}` already holds, and the two are not \
                         convertible: an override owes agreement \
                         (docs/traits-layer1-design.md §4.5). The kernel said: {}",
                        e
                    ),
                    span,
                }
            })?;
        }

        // 5. Canonical parents not yet registered — synthesized as this
        // instance's projections, sharing its very field expressions, so a
        // diamond collapses by construction (design §4.4).
        let parameterized = !d.tyvars.is_empty() || !d.requires.is_empty();
        for a in class.ancestors.clone() {
            let Some(akey) = self.key_of(&a.name) else {
                return err(format!("`{}` is not a class in scope", a.name), span);
            };
            if self.instances.contains_key(&instance_key(&akey, head)) {
                continue;
            }
            let Some(ainfo) = self.classes.get(&akey).cloned() else { continue };
            let aname = format!("{head}::{}", ainfo.name);
            let aargs = anc_args(&a);
            let aty =
                Ty { kind: TyKind::Named { name: a.name.clone(), args: aargs.clone() }, span };
            // Every field of a flattened ancestor is one of the child's, by
            // construction (design §3) — so the parent's value is literally
            // built from the child's own field expressions, which is what makes
            // the diamond collapse structural rather than incidental. Reported
            // rather than asserted: a violation would mean the flattening and
            // the registry disagree, and a library must not panic to say so.
            let mut afields: Vec<RecordLitField> = Vec::new();
            for n in ainfo.fields.iter().filter_map(|g| g.name.clone()) {
                match lit_fields.iter().find(|x| x.name == n) {
                    Some(x) => afields.push(x.clone()),
                    None => {
                        return err(
                            format!(
                                "internal: `{}` inherits `{n}` from `{}`, which the \
                                 flattened field list does not have",
                                class.name, ainfo.name
                            ),
                            span,
                        )
                    }
                }
            }
            let alit = span_expr(
                ExprKind::RecordLit {
                    name: ainfo.name.clone(),
                    tyargs: aargs.clone(),
                    fields: afields,
                },
                span,
            );
            self.synth_decl(DeclKind::Fn, &aname, d, aty, alit, span)?;
            self.instances.insert(
                instance_key(&akey, head),
                InstanceInfo {
                    global: aname,
                    written: class_ref_written(&ClassRef {
                        name: a.name.clone(),
                        args: aargs,
                        span,
                    }),
                    parameterized,
                },
            );
        }
        Ok(())
    }

    /// Structural decrease of the `requires` subgoals against the instance
    /// head (docs/traits-layer2-design.md §6, record §6.3): Paterson's
    /// condition, checked at the declaration over the *written* types.
    ///
    /// A `requires` binder whose type is not a class is not a subgoal at all —
    /// it is an `infer` goal, answered by the scope and never by backchaining
    /// — so it cannot feed a loop and is skipped.
    fn check_decrease(&self, d: &InstanceDecl, written: &str) -> R<()> {
        let vars: Vec<&str> = d.tyvars.iter().map(|t| t.name.as_str()).collect();
        let head: usize = d.class.args.iter().map(ty_size).sum();
        for p in &d.requires {
            // `instance<A: Mag> …` — the inline form's class is checked here,
            // the first place the instance head is known to be one.
            self.check_constraint_param(p)?;
            let TyKind::Named { name, args } = &p.ty.kind else { continue };
            if args.is_empty() || self.lookup_class(name).is_none() {
                continue;
            }
            let sub: usize = args.iter().map(ty_size).sum();
            let refuse = |why: String| {
                err::<()>(
                    format!(
                        "`instance {written}` cannot be resolved for: the subgoal \
                         `{}: {}` {why}, so a search that used this instance could \
                         feed itself forever. Each `requires` subgoal must be \
                         structurally smaller than the instance head \
                         (docs/traits-layer2-design.md §6); the escape is a named \
                         instance value, applied by hand.",
                        p.name,
                        render_ty(&p.ty)
                    ),
                    p.span,
                )
            };
            // The variable condition first: where both fail it is the more
            // specific complaint, and it is the one a reader can act on.
            for v in &vars {
                if ty_var_count(&p.ty, v) > d.class.args.iter().map(|a| ty_var_count(a, v)).sum() {
                    refuse(format!("mentions `{v}` more often than the head does"))?;
                }
            }
            if sub >= head {
                refuse(format!(
                    "is not smaller than the head `{}` ({sub} against {head})",
                    class_ref_written(&d.class)
                ))?;
            }
        }
        Ok(())
    }

    /// One synthesized declaration carrying the instance's own telescope.
    fn synth_decl(
        &mut self,
        kind: DeclKind,
        name: &str,
        d: &InstanceDecl,
        result: Ty,
        body: Expr,
        span: Span,
    ) -> R<()> {
        let decl = Decl {
            kind,
            is_meta: false,
            elaborates: None,
            name: name.to_string(),
            tyvars: d.tyvars.clone(),
            params: d.requires.clone(),
            result,
            body: body_of(body),
            span,
        };
        self.elab_decl(&decl)
    }
}
