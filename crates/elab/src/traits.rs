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
    Block, ClassDecl, ClassRef, CtorDecl, Decl, DeclKind, DesignationDecl, Expr, ExprKind, FieldDecl,
    InductiveDecl,
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
    /// `class Monoid<A>(op: A -> A -> A)` — the declared **value indices**
    /// (docs/operation-indexed-classes-design.md §3), types written in terms
    /// of `params`. Empty for an unindexed class. Their names are what a
    /// constraint binder binds the index under (§4).
    pub valparams: Vec<Param>,
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
    /// The **index spelling** this instance is keyed at
    /// (docs/operation-indexed-classes-design.md §3.1) — the resolved global
    /// key of each index argument, joined. Empty at an unindexed class. It is
    /// part of the registry key and it is what a value-slot refusal lists.
    pub index: String,
    /// `true` when the instance takes parameters (generic instance or
    /// `requires` binders), in which case it cannot be projected from by name
    /// alone — fill-by-reference is refused against it with a clear message.
    pub parameterized: bool,
}

/// A registered **designation**: what one operator symbol means at one
/// carrier head (docs/operators-onto-classes-design.md §3).
#[derive(Clone)]
pub(crate) struct DesignationInfo {
    /// The designated operation, as a bare global name. Emitted bare at each
    /// use site and instantiated there by ordinary implicit inference — which
    /// is why the declaration refuses anything but a name (§3.2).
    pub op: String,
    /// The declaration as written, for the duplicate diagnostic.
    pub written: String,
}

/// The key an instance is registered under. Deliberately *not* the rendered
/// carrier: see design §4.1 and §7.1.
///
/// The third component is the **index spelling**
/// (docs/operation-indexed-classes-design.md §3.1): two instances at one key
/// are the duplicate-declaration error they always were, two at different
/// indices coexist as equals. Empty at an unindexed class, so every key that
/// predates value indices is unchanged.
pub(crate) type InstKey = (String, String, String);

pub(crate) fn instance_key(class_key: &str, head: &str, index: &str) -> InstKey {
    (class_key.to_string(), head.to_string(), index.to_string())
}

/// The index spelling as a *name* fragment: a key may contain `::` (a
/// resolved global's qualifier) and a declaration name must not, since one
/// `::` is a member qualifier and two are refused.
fn name_suffix(index: &str) -> String {
    index.replace("::", "#").replace(", ", "#")
}

/// The head name of a surface type — the carrier's constructor, which is what
/// the canonical name is built from and what has to name a type in scope.
fn head_name(t: &Ty) -> Option<&str> {
    match &t.kind {
        TyKind::Nat => Some("Nat"),
        TyKind::Named { name, .. } => Some(name),
        // An **applied type former** — `Le(n, m)`, `Not(P)` — whose head is the
        // former's own name (widened 2026-08-17, docs/decide-class-design.md §2).
        // A proposition stated by recursion into `Type` is the carrier a
        // decidability class is *for*, and it arrives here as an ordinary
        // application rather than as a `Named` type, because `Le` is a `fn`.
        //
        // Deliberately NOT `TyKind::Eq`: an equation's head would have to be one
        // reserved key for every equality at every type, so `Decide<n = m>` at
        // `Nat` and at `Bool` would collide as duplicates. Keying that needs the
        // endpoints' type in the key, which is the (class, carrier-syntax) key
        // §7.1 defers to layer 2 — the one case of this round that genuinely
        // wants it (issues/decidable-equation-carrier.md).
        TyKind::OfExpr(e) => match &e.kind {
            ExprKind::App { head, .. } => match &head.kind {
                ExprKind::Var(name) => Some(name),
                _ => None,
            },
            _ => None,
        },
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
        // `Monoid<A>(op)` — a class at its index, which arrives applied
        // (docs/operation-indexed-classes-design.md §3). Rendering it as `_`
        // would empty out every diagnostic the indexed classes produce.
        TyKind::OfExpr(e) => match &e.kind {
            ExprKind::App { head, args, .. } => {
                let h = match &head.kind {
                    ExprKind::TyApp { head, args } => format!(
                        "{}<{}>",
                        render_expr(head),
                        args.iter().map(render_ty).collect::<Vec<_>>().join(", ")
                    ),
                    _ => render_expr(head),
                };
                format!("{h}({})", args.iter().map(render_expr).collect::<Vec<_>>().join(", "))
            }
            _ => render_expr(e),
        },
        _ => "_".into(),
    }
}

/// The written form of the few expression shapes that appear inside a *type*
/// worth displaying — an equation's endpoints. Anything larger renders as
/// `_`: this is a diagnostic's display, and nothing keys on it.
pub(crate) fn render_expr(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Var(n) => n.clone(),
        ExprKind::OpSymbol(s) => s.clone(),
        ExprKind::Num(n) => n.to_string(),
        // An operator application renders as what was **written**
        // (`a + b`, never `add(a, b)`) — the standing ask of
        // `issues/diagnostics-name-the-written-form.md`, arriving free now
        // that the symbol survives into the AST.
        ExprKind::App { head, args, .. }
            if matches!(head.kind, ExprKind::OpSymbol(_)) && args.len() == 2 =>
        {
            format!("{} {} {}", render_expr(&args[0]), render_expr(head), render_expr(&args[1]))
        }
        ExprKind::App { head, args, .. } => format!(
            "{}({})",
            render_expr(head),
            args.iter().map(render_expr).collect::<Vec<_>>().join(", ")
        ),
        ExprKind::Dot { recv, name, .. } => format!("{}.{name}", render_expr(recv)),
        _ => "_".into(),
    }
}

pub(crate) fn class_ref_written(r: &ClassRef) -> String {
    let head =
        format!("{}<{}>", r.name, r.args.iter().map(render_ty).collect::<Vec<_>>().join(", "));
    if r.index.is_empty() {
        return head;
    }
    format!("{head}({})", r.index.iter().map(render_expr).collect::<Vec<_>>().join(", "))
}

fn span_expr(kind: ExprKind, span: Span) -> Expr {
    Expr { kind, span }
}

fn var(name: &str, span: Span) -> Expr {
    span_expr(ExprKind::Var(name.to_string()), span)
}

/// What [`Elaborator::expand_constraints`] produces: the rewritten parameter
/// telescope, plus the two per-declaration facts the desugaring is the only
/// thing that knows.
pub(crate) struct Expanded {
    pub params: Vec<Param>,
    /// Index names a *repeated* constraint left bound to nothing
    /// (docs/operation-indexed-classes-design.md §5.2), with the refusal each
    /// one owes.
    pub ambiguous: Vec<(String, String)>,
    /// Operator symbols a `C(+)` slot installed, as (symbol, binder name)
    /// (docs/operators-onto-classes-design.md §5).
    pub symbols: Vec<(String, String)>,
}

/// The generated name of an index binder a SYMBOL slot introduced
/// (docs/operators-onto-classes-design.md §5.1).
///
/// The **symbol is in the name**, because a call site fills this slot from the
/// designation table and the only thing that reaches it about the callee's
/// parameters is their names. Same device as `#index{i}_{k}` and
/// `#constraint{ix}`: `#` never begins an identifier, so nothing in a body can
/// reach it and the name is free to carry data. `@` separates because no
/// operator symbol contains one.
pub(crate) fn op_index_binder(sym: &str, i: usize, k: usize) -> String {
    format!("#op{sym}@{i}_{k}")
}

/// The symbol an index binder's generated name carries, if it was made by
/// [`op_index_binder`].
pub(crate) fn op_index_symbol(name: &str) -> Option<&str> {
    let rest = name.strip_prefix("#op")?;
    let (sym, _) = rest.rsplit_once('@')?;
    (!sym.is_empty()).then_some(sym)
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
        // A symbol is never renamed: it names nothing in the telescope a
        // parent instantiation renames.
        OpSymbol(s) => OpSymbol(s.clone()),
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
        Match { form, generated, scrut, eqbind, motive, arms } => Match {
            form: *form,
            generated: *generated,
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
        // A `match code` cannot appear in a class member's body — the renamer
        // walks program-layer declarations and `match code` is layer-m only —
        // but a walk that silently dropped a form would rename the wrong
        // thing, so it recurses like every other binder-carrying node.
        MatchCode { scrut, motive, arms } => MatchCode {
            scrut: Box::new(rename_expr(m, scrut)),
            motive: Box::new(rename_ty(m, motive)),
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

/// A class's declared index type, at the constraint's arguments: the class's
/// type parameters replaced by the types the constraint applies it to. A
/// substitution rather than [`rename_ty`]'s rename, because a constraint may
/// name a *composite* carrier (`requires m: Monoid<List<A>>(append)`).
fn subst_ty(m: &HashMap<String, Ty>, t: &Ty) -> Ty {
    if let TyKind::Named { name, args } = &t.kind
        && args.is_empty()
        && let Some(a) = m.get(name)
    {
        return a.clone();
    }
    let ren: Ren = Ren::new();
    let kind = match &t.kind {
        TyKind::Named { name, args } => TyKind::Named {
            name: name.clone(),
            args: args.iter().map(|a| subst_ty(m, a)).collect(),
        },
        TyKind::Fn { binder, implicit, dom, cod } => TyKind::Fn {
            binder: binder.clone(),
            implicit: *implicit,
            dom: Box::new(subst_ty(m, dom)),
            cod: Box::new(subst_ty(m, cod)),
        },
        TyKind::Vec { elem, len } => TyKind::Vec {
            elem: Box::new(subst_ty(m, elem)),
            len: len.clone(),
        },
        // Every other shape's payload is a term, and a class's index type is a
        // type expression: `rename_ty`'s walk with an empty map is the identity
        // and keeps this total without a wildcard clone.
        _ => return rename_ty(&ren, t),
    };
    Ty { kind, span: t.span }
}

/// Does this written type mention `name` as a bare variable? Used only to spot
/// the dependency cycle a linked index can close.
fn ty_mentions(t: &Ty, name: &str) -> bool {
    ty_var_count(t, name) > 0
        || match &t.kind {
            TyKind::Eq(a, b) => expr_mentions(a, name) || expr_mentions(b, name),
            TyKind::OfExpr(e) => expr_mentions(e, name),
            TyKind::Fn { dom, cod, .. } => ty_mentions(dom, name) || ty_mentions(cod, name),
            TyKind::Named { args, .. } => args.iter().any(|a| ty_mentions(a, name)),
            _ => false,
        }
}

fn expr_mentions(e: &Expr, name: &str) -> bool {
    match &e.kind {
        ExprKind::Var(n) => n == name,
        ExprKind::App { head, args, .. } => {
            expr_mentions(head, name) || args.iter().any(|a| expr_mentions(a, name))
        }
        ExprKind::TyApp { head, args } => {
            expr_mentions(head, name) || args.iter().any(|a| ty_mentions(a, name))
        }
        ExprKind::Dot { recv, args, .. } => {
            expr_mentions(recv, name)
                || args.iter().flatten().any(|a| expr_mentions(a, name))
        }
        ExprKind::Eq(a, b) => expr_mentions(a, name) || expr_mentions(b, name),
        _ => false,
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
        // An applied type former (`Not(P)`, `Le(n, m)`) is a carrier as of the
        // 2026-08-17 widening, so the measure has to see into it. Falling
        // through to `1` was harmless only while such a carrier could not be
        // declared: a head of size 1 admits no strictly smaller subgoal, so
        // every instance at one refused, whatever it required.
        TyKind::OfExpr(e) => expr_size(e),
        _ => 1,
    }
}

/// [`ty_size`] through an application's expression spine. An argument that is
/// itself a type (a `TyApp`'s) re-enters [`ty_size`], so `Not(P)` and `And<P, Q>`
/// are measured on one scale and a mixed carrier cannot game the comparison.
fn expr_size(e: &Expr) -> usize {
    match &e.kind {
        ExprKind::App { head, args, .. } => {
            expr_size(head) + args.iter().map(expr_size).sum::<usize>()
        }
        ExprKind::TyApp { head, args } => {
            expr_size(head) + args.iter().map(ty_size).sum::<usize>()
        }
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
        // The occurrence half of the same widening: a parameter of an applied
        // former (`Not(P)`'s `P`) is a bare occurrence exactly as `And<P, Q>`'s
        // is, and Paterson's second condition has to count it.
        TyKind::OfExpr(e) => expr_var_count(e, v),
        _ => 0,
    }
}

/// [`ty_var_count`] through an application's expression spine.
fn expr_var_count(e: &Expr, v: &str) -> usize {
    match &e.kind {
        // The head is walked rather than skipped. A former's own name is never
        // one of the carrier's variables, so in practice this adds zero; if it
        // ever did not, a higher count on the *subgoal* side is the direction
        // that refuses, which is the safe way to be wrong.
        ExprKind::App { head, args, .. } => {
            expr_var_count(head, v) + args.iter().map(|a| expr_var_count(a, v)).sum::<usize>()
        }
        ExprKind::TyApp { head, args } => {
            expr_var_count(head, v) + args.iter().map(|a| ty_var_count(a, v)).sum::<usize>()
        }
        ExprKind::Var(name) => (name == v) as usize,
        _ => 0,
    }
}

/// How often `v` occurs in the instance head's **class arguments** — the part
/// of the head a binder may be recovered from. The index is measured separately
/// by [`index_var_count`] and is not a substitute: see [`Elaborator::check_valparams`].
fn head_var_count(c: &ClassRef, v: &str) -> usize {
    c.args.iter().map(|a| ty_var_count(a, v)).sum()
}

/// How often `v` occurs in the instance head's **index arguments**. Only ever
/// asked in order to refuse: an index joins the registry *key* as a spelling.
fn index_var_count(c: &ClassRef, v: &str) -> usize {
    c.index.iter().map(|e| expr_var_count(e, v)).sum()
}

/// The instance's telescope after its type parameters
/// (docs/value-generic-instances-design.md §3): the **value binders** first,
/// then the solver parameters.
///
/// Value binders lead because a `requires` type may mention one —
/// `instance(n: Nat) C<F(n)> requires D<G(n)>` — while the converse cannot
/// happen: a solver parameter's type is a class type, and no binder's type is
/// written in terms of a dictionary.
fn instance_params(d: &InstanceDecl) -> Vec<Param> {
    d.valparams.iter().cloned().chain(d.requires.iter().cloned()).collect()
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
                    index: a.index.iter().map(|e| rename_expr(&rename, e)).collect(),
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
                    index: parent.index.clone(),
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
            valparams: d.valparams.clone(),
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
            valparams: d.valparams.clone(),
            fields,
            ancestors,
            owner,
        };
        self.classes.insert(qkey(&self.scope.module, &d.name), Rc::new(info));
        Ok(())
    }

    /// The **index spelling** of an instance head
    /// (docs/operation-indexed-classes-design.md §3.1): each index argument's
    /// resolved global key, joined. This is a *key*, computed from the
    /// declaration alone, which is why the shapes it admits are exactly the
    /// ones a name can be read off — a global reference, possibly applied to
    /// the instance's own type parameters. An arbitrary λ is refused here, and
    /// the alternative is stated: a structure built from an unnamed operation
    /// is what scope is for.
    fn index_spelling(&self, cref: &ClassRef, class: &ClassInfo) -> R<String> {
        let mut parts = Vec::with_capacity(cref.index.len());
        for (p, a) in class.valparams.iter().zip(cref.index.iter()) {
            let head = match &a.kind {
                ExprKind::Var(n) => Some(n),
                ExprKind::TyApp { head, .. } => match &head.kind {
                    ExprKind::Var(n) => Some(n),
                    _ => None,
                },
                _ => None,
            };
            let Some(n) = head else {
                // A symbol in an instance head would make the registry key
                // depend on the designation table's state at declaration
                // time, which the key exists not to depend on.
                if let ExprKind::OpSymbol(s) = &a.kind {
                    return err(
                        format!(
                            "an instance names its index by the **operation**, not by a \
                             symbol: write the operation `{s}` designates here. A \
                             designation says what a symbol means at a carrier \
                             (`designation {s} at … := …`); the registry key is the \
                             operation, so the two stay separable \
                             (docs/operators-onto-classes-design.md §3.3)"
                        ),
                        a.span,
                    );
                }
                return err(
                    format!(
                        "the index `{}` of this instance is not spellable: `{}` must be a \
                         global reference (possibly at this instance's own type \
                         parameters), because the registry key is computed from the \
                         declaration alone (docs/operation-indexed-classes-design.md \
                         §3.1). A structure built from an unnamed operation is a `let`-bound \
                         value, found by scope rather than registered",
                        p.name,
                        render_expr(a)
                    ),
                    a.span,
                );
            };
            parts.push(self.key_of(n).unwrap_or_else(|| n.clone()));
        }
        Ok(parts.join(", "))
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
        // The parent's **index**, at the child's own spelling
        // (docs/operation-indexed-classes-design.md §3): a single-op chain
        // passes its index up unchanged, so an `extends` index argument is
        // restricted exactly as an `extends` type argument is — to one of the
        // child's own value parameters — which keeps instantiating the parent
        // a rename rather than a substitution.
        if info.valparams.len() != parent.index.len() {
            return err(
                format!(
                    "`{}` takes {} index argument(s), {} given: write `extends {}<…>({})`",
                    parent.name,
                    info.valparams.len(),
                    parent.index.len(),
                    parent.name,
                    info.valparams.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join(", ")
                ),
                parent.span,
            );
        }
        for (p, a) in info.valparams.iter().zip(parent.index.iter()) {
            let ExprKind::Var(n) = &a.kind else {
                return err(
                    format!(
                        "an `extends` index must be one of `{}`'s own value parameters \
                         (`{}`), and `{}` is not: a chain passes its index up unchanged, \
                         and a parent at a *computed* index is the diamond \
                         (docs/operation-indexed-classes-design.md §8), not this form",
                        d.name,
                        d.valparams.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join(", "),
                        render_expr(a)
                    ),
                    a.span,
                );
            };
            if !d.valparams.iter().any(|q| q.name == *n) {
                return err(
                    format!(
                        "`{n}` is not a value parameter of `{}`: an `extends` index must be \
                         one of the child's own (`{}`)",
                        d.name,
                        d.valparams.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join(", ")
                    ),
                    a.span,
                );
            }
            rename.insert(p.name.clone(), n.clone());
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

    /// A parameter's type read as a **class reference**: the class's name, its
    /// type arguments, and its written index arguments. Both spellings — the
    /// unindexed `Named` one and the applied `OfExpr` one
    /// [`heather_syntax::class_ty`] builds — read back through here, so no
    /// consumer has to know which it is holding.
    pub(crate) fn class_ref_of_ty(&self, t: &Ty) -> Option<ClassRef> {
        match &t.kind {
            TyKind::Named { name, args } if self.lookup_class(name).is_some() => Some(ClassRef {
                name: name.clone(),
                args: args.clone(),
                index: Vec::new(),
                span: t.span,
            }),
            TyKind::OfExpr(e) => {
                let ExprKind::App { head, args, .. } = &e.kind else { return None };
                let (name, targs) = crate::inductive::named_head(head)?;
                self.lookup_class(name)?;
                Some(ClassRef {
                    name: name.to_string(),
                    args: targs.to_vec(),
                    index: args.clone(),
                    span: t.span,
                })
            }
            _ => None,
        }
    }

    /// The constraint binders' desugaring
    /// (docs/operation-indexed-classes-design.md §4, §4.1).
    ///
    /// At an **indexed** class a solver parameter with an EMPTY index slot
    /// grows the index binders in front of it, under the class's own declared
    /// parameter names — so the body writes `op` as an ordinary variable and
    /// the operation rides exactly the machinery the carrier type rides. A
    /// LINKED slot (`<A: Monoid(op)>`) binds nothing and instead floats the
    /// dictionary binder past the parameters it names, which is the whole of
    /// the forward-reference license: only a constraint's index slot, only into
    /// its own declaration's parameter list, written order still authoritative
    /// for every positional call site and every diagnostic.
    ///
    /// A no-op for every declaration with no indexed-class constraint, which is
    /// every declaration written before this grammar existed.
    #[allow(clippy::type_complexity)]
    pub(crate) fn expand_constraints(&self, decl: &Decl) -> R<Option<Expanded>> {
        let mut refs: Vec<Option<ClassRef>> = Vec::with_capacity(decl.params.len());
        let mut indexed = false;
        for p in &decl.params {
            let r = p.solver.is_some().then(|| self.class_ref_of_ty(&p.ty)).flatten();
            indexed |= r
                .as_ref()
                .and_then(|r| self.lookup_class(&r.name))
                .is_some_and(|c| !c.valparams.is_empty());
            refs.push(r);
        }
        if !indexed {
            return Ok(None);
        }
        // Which classes appear more than once among the constraints: §5.2's
        // uniqueness rule, decided before any binder is named.
        let mut repeated: Vec<String> = Vec::new();
        for (i, r) in refs.iter().enumerate() {
            let Some(r) = r else { continue };
            if refs[..i].iter().flatten().any(|q| q.name == r.name) {
                repeated.push(r.name.clone());
            }
        }
        // §5.2: the bare declared index name binds only when its class appears
        // once in the constraint list. Where it does not, the name is bound by
        // nothing and a bare use is refused *naming both constraints* — which
        // is a better answer than "unbound name" for a name the reader has
        // every reason to expect.
        let mut ambiguous: Vec<(String, String)> = Vec::new();
        // The symbols a SYMBOL slot installs, in written order — later
        // entries shadow earlier ones, which is `Cx::op_locals`'s rule.
        let mut symbols: Vec<(String, String)> = Vec::new();
        for c in &repeated {
            let Some(class) = self.lookup_class(c) else { continue };
            let at = refs
                .iter()
                .flatten()
                .filter(|r| r.name == *c)
                .map(class_ref_written)
                .collect::<Vec<_>>()
                .join("` and `");
            for v in &class.valparams {
                ambiguous.push((
                    v.name.clone(),
                    format!(
                        "`{}` is the index of `{c}`, and `{c}` constrains this \
                         declaration twice (`{at}`): the bare name binds only where the \
                         class appears once. Link each index to a parameter \
                         (`<A: {c}({}1) + {c}({}2)>`) and write the one you mean",
                        v.name, v.name, v.name
                    ),
                ));
            }
        }
        let mut out: Vec<Param> = Vec::new();
        // Where each written parameter ended up, so the float below can be
        // stated over positions rather than over names.
        for (i, p) in decl.params.iter().enumerate() {
            let Some(r) = &refs[i] else {
                out.push(p.clone());
                continue;
            };
            let Some(class) = self.lookup_class(&r.name) else {
                out.push(p.clone());
                continue;
            };
            if class.valparams.is_empty() {
                out.push(p.clone());
                continue;
            }
            if !r.index.is_empty() {
                if r.index.len() != class.valparams.len() {
                    return err(
                        format!(
                            "`{}` takes {} index argument(s), {} given",
                            r.name,
                            class.valparams.len(),
                            r.index.len()
                        ),
                        p.span,
                    );
                }
                // SYMBOL (docs/operators-onto-classes-design.md §5): a slot
                // written as an operator binds the index like an EMPTY slot
                // does — an ordinary implicit, filled by unification — and
                // additionally *installs* the symbol as that binder's local
                // meaning for the whole declaration. A mixed list
                // (`Semiring<A>(+, mul)`) is per-slot, because there is
                // nothing to gain from refusing it.
                if !r.index.iter().any(|a| matches!(a.kind, ExprKind::OpSymbol(_))) {
                    out.push(p.clone());
                    continue;
                }
                let sub: HashMap<String, Ty> =
                    class.params.iter().cloned().zip(r.args.iter().cloned()).collect();
                let mut index: Vec<Expr> = Vec::new();
                for (k, (v, a)) in class.valparams.iter().zip(r.index.iter()).enumerate() {
                    let ExprKind::OpSymbol(sym) = &a.kind else {
                        index.push(a.clone());
                        continue;
                    };
                    // The generated name **carries its symbol**, because the
                    // call site has to recover "this slot was designated by
                    // `+`" from the callee's parameter list and nothing else
                    // travels there (§5.1). `#` never begins an identifier, so
                    // the name is unspellable and free to be a record.
                    let name = op_index_binder(sym, i, k);
                    symbols.push((sym.clone(), name.clone()));
                    // §5.1: each referent binds exactly one spelling, and a
                    // SYMBOL slot's is the symbol. The declared name is left
                    // bound to nothing, and a bare use of it says which
                    // spelling does work — the same device §5.2 uses, and
                    // consulted at the same one place.
                    ambiguous.push((
                        v.name.clone(),
                        format!(
                            "`{}` is the index of `{}`, and `<…: {}({sym})>` binds it under \
                             the SYMBOL: write `x {sym} y`, which is the same binder. Each \
                             of the index slot's three referents binds one spelling — the \
                             empty slot binds `{}`, a linked slot binds your parameter's \
                             name, and a symbol binds the symbol \
                             (docs/operators-onto-classes-design.md §5.1)",
                            v.name, r.name, r.name, v.name
                        ),
                    ));
                    out.push(Param {
                        name: name.clone(),
                        ty: subst_ty(&sub, &v.ty),
                        implicit: true,
                        is_self: false,
                        solver: None,
                        // The generated index binder is not a declaring
                        // occurrence the user wrote, and a class's own `as`
                        // is strictly local to its body — it is not an
                        // advertisement to its users' binders
                        // (issues/class-default-operators.md owns that).
                        symbol: None,
                        span: p.span,
                    });
                    index.push(var(&name, p.span));
                }
                let mut p = p.clone();
                p.ty = heather_syntax::class_ty(r.name.clone(), r.args.clone(), index, p.ty.span);
                out.push(p);
                continue;
            }
            // EMPTY: the index binders, then the instance binder over them.
            let sub: HashMap<String, Ty> =
                class.params.iter().cloned().zip(r.args.iter().cloned()).collect();
            let mut index: Vec<Expr> = Vec::new();
            for (k, v) in class.valparams.iter().enumerate() {
                let bare = !repeated.contains(&r.name);
                let name = if bare { v.name.clone() } else { format!("#index{i}_{k}") };
                if bare
                    && (decl.params.iter().any(|q| q.name == name)
                        || decl.tyvars.iter().any(|q| q.name == name))
                {
                    return err(
                        format!(
                            "`{name}` is already bound here, and `<{}: {}>` binds the index \
                             under `{}`'s own parameter name: link the index instead \
                             (`{}({name})`), which says the two are the same thing rather \
                             than shadowing one with the other",
                            render_ty(&r.args[0]),
                            r.name,
                            r.name,
                            r.name
                        ),
                        p.span,
                    );
                }
                out.push(Param {
                    name: name.clone(),
                    ty: subst_ty(&sub, &v.ty),
                    implicit: true,
                    is_self: false,
                    solver: None,
                    symbol: None,
                    span: p.span,
                });
                index.push(var(&name, p.span));
            }
            let mut p = p.clone();
            p.ty = heather_syntax::class_ty(r.name.clone(), r.args.clone(), index, p.ty.span);
            out.push(p);
        }
        self.float_linked(decl, &mut out)?;
        Ok(Some(Expanded { params: out, ambiguous, symbols }))
    }

    /// The linked slot's float (§4.1): a constraint binder moves to just after
    /// the last parameter its index names, and nothing else moves. A parameter
    /// that mentions a constraint the constraint would have to follow is the
    /// dependency cycle, refused by name.
    fn float_linked(&self, decl: &Decl, params: &mut Vec<Param>) -> R<()> {
        let pos = |name: &str| params.iter().position(|q| q.name == name);
        let mut keys: Vec<(usize, usize)> = (0..params.len()).map(|i| (i * 2, i)).collect();
        let mut moved: Vec<(usize, usize)> = Vec::new();
        for (i, p) in params.iter().enumerate() {
            if p.solver.is_none() {
                continue;
            }
            let Some(r) = self.class_ref_of_ty(&p.ty) else { continue };
            let mut want = i * 2;
            for a in &r.index {
                let ExprKind::Var(n) = &a.kind else { continue };
                // A *global* index needs no float: `requires m: Mon<U>(ul)`
                // names a declaration, not a parameter, and the slot is
                // already ground where the binder stands.
                if pos(n).is_none()
                    && (self.lookup_global(n).is_some() || self.ctor_of(n).is_some())
                {
                    continue;
                }
                let Some(j) = pos(n) else {
                    return err(
                        format!(
                            "`{n}` is not a parameter of `{}`: a constraint's index slot links \
                             the index to an explicit parameter of this same declaration \
                             (`<A: {}({n})>(…, {n}: …)`), and that is the only forward \
                             reference the language has",
                            decl.name, r.name
                        ),
                        a.span,
                    );
                };
                want = want.max(j * 2 + 1);
            }
            if want > i * 2 {
                moved.push((i, want));
                keys[i].0 = want;
            }
        }
        if moved.is_empty() {
            return Ok(());
        }
        // A cycle: an earlier parameter's type names the very dictionary that
        // now has to follow it. Only a `requires` binder is nameable, so this
        // is the one shape that can close the loop.
        for (i, want) in &moved {
            let name = &params[*i].name;
            if name.starts_with('#') {
                continue;
            }
            for (j, q) in params.iter().enumerate() {
                if j * 2 <= *want && j != *i && ty_mentions(&q.ty, name) {
                    return err(
                        format!(
                            "`{name}` and `{}` depend on each other: `{name}`'s index names \
                             `{}`, whose type names `{name}` — a constraint's index may look \
                             forward, and a cycle is refused rather than ordered by guess",
                            q.name, q.name
                        ),
                        params[*i].span,
                    );
                }
            }
        }
        keys.sort();
        let src = std::mem::take(params);
        let mut src: Vec<Option<Param>> = src.into_iter().map(Some).collect();
        for (_, i) in keys {
            params.push(src[i].take().expect("each index taken once"));
        }
        Ok(())
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
        // The applied spelling (`<A: Monoid(op)>`) is already a class reference
        // by construction — nothing else parses into it — so only the bare one
        // can name a non-class.
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

    // -- designations -------------------------------------------------------

    /// `designation + at Nat := add`
    /// (docs/operators-onto-classes-design.md §3).
    ///
    /// A table entry and nothing else: no global is minted, no value is
    /// assembled, nothing reaches Ψ. What it buys is that the symbol `+` has a
    /// meaning at that carrier, which is the half of an operator that the
    /// parser could never supply.
    pub(crate) fn elab_designation(&mut self, d: &DesignationDecl) -> R<()> {
        let Some(head) = head_name(&d.carrier) else {
            return err(
                format!(
                    "the carrier `{}` has no head type name, so `{}` has nothing to be \
                     designated at: a designation is keyed on the carrier's *head*, \
                     exactly as an instance's canonical name is",
                    render_ty(&d.carrier),
                    d.symbol
                ),
                d.carrier.span,
            );
        };
        let head = head.to_string();
        // A type parameter of this very declaration is not a carrier: it names
        // no head, so keying on it would key on a binder.
        if !self.names_a_carrier(&head) || d.tyvars.contains(&head) {
            return err(
                format!(
                    "`{head}` is not a type or a type former in scope, so a designation \
                     of `{}` at it attaches to nothing",
                    d.symbol
                ),
                d.carrier.span,
            );
        }
        // The right-hand side is a **bare global name** (§3.2): a designated
        // operation is emitted bare at each use site and instantiated there by
        // ordinary implicit inference, which is how `mconcat(append, xss)`
        // already reaches the generic instance. A written type application
        // would pin the wrong site's arguments, so it is refused here rather
        // than half-supported.
        let ExprKind::Var(op) = &d.op.kind else {
            return err(
                format!(
                    "the operation `{}` designates must be a bare global name, and this \
                     is not: it is emitted bare at each use site and instantiated there, \
                     so a written type application — or anything unnamed — would pin this \
                     declaration's arguments rather than the caller's \
                     (docs/operators-onto-classes-design.md §3.2). Name the operation, or \
                     declare one that wraps it",
                    d.symbol
                ),
                d.op.span,
            );
        };
        if self.lookup_global(op.as_str()).is_none() && self.ctor_of(op.as_str()).is_none() {
            return Err(self.name_miss(
                op.as_str(),
                format!(
                    "`{op}` is not in scope, so `{}` cannot designate it at `{head}`",
                    d.symbol
                ),
                d.op.span,
            ));
        }
        let op = self.key_of(op.as_str()).unwrap_or_else(|| op.clone());
        let written = format!(
            "designation {} at {} := {}",
            d.symbol,
            render_ty(&d.carrier),
            render_expr(&d.op)
        );
        let key = (d.symbol.clone(), head.clone());
        if let Some(prev) = self.designations.get(&key) {
            return err(
                format!(
                    "`{}` already designates `{}` at `{head}` (`{}`): one entry per \
                     (symbol, carrier head), so this is refused rather than silently \
                     overwritten. Two operations at one carrier are two *symbols* — \
                     which is how `+` is `or` and `*` is `and` at `Bool`",
                    d.symbol, prev.op, prev.written
                ),
                d.span,
            );
        }
        self.designations.insert(key, DesignationInfo { op, written });
        Ok(())
    }

    /// The operation `sym` designates at a carrier whose head is `head`, if
    /// any. The whole of the designation table's read side.
    pub(crate) fn designated(&self, sym: &str, head: &str) -> Option<String> {
        self.designations.get(&(sym.to_string(), head.to_string())).map(|d| d.op.clone())
    }

    /// Every designation at one carrier head, as `` (`+`, `or`) `` pairs
    /// sorted by symbol — what a value-slot refusal lists so that the reader
    /// is told which binder would have worked (§6, §7).
    pub(crate) fn designations_at(&self, head: &str) -> Vec<(String, String)> {
        let mut out: Vec<(String, String)> = self
            .designations
            .iter()
            .filter(|((_, h), _)| h == head)
            .map(|((s, _), d)| (s.clone(), d.op.clone()))
            .collect();
        out.sort();
        out
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
        if !self.names_a_carrier(&head) {
            return err(
                format!(
                    "`{head}` is not a type or a type former in scope, so `{head}::{}` \
                     attaches to nothing",
                    d.class.name
                ),
                carrier.span,
            );
        }
        // The index (docs/operation-indexed-classes-design.md §3.1). Its
        // spelling joins the registry key, so it is computed from the
        // declaration alone and an unspellable one is refused here.
        if class.valparams.len() != d.class.index.len() {
            return err(
                format!(
                    "`{}` takes {} index argument(s), {} given: an instance names its \
                     index in the head (`instance {}<{}>({})`)",
                    class.name,
                    class.valparams.len(),
                    d.class.index.len(),
                    class.name,
                    render_ty(carrier),
                    class.valparams.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join(", ")
                ),
                d.class.span,
            );
        }
        self.check_valparams(d)?;
        let index = self.index_spelling(&d.class, &class)?;
        let prefix = if index.is_empty() {
            format!("{head}::{}", class.name)
        } else {
            // Two instances of one class at one carrier are the point (§3), so
            // the canonical name carries the index. `#` never begins an
            // identifier, so the suffix is unwritable and `Bool::Monoid(or)`
            // — the `T::C(args)` spelling of §5.1 — is how it is reached.
            format!("{head}::{}#{}", class.name, name_suffix(&index))
        };
        let key = instance_key(&class_key, &head, &index);
        if let Some(prev) = self.instances.get(&key) {
            return err(
                format!(
                    "`{}` already has an instance of `{}`{} (`{}`), declared as `{}`: at \
                     layer 1 the canonical name is keyed on the carrier's *head* and the \
                     index spelling, so two carriers with the same head collide — this is \
                     refused rather than silently overwritten \
                     (docs/traits-layer1-design.md §4.1)",
                    head,
                    class.name,
                    if index.is_empty() {
                        String::new()
                    } else {
                        format!(" at the index `{index}`")
                    },
                    prev.global,
                    prev.written
                ),
                d.class.span,
            );
        }
        let parameterized =
            !d.tyvars.is_empty() || !d.requires.is_empty() || !d.valparams.is_empty();
        let written = class_ref_written(&d.class);
        // Termination, checked here rather than detected when it hangs
        // (docs/traits-layer2-design.md §6).
        self.check_decrease(d, &written)?;

        // The class type as a surface type: `Monoid<Rat>`, or `Monoid<Nat>(add)`
        // where the class is indexed.
        let class_ty = heather_syntax::class_ty(
            d.class.name.clone(),
            d.class.args.clone(),
            d.class.index.clone(),
            d.class.span,
        );

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
                    params: instance_params(d).into_iter().chain(m.params.iter().cloned()).collect(),
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
            InstanceInfo { global: prefix, written, index, parameterized },
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
        // The same substitution at the index: an ancestor's index arguments are
        // the child's own value-parameter names (`parent_view`'s restriction),
        // so instantiating is the positional lookup again.
        let anc_index = |a: &ClassRef| -> Vec<Expr> {
            a.index
                .iter()
                .map(|arg| match &arg.kind {
                    ExprKind::Var(name) => class
                        .valparams
                        .iter()
                        .position(|p| p.name == *name)
                        .and_then(|i| d.class.index.get(i).cloned())
                        .unwrap_or_else(|| arg.clone()),
                    _ => arg.clone(),
                })
                .collect()
        };
        let anc_ref = |a: &ClassRef| -> ClassRef {
            ClassRef {
                name: a.name.clone(),
                args: anc_args(a),
                index: anc_index(a),
                span,
            }
        };

        // Ancestors that already have a canonical instance at this carrier —
        // the fill-by-reference source (design §4.3 rule 3) and the agreement
        // partner (§4.5).
        let mut registered: Vec<(String, Rc<ClassInfo>, String)> = Vec::new();
        for a in &class.ancestors {
            let Some(akey) = self.key_of(&a.name) else { continue };
            let Some(ainfo) = self.classes.get(&akey).cloned() else { continue };
            let aindex = self.index_spelling(&anc_ref(a), &ainfo)?;
            let Some(inst) = self.instances.get(&instance_key(&akey, head, &aindex)) else {
                continue;
            };
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

        // 3. The value itself. At an **indexed** class the type arguments are
        // left off: a record literal with them written is an inference-position
        // spelling, and the index has to come from the expected type, which is
        // exactly what checking mode against `class_ty` supplies.
        let lit = span_expr(
            ExprKind::RecordLit {
                name: class.name.clone(),
                tyargs: if class.valparams.is_empty() {
                    d.class.args.clone()
                } else {
                    Vec::new()
                },
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
        let parameterized =
            !d.tyvars.is_empty() || !d.requires.is_empty() || !d.valparams.is_empty();
        for a in class.ancestors.clone() {
            let Some(akey) = self.key_of(&a.name) else {
                return err(format!("`{}` is not a class in scope", a.name), span);
            };
            let Some(ainfo) = self.classes.get(&akey).cloned() else { continue };
            let aref = anc_ref(&a);
            let aindex = self.index_spelling(&aref, &ainfo)?;
            if self.instances.contains_key(&instance_key(&akey, head, &aindex)) {
                continue;
            }
            let aname = if aindex.is_empty() {
                format!("{head}::{}", ainfo.name)
            } else {
                format!("{head}::{}#{}", ainfo.name, name_suffix(&aindex))
            };
            let aargs = anc_args(&a);
            let aty = heather_syntax::class_ty(
                a.name.clone(),
                aargs.clone(),
                aref.index.clone(),
                span,
            );
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
                    tyargs: if ainfo.valparams.is_empty() { aargs.clone() } else { Vec::new() },
                    fields: afields,
                },
                span,
            );
            self.synth_decl(DeclKind::Fn, &aname, d, aty, alit, span)?;
            self.instances.insert(
                instance_key(&akey, head, &aindex),
                InstanceInfo {
                    global: aname,
                    written: class_ref_written(&aref),
                    index: aindex,
                    parameterized,
                },
            );
        }
        Ok(())
    }

    /// The instance's **value binders** (docs/value-generic-instances-design.md
    /// §4): each has to be a name of its own, and each has to occur in the head.
    ///
    /// The occurrence rule is what makes the binder *recoverable*. Resolution
    /// determines a value binder in exactly one way — by unifying the instance
    /// head against the goal — so a binder the head does not mention is a
    /// metavariable nothing can ever solve, and the failure it causes surfaces
    /// far from here as an uninstantiated implicit at some use site. It is
    /// checked at the declaration instead, where the name to blame is in hand.
    fn check_valparams(&self, d: &InstanceDecl) -> R<()> {
        for (i, p) in d.valparams.iter().enumerate() {
            if d.tyvars.iter().any(|t| t.name == p.name) {
                return err(
                    format!(
                        "`{}` is already a type parameter of this instance: one binder \
                         list cannot rebind the other's name",
                        p.name
                    ),
                    p.span,
                );
            }
            if d.valparams[..i].iter().any(|q| q.name == p.name) {
                return err(format!("duplicate value binder `{}`", p.name), p.span);
            }
            if head_var_count(&d.class, &p.name) == 0 {
                // Occurring in the *index* is not occurring in the head, and
                // the distinction is worth its own sentence: an index joins the
                // registry key as a **spelling**, computed from the declaration
                // alone, and a local binder has none — `index_spelling` would
                // key the instance under the binder's own name, so two
                // instances differing only in what they called `k` would land
                // at different keys and two agreeing on it would collide.
                if index_var_count(&d.class, &p.name) > 0 {
                    return err(
                        format!(
                            "the value binder `{}` occurs only in this instance's index, \
                             which is not a position a binder can be recovered from: an \
                             index argument joins the registry key as a spelling and must \
                             therefore be a global reference \
                             (docs/operation-indexed-classes-design.md §3.1). An instance \
                             generic in its index is a different feature from one generic \
                             in its carrier's values",
                            p.name
                        ),
                        p.span,
                    );
                }
                return err(
                    format!(
                        "the value binder `{}` does not occur in the head `{}`, so \
                         resolution has no way to determine it: a value binder is \
                         recovered by unifying the head against the goal, and one the \
                         head does not mention would stay an unsolved metavariable at \
                         every use site (docs/value-generic-instances-design.md §4)",
                        p.name,
                        class_ref_written(&d.class)
                    ),
                    p.span,
                );
            }
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
        // Value binders are counted alongside type parameters: Paterson's
        // variable condition is about what a subgoal may *duplicate*, and a
        // value binder duplicates exactly as a type parameter does —
        // `instance(n: Nat) C<F(n)> requires D<G(n, n)>` grows the term it
        // searches at, whichever kind of binder `n` is.
        let vars: Vec<&str> = d
            .tyvars
            .iter()
            .map(|t| t.name.as_str())
            .chain(d.valparams.iter().map(|p| p.name.as_str()))
            .collect();
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
            params: instance_params(d),
            result,
            body: body_of(body),
            span,
        };
        self.elab_decl(&decl)
    }
}
