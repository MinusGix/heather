//! State-free surface-expression traversals and argument-slot lowering.

use heather_kernel::rc::Rc;

use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::Term;
use heather_syntax::{Decl, Expr, ExprKind, LamBinder, OnTarget, OpFixity, Span, Stmt, Ty, TyKind};

use crate::{ElabError, R, err};

/// `<<` and `>>`: the operators whose right operand is a count rather than a
/// second value at the carrier (issues/integer-operator-symbols.md), so the
/// carrier probes read their left operand alone.
pub(crate) fn is_shift(symbol: &str) -> bool {
    matches!(symbol, "<<" | ">>")
}

/// The first non-numeral, inference-capable leaf of an operator expression.
/// Otherwise prefer its first numeral, or its first checking-only leaf if
/// there are no numerals. The caller classifies checking-only expressions;
/// named calls remain leaves, owning their arguments and result type.
///
/// Search syntax, never infer an operator subtree here. Inferring the prefix
/// afresh at every operator would restore exponential work on a left chain.
/// The explicit stack also keeps a long operator spine off the Rust stack.
pub(crate) fn operator_carrier_leaf(
    e: &Expr,
    mut checking_only: impl FnMut(&Expr) -> bool,
) -> &Expr {
    let mut leaf = e;
    let mut pending = Vec::new();
    let mut first_numeral = None;
    let mut first_leaf = None;
    loop {
        if let ExprKind::App { head, args, .. } = &leaf.kind
            && let ExprKind::OpSymbol { symbol, .. } = &head.kind
            && !is_cast(leaf)
            && let Some(first) = args.first()
        {
            // A shift's count is not at the carrier (`x << 2` shifts a word
            // by a `Nat`), so only its left operand can name it.
            if !is_shift(symbol) {
                pending.extend(args[1..].iter().rev());
            }
            leaf = first;
            continue;
        }
        let numeral = matches!(leaf.kind, ExprKind::Num(_));
        // A cast `↑e` is a leaf, and checking-only: its operand's carrier is
        // the source, never the spine's (docs/casting-design.md §5.2).
        if !numeral && !is_cast(leaf) && !checking_only(leaf) {
            return leaf;
        }
        first_leaf.get_or_insert(leaf);
        if numeral {
            first_numeral.get_or_insert(leaf);
        }
        match pending.pop() {
            Some(next) => leaf = next,
            None => return first_numeral.or(first_leaf).expect("visited a leaf"),
        }
    }
}

/// `↑e`, a cast (docs/casting-design.md §5.2): the prefix symbol `↑` applied
/// to one operand.
pub(crate) fn is_cast(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::App { head, args, .. }
        if args.len() == 1
            && matches!(&head.kind, ExprKind::OpSymbol { symbol, fixity: heather_syntax::OpFixity::Prefix } if symbol == "↑"))
}

/// Numerals with no inference-capable anchor need a checking carrier.
/// `1 + a` can infer, while `1 + make()` still needs a carrier when `make`'s
/// implicit type can only be recovered from its expected result.
pub(crate) fn expression_needs_numeral_carrier(
    e: &Expr,
    checking_only: impl FnMut(&Expr) -> bool,
) -> bool {
    // A cast needs its target exactly as a numeral needs its carrier.
    match &e.kind {
        ExprKind::Num(_) => true,
        ExprKind::App { .. } if is_cast(e) => true,
        ExprKind::App { head, .. } if matches!(head.kind, ExprKind::OpSymbol { .. }) => {
            let leaf = operator_carrier_leaf(e, checking_only);
            matches!(leaf.kind, ExprKind::Num(_)) || is_cast(leaf)
        }
        _ => false,
    }
}

/// Preserve the existing expected-result hint for a numeral-led operator
/// spine, even if a later ordinary call cannot infer without that hint.
pub(crate) fn expression_left_leaf_is_numeral(mut e: &Expr) -> bool {
    while let ExprKind::App { head, args, .. } = &e.kind
        && matches!(head.kind, ExprKind::OpSymbol { .. })
        && !is_cast(e)
        && let Some(first) = args.first()
    {
        e = first;
    }
    // A character literal is as flexible as a numeral: `'\t' <= b` at a
    // byte takes its carrier from `b`, through `CharLiteral`.
    matches!(e.kind, ExprKind::Num(_) | ExprKind::Scaled(_) | ExprKind::Char(_)) || is_cast(e)
}

/// Read an expression as type syntax when its shape has that second reading.
///
/// This mirrors the parser's type-atom bridge: names, applied type names,
/// universes, equations, and explicit type literals qualify. Everything else
/// remains an expression and returns `None`.
pub(crate) fn expression_as_type(e: &Expr) -> Option<Ty> {
    let kind = match &e.kind {
        ExprKind::Univ { level } => TyKind::Univ { level: *level },
        ExprKind::Eq(a, b) => TyKind::Eq(a.clone(), b.clone()),
        ExprKind::TyLit(ty) => return Some((**ty).clone()),
        ExprKind::Var(name) if name == "Nat" => TyKind::Nat,
        ExprKind::Var(name) => TyKind::Named {
            name: name.clone(),
            args: vec![],
        },
        ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            ..
        } if matches!(&head.kind, ExprKind::Var(name) if name == "Fin")
            && args.len() == 1
            && named.is_empty() =>
        {
            TyKind::Fin(Box::new(args[0].clone()))
        }
        ExprKind::TyApp { head, args } => match &head.kind {
            ExprKind::Var(name) => TyKind::Named {
                name: name.clone(),
                args: args.clone(),
            },
            _ => return None,
        },
        _ => return None,
    };
    Some(Ty { kind, span: e.span })
}

/// The condition of an `if` or `while` the parser lowered to
/// `decide_bit<c>()` (`decide<c>()` with an evidence binder): the condition
/// as written in type position, the expression it was written as when it has
/// one, and whether it is the evidence form. The parser gives the call's head
/// the condition's own span, which a written `decide_bit<P>()` (head spanning
/// the name alone) never has, so only the lowered form takes the `Bool` and
/// mixed readings (issues/bool-conditions-and-literals.md,
/// issues/mixed-bool-prop-condition.md). A condition that is type syntax
/// with no expression reading (`Fin(n)`, `T<A>`, `x = y`, `P ∧ Q`) has no
/// `expr`: it is not a `Bool`, though a connective's operands may be.
pub(crate) struct Condition {
    pub(crate) ty: Ty,
    pub(crate) expr: Option<Expr>,
    pub(crate) evidence: bool,
    /// The lowered call's head (`decide_bit`, `decide`, or an `if h:`'s
    /// `decide_true`/`decide_false`) and its arguments (the bit's equation).
    pub(crate) head: String,
    pub(crate) args: Vec<Expr>,
}

impl Condition {
    /// The same lowered call at another reading of its condition.
    pub(crate) fn call(&self, proposition: Ty, span: Span) -> Expr {
        let mut call = decide_call(proposition, false, span);
        if let ExprKind::App { head, args, .. } = &mut call.kind {
            if let ExprKind::TyApp { head, .. } = &mut head.kind {
                head.kind = ExprKind::Var(self.head.clone());
            }
            args.clone_from(&self.args);
        }
        call
    }
}

pub(crate) fn lowered_condition(e: &Expr) -> Option<Condition> {
    let ExprKind::App { head, args, named, explicit: false, .. } = &e.kind else { return None };
    if !named.is_empty() {
        return None;
    }
    let ExprKind::TyApp { head: callee, args: tyargs } = &head.kind else { return None };
    let ExprKind::Var(name) = &callee.kind else { return None };
    let (evidence, arity) = match name.as_str() {
        "decide_bit" => (false, 0),
        "decide" => (true, 0),
        "decide_true" | "decide_false" => (true, 1),
        _ => return None,
    };
    if args.len() != arity {
        return None;
    }
    let [condition] = tyargs.as_slice() else { return None };
    if callee.span != condition.span {
        return None;
    }
    Some(Condition { ty: condition.clone(), expr: condition_expression(condition), evidence, head: name.clone(), args: args.clone() })
}

/// The expression a condition's type syntax was written as, when it is one
/// the `Bool` reading can elaborate: a bare name, or a decoded expression.
pub(crate) fn condition_expression(ty: &Ty) -> Option<Expr> {
    match &ty.kind {
        TyKind::Named { name, args } if args.is_empty() => Some(Expr { kind: ExprKind::Var(name.clone()), span: ty.span }),
        TyKind::OfExpr(c) => Some((**c).clone()),
        _ => None,
    }
}

/// A condition's connective, read on the proposition side, with its
/// operands: `∧`, `∨`, `↔`, a non-dependent `→` and `¬` as written, and the
/// Boolean `&&`, `||` and `!` as the connective each decides
/// (issues/mixed-bool-prop-condition.md). `None` for a leaf.
pub(crate) fn condition_connective(ty: &Ty) -> Option<(&'static str, Vec<Ty>)> {
    fn operand(e: &Expr) -> Ty {
        expression_as_type(e).unwrap_or_else(|| Ty { kind: TyKind::OfExpr(Box::new(e.clone())), span: e.span })
    }
    match &ty.kind {
        TyKind::Named { name, args } if args.len() == 2 => {
            let name = match name.as_str() {
                "And" => "And",
                "Or" => "Or",
                "Iff" => "Iff",
                _ => return None,
            };
            Some((name, args.clone()))
        }
        TyKind::Fn { binder: None, implicit: false, dom, cod } => Some(("->", vec![(**dom).clone(), (**cod).clone()])),
        TyKind::OfExpr(e) => {
            let ExprKind::App { head, args, named, explicit: false, .. } = &e.kind else { return None };
            if !named.is_empty() {
                return None;
            }
            let name = match (&head.kind, args.len()) {
                (ExprKind::Var(name), 1) if name == "Not" => "Not",
                (ExprKind::OpSymbol { symbol, fixity: OpFixity::Prefix }, 1) if symbol == "!" => "Not",
                (ExprKind::OpSymbol { symbol, fixity: OpFixity::Infix }, 2) if symbol == "&&" => "And",
                (ExprKind::OpSymbol { symbol, fixity: OpFixity::Infix }, 2) if symbol == "||" => "Or",
                _ => return None,
            };
            Some((name, args.iter().map(operand).collect()))
        }
        _ => None,
    }
}

/// The connective [`condition_connective`] named, rebuilt over new operands
/// as the parser builds it.
pub(crate) fn rebuild_connective(name: &str, mut operands: Vec<Ty>, span: Span) -> Ty {
    let kind = match name {
        "->" => {
            let cod = operands.pop().expect("an arrow has two operands");
            let dom = operands.pop().expect("an arrow has two operands");
            TyKind::Fn { binder: None, implicit: false, dom: Box::new(dom), cod: Box::new(cod) }
        }
        "Not" => {
            let inner = operands.pop().expect("a negation has one operand");
            let arg = Expr { span: inner.span, kind: ExprKind::TyLit(Box::new(inner)) };
            TyKind::OfExpr(Box::new(Expr {
                kind: ExprKind::App {
                    head: Box::new(Expr { kind: ExprKind::Var("Not".into()), span }),
                    args: vec![arg],
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            }))
        }
        _ => TyKind::Named { name: name.to_string(), args: operands },
    };
    Ty { kind, span }
}

/// `b.IsTrue()`: a `Bool` read as the proposition its `IsTrue` instance
/// decides.
pub(crate) fn is_true_of(b: &Expr) -> Expr {
    Expr {
        kind: ExprKind::Dot { recv: Box::new(b.clone()), name: "IsTrue".into(), tyargs: Vec::new(), args: Some(Vec::new()), named: Vec::new() },
        span: b.span,
    }
}

/// `decide_bit<P>()` (`decide<P>()` with `evidence`), spanned as the parser
/// spans its lowered condition.
pub(crate) fn decide_call(proposition: Ty, evidence: bool, span: Span) -> Expr {
    Expr {
        kind: ExprKind::App {
            head: Box::new(Expr {
                kind: ExprKind::TyApp {
                    head: Box::new(Expr { kind: ExprKind::Var(if evidence { "decide" } else { "decide_bit" }.into()), span }),
                    args: vec![proposition],
                },
                span,
            }),
            args: Vec::new(),
            named: Vec::new(),
            explicit: false,
            goal_oriented: false,
        },
        span,
    }
}

// -- anonymous argument-slot sections --------------------------------------

/// A resource bound, not a semantic arity limit. Indexed lowering allocates
/// one binder through the largest position, so a source-controlled giant
/// subscript must not become an allocation attack.
const MAX_ARGUMENT_SLOTS: usize = 256;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum SlotStyle {
    Unindexed,
    Indexed,
}

pub(super) struct SlotProfile {
    style: SlotStyle,
    count: usize,
}

/// Visit slots free at this expression's abstraction boundary. An explicit
/// lambda — including a parser-lowered sequent binder — starts a new boundary.
pub(super) fn for_each_free_slot(e: &Expr, f: &mut impl FnMut(Option<u64>, Span)) {
    let mut go = |e: &Expr| for_each_free_slot(e, f);
    match &e.kind {
        ExprKind::ArgSlot(index) => f(*index, e.span),
        ExprKind::App {
            head, args, named, ..
        } => {
            go(head);
            args.iter()
                .chain(named.iter().map(|a| &a.expr))
                .for_each(go);
        }
        ExprKind::TyApp { head, .. } => go(head),
        ExprKind::Lam { .. } => {}
        ExprKind::CollectionLit(xs) => xs.iter().for_each(go),
        ExprKind::Eq(a, b) => {
            go(a);
            go(b);
        }
        ExprKind::Match {
            scrut,
            motive,
            arms,
            ..
        } => {
            go(scrut);
            if let Some(motive) = motive {
                go(motive);
            }
            arms.iter().for_each(|a| go(&a.body));
        }
        ExprKind::MatchCode { scrut, arms, .. } => {
            go(scrut);
            arms.iter().for_each(|a| go(&a.body));
        }
        ExprKind::Dot {
            recv, args, named, ..
        } => {
            go(recv);
            args.iter()
                .flatten()
                .chain(named.iter().map(|a| &a.expr))
                .for_each(go);
        }
        ExprKind::Index { recv, idx } => {
            go(recv);
            go(idx);
        }
        ExprKind::RecordLit { fields, .. } => fields.iter().for_each(|x| go(&x.expr)),
        ExprKind::RecordUpdate { base, fields } => {
            go(base);
            fields.iter().for_each(|x| go(&x.expr));
        }
        ExprKind::Block(b) => {
            for stmt in &b.stmts {
                match stmt {
                    Stmt::Let { expr, .. }
                    | Stmt::LetRecord { expr, .. }
                    | Stmt::LetCode { expr, .. } => go(expr),
                }
            }
            go(&b.result);
            b.ons.iter().for_each(|o| go(&o.expr));
        }
        ExprKind::Quote(x) | ExprKind::Splice(x) => go(x),
        ExprKind::J {
            proof,
            motive,
            case,
            ..
        } => {
            go(proof);
            go(motive);
            go(case);
        }
        ExprKind::Var(_)
        | ExprKind::OpSymbol { .. }
        | ExprKind::Univ { .. }
        | ExprKind::Num(_)
        | ExprKind::SuffixedNum { .. }
        | ExprKind::Scaled(_)
        | ExprKind::Char(_)
        | ExprKind::Str(_)
        | ExprKind::TyLit(_)
        | ExprKind::Refl
        | ExprKind::AutoRefl
        | ExprKind::Hole(_) => {}
    }
}

pub(super) fn has_free_slots(e: &Expr) -> bool {
    let mut found = false;
    for_each_free_slot(e, &mut |_, _| found = true);
    found
}

/// `·.f`, `·.f.g`, …: a projection section, a slot reached only through
/// bare field projections (issues/field-projection-sections.md). No checking
/// position inside it can own the slot.
pub(super) fn is_projection_section(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Dot {
            recv, args: None, ..
        } => matches!(recv.kind, ExprKind::ArgSlot(_)) || is_projection_section(recv),
        _ => false,
    }
}

pub(super) fn slot_profile(e: &Expr, excluded: &[Span]) -> R<Option<SlotProfile>> {
    let mut style: Option<(SlotStyle, Span)> = None;
    let mut unindexed = 0usize;
    let mut max_index = None::<u64>;
    let mut conflict = None;
    for_each_free_slot(e, &mut |index, span| {
        if excluded.contains(&span) {
            return;
        }
        let here = if index.is_some() {
            SlotStyle::Indexed
        } else {
            SlotStyle::Unindexed
        };
        match style {
            None => style = Some((here, span)),
            Some((was, first)) if was != here && conflict.is_none() => {
                conflict = Some((first, span));
            }
            _ => {}
        }
        match index {
            Some(i) => max_index = Some(max_index.map_or(i, |m| m.max(i))),
            None => unindexed += 1,
        }
    });
    if let Some((first, second)) = conflict {
        return err(
            "indexed and unindexed argument slots cannot mix in one section: use \
             either `f(·, ·)` or explicit zero-based slots such as `f(·₀, ·₂)`",
            first.join(second),
        );
    }
    let Some((style, span)) = style else {
        return Ok(None);
    };
    let count = match style {
        SlotStyle::Unindexed => unindexed,
        SlotStyle::Indexed => {
            let max = max_index.expect("indexed style has an index");
            usize::try_from(max)
                .ok()
                .and_then(|n| n.checked_add(1))
                .ok_or_else(|| ElabError::Elab {
                    msg: "argument-slot index is too large".into(),
                    span,
                })?
        }
    };
    if count > MAX_ARGUMENT_SLOTS {
        return err(
            format!(
                "an argument-slot section may introduce at most {MAX_ARGUMENT_SLOTS} arguments"
            ),
            span,
        );
    }
    Ok(Some(SlotProfile { style, count }))
}

/// Replace the free slots selected by [`slot_profile`] with impossible source
/// names for the generated lambda binders. Mirrors [`for_each_free_slot`].
fn replace_free_slots(e: &mut Expr, style: SlotStyle, next: &mut usize, excluded: &[Span]) {
    let mut go = |e: &mut Expr| replace_free_slots(e, style, next, excluded);
    match &mut e.kind {
        ExprKind::ArgSlot(index) => {
            if excluded.contains(&e.span) {
                return;
            }
            let i = match style {
                SlotStyle::Unindexed => {
                    let i = *next;
                    *next += 1;
                    i
                }
                SlotStyle::Indexed => usize::try_from(index.expect("profile checked style"))
                    .expect("profile checked index range"),
            };
            e.kind = ExprKind::Var(format!("#argument_slot{i}"));
        }
        ExprKind::App {
            head, args, named, ..
        } => {
            go(head);
            args.iter_mut()
                .chain(named.iter_mut().map(|a| &mut a.expr))
                .for_each(go);
        }
        ExprKind::TyApp { head, .. } => go(head),
        ExprKind::Lam { .. } => {}
        ExprKind::CollectionLit(xs) => xs.iter_mut().for_each(go),
        ExprKind::Eq(a, b) => {
            go(a);
            go(b);
        }
        ExprKind::Match {
            scrut,
            motive,
            arms,
            ..
        } => {
            go(scrut);
            if let Some(motive) = motive {
                go(motive);
            }
            arms.iter_mut().for_each(|a| go(&mut a.body));
        }
        ExprKind::MatchCode { scrut, arms, .. } => {
            go(scrut);
            arms.iter_mut().for_each(|a| go(&mut a.body));
        }
        ExprKind::Dot {
            recv, args, named, ..
        } => {
            go(recv);
            args.iter_mut()
                .flatten()
                .chain(named.iter_mut().map(|a| &mut a.expr))
                .for_each(go);
        }
        ExprKind::Index { recv, idx } => {
            go(recv);
            go(idx);
        }
        ExprKind::RecordLit { fields, .. } => fields.iter_mut().for_each(|x| go(&mut x.expr)),
        ExprKind::RecordUpdate { base, fields } => {
            go(base);
            fields.iter_mut().for_each(|x| go(&mut x.expr));
        }
        ExprKind::Block(b) => {
            for stmt in &mut b.stmts {
                match stmt {
                    Stmt::Let { expr, .. }
                    | Stmt::LetRecord { expr, .. }
                    | Stmt::LetCode { expr, .. } => go(expr),
                }
            }
            go(&mut b.result);
            b.ons.iter_mut().for_each(|o| go(&mut o.expr));
        }
        ExprKind::Quote(x) | ExprKind::Splice(x) => go(x),
        ExprKind::J {
            proof,
            motive,
            case,
            ..
        } => {
            go(proof);
            go(motive);
            go(case);
        }
        ExprKind::Var(_)
        | ExprKind::OpSymbol { .. }
        | ExprKind::Univ { .. }
        | ExprKind::Num(_)
        | ExprKind::SuffixedNum { .. }
        | ExprKind::Scaled(_)
        | ExprKind::Char(_)
        | ExprKind::Str(_)
        | ExprKind::TyLit(_)
        | ExprKind::Refl
        | ExprKind::AutoRefl
        | ExprKind::Hole(_) => {}
    }
}

pub(super) fn lower_argument_slots(e: &Expr, profile: SlotProfile, excluded: &[Span]) -> Expr {
    let mut body = e.clone();
    replace_free_slots(&mut body, profile.style, &mut 0, excluded);
    let binders = (0..profile.count)
        .map(|i| LamBinder {
            name: format!("#argument_slot{i}"),
            ty: None,
            implicit: false,
            span: e.span,
        })
        .collect();
    Expr {
        kind: ExprKind::Lam {
            binders,
            body: Box::new(body),
        },
        span: e.span,
    }
}

/// The walkers of [`count_holes`], at module level so that the pattern
/// compiler can ask the same question of one expression
/// (`docs/nested-match-patterns-design.md` §10.3): a body it would copy
/// into several arms must not contain a hole, since a hole is keyed by its
/// context and cannot be elaborated twice.
mod count_holes_impl {
    use super::*;

    pub(super) fn ty(t: &Ty, n: &mut u32) {
        match &t.kind {
            TyKind::Nat | TyKind::Univ { .. } => {}
            TyKind::Eq(a, b) => {
                expr(a, n);
                expr(b, n);
            }
            TyKind::OfExpr(e) | TyKind::TypeOf(e) => expr(e, n),
            TyKind::Named { args, .. } => args.iter().for_each(|a| ty(a, n)),
            TyKind::Fn { dom, cod, .. } => {
                ty(dom, n);
                ty(cod, n);
            }
            TyKind::Vec { elem, len } => {
                ty(elem, n);
                expr(len, n);
            }
            TyKind::Fin(len) => expr(len, n),
            TyKind::Squash(inner) => ty(inner, n),
            TyKind::Ctx | TyKind::TyCode { .. } | TyKind::Splice { .. } => {}
            TyKind::Code { ty: t, .. } => ty(t, n),
        }
    }
    pub(super) fn expr(e: &Expr, n: &mut u32) {
        match &e.kind {
            ExprKind::Hole(_) => *n += 1,
            ExprKind::Eq(a, b) => {
                expr(a, n);
                expr(b, n);
            }
            ExprKind::TyLit(t) => ty(t, n),
            ExprKind::Var(_)
            | ExprKind::OpSymbol { .. }
            | ExprKind::Num(_)
            | ExprKind::SuffixedNum { .. }
            | ExprKind::Scaled(_)
            | ExprKind::Char(_)
            | ExprKind::Str(_)
            | ExprKind::ArgSlot(_)
            | ExprKind::Refl
            | ExprKind::Univ { .. } => {}
            // The empty block's speculative `refl` may fail, and then it
            // raises a goal — so it must be counted. The pre-count is
            // documented as an upper bound, so counting one that turns out to
            // be discharged by `refl` costs a reserved-but-unused slot and
            // nothing else (issues/auto-refl-empty-block.md).
            ExprKind::AutoRefl => *n += 1,
            ExprKind::App {
                head, args, named, ..
            } => {
                expr(head, n);
                args.iter().for_each(|a| expr(a, n));
                // A `?hole` inside a named argument is still a hole, and the
                // pre-count is the one thing the goal mechanism cannot survive
                // under-counting.
                named.iter().for_each(|a| expr(&a.expr, n));
            }
            // A type argument can contain a hole (`f<a = ?p>(…)`), and the
            // pre-count is the one thing the goal mechanism cannot survive
            // under-counting (see this function's doc comment).
            ExprKind::TyApp { head, args } => {
                expr(head, n);
                args.iter().for_each(|t| ty(t, n));
            }
            ExprKind::Lam { binders, body } => {
                binders
                    .iter()
                    .filter_map(|b| b.ty.as_ref())
                    .for_each(|t| ty(t, n));
                expr(body, n);
            }
            ExprKind::CollectionLit(elems) => elems.iter().for_each(|x| expr(x, n)),
            ExprKind::Index { recv, idx } => {
                expr(recv, n);
                expr(idx, n);
            }
            ExprKind::RecordUpdate { base, fields } => {
                expr(base, n);
                fields.iter().for_each(|f| expr(&f.expr, n));
            }
            // The receiver counts whether or not `.f` turns out to be a
            // projection: the method fallback re-elaborates it as an argument,
            // and a hole is keyed by span, so one syntactic hole stays one
            // goal either way.
            ExprKind::Dot {
                recv, tyargs, args, named, ..
            } => {
                expr(recv, n);
                tyargs.iter().for_each(|t| ty(t, n));
                args.iter().flatten().for_each(|a| expr(a, n));
                named.iter().for_each(|a| expr(&a.expr, n));
            }
            ExprKind::RecordLit { tyargs, fields, .. } => {
                tyargs.iter().for_each(|t| ty(t, n));
                fields.iter().for_each(|f| expr(&f.expr, n));
            }
            ExprKind::Match {
                scrut,
                motive,
                arms,
                eqbind: _,
                form: _,
                generated: _,
            } => {
                expr(scrut, n);
                if let Some(m) = motive {
                    expr(m, n);
                }
                arms.iter().for_each(|a| expr(&a.body, n));
            }
            ExprKind::MatchCode {
                scrut,
                motive,
                arms,
            } => {
                expr(scrut, n);
                ty(motive, n);
                arms.iter().for_each(|a| expr(&a.body, n));
            }
            ExprKind::J {
                proof,
                motive,
                case,
                ..
            } => {
                expr(proof, n);
                expr(motive, n);
                expr(case, n);
            }
            ExprKind::Quote(e) | ExprKind::Splice(e) => expr(e, n),
            // A block's statements **and** its result: a hole in either is a
            // goal in the declaration's list, and an under-count is
            // `internal: more goals than the pre-count reserved`, not a wrong
            // answer (this function's doc comment).
            ExprKind::Block(b) => {
                stmts(&b.stmts, n);
                expr(&b.result, n);
            }
        }
    }
    /// A block's statements, shared by the declaration body's own walk below
    /// so a nested block cannot be walked differently from a top-level one.
    pub(super) fn stmts(ss: &[Stmt], n: &mut u32) {
        for s in ss {
            match s {
                Stmt::Let { ty: t, expr: e, .. } => {
                    if let Some(t) = t {
                        ty(t, n);
                    }
                    expr(e, n);
                }
                Stmt::LetRecord { expr: e, .. } => expr(e, n),
                Stmt::LetCode { expr: e, .. } => expr(e, n),
            }
        }
    }
}

/// Every `?` in one expression — see [`count_holes_impl`].
pub(crate) fn count_holes_expr(e: &Expr) -> u32 {
    let mut n = 0;
    count_holes_impl::expr(e, &mut n);
    n
}

/// Slots an `omega` reserves for atom lists: an equality goal is two calls,
/// one per side of its antisymmetry.
const OMEGA_ATOM_SLOTS: u32 = 2;

/// Slots a `bv_omega` reserves beyond its own, for the atom lists of the
/// `omega` calls in the proof it writes (side conditions that share a
/// context and atoms share a slot).
const BV_OMEGA_ATOM_SLOTS: u32 = 4;

/// Slots a declaration's tactics may fill besides its goals: a `bv_omega`
/// lifts its proof into one (`docs/bv-omega-design.md` §6) and every `omega`
/// names its atom list by one (a `positivity` counts as one `omega`; a run
/// that needs more restarts once). Reserved up front, since a slot
/// discovered mid-body restarts the declaration; an over-count costs an
/// unused slot.
pub(crate) fn count_tactic_slots(decl: &Decl) -> u32 {
    if decl.kind == heather_syntax::DeclKind::Axiom {
        return 0;
    }
    let mut n = 0u32;
    let mut count = |e: &Expr| {
        walk_expr(e, &mut |x| match &x.kind {
            ExprKind::Var(v) if v == "omega" || v == "positivity" => n += OMEGA_ATOM_SLOTS,
            ExprKind::Var(v) if v == "bv_omega" => n += 1 + BV_OMEGA_ATOM_SLOTS,
            ExprKind::Var(v) if v == crate::measure::CLOSER => n += OMEGA_ATOM_SLOTS + 1 + BV_OMEGA_ATOM_SLOTS,
            _ => {}
        })
    };
    for s in &decl.body.stmts {
        if let Stmt::Let { expr, .. } | Stmt::LetRecord { expr, .. } | Stmt::LetCode { expr, .. } = s {
            count(expr);
        }
    }
    count(&decl.body.result);
    decl.body.ons.iter().for_each(|o| count(&o.expr));
    // A value default is elaborated in the declaration's telescope
    // (`defaults::check_default_at_declaration`), so its tactics run there.
    decl.params.iter().filter_map(|p| p.default.as_deref()).for_each(&mut count);
    n
}

/// Syntactic upper bound on the goals a declaration can raise: every `?` in
/// it. An *upper* bound, not the count — `calc` clones sub-expressions into
/// its `@trans` spine (parser.rs) and the elaborator visits some expressions
/// twice — which is why goals are numbered in creation order and the unused
/// slots are padded. Under-counting is impossible: nothing invents a hole.
pub(crate) fn count_holes(decl: &Decl) -> u32 {
    use count_holes_impl::{expr, stmts, ty};
    let mut n = 0;
    for p in &decl.params {
        ty(&p.ty, &mut n);
    }
    ty(&decl.result, &mut n);
    if decl.kind == heather_syntax::DeclKind::Axiom {
        return n;
    }
    stmts(&decl.body.stmts, &mut n);
    expr(&decl.body.result, &mut n);
    // Under `decreases`, every recursive call owes one obligation hole
    // (measure.rs); calls are counted by name, which over-counts a shadowed
    // name — an upper bound, as required. The hole itself is raised in the
    // site's own `f#obl_N` (`docs/decreases-unfolding-design.md` §4), whose
    // count comes from the ordinary body walk above; this stays for the
    // measure preflight, which reserves against the *written* declaration.
    if let Some(measure) = &decl.decreases {
        expr(measure, &mut n);
        let base = decl.name.rsplit("::").next().unwrap_or(&decl.name);
        let mut calls = 0u32;
        let mut count = |e: &Expr| {
            walk_expr(e, &mut |x| {
                if let ExprKind::App { head, .. } = &x.kind {
                    let callee = match &head.kind {
                        ExprKind::TyApp { head, .. } => &head.kind,
                        other => other,
                    };
                    if matches!(callee, ExprKind::Var(v) if v == base || v == &decl.name) {
                        calls += 1;
                    }
                }
            });
        };
        for s in &decl.body.stmts {
            match s {
                Stmt::Let { expr, .. } | Stmt::LetRecord { expr, .. } | Stmt::LetCode { expr, .. } => count(expr),
            }
        }
        count(&decl.body.result);
        n += calls;
    }
    for on in &decl.body.ons {
        if let OnTarget::Stmt(t) = &on.target {
            ty(t, &mut n);
        }
        expr(&on.expr, &mut n);
    }
    n
}

/// Strengthen a discharge out of the goal world. An `on` right-hand side is
/// elaborated *with* the goal prefix in scope — it has to be, since the goal's
/// context and statement live there — but a `GlobalSubst` payload is scoped in
/// the source Ψ, below the prefix (subst.rs). Applying a `g`-entry σ whose
/// payloads are never reached renumbers every committed global back down by
/// `g`. "Never reached" is exactly the `frozen` restriction: no new hole, so
/// no goal occurrence survives in the payload to meet a dummy.
pub(crate) fn strengthen_global(t: &Term, g: u32) -> Term {
    if g == 0 {
        return t.clone();
    }
    let entries = (0..g)
        .map(|_| GlobalEntry::Tm(Rc::new(Term::Zero)))
        .collect();
    t.apply_global(&GlobalSubst { entries })
}

/// Pre-order walk over an expression's subexpressions.
///
/// Total over the expression forms a *self-call* can hide in, which is what
/// its callers need: the recursion scans (`recursion::recurses_on`,
/// [`Generalize::varying_params`](crate::generalize::Generalize::varying_params), [`Routes::cov_depth`](crate::matching::Routes::cov_depth)) are
/// sizing decisions, so a form missed here costs a refusal, never a wrong
/// term. Types (`TyLit`, type arguments, annotations) are not entered.
pub(super) fn walk_expr(e: &Expr, f: &mut impl FnMut(&Expr)) {
    f(e);
    for_each_child(e, &mut |c| walk_expr(c, f));
}

/// The immediate subexpressions [`walk_expr`] descends into, in source order.
pub(super) fn for_each_child(e: &Expr, go: &mut impl FnMut(&Expr)) {
    match &e.kind {
        ExprKind::App {
            head, args, named, ..
        } => {
            go(head);
            args.iter()
                .chain(named.iter().map(|a| &a.expr))
                .for_each(go);
        }
        ExprKind::TyApp { head, .. } => go(head),
        ExprKind::Lam { body, .. } => go(body),
        ExprKind::CollectionLit(xs) => xs.iter().for_each(go),
        ExprKind::Eq(a, b) => {
            go(a);
            go(b);
        }
        ExprKind::Match {
            scrut, motive, arms, ..
        } => {
            go(scrut);
            motive.iter().for_each(|m| go(m));
            arms.iter().for_each(|a| go(&a.body));
        }
        ExprKind::MatchCode { scrut, arms, .. } => {
            go(scrut);
            arms.iter().for_each(|a| go(&a.body));
        }
        ExprKind::Dot {
            recv, args, named, ..
        } => {
            go(recv);
            args.iter()
                .flatten()
                .chain(named.iter().map(|a| &a.expr))
                .for_each(go);
        }
        ExprKind::Index { recv, idx } => {
            go(recv);
            go(idx);
        }
        ExprKind::RecordLit { fields, .. } => fields.iter().for_each(|x| go(&x.expr)),
        ExprKind::RecordUpdate { base, fields } => {
            go(base);
            fields.iter().for_each(|x| go(&x.expr));
        }
        ExprKind::Block(b) => {
            for s in &b.stmts {
                match s {
                    Stmt::Let { expr, .. }
                    | Stmt::LetRecord { expr, .. }
                    | Stmt::LetCode { expr, .. } => go(expr),
                }
            }
            go(&b.result);
            b.ons.iter().for_each(|o| go(&o.expr));
        }
        ExprKind::Quote(x) | ExprKind::Splice(x) => go(x),
        // `j(p, λ y q => T, case)`: a self-call in the case is the arm's own
        // (issues/ih-generalization-misses-call-under-j.md).
        ExprKind::J {
            proof,
            motive,
            case,
        } => {
            go(proof);
            go(motive);
            go(case);
        }
        // Exhaustive on purpose: a form added to the surface without a line
        // here is a compile error, not a self-call the scans silently miss.
        ExprKind::Var(_)
        | ExprKind::OpSymbol { .. }
        | ExprKind::Univ { .. }
        | ExprKind::Num(_)
        | ExprKind::SuffixedNum { .. }
        | ExprKind::Scaled(_)
        | ExprKind::Char(_)
        | ExprKind::Str(_)
        | ExprKind::ArgSlot(_)
        | ExprKind::TyLit(_)
        | ExprKind::Refl
        | ExprKind::AutoRefl
        | ExprKind::Hole(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn slot(index: Option<u64>, start: usize) -> Expr {
        Expr {
            kind: ExprKind::ArgSlot(index),
            span: Span {
                start,
                end: start + 1,
            },
        }
    }

    #[test]
    fn indexed_slot_lowering_is_a_pure_structural_rewrite() {
        let source = slot(Some(2), 7);
        let profile = slot_profile(&source, &[])
            .expect("profile")
            .expect("one slot");
        assert_eq!(profile.count, 3);

        let lowered = lower_argument_slots(&source, profile, &[]);
        assert!(matches!(
            lowered.kind,
            ExprKind::Lam { ref binders, ref body }
                if binders.len() == 3
                    && matches!(body.kind, ExprKind::Var(ref name) if name == "#argument_slot2")
        ));
        assert!(matches!(source.kind, ExprKind::ArgSlot(Some(2))));
    }

    #[test]
    fn an_excluded_nested_slot_is_not_owned_by_this_boundary() {
        let source = slot(None, 11);
        assert!(
            slot_profile(&source, &[source.span])
                .expect("profile")
                .is_none()
        );
    }
}
