//! The stage-1 elaborator: surface AST → fully explicit kernel core.
//!
//! Scope (issues/elaborator-design.md, order of attack, stage 1): name
//! resolution into the kernel's namespaces and bidirectional
//! annotation-filling — no metavariables, no level inference (everything in
//! stage 1 lives at level 0, though levels are tracked honestly), no modal
//! layer. The kernel remains the gate: every elaborated declaration is
//! re-checked from scratch by `heather_kernel::typing` before it is
//! recorded, so nothing here is trusted.
//!
//! Definition story (elaborator-design; revised 2026-07-31 by
//! issues/simulate-conversion-cost.md). Both kinds bind a closed Ψ-global
//! `u : Trm_c(· ⊢ Stmt @ l)` and are referenced by name as `u^δ` (ch. 04
//! admits referencing a layer-c global from any layer ≥ c: `i' ≤ i`,
//! typing.rs). They differ in one field of that binding:
//! - `fn` (computes): the binding carries the elaborated term as its
//!   **body**, so conversion δ-unfolds it at layer p exactly when running
//!   it is what a comparison needs. Previously a `fn` was **inlined** at
//!   every use, which put a copy of the whole body into every statement and
//!   every induction hypothesis that mentioned it.
//! - `theorem` (never computes): the proof is kernel-checked against the
//!   statement, then discarded — the binding stays **opaque**. Later proofs
//!   refer to it as a neutral; proofs are transported, never evaluated.
//!
//! Everything is checked at layer c (full MLTT, no computation *rules* —
//! conversion still β-reduces during checking, which is all the Nat suite
//! needs) so that theorems are bindable as `Trm_c` globals.
//!
//! # Determinism is a guarantee, not hygiene
//!
//! **The same source must elaborate to the same kernel terms, byte for
//! byte, every time.** This is load-bearing, not tidiness
//! (issues/elaboration-determinism.md): `.code` quotes the *elaborated*
//! term and meta-programs pattern-match on it, so two elaborations that
//! differ anywhere a `match code` can see are two different programs; and
//! the content-addressed build cache
//! (issues/parallel-checking-and-caching.md) keys on hashes of this
//! crate's output, so a wobble there is a wrong cache hit, not a cosmetic
//! diff.
//!
//! The rule that follows, for anyone adding a table here: **never let the
//! iteration order of a `HashMap`/`HashSet` reach an emitted term** — or
//! the order of diagnostics, which readers and tests also key on. Std's
//! `RandomState` reseeds *per map instance*, so such an order varies
//! between two elaborations in one process, not merely between runs. The
//! maps in this crate are lookup-only today (audited 2026-08-06) and that
//! is what makes them safe; if you need to iterate one, reach for a
//! `BTreeMap`, a `Vec` in insertion order, or an explicit sort. Swapping
//! in a fixed-seed hasher would work by accident and hide the intent, so
//! don't.
//!
//! `crates/elab/tests/determinism.rs` enforces both halves: repeated fresh
//! elaborations must agree, and the Nat suite's elaborated Ψ must hash to a
//! stored golden value.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use heather_kernel::conv::{conv_term, conv_type};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{
    step_type_delta, whnf_term, whnf_term_delta, whnf_type_delta, Defs,
};
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{
    nth, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    SubstTail, Term, Type,
};
use heather_kernel::typing::{self, TypeError, DEFAULT_FUEL};
use heather_syntax::{
    parse_file, Arm, Decl, DeclKind, Expr, ExprKind, Item, LamBinder, MatchForm, OnStmt, OnTarget,
    ParseError, Span, Stmt, RecordLitField, Ty, TyKind,
};

mod access;
pub mod certgen;
pub mod gate;
pub mod stats;
mod code;
mod datarepr;
pub use datarepr::{Obligation, Provenance};
pub mod reprgen;
mod names;
mod patterns;
mod forded;
mod gendefs;
mod indexed;
mod inductive;
mod lgg;
mod quote;
pub mod resolve;
mod slots;
mod traits;
mod vec;
mod wf;

use inductive::Inductive;
use traits::{ClassInfo, InstanceInfo};
use names::{
    miss_msg, qkey, split_qual, ImportSpec, NameIndex, NameKind, NameRes,
    Scope, DEFAULT_MODULE,
};
use slots::{Ingredient, Slot};

/// The stage-1 prelude: `sym`/`trans`/`cong`/`cong_succ`, monomorphic at
/// `Nat` where the equation's type is not a parameter.
/// (The universe-polymorphic versions are layer-m `Λ ℓ⃗` territory — later
/// stage; the Nat suite only ever congs by `Succ`.)
pub const PRELUDE: &str = include_str!("prelude.hthr");

/// The prelude's module name: an implicit import of every module
/// (docs/modules-design.md §3.2). Public so a loader can skip resolving it to
/// a file — there is no `prelude.hthr` on disk to find.
pub const PRELUDE_MODULE: &str = names::PRELUDE_MODULE;

#[derive(Debug)]
pub enum ElabError {
    Parse(ParseError),
    /// A surface-level elaboration failure (unbound name, unsupported form,
    /// arity mismatch, missing motive, …).
    Elab { msg: String, span: Span },
    /// The kernel rejected an elaborated declaration. This is the trust
    /// boundary speaking: either the source is ill-typed or the elaborator
    /// has a bug — the kernel does not care which. The span is the whole
    /// declaration's: a `TypeError` speaks about an elaborated term, which
    /// has no source position — a finer span means fixing the kernel's
    /// error type, not this one (issues/cli-check-diagnostics.md).
    Kernel { decl: String, span: Span, err: TypeError, note: Option<String> },
    /// Goals raised in a block that no `on` statement discharged
    /// (issues/goal-holes.md). Not one error per goal: the *listing* is the
    /// point — it is how the checker shows goal state.
    UnsolvedGoals { decl: String, goals: Vec<GoalReport> },
    /// A solver parameter whose goal could not be resolved
    /// (docs/traits-layer2-design.md §7). The search is deterministic, so its
    /// failure has a well-defined *trace* — which scopes were consulted,
    /// which candidates were tried, which subgoal failed — and the trace is
    /// the diagnostic, as data rather than as prose.
    Resolution { goal: String, span: Span, trace: Vec<resolve::TraceLine> },
}

/// One entry of the unsolved-goal listing. Types are decoded for display and
/// rendered eagerly with the kernel's budget-bounded `Debug`
/// (crates/kernel/src/fmt.rs), so no kernel type escapes into the public error.
#[derive(Debug)]
pub struct GoalReport {
    /// Discharge name: `on ?{name} := …`.
    pub name: String,
    /// The goal's statement.
    pub statement: String,
    /// The context captured at the hole — the names a discharge may use, which
    /// is not the same as what is lexically in scope at the `on`.
    pub context: Vec<(String, String)>,
    /// Where the goal came from, when it was an argument: "the `p` parameter
    /// of `sym`". Proof-parameter names are API precisely so this reads.
    pub origin: Option<String>,
    pub span: Span,
}

/// Diagnostics get a small, independent reduction allowance. This is not
/// elaboration fuel: exhausting it must only make the message less pretty.
const DISPLAY_DECODE_STEPS: usize = 32;

/// The lowering selected for an indexed inductive declaration.
///
/// Exposed as a small piece of elaboration metadata so a benchmark or test
/// whose subject is one route can assert that it is measuring that route.
/// The classifier itself and its intermediate rows remain private.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IndexedRoute {
    /// Route 1: the family is defined by elimination on its index.
    One,
    /// Route 2b: indices are erased into a skeleton and recovered by fording.
    Forded,
}

/// A diagnostic that is **not** a failure: something true about a checked
/// declaration that its author would want to know, said without refusing the
/// file (`docs/diagnostic-warnings-design.md`).
///
/// Deliberately not a variant of [`ElabError`] and deliberately not carried in
/// its `Vec`: `check_source`'s contract is "empty means the file is good", and
/// every caller in the tree reads it that way (§2). A warning is read out of
/// [`Elaborator::take_warnings`] instead, by whoever wants to show one.
///
/// One shape, a message at a span, because every warning anyone has asked for
/// is one (§5). A listing-shaped warning can join `ElabError::UnsolvedGoals`
/// in having its own rendering the day a customer needs it.
#[derive(Debug, Clone)]
pub struct Warning {
    pub msg: String,
    pub span: Span,
}

impl Warning {
    /// One line with the source position — the compact form, matching
    /// [`ElabError::render`].
    pub fn render(&self, src: &str) -> String {
        let (line, col) = line_col(src, self.span.start);
        format!("{line}:{col}: warning: {}", self.msg)
    }

    /// The full CLI diagnostic: heading, location, caret line. The same
    /// renderer [`ElabError::render_snippet`] uses, with `warning` in front
    /// instead of `error` — the severity is the only thing that differs, and
    /// a reader should not have to learn two shapes.
    pub fn render_snippet(&self, src: &str, file: &str) -> String {
        headed("warning", &self.msg, self.span, src, file)
    }
}

impl From<ParseError> for ElabError {
    fn from(e: ParseError) -> Self {
        ElabError::Parse(e)
    }
}

impl ElabError {
    /// The message alone, for an error being *quoted* inside another — a
    /// rejected resolution candidate, whose own failure is one line of the
    /// enclosing trace.
    pub(crate) fn message(&self) -> String {
        match self {
            ElabError::Elab { msg, .. } => msg.clone(),
            other => other.to_string(),
        }
    }

    /// The error with source positions resolved — what a front-end should
    /// print. [`std::fmt::Display`] gives the same text without them, for
    /// where the source is no longer at hand.
    pub fn render(&self, src: &str) -> String {
        let at = |span: Span| {
            let (line, col) = line_col(src, span.start);
            format!("{line}:{col}")
        };
        match self {
            ElabError::Parse(e) => format!("{}:{}: {}", at(e.span), "parse error", e.msg),
            ElabError::Elab { msg, span } => format!("{}: {msg}", at(*span)),
            ElabError::Resolution { span, .. } => format!("{}: {self}", at(*span)),
            ElabError::Kernel { span, .. } => format!("{}: {self}", at(*span)),
            ElabError::UnsolvedGoals { decl, goals } => {
                let mut s = format!("unsolved goals in `{decl}`:\n");
                for g in goals {
                    s.push('\n');
                    s.push_str(&g.render(Some(&at(g.span))));
                }
                s.push_str("\ndischarge each with `on ?name := proof;`\n");
                s
            }
        }
    }

    /// The error as a full CLI diagnostic: message, `file:line:col`
    /// location, and a caret line under the offending span. [`Self::render`]
    /// is the compact one-line form for harnesses; this is what
    /// `heather check` prints. The goal listing keeps its listing shape —
    /// per-goal carets would drown the statements, which are the point.
    pub fn render_snippet(&self, src: &str, file: &str) -> String {
        let loc = |span: Span| {
            let (line, col) = line_col(src, span.start);
            format!("{file}:{line}:{col}")
        };
        let headed = |msg: &str, span: Span| headed("error", msg, span, src, file);
        match self {
            ElabError::Parse(e) => headed(&format!("parse error: {}", e.msg), e.span),
            ElabError::Elab { msg, span } => headed(msg, *span),
            ElabError::Resolution { span, .. } => headed(&self.to_string(), *span),
            ElabError::Kernel { span, .. } => headed(&self.to_string(), *span),
            ElabError::UnsolvedGoals { decl, goals } => {
                let mut s = format!("error: unsolved goals in `{decl}`:\n");
                for g in goals {
                    s.push('\n');
                    s.push_str(&g.render(Some(&loc(g.span))));
                }
                s.push_str("\ndischarge each with `on ?name := proof;`\n");
                s
            }
        }
    }
}

/// One `render_snippet` diagnostic: severity heading, `file:line:col`, and the
/// caret line. Shared by [`ElabError`] and [`Warning`] so that the severity
/// word is the only thing that can differ between them.
fn headed(severity: &str, msg: &str, span: Span, src: &str, file: &str) -> String {
    let (line, col) = line_col(src, span.start);
    format!("{severity}: {msg}\n  --> {file}:{line}:{col}\n{}", snippet(src, span))
}

/// The quoted source line with a caret run under `span` — the body of a
/// `render_snippet` diagnostic. Columns are counted in characters, not
/// bytes, so the carets stay aligned past non-ASCII; a span that runs past
/// its first line is pointed at where it starts.
fn snippet(src: &str, span: Span) -> String {
    let offset = span.start.min(src.len());
    let line_start = src[..offset].rfind('\n').map_or(0, |nl| nl + 1);
    let line_end = src[offset..].find('\n').map_or(src.len(), |nl| offset + nl);
    let text = &src[line_start..line_end];
    let (line, _) = line_col(src, span.start);
    let col = src[line_start..offset].chars().count();
    let line_rest = text.chars().count().saturating_sub(col);
    let span_chars = src[offset..span.end.clamp(offset, src.len())].chars().count();
    let width = span_chars.clamp(1, line_rest.max(1));
    let num = line.to_string();
    let pad = " ".repeat(num.len());
    format!(
        "{pad} |\n{num} | {text}\n{pad} | {}{}\n",
        " ".repeat(col),
        "^".repeat(width),
    )
}

impl GoalReport {
    fn render(&self, at: Option<&str>) -> String {
        let mut s = match at {
            Some(at) => format!("  ?{} : {}   ({at})\n", self.name, self.statement),
            None => format!("  ?{} : {}\n", self.name, self.statement),
        };
        // The context is not decoration: a goal captured in a `match` arm is
        // discharged with that arm's binders in scope, which is not what is
        // lexically visible at the `on`.
        for (name, ty) in &self.context {
            s.push_str(&format!("      {name} : {ty}\n"));
        }
        if let Some(origin) = &self.origin {
            s.push_str(&format!("      from {origin}\n"));
        }
        s
    }
}

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ElabError::Parse(e) => write!(f, "parse error: {}", e.msg),
            ElabError::Elab { msg, .. } => write!(f, "{msg}"),
            ElabError::Resolution { goal, trace, .. } => write!(
                f,
                "no instance for `{goal}` — the search:{}",
                resolve::render_trace(trace)
            ),
            ElabError::Kernel { decl, err, note, .. } => {
                write!(f, "the kernel rejected `{decl}`: {err:?}")?;
                if let Some(note) = note {
                    write!(f, ". {note}")?;
                }
                Ok(())
            }
            ElabError::UnsolvedGoals { decl, goals } => {
                writeln!(f, "unsolved goals in `{decl}`:")?;
                for g in goals {
                    writeln!(f)?;
                    write!(f, "{}", g.render(None))?;
                }
                writeln!(f, "\ndischarge each with `on ?name := proof;`")
            }
        }
    }
}

/// 1-based line and column of a byte offset.
fn line_col(src: &str, offset: usize) -> (usize, usize) {
    let upto = &src[..offset.min(src.len())];
    let line = upto.matches('\n').count() + 1;
    let col = upto.rfind('\n').map_or(upto.len(), |nl| upto.len() - nl - 1) + 1;
    (line, col)
}

type R<T> = Result<T, ElabError>;

/// A motive written as a lambda: take it apart into its `n` binder names and
/// its body *as a type* (docs/surface-universe.md §13).
///
/// The surface has exactly one binder form, so this is where "a motive is a
/// function" is understood rather than a second binder syntax. The body is a
/// type by the ordinary bridge: read directly where it has type syntax
/// (`a = b`, a name, an applied name), and decoded through `El` otherwise.
fn motive_lam(e: &Expr, n: usize, what: &str) -> R<(Vec<String>, Ty)> {
    let ExprKind::Lam { binders, body } = &e.kind else {
        return err(
            format!("a motive is a lambda: {what}"),
            e.span,
        );
    };
    if binders.len() != n {
        return err(
            format!(
                "this motive binds {} name(s), but {n} are needed: {what}",
                binders.len()
            ),
            e.span,
        );
    }
    if let Some(b) = binders.iter().find(|b| b.ty.is_some()) {
        return err(
            format!(
                "a motive binder takes no annotation: `{}`'s type is fixed by what the \
                 motive is a motive for",
                b.name
            ),
            e.span,
        );
    }
    let names = binders.iter().map(|b| b.name.clone()).collect();
    let ty = expr_as_ty(body)
        .unwrap_or_else(|| Ty { kind: TyKind::OfExpr(body.clone()), span: body.span });
    Ok((names, ty))
}

fn err<T>(msg: impl Into<String>, span: Span) -> R<T> {
    Err(ElabError::Elab { msg: msg.into(), span })
}

/// Read an expression *as a type*, for a position whose expected type is a
/// universe (docs/surface-universe.md §4). `None` when the expression is not a
/// type by shape, which is a diagnostic rather than a failure.
///
/// The mirror of what `parser.rs`'s `ty_atom` already does in the other
/// direction — it parses an expression and reinterprets a bare name as a type
/// name — so the two readings are deliberately the same shape: a name, an
/// applied name, or a universe. Anything structural (`Π`, `[T; n]`) has type
/// syntax that cannot occur in an expression position in the first place.
fn expr_as_ty(e: &Expr) -> Option<Ty> {
    let kind = match &e.kind {
        ExprKind::Univ { level } => TyKind::Univ { level: *level },
        ExprKind::Eq(a, b) => TyKind::Eq(a.clone(), b.clone()),
        // A motive body, parsed in type syntax: it may be a *function* type,
        // which no expression form can be (`issues/ih-generalization.md`).
        ExprKind::TyLit(t) => return Some((**t).clone()),
        ExprKind::Var(name) if name == "Nat" => TyKind::Nat,
        ExprKind::Var(name) => TyKind::Named { name: name.clone(), args: vec![] },
        // `Fin(n)`, as the parser's own `expr_as_ty` reads it — the two
        // readings must not drift (docs/surface-fin-indexing-design.md §2.2).
        ExprKind::App { head, args, explicit: false }
            if matches!(&head.kind, ExprKind::Var(s) if s == "Fin") && args.len() == 1 =>
        {
            TyKind::Fin(Box::new(args[0].clone()))
        }
        // `List<Nat>` — the one expression form that already carries type
        // arguments (`ExprKind::TyApp`, ast.rs).
        ExprKind::TyApp { head, args } => match &head.kind {
            ExprKind::Var(name) => TyKind::Named { name: name.clone(), args: args.clone() },
            _ => return None,
        },
        _ => return None,
    };
    Some(Ty { kind, span: e.span })
}

/// What to call a type projection's subject in a diagnostic: the text that
/// was written, when the shape is one a reader would recognize
/// (docs/traits-type-projection-design.md §7). `None` for anything else, which
/// falls back to the carrier's nominal tag. A display and never a key.
fn subject_text(e: &Expr) -> Option<String> {
    match &e.kind {
        ExprKind::Var(n) => Some(n.clone()),
        ExprKind::TyApp { head, .. } => subject_text(head),
        _ => None,
    }
}

/// A level for a diagnostic. Every level the surface can write is a numeral,
/// so this is exact for them and falls back to the kernel's bounded `Debug`
/// for an elaborator-built one.
fn show_level(l: &Level) -> String {
    let mut n = 0u64;
    let mut cur = l;
    loop {
        match cur {
            Level::Zero => return n.to_string(),
            Level::Succ(inner) => {
                n += 1;
                cur = inner;
            }
            _ => return format!("{l:?}"),
        }
    }
}

/// `True` in a rendered type, wherever the kernel wrote its `Unit^0` spelling
/// (`issues/true-prop-trivial-hypotheses.md`: what is printed should be what
/// can be written). A *display* transform and nothing else — the same boundary
/// [`Elaborator::display_paths`] de-mangles minted names at, for the same
/// reason: the stored type is the kernel's and is deliberately left alone.
///
/// String-level, like `display_paths`, because a kernel type is rendered by
/// `Debug` and there is no surface printer to hook. It is not ambiguous: the
/// kernel prints `Unit {level:?}` and a level renders as a numeral with no
/// leading zero, so `Unit 0` occurs exactly at `Unit^0` (`Unit 10` and
/// `Unit (0 ⊔ ℓ0)` cannot be prefixes of it). The code spelling `«Unit 0»`
/// becomes `«True»`, which is right: `True` in expression position *is* that
/// code.
fn dress_true(s: &str) -> String {
    if s.contains("Unit 0") {
        s.replace("Unit 0", "True")
    } else {
        s.to_string()
    }
}

/// The §3.4 shared refusal: an implicit mark whose skeleton would have no
/// consumer must not be silently erased — the writer believes call sites
/// will infer, and they will not (docs/implicit-binders-design.md §3.4).
pub(crate) const IMPLICIT_MARK_REFUSED: &str =
    "implicit binders take effect in parameter types, `let` annotations, field \
     types, and lambdas; this position cannot use one — see \
     issues/implicit-binders-in-function-types.md";

/// The receiver-shaped builtins: names that a `.` call reaches without any
/// declaration behind them, so [`Elaborator::shadowed`] cannot see them. Read
/// only by receiver dispatch (docs/traits-receiver-dispatch-design.md §3),
/// which needs to know whether a call *had* another reading before it claims
/// one — a class field named `map` must make `xs.map(f)` ambiguous, never
/// silently the class's.
const BUILTIN_METHODS: [&str; 8] =
    ["map", "fold", "head", "tail", "cons", "cong", "inj", "absurd"];

/// The implicitness skeleton of a surface-written function type
/// (issues/implicit-binders-in-function-types.md, option 1;
/// docs/implicit-binders-design.md §2). Positional: entry `i` speaks for the
/// `i`-th Π along the type's spine, and for no Π past `params.len()` —
/// `whnf` can expose further Πs (an `OfExpr` codomain decoding to a function
/// type), and those are explicit by the degradation rule. Contains no terms,
/// no de Bruijn indices, and no name that resolves — binder names are
/// carried only as goal-name hints and diagnostic labels — so substitution,
/// shifts and discharge have nothing to act on and skeletons travel with
/// their context entry with no update operation at all (§3.2).
#[derive(Clone, Debug)]
pub(crate) struct Skel {
    params: Vec<SkelBinder>,
}

#[derive(Clone, Debug)]
pub(crate) struct SkelBinder {
    /// The written binder name, for goal-name hints and the §7 messages.
    name: Option<String>,
    implicit: bool,
    /// The surface domain was `Type<n>` — selects the "type argument"
    /// message flavor, exactly as `ParamMeta.is_type` does for globals.
    is_type: bool,
    /// The domain's own skeleton, when the domain is itself a function type
    /// carrying implicits — a lemma-shaped callback's implicits.
    dom: Option<Rc<Skel>>,
}

impl Skel {
    /// The leading implicit prefix — the §5.2 bare-reference mask.
    fn leading_implicit(&self) -> usize {
        self.params.iter().take_while(|b| b.implicit).count()
    }
}

/// Derive a type's skeleton, purely syntactically. Sparse by rule: `None`
/// unless an implicit mark occurs somewhere along the spine or in a nested
/// domain, so every existing program allocates nothing and changes nothing.
/// The codomain chain flattens (Π is right-nested and positional along the
/// spine); the domain nests (`SkelBinder::dom`); the final result type past
/// the last written arrow carries nothing (docs/implicit-binders-design.md
/// §2.1).
fn skel_of_ty(ty: &Ty) -> Option<Rc<Skel>> {
    let mut params = Vec::new();
    let mut any = false;
    let mut cur = ty;
    while let TyKind::Fn { binder, implicit, dom, cod } = &cur.kind {
        let dom_skel = skel_of_ty(dom);
        any |= *implicit || dom_skel.is_some();
        params.push(SkelBinder {
            name: binder.clone(),
            implicit: *implicit,
            is_type: matches!(dom.kind, TyKind::Univ { .. }),
            dom: dom_skel,
        });
        cur = cod;
    }
    any.then(|| Rc::new(Skel { params }))
}

/// The skeleton of a *written* lambda's binder marks — the `let`-RHS harvest
/// of docs/implicit-binders-design.md §6.3. Same sparse rule as
/// [`skel_of_ty`]. Prefix authority: the skeleton speaks for the written
/// binders only; whatever function type the body returns is past its end.
fn skel_of_lam_binders(binders: &[LamBinder]) -> Option<Rc<Skel>> {
    let mut any = false;
    let params = binders
        .iter()
        .map(|b| {
            let dom = b.ty.as_ref().and_then(skel_of_ty);
            any |= b.implicit || dom.is_some();
            SkelBinder {
                name: Some(b.name.clone()),
                implicit: b.implicit,
                is_type: matches!(b.ty.as_ref().map(|t| &t.kind), Some(TyKind::Univ { .. })),
                dom,
            }
        })
        .collect();
    any.then(|| Rc::new(Skel { params }))
}

/// Does an implicit mark occur anywhere in this surface type? The §3.4
/// refusal walker, called at the `elab_ty` entry points whose skeleton would
/// have no consumer — mirroring how `count_holes` already walks `Ty`.
fn has_implicit_mark(ty: &Ty) -> bool {
    match &ty.kind {
        TyKind::Fn { implicit, dom, cod, .. } => {
            *implicit || has_implicit_mark(dom) || has_implicit_mark(cod)
        }
        TyKind::Named { args, .. } => args.iter().any(has_implicit_mark),
        TyKind::Vec { elem, .. } => has_implicit_mark(elem),
        TyKind::Code { ty, .. } => has_implicit_mark(ty),
        TyKind::Nat
        | TyKind::Eq(..)
        | TyKind::Univ { .. }
        | TyKind::OfExpr(_)
        | TyKind::Fin(_)
        | TyKind::Ctx
        | TyKind::TyCode { .. }
        | TyKind::Splice { .. } => false,
    }
}

/// Synthesize the [`ParamMeta`] table a *value* callee offers from its
/// skeleton (docs/implicit-binders-design.md §4.2): goal-name hints, the
/// deferral hint at retry, and the per-slot discharge messages all work
/// verbatim from skeleton binder names. `#i` for an unnamed position —
/// unspellable, so it cannot collide with a written name.
fn skel_params(skel: &Skel) -> Rc<Vec<ParamMeta>> {
    Rc::new(
        skel.params
            .iter()
            .enumerate()
            .map(|(i, b)| ParamMeta {
                name: b.name.clone().unwrap_or_else(|| format!("#{i}")),
                implicit: b.implicit,
                is_type: b.is_type,
                is_self: false,
                skel: b.dom.clone(),
                solver: None,
            })
            .collect(),
    )
}

/// Where a resolved dictionary came from, when it came by **upcast**: the
/// *child* dictionary and its class type ([`Elaborator::resolve_goal_from`],
/// `docs/traits-named-upcast-design.md` §2.1). `None` for every other answer,
/// which is every answer already at the goal's own class.
type Upcast = Option<(Term, Type)>;

/// One parameter of a callable global, in declaration/telescope order.
///
/// `implicit` flags a `{}`-parameter, filled by unification at call sites
/// (issues/elab-stage2-metas.md). The *name* is API: it is the default name of
/// a goal raised in that argument position (issues/goal-holes.md), so callers
/// discharge by it.
struct ParamMeta {
    name: String,
    implicit: bool,
    /// A `<A, B>` type parameter (docs/surface-polymorphism.md §2): a leading
    /// implicit parameter at `Ty 0`. Flagged rather than merely counted so
    /// that `f<T, …>` can check it is filling type parameters and not the
    /// first few `{}`-implicits, which are a different thing that happens to
    /// share the mask.
    is_type: bool,
    /// Written `self p: T` — the parameter a method call's receiver fills.
    /// See [`Elab::subject_index`] and issues/method-receiver-position.md.
    is_self: bool,
    /// The parameter's own domain skeleton, when its written type carries
    /// implicit marks (`f: {A: Type<0>} -> A -> A`). This is what an
    /// argument-position lambda is checked against (§6.1) and what
    /// suppresses bare-reference insertion at the argument (§5.3) — derived
    /// once from the same surface node the kernel domain was lowered from,
    /// per the §3.3 pairing guard. `None` for every markless parameter, so
    /// existing declarations store nothing new.
    skel: Option<Rc<Skel>>,
    /// A **solver parameter** (docs/traits-layer2-design.md §1): written
    /// `requires m: C<A>` or `p: T := infer`, filled at the call site by
    /// resolution rather than by unification. Carries the parameter's written
    /// type, which is what the failure diagnostic displays the goal as —
    /// nothing keys on it (§7). `None` for every ordinary parameter, and for
    /// every skeleton-derived table (a value head has no declaration to have
    /// written `requires` on).
    solver: Option<Rc<Ty>>,
}

/// What a global name refers to: the absolute position of its `Trm_c`
/// binding in Ψ, plus the surface parameter metadata.
///
/// `fn` and `theorem` differ only in whether that binding carries a *body*
/// — a definition or a declaration (`GlobalBinding::Tm`'s `body`,
/// issues/simulate-conversion-cost.md). Both are referenced by name as
/// `u^δ`; a `fn` used to be substituted in whole at every use, which put a
/// copy of its body in every theorem statement and every induction
/// hypothesis that mentioned it.
#[derive(Clone)]
struct GlobalInfo {
    abs: u32,
    params: Rc<Vec<ParamMeta>>,
}

/// `Clone` is deliberate and cheap: every field is a `HashMap` of `Rc`s or a
/// small `Vec`, so cloning a prelude'd elaborator costs microseconds where
/// [`Self::with_prelude`] costs milliseconds. The frontend benchmark suite
/// needs it — a timed unit of work has to be repeatable, and `check_source`
/// mutates — and speculative elaboration (an LSP, a tactic that tries a
/// branch) is the same need one layer up.
#[derive(Clone)]
pub struct Elaborator {
    psi: GlobalCtx,
    /// [`Self::psi`] padded with `goal_base` bodiless slots, so that a
    /// `GlobalVar` as the *term* world numbers it (goals innermost) resolves
    /// to the right binding. Only δ-unfolding reads it, and a goal never has
    /// a body, so the padding's contents are irrelevant and it can be kept
    /// in step with two cheap rebuilds rather than recomputed per lookup
    /// (unlike [`Self::goal_psi`], which conversion needs statements from).
    delta_psi: GlobalCtx,
    /// The module being elaborated and what it can see
    /// (docs/modules-design.md §4). Every table below keys `module::name`
    /// ([`names::qkey`]); this is what turns a written name into that key.
    scope: Scope,
    /// Declaration scopes temporarily installed while stored inductive
    /// syntax is re-lowered. A stack handles one stored declaration referring
    /// to another; the innermost declaration owns the syntax being read.
    resolution_scopes: RefCell<Vec<Rc<Scope>>>,
    /// Every module elaborated into this accumulator, with the scope it was
    /// elaborated in. `import m;` requires that `m` already landed here, which
    /// is what the CLI's topological walk guarantees. Inductives also retain
    /// their declaration's value from this table: their surface field syntax
    /// is re-lowered at uses, under that scope rather than the use site's.
    module_scopes: HashMap<String, Scope>,
    /// Which module declares what: the ambiguity oracle (`names.rs`).
    names: NameIndex,
    globals: HashMap<String, GlobalInfo>,
    /// Declared inductives by qualified name, by nominal tag, and by
    /// constructor name. Constructor names are per-module and qualified by
    /// their *type* (`Option::None`), not globally unique
    /// (docs/inductive-tier0-lowering.md, scoped by docs/modules-design.md §4).
    inductives: HashMap<String, Rc<Inductive>>,
    by_tag: HashMap<u32, Rc<Inductive>>,
    /// Route 2b's fingerprint anchor (`docs/inductive-fording-lowering.md`
    /// §6.3): the **skeleton's** nominal tag → the forded declaration it is the
    /// skeleton of. A forded type is a Σ whose first component is the skeleton,
    /// so reading the declaration back is `tag_of` plus this one lookup.
    forded_by_skel: HashMap<u32, Rc<Inductive>>,
    /// Machine-named Ψ definitions for generator-emitted artifacts
    /// (`issues/generated-term-defs.md`, `gendefs.rs`): `μ_D`, the index
    /// type's tag predicates, its child projections. Registered once at
    /// declaration time; every emission site references them and falls back
    /// to inlining when a key is absent.
    gdefs: gendefs::GenDefs,
    ctors: HashMap<String, (Rc<Inductive>, usize)>,
    /// Every field name of every declared `record`, across all of them. Not a
    /// resolution table — which record a name belongs to is decided by the
    /// receiver's type — but the **cheap negative test** that keeps `.`
    /// resolution off the hot path: a name that is nobody's field takes the
    /// method fallback without inferring the receiver at all
    /// (docs/surface-records.md §4.2). That is every use that existed before
    /// records, which is what makes the move of `.` into the elaborator a
    /// no-op for them.
    record_fields: HashSet<String>,
    /// Every *base* name attached to some type's namespace by a `fn D::m` /
    /// `theorem D::m` declaration, across all of them
    /// (issues/type-owned-members-receiver-slice.md). The same cheap negative
    /// test as [`Self::record_fields`], and for the same reason: `t.m(a)`
    /// consults this before inferring the receiver's type, so a `.` call on a
    /// name nobody attaches costs exactly what it cost before members existed.
    /// Which type a base name belongs to is not recorded here — that is
    /// decided by the receiver, against the ordinary name tables.
    member_bases: HashSet<String>,
    /// Every field name of every declared `class`, across all of them
    /// (docs/traits-receiver-dispatch-design.md §3). The same **cheap negative
    /// test** as [`Self::record_fields`] and [`Self::member_bases`], and for
    /// the same reason: `x.op(y)` consults this before inferring the
    /// receiver's type or building a resolution goal, so a `.` call on a name
    /// that is nobody's class field costs exactly what it cost before classes
    /// existed. Which class a name belongs to — and whether an instance exists
    /// at the receiver's carrier — is decided by the receiver and the
    /// resolver, never here.
    class_members: HashSet<String>,
    /// Declared classes, by qualified name (docs/traits-layer1-design.md §2).
    /// A class *is* a record — `inductives` holds it too — so this table
    /// carries only what `extends` and the instance assembler need beyond the
    /// record: the flattened field list with its per-field owner, and the
    /// transitive ancestor list. Layer 2's resolver is the consumer it exists
    /// for.
    classes: HashMap<String, Rc<ClassInfo>>,
    /// One canonical value per (class, carrier head)
    /// (docs/traits-layer1-design.md §4.1). Declaring is registering; there is
    /// no search over this table at layer 1, only the fill-by-reference and
    /// parent-synthesis lookups the `extends` discipline makes.
    instances: HashMap<traits::InstKey, InstanceInfo>,
    /// What an operator symbol means at a carrier: one entry per **(symbol,
    /// carrier head)** (docs/operators-onto-classes-design.md §3.2).
    ///
    /// Beside `instances` and keyed the same way — on the carrier's *head*,
    /// by the same `head_name` — for the same reason: declaring is
    /// registering, and there is no search over it. What it is *not* is a
    /// default-instance table: it says what a symbol means, never which
    /// structure a carrier has, which is why `+` at `Bool` can be `or` while
    /// both Bool monoids stay registered as equals (§3.3).
    designations: HashMap<(String, String), traits::DesignationInfo>,
    /// One repr per spec type, keyed per `docs/datarepr-design.md` §4: the
    /// spec inductive's *elaborated declaration* identity plus the elaborated
    /// arguments of the instantiation. Declaration keying and not nominal
    /// keying, so that editing `S` invalidates its repr instead of leaving a
    /// stale basis that still resolves (§4's failure mode).
    datareprs: HashMap<datarepr::DatareprKey, datarepr::DatareprInfo>,
    /// The monomorph names a `datarepr` minted for parameterized
    /// instantiations (§1.4 item 2), keyed on (declaration tag, argument
    /// spelling). `List<Tok>` is spellable as a *type* and unspellable as a
    /// *name*; this table is what lets a generator name a function about it.
    monomorphs: HashMap<(u32, String), String>,
    /// Reprs by their own name, for `impl f for Rp` to find `Rp`'s carrier
    /// and the namespace its `abs`/`inv` live in.
    datarepr_by_name: HashMap<String, datarepr::DatareprInfo>,
    /// One `Impl` per (repr, operation) — the open, per-operation registry of
    /// design §1.2, keyed per §4. The entry carries how it got there, which is
    /// recorded for humans and tools and read by no certificate
    /// (docs/obligation-records-design.md §4.4).
    impls: HashMap<(String, String), datarepr::ImplEntry>,
    /// Every obligation every obligation-bearing declaration stated, in
    /// declaration order — what `heather obligations` lists
    /// (docs/obligation-records-design.md §6). Recorded only on success, which
    /// under inline-first is the only outcome that leaves anything behind.
    obligations: Vec<datarepr::Obligation>,
    /// The designed access spellings of every repr and `Impl` declared so far,
    /// and the generated-mode depth that exempts an emission from them
    /// (`access.rs`, `docs/repr-access-spellings-design.md`).
    access: access::AccessTable,
    /// Set while a `:= derive()` route elaborates the transfer generator's
    /// emission, so that the `impl` block *inside* that emission records
    /// `Derived` rather than what its own clauses look like. `None` everywhere
    /// else, which makes the mechanism inert.
    impl_provenance: Option<datarepr::Provenance>,
    /// Surface declarations by name; see the note in `elab_decl`.
    decls: HashMap<String, Decl>,
    /// Operator fallbacks taken while elaborating the current declaration
    /// after a designation table was consulted at a known, uncovered carrier.
    /// Kept only to turn an otherwise source-free kernel rejection into a
    /// diagnostic about the notation the writer actually used.
    op_fallback_notes: RefCell<Vec<String>>,
    /// While an `instance` block is being elaborated: the members that have
    /// already landed, as (written name, full name). An unqualified reference
    /// to one of them resolves to its global, which is the whole of "later
    /// members use earlier members by name" (docs/traits-layer1-design.md
    /// §4.2). Empty outside a block, which makes the mechanism inert.
    instance_scope: Vec<(String, String)>,
    /// Canonical derived instances, minted into Ψ, one per derivation
    /// (docs/traits-layer2-design.md §8). A `Vec` and not a map: the key is
    /// the goal type *up to conversion*, so lookup is a scan and the table is
    /// small by construction (one entry per distinct derived dictionary in
    /// the program).
    derived: Vec<resolve::DerivedInst>,
    /// Goals this item's elaboration derived and that deserve a canonical
    /// global. Ψ must not grow mid-declaration, so minting is a **restart**:
    /// the item is rolled back, the queue drained, the item elaborated again
    /// (§8). Empty for every program that resolves nothing, which is what
    /// keeps the whole mechanism free.
    pending_derived: RefCell<Vec<(Type, Level, u32)>>,
    /// Non-fatal diagnostics raised so far, in the order they were raised
    /// (`docs/diagnostic-warnings-design.md` §3). A `RefCell` because the
    /// places that raise one hold `&self` — the pattern compiler is the first
    /// customer and takes `&self` throughout, exactly as `goals` and
    /// `pending_derived` do.
    ///
    /// Drained by [`Self::take_warnings`], never by the elaborator: a warning
    /// belongs to whoever has the source text to render it against, and that
    /// is the caller (§3).
    warnings: RefCell<Vec<Warning>>,
    /// Backchaining depth, for the recursion cap. A `Cell` because resolution
    /// recurses *through* `elab_check` — the nested obligation is discovered
    /// by `apply_implicit`, not passed down.
    resolve_depth: Cell<usize>,
    next_tag: u32,
    fuel: u64,
    /// Number of Ψ slots reserved for the current declaration's goals — a
    /// syntactic pre-count of its holes. Goals occupy the *innermost* indices
    /// `[0, goal_base)` for the whole declaration, so every reference to a
    /// committed global is offset by it (see [`Self::resolve`]). Zero outside
    /// a declaration body, which makes the whole mechanism inert.
    goal_base: u32,
    /// Goals in creation order; goal `k` is `GlobalVar(goal_base - 1 - k)`.
    /// Interior mutability because the elaboration methods take `&self` and
    /// `Cx` is cloned at every binder.
    goals: RefCell<Vec<Goal>>,
    /// Hole span → goal index. The elaborator visits some expressions twice
    /// (motive synthesis; `calc`'s cloned `@trans` spine), and one syntactic
    /// hole must stay one goal.
    goal_spans: RefCell<HashMap<(usize, usize), usize>>,
    /// Set while elaborating an `on` right-hand side, where a *new* hole is
    /// refused. Load-bearing: it is what makes [`strengthen_global`] sound.
    frozen: Cell<bool>,
    /// Set while a motive-less `match` is speculatively inferring one arm's
    /// type ([`Self::infer_match_constant_motive`]). Its only job is to keep
    /// that speculation from *nesting*: the inner `match` declines to
    /// speculate, so the outer attempt fails and falls back to the message
    /// that names the motive. Without the guard the work at a `match` nested
    /// `d` deep would be 2^d — the shape
    /// `issues/type-argument-speculation-cost.md` was filed for, and the
    /// reason this is a flag rather than a syntactic scan of the arm.
    motive_speculation: Cell<bool>,
    /// `meta fn` definitions, **elaborator-held** (docs/in-language-map-design.md
    /// §4): kernel-checked at `Layer::Meta` against Ψ, never pushed to it —
    /// ch. 04 admits no layer-m term in a global context. The evaluation hook
    /// applies these to code arguments and reduces the application away.
    meta_defs: HashMap<String, MetaDef>,
    /// Which template elaborates which slot
    /// (docs/meta-def-registration-design.md §2). Populated by the `for`
    /// clause and by nothing else: a `meta fn` named `map_code` without one is
    /// not a template, which is the point at which "the name is the contract"
    /// was retired. One slot takes one template — a second claim is an error
    /// at its declaration, not a shadowing.
    /// Global across the program, deliberately: one template per slot, and a
    /// second claim is an error at the join. The value is
    /// `(module, template name)` so that the error can name both modules when
    /// the collision arrives through an import (docs/modules-design.md §4).
    meta_slots: HashMap<Slot, (String, String)>,
    /// The Ψ-extending binders of the `meta fn` currently elaborating (its
    /// `Ctx`/`TyCode` binders, plus letbox-bound code globals during quote
    /// assembly). The whnf/conv oracles append these to Ψ so meta-bound
    /// `GlobalVar`s resolve to the right bindings — the goal machinery's
    /// padding trick, one layer up. Empty outside a `meta fn`.
    meta_pushed: RefCell<Vec<GlobalBinding>>,
    /// The oracle consulted at the kernel gate (`gate.rs`), if any. `None` —
    /// the default, and what every test and the unflagged CLI use — means the
    /// kernel runs on every declaration, exactly as it always has.
    gate: Option<Rc<dyn gate::KernelGate>>,
}

/// Restores the ambient name-resolution environment after re-lowering one
/// declaration's stored surface syntax.
struct ResolutionScope<'a> {
    stack: &'a RefCell<Vec<Rc<Scope>>>,
}

impl Drop for ResolutionScope<'_> {
    fn drop(&mut self) {
        self.stack.borrow_mut().pop().expect("a resolution scope was installed");
    }
}

/// One registered `meta fn`: its closed layer-m term and statement type,
/// plus — for a template that claimed a slot — the Π **order** its signature
/// declared (docs/meta-def-registration-design.md §2.2).
///
/// The hook types its *evaluated payload* by kernel inference rather than by
/// peeling `stmt`, so the statement is currently the registration's record
/// only — kept because it is the checked fact about `term`.
///
/// `order` holds positions into the slot spec's ingredient list, in the
/// template's own binder order: it is the one place that knowledge lives, and
/// [`Elaborator::try_code_template`] is the only reader.
#[derive(Clone)]
pub(crate) struct MetaDef {
    pub(crate) term: Rc<Term>,
    #[allow(dead_code)]
    pub(crate) stmt: Rc<Type>,
    /// `|Ψ|` when this definition was registered.
    ///
    /// A meta definition is **elaborator-held**, so nothing rescopes it when Ψ
    /// grows — unlike a Ψ-resident binding, whose body is prefix-scoped and
    /// rescoped at every lookup. A `GlobalVar` counts from the *end* of Ψ, so
    /// every declaration elaborated after this one moves what its references
    /// mean, and a use site has to shift by the growth
    /// (`MetaDef::at`). Invisible while templates were pure quotation — a
    /// template that references no global has nothing to go stale — and the
    /// first analyzer, whose arms call library functions, hits it at once.
    pub(crate) psi_len: u32,
    /// The slot this template claimed, if any. `None` is an ordinary meta
    /// definition: registered, never dispatched.
    #[allow(dead_code)]
    pub(crate) slot: Option<Slot>,
    pub(crate) order: Vec<usize>,
}

impl MetaDef {
    /// This definition's term and statement, rescoped to a Ψ of length `now`.
    pub(crate) fn at(&self, now: usize) -> (Rc<Term>, Rc<Type>) {
        let growth = now as u32 - self.psi_len;
        if growth == 0 {
            return (Rc::clone(&self.term), Rc::clone(&self.stmt));
        }
        (
            Rc::new(self.term.shift_global(growth)),
            Rc::new(self.stmt.shift_global(growth)),
        )
    }
}

/// What a `p.f` turned out to be (docs/surface-records.md §4.2).
enum DotResolution {
    /// A record field: the projection, its type and level, plus the field's
    /// implicitness skeleton, derived on demand from the *stored surface*
    /// field type — no new storage, keyed positionally by the same index the
    /// kernel Σ-walk uses (docs/implicit-binders-design.md §3.1).
    Project(Term, Type, Level, Option<Rc<Skel>>),
    /// A **class member reached through an instance**
    /// (docs/traits-receiver-dispatch-design.md §2): the projection of a
    /// *resolved* dictionary, carrying its own argument list because the
    /// receiver is one of the arguments (`x.op(y)` is `π_op(dict)(x, y)`) and
    /// the written list is not.
    Dispatch(Term, Type, Level, Option<Rc<Skel>>, Vec<Expr>),
    /// Not a field: the method-call desugaring `f(args…, recv)`, to be
    /// elaborated in whichever mode the caller is in — which is what keeps
    /// checking-only methods like `p.absurd()` working.
    Method(Expr),
}

/// A goal: a hole that survives to the end of its block. Represented exactly
/// like the elaborator's other metavariables (issues/elab-stage2-metas.md) —
/// an innermost Ψ-binding `u : Trm(Γ ⊢ T @ l)` occurring as `u^{id_Γ}` — but
/// allocated for the whole declaration and discharged by an `on` statement
/// rather than by unification.
#[derive(Clone)]
struct Goal {
    /// Discharge name (site-written `?first`, or checker-assigned).
    name: String,
    /// The context *at the hole*. This capture is the point of the design: an
    /// `on` written at block end elaborates here, so a goal raised inside a
    /// `match` arm is discharged with that arm's binders in scope.
    cx: Cx,
    ty: Type,
    level: Level,
    span: Span,
    /// `(callee, parameter)` when the hole is an argument — the provenance the
    /// listing reports, and where an anonymous hole's default name comes from.
    origin: Option<(String, String)>,
    solution: Option<Rc<Term>>,
}

impl Default for Elaborator {
    fn default() -> Self {
        Self::new()
    }
}

impl Elaborator {
    /// An empty elaborator (no prelude).
    pub fn new() -> Self {
        Elaborator {
            psi: GlobalCtx::default(),
            delta_psi: GlobalCtx::default(),
            scope: Scope::new(DEFAULT_MODULE),
            resolution_scopes: RefCell::new(Vec::new()),
            module_scopes: HashMap::new(),
            names: NameIndex::default(),
            globals: HashMap::new(),
            inductives: HashMap::new(),
            by_tag: HashMap::new(),
            forded_by_skel: HashMap::new(),
            gdefs: gendefs::GenDefs::default(),
            ctors: HashMap::new(),
            record_fields: HashSet::new(),
            member_bases: HashSet::new(),
            class_members: HashSet::new(),
            classes: HashMap::new(),
            instances: HashMap::new(),
            designations: HashMap::new(),
            datareprs: HashMap::new(),
            monomorphs: HashMap::new(),
            datarepr_by_name: HashMap::new(),
            impls: HashMap::new(),
            obligations: Vec::new(),
            access: access::AccessTable::default(),
            impl_provenance: None,
            decls: HashMap::new(),
            op_fallback_notes: RefCell::new(Vec::new()),
            instance_scope: Vec::new(),
            derived: Vec::new(),
            pending_derived: RefCell::new(Vec::new()),
            warnings: RefCell::new(Vec::new()),
            resolve_depth: Cell::new(0),
            next_tag: 0,
            fuel: DEFAULT_FUEL,
            goal_base: 0,
            goals: RefCell::new(Vec::new()),
            goal_spans: RefCell::new(HashMap::new()),
            frozen: Cell::new(false),
            motive_speculation: Cell::new(false),
            meta_defs: HashMap::new(),
            meta_slots: HashMap::new(),
            meta_pushed: RefCell::new(Vec::new()),
            gate: None,
        }
    }

    /// Install the oracle consulted at the kernel gate (`gate.rs`).
    ///
    /// **This is a trust decision**, not a performance knob: a gate that
    /// admits a declaration means the kernel never sees it. The elaborator
    /// neither audits the oracle nor knows what it is —
    /// `docs/cache-v1-design.md` §6 is where the argument for the one shipped
    /// implementation lives.
    pub fn set_gate(&mut self, gate: Rc<dyn gate::KernelGate>) {
        self.gate = Some(gate);
    }

    /// An elaborator with the stage-1 prelude already elaborated and
    /// kernel-checked.
    ///
    /// The degenerate module call (docs/modules-design.md §10.2): the prelude
    /// is an ordinary module that happens to be elaborated first and to be
    /// implicitly imported by every other one.
    pub fn with_prelude() -> R<Self> {
        let mut e = Self::new();
        e.elab_module_source(PRELUDE_MODULE, PRELUDE)?;
        Ok(e)
    }

    /// Parse and elaborate a source file, kernel-checking every declaration.
    pub fn elab_source(&mut self, src: &str) -> R<()> {
        self.elab_module_source(DEFAULT_MODULE, src)
    }

    /// [`Self::elab_source`] for text a *generator* wrote: the minted names
    /// (`Repr_N::abs`, `Impl_R_f::body`) are the surface inside it, exactly as
    /// they are when the same text is elaborated as part of the declaration
    /// that produced it (`docs/repr-access-spellings-design.md` §6).
    ///
    /// The standing customer is the perturbed-emission mutation control: it
    /// re-checks generated text with one byte changed, and through the user
    /// entry point it would be refused for spelling a generated name instead
    /// of for the mutation — a control passing for the wrong reason.
    pub fn elab_generated_source(&mut self, src: &str) -> R<()> {
        self.generated_mode(|me| me.elab_source(src))
    }

    /// [`Self::elab_source`] into a named module. The elaborator does no file
    /// IO: an `import m;` here requires that `m` has *already* been elaborated
    /// into this same accumulator, which is exactly what the CLI's topological
    /// walk guarantees (docs/modules-design.md §3.2).
    pub fn elab_module_source(&mut self, module: &str, src: &str) -> R<()> {
        let file = parse_file(src)?;
        self.enter_module(module, &file)?;
        for item in &file.items {
            let warn_mark = self.warnings.borrow().len();
            let r = match item {
                Item::Decl(d) => self.elab_decl(d),
                Item::Inductive(i) => self.elab_inductive(i),
                Item::Class(c) => self.elab_class(c),
                Item::Instance(i) => self.elab_instance(i),
                Item::Designation(d) => self.elab_designation(d),
                Item::Datarepr(d) => self.elab_datarepr(d),
                Item::Impl(i) => self.elab_impl(i),
                Item::Import(_) => Ok(()),
            };
            // Canonical derived instances are minted **between** items, where
            // Ψ may grow (docs/traits-layer2-design.md §8). A failed item
            // mints nothing: its derivations are as speculative as the rest of
            // it.
            if r.is_err() {
                self.pending_derived.borrow_mut().clear();
                self.warnings.borrow_mut().truncate(warn_mark);
            } else {
                self.mint_pending();
            }
            r?;
        }
        Ok(())
    }

    /// Set the scope for a module about to be elaborated: its own name plus
    /// its written imports, each checked for existence and for the one
    /// import-time error the regime has (two lists claiming one name).
    fn enter_module(&mut self, module: &str, file: &heather_syntax::File) -> R<()> {
        // Re-entering a module is *not* an error here, and it is **additive**:
        // a caller that feeds one accumulator two chunks of the same module
        // (every test that calls `check_source` twice, and every REPL-shaped
        // use) is doing what one file would do, so the second chunk keeps the
        // first's imports and may add to them. Duplicate declarations already
        // error one layer down; two distinct *files* claiming one module name
        // is a loader concern, where the paths are known.
        let mut scope =
            self.module_scopes.get(module).cloned().unwrap_or_else(|| Scope::new(module));
        let mut written: Vec<&str> = Vec::new();
        for item in &file.items {
            let Item::Import(imp) = item else { continue };
            if imp.module == module {
                return err(format!("a module cannot import itself (`{module}`)"), imp.span);
            }
            if imp.module != PRELUDE_MODULE && !self.module_scopes.contains_key(&imp.module) {
                return err(
                    format!(
                        "unknown module `{}`: it is not in this run's import closure",
                        imp.module
                    ),
                    imp.module_span,
                );
            }
            // Twice *in this file* is the error; an import repeated across
            // two chunks of one module is the same import.
            if written.contains(&imp.module.as_str()) {
                return err(format!("`{}` is imported twice", imp.module), imp.span);
            }
            written.push(&imp.module);
            for (n, nspan) in &imp.listed {
                if !self.names.declares(&imp.module, n) {
                    return err(
                        format!("`{}` declares no `{n}`", imp.module),
                        *nspan,
                    );
                }
                if let Some(other) = scope
                    .imports
                    .iter()
                    .find(|i| i.module != imp.module && i.listed.iter().any(|l| l == n))
                    .map(|i| i.module.clone())
                {
                    // Both were asked for by name; there is nothing left to
                    // prefer, so this is the error the regime promises rather
                    // than a silent precedence.
                    return err(
                        format!(
                            "`{n}` is listed by two imports (`{other}` and `{}`): a listed \
                             name is a standing choice, so only one import may claim it",
                            imp.module
                        ),
                        *nspan,
                    );
                }
            }
            let listed: Vec<String> = imp.listed.iter().map(|(n, _)| n.clone()).collect();
            match scope.imports.iter_mut().find(|i| i.module == imp.module) {
                Some(existing) => existing.listed.extend(listed),
                None => scope.imports.push(ImportSpec { module: imp.module.clone(), listed }),
            }
        }
        self.module_scopes.insert(module.to_string(), scope.clone());
        self.scope = scope;
        Ok(())
    }

    // -- name resolution (docs/modules-design.md §4) -------------------------

    /// Resolve a written name to the module that declares it, by the §4
    /// regime. Every table lookup below goes through this.
    fn resolve_name(&self, name: &str) -> NameRes {
        // A generated name written in user source, and an access path naming
        // no declaration, are refused *here* — before anything can report them
        // as unknown, since "unknown" is exactly the wrong thing to say about
        // a name that exists and is not the surface
        // (docs/repr-access-spellings-design.md §6).
        if let Some(msg) = self.access_refusal(name) {
            return NameRes::Restricted(msg);
        }
        if let Some(msg) = self.unknown_access_path(name) {
            return NameRes::Restricted(msg);
        }
        self.resolve_declared(name)
    }

    /// [`Self::resolve_name`] without the surface refusal: what the *tables*
    /// say. The alias's target is looked up through this — a designed path
    /// resolves to a declaration whose own name is not spellable, which is the
    /// whole point of the alias (design §5).
    fn resolve_declared(&self, name: &str) -> NameRes {
        self.resolve_declared_kinds(name, names::ANY_KIND)
    }

    fn resolve_declared_kinds(&self, name: &str, kinds: &[NameKind]) -> NameRes {
        let scopes = self.resolution_scopes.borrow();
        let scope = scopes.last().map(Rc::as_ref).unwrap_or(&self.scope);
        names::resolve_kinds(&self.names, scope, name, kinds, |m, ty, ctor| {
            self.inductives
                .get(&qkey(m, ty))
                .is_some_and(|i| i.ctors.iter().any(|c| c.name == ctor))
        })
    }

    /// Install the declaration scope for one read of stored inductive syntax.
    /// The guard restores the caller's scope on every return path.
    fn use_inductive_scope<'a>(&'a self, ind: &inductive::Inductive) -> ResolutionScope<'a> {
        self.resolution_scopes.borrow_mut().push(Rc::clone(&ind.scope));
        ResolutionScope { stack: &self.resolution_scopes }
    }

    /// The base half of a written name — `nat::sub` and `sub` both name `sub`.
    fn base_name(name: &str) -> &str {
        split_qual(name).map(|(_, b)| b).unwrap_or(name)
    }

    /// The qualified table key a written name resolves to, if it resolves.
    ///
    /// A **designed access path** (`BinNat::abs`,
    /// `Impl(add, BinNat)::refines`) resolves to the declaration it names, and
    /// strictly as a *fallback*: only a name with no reading of its own takes
    /// it, so nothing that resolved before the alias existed can be
    /// reinterpreted by it (docs/repr-access-spellings-design.md §5).
    fn key_of(&self, name: &str) -> Option<String> {
        self.key_of_kinds(name, names::ANY_KIND)
    }

    /// [`Self::key_of`] with the candidate set restricted by declaration kind.
    /// See [`Self::lookup_inductive`] for the one restricted caller and why
    /// the restriction is licensed there and nowhere else.
    fn key_of_kinds(&self, name: &str, kinds: &[NameKind]) -> Option<String> {
        if self.access_refusal(name).is_some() {
            return None;
        }
        if let Some(k) = self.key_of_declared_kinds(name, kinds) {
            return Some(k);
        }
        // The alias, strictly as a fallback. Its target is resolved through
        // `key_of_declared` and not `key_of`, because the target's own name is
        // the one the surface refuses — that is what the alias is for.
        self.key_of_declared_kinds(self.access_alias(name)?, kinds)
    }

    fn key_of_declared_kinds(&self, name: &str, kinds: &[NameKind]) -> Option<String> {
        match self.resolve_declared_kinds(name, kinds) {
            NameRes::Found(m) => {
                // A *member* declares the qualified string itself
                // (issues/type-owned-members-receiver-slice.md), so its key
                // keeps both halves: `List::nth` in module `list` is
                // `list::List::nth`. The two other qualified readings —
                // `nat::sub` (module path) and `Option::None` (constructor by
                // type) — declare the base name, and this is what tells them
                // apart without a second resolution judgment.
                if split_qual(name).is_some() && self.names.declares(&m, name) {
                    return Some(qkey(&m, name));
                }
                Some(qkey(&m, Self::base_name(name)))
            }
            _ => None,
        }
    }

    fn lookup_global(&self, name: &str) -> Option<&GlobalInfo> {
        self.globals.get(&self.key_of(self.instance_alias(name))?)
    }

    /// Inside an `instance` block, an unqualified name that is an *earlier*
    /// member of this block names that member's global
    /// (docs/traits-layer1-design.md §4.2). A name rewrite and nothing more:
    /// the members' own parameters are unaffected, so in a *generic* instance
    /// a cross-member call still passes the `requires` binders — layer 1 has
    /// no resolution to fill them with.
    ///
    /// Consulted only from [`Self::lookup_global`], so locals, aliases,
    /// constructors and the self-reference all shadow it exactly as they
    /// shadow any global.
    fn instance_alias<'a>(&'a self, name: &'a str) -> &'a str {
        if self.instance_scope.is_empty() {
            return name;
        }
        match self.instance_scope.iter().rev().find(|(base, _)| base == name) {
            Some((_, full)) => full,
            None => name,
        }
    }

    /// The inductive a name denotes **in type position**.
    ///
    /// Resolved with the candidate set restricted to `Inductive` declarations
    /// (`names::resolve_kinds`), which is what lets `logic::False` the type
    /// and `bool::False` the constructor coexist under one import each: a
    /// constructor is not a type, so it could never have been meant here, and
    /// dropping it is a shrink rather than a choice
    /// (issues/false-collides-with-bools-constructor.md).
    pub(crate) fn lookup_inductive(&self, name: &str) -> Option<&Rc<Inductive>> {
        self.inductives.get(&self.key_of_kinds(name, &[NameKind::Inductive])?)
    }

    pub(crate) fn lookup_ctor(&self, name: &str) -> Option<(Rc<Inductive>, usize)> {
        // `Option::None` resolves through the *type*, so the key is the
        // constructor's own name in the type's module.
        let key = self.key_of(name)?;
        self.ctors.get(&key).map(|(i, k)| (Rc::clone(i), *k))
    }

    /// The error for a name that did not resolve. An ambiguous name must
    /// never be reported as an unknown one — that is the whole point of the
    /// regime — so every "unknown X" site routes its message through here and
    /// gets overridden when ambiguity is the real reason.
    fn name_miss(&self, name: &str, fallback: impl Into<String>, span: Span) -> ElabError {
        let res = self.resolve_name(name);
        let msg = miss_msg(&res, name, fallback.into())
            .unwrap_or_else(|| format!("`{name}` cannot be used here"));
        ElabError::Elab { msg, span }
    }

    /// Is `name` declared in the module being elaborated, as one of `kinds`?
    /// The duplicate-declaration test: a *module* never declares one name
    /// twice, while two modules may.
    fn own_declares(&self, name: &str, kinds: &[NameKind]) -> bool {
        self.names.declares_as(&self.scope.module, name, kinds)
    }

    /// The one collision the regime turns into an error at the *declaration*:
    /// a local name that an import listed by name. (An unlisted collision is
    /// fine — locals win.) Checked before anything is registered, since a
    /// failed declaration must register nothing.
    fn check_declarable(&self, name: &str, span: Span) -> R<()> {
        if let Some(m) = self
            .scope
            .imports
            .iter()
            .find(|i| i.listed.iter().any(|l| l == name))
            .map(|i| i.module.clone())
        {
            return err(
                format!(
                    "`{name}` is declared here and also listed by `import {m}::{{{name}}};` \
                     — a listed name is the file asking for that one, so the two cannot \
                     both stand: drop it from the import list and qualify (`{m}::{name}`)"
                ),
                span,
            );
        }
        Ok(())
    }

    /// Record a name as declared by the module being elaborated. Called at
    /// registration time — after the kernel gate — so that the index and the
    /// tables land together.
    pub(crate) fn add_name(&mut self, name: &str, kind: NameKind) {
        self.names.insert(&self.scope.module, name, kind);
    }

    /// [`Self::check_declarable`] then [`Self::add_name`], for the sites that
    /// register in one step.
    fn declare_name(&mut self, name: &str, kind: NameKind, span: Span) -> R<()> {
        self.check_declarable(name, span)?;
        self.add_name(name, kind);
        Ok(())
    }


    /// Check a whole file, recovering per declaration: a failed declaration
    /// registers nothing (globals and Ψ are touched only after the kernel
    /// gate), so the rest of the file still checks against everything that
    /// did succeed. Returns every diagnostic in source order; empty means
    /// the file is good.
    ///
    /// [`Self::elab_source`] is the all-or-nothing form: library code wants
    /// the first error as a `Result`, a human checking a file wants all of
    /// them — including the unsolved-goal listing of a proof further down.
    /// A parse error is still wholesale, since there is no recovery point
    /// inside a half-parsed file.
    pub fn check_source(&mut self, src: &str) -> Vec<ElabError> {
        self.check_module_source(DEFAULT_MODULE, src)
    }

    /// Take the warnings raised since the last call
    /// (`docs/diagnostic-warnings-design.md` §3). Draining rather than
    /// borrowing is the point: the CLI renders each module against *that
    /// module's* source, so a warning has to leave with the text its span
    /// indexes into, before the next file is checked.
    ///
    /// Empty is the overwhelmingly common answer, and warnings never affect
    /// whether a file checked — a caller that never calls this sees exactly
    /// the behaviour it saw before warnings existed (§4).
    pub fn take_warnings(&mut self) -> Vec<Warning> {
        std::mem::take(&mut self.warnings.borrow_mut())
    }

    /// Raise a warning. Takes `&self`: the customers hold shared borrows.
    ///
    /// Nothing here decides whether the warning *survives* — a declaration
    /// that goes on to fail drops the ones it raised, at the same site that
    /// drops its pending derivations (§4).
    pub(crate) fn warn(&self, msg: impl Into<String>, span: Span) {
        // §4.1: a span into *generated* text does not index into any file a
        // reader has, and a `datarepr`'s emission is elaborated inside an
        // ordinary `check` of the declaration that owns it. Rendering such a
        // span against the user's source would point a caret at an unrelated
        // line. Generated code is the generator's problem, so it is dropped
        // here rather than filtered by whoever renders.
        if self.access.in_generated() {
            return;
        }
        self.warnings.borrow_mut().push(Warning { msg: msg.into(), span });
    }

    /// [`Self::check_source`] into a named module — what the CLI's loader
    /// calls once per file of the import closure, in topological order
    /// (docs/modules-design.md §3.2). A module whose imports are themselves
    /// broken reports that and checks nothing: there is no recovery point
    /// before the scope exists.
    pub fn check_module_source(&mut self, module: &str, src: &str) -> Vec<ElabError> {
        let file = match parse_file(src) {
            Ok(f) => f,
            Err(e) => return vec![e.into()],
        };
        if let Err(e) = self.enter_module(module, &file) {
            return vec![e];
        }
        let mut errs = Vec::new();
        for item in &file.items {
            let warn_mark = self.warnings.borrow().len();
            let r = match item {
                Item::Decl(d) => self.elab_decl(d),
                Item::Inductive(i) => self.elab_inductive(i),
                Item::Class(c) => self.elab_class(c),
                Item::Instance(i) => self.elab_instance(i),
                Item::Designation(d) => self.elab_designation(d),
                Item::Datarepr(d) => self.elab_datarepr(d),
                Item::Impl(i) => self.elab_impl(i),
                Item::Import(_) => Ok(()),
            };
            if r.is_err() {
                self.pending_derived.borrow_mut().clear();
                // §4: a failed item's warnings are as speculative as the rest
                // of it — it registers nothing, and it says nothing.
                self.warnings.borrow_mut().truncate(warn_mark);
            } else {
                self.mint_pending();
            }
            if let Err(e) = r {
                errs.push(e);
            }
        }
        errs
    }

    /// The canonical derived instances minted so far, in mint order
    /// (docs/traits-layer2-design.md §8) — one per *derivation*, not per use
    /// site, which is the coherence invariant this table is.
    pub fn derived_instances(&self) -> Vec<&str> {
        self.derived.iter().map(|d| d.name.as_str()).collect()
    }

    /// A declared global's elaborated statement and body, by written name —
    /// what an analyzer's input is read out of (the fn to transcribe is an
    /// ordinary declaration, already checked and in Ψ).
    pub(crate) fn global_body(&self, name: &str) -> Option<(Rc<Type>, Rc<Term>)> {
        let info = self.lookup_global(name)?;
        match &self.psi.bindings[info.abs as usize] {
            GlobalBinding::Tm { ty, body: Some(body), .. } => {
                Some((Rc::clone(ty), Rc::clone(body)))
            }
            _ => None,
        }
    }

    /// The **pull reflection API**, first cut
    /// (issues/fn-reflection-for-analyzers.md,
    /// docs/fn-signature-reflection-design.md §1): a declared fn's *type as
    /// code* — a `Term::BoxTy` of type `CodeTy(·, 0)`, ready for the
    /// type-code recursor. Nothing is stored per declaration; the type is
    /// read out of Ψ on request, which is what makes this pull and not push.
    ///
    /// THIS IMPLEMENTATION IS FINAL, and that is a correction to what the
    /// signature-reflection round expected here
    /// (docs/opaque-globals-analysis-design.md §2): the opaque-globals round
    /// settled unfolding-for-analysis *at the reflection boundary*, so the
    /// Ψ-read + rescope below (`shift_global` by the Ψ growth since the
    /// binding — the same `v + 1` convention `Defs::body` uses on
    /// prefix-scoped kernel data) already *is* `u^δ` unfolding-on-request.
    /// No kernel machinery replaces it and no ch. 07 obligation attaches,
    /// because the kernel never learns reflection happened.
    pub(crate) fn fn_type_code(&self, name: &str) -> Option<Term> {
        let info = self.lookup_global(name)?;
        let abs = info.abs as usize;
        let GlobalBinding::Tm { ty, .. } = &self.psi.bindings[abs] else {
            return None;
        };
        let growth = (self.psi.bindings.len() - abs) as u32;
        let ty = ty.shift_global(growth);
        // Unfolding-for-analysis, per the doctrine above, now with a second
        // case: a statement spells registered lowerings as `El (D#tycode^δ)`
        // (`docs/annotation-component-respell-design.md` §2.1), and at layer
        // m a boxed global reference is *syntax* — the analyzer cannot δ
        // through it, so the signature checker would decline every fn whose
        // result is a coded declaration. The reflection boundary is where
        // that unfolds: hand the analyzer the inline lowering the reference
        // decodes to, i.e. exactly the type it analyzed before the respell
        // existed.
        let len = self.psi.bindings.len() as u32;
        let ty = match self.unspell_ty_deep(len, &ty) {
            Some(t) => t,
            None => ty,
        };
        Some(Term::BoxTy(Rc::new(ty)))
    }

    /// The pull reflection API's **body half**
    /// (docs/opaque-globals-analysis-design.md §2, the primitive the
    /// fn-reflection round left "to be named with the opaque-globals
    /// round"): a declared fn's elaborated body as *marked, closed code* —
    /// every bound-variable occurrence a level marker, every cross-function
    /// call head a callee marker, boxed — with the arity and the
    /// tag→name table the markers are read against. Pull like
    /// [`Self::fn_type_code`]: nothing stored per declaration, the body read
    /// out of Ψ per invocation (`GlobalBinding::Tm`'s `body`, the
    /// definitions round's field).
    ///
    /// Marked code IS the reflection contract: a raw body is exactly what an
    /// analyzer cannot use (variables are opaque to `tm_var`, globals are
    /// neutral to `elim^Trm`), so the primitive hands over the analyzable
    /// coordinate system and the key to read it. A body-less global —
    /// theorems' proofs are deliberately opaque — declines.
    pub fn fn_body_code(&self, name: &str) -> Result<certgen::BodyCode, String> {
        certgen::body_code(self, name)
    }

    /// A global's binding index by written name — the Ψ coordinate
    /// [`Self::global_name_at`] inverts. Reflection-internal.
    pub(crate) fn global_abs(&self, name: &str) -> Option<usize> {
        Some(self.lookup_global(name)?.abs as usize)
    }

    /// The written (base) name of the binding at absolute Ψ index `abs` —
    /// the reverse of [`Self::global_abs`], for resolving a stored body's
    /// `GlobalVar`s to callee names. A linear scan of the name table: callee
    /// resolution happens a handful of times per reflection request.
    pub(crate) fn global_name_at(&self, abs: usize) -> Option<String> {
        let key = self
            .globals
            .iter()
            .find_map(|(k, info)| (info.abs as usize == abs).then_some(k))?;
        Some(key.rsplit("::").next().unwrap_or(key).to_string())
    }

    /// The `meta fn` claiming an analyzer slot, with the arity of its Π spine
    /// fixed by the slot's own signature
    /// (docs/certgen-transcriber-in-language-design.md §6). `None` is the
    /// honest decline every caller falls back from: no template claimed it.
    pub(crate) fn analyzer_def(&self, slot: Slot) -> Option<&MetaDef> {
        let (m, name) = self.meta_slots.get(&slot)?;
        self.meta_defs.get(&names::qkey(m, name))
    }

    /// The accumulated global context (theorem statements).
    pub fn psi(&self) -> &GlobalCtx {
        &self.psi
    }

    /// Which indexed lowering was selected for `name` in the current module.
    /// Returns `None` when the name is absent or is not an indexed inductive.
    pub fn indexed_route(&self, name: &str) -> Option<IndexedRoute> {
        let key = if name.contains("::") {
            name.to_string()
        } else {
            names::qkey(&self.scope.module, name)
        };
        let ind = self.inductives.get(&key)?;
        ind.index.as_ref()?;
        Some(if ind.skel.is_some() { IndexedRoute::Forded } else { IndexedRoute::One })
    }

    // -- declarations -------------------------------------------------------

    /// Elaborate one declaration, always leaving the goal state clean — the
    /// `Elaborator` outlives a declaration (and an `elab_source` call), so a
    /// stale `goal_base` would silently corrupt the next one.
    fn elab_decl(&mut self, decl: &Decl) -> R<()> {
        // A `meta fn` is a different declaration form: modal signature,
        // quotation body, `Layer::Meta` check, elaborator-side registration
        // (docs/in-language-map-design.md §3–4).
        if decl.is_meta {
            return self.elab_meta_decl(decl);
        }
        self.op_fallback_notes.borrow_mut().clear();
        let r = self.elab_decl_inner(decl);
        self.goal_base = 0;
        self.refresh_delta_psi();
        self.goals.borrow_mut().clear();
        self.goal_spans.borrow_mut().clear();
        self.frozen.set(false);
        self.op_fallback_notes.borrow_mut().clear();
        // The surface signature, kept for the declaration forms that have to
        // *restate* it: `impl f for Rp` computes `f`'s refinement obligation
        // by rewriting `f`'s own parameter and result types
        // (docs/datarepr-design.md §1.2). Nothing in the ordinary path reads
        // this table.
        if r.is_ok() {
            self.decls.insert(decl.name.clone(), decl.clone());
        }
        r
    }

    fn elab_decl_inner(&mut self, decl: &Decl) -> R<()> {
        // The constraint binders' desugaring at an **indexed** class
        // (docs/operation-indexed-classes-design.md §4): the index binders in
        // front of the dictionary, or the dictionary floated past the
        // parameters its index links to. `None` — every declaration with no
        // indexed-class constraint — is the identity and costs one walk of the
        // parameter list.
        let expanded;
        let (decl, ambiguous, symbols) = match self.expand_constraints(decl)? {
            None => (decl, Vec::new(), Vec::new()),
            Some(x) => {
                expanded = Decl { params: x.params, ..decl.clone() };
                (&expanded, x.ambiguous, x.symbols)
            }
        };
        if self.own_declares(&decl.name, &[NameKind::Global]) {
            return err(format!("duplicate name `{}`", decl.name), decl.span);
        }
        self.check_declarable(&decl.name, decl.span)?;
        // `fn D::m(…)` — a member of `D`'s namespace. The attachment is
        // *checked*: `D` has to name a type visible here, which is the whole
        // difference between this and a naming convention
        // (issues/type-owned-members-receiver-slice.md). What is declared is
        // the qualified string, so the base name stays out of the ambient
        // namespace and is reached through the receiver or by qualification.
        let member = split_qual(&decl.name);
        if let Some((owner, base)) = member {
            // A **type former** owns a namespace too, as of the 2026-08-17
            // carrier widening (docs/decide-class-design.md §2): `Le::Decide` is
            // the canonical name of the decidability instance at `Le`, and it is
            // an ordinary member declaration like every other instance value.
            // Widened here rather than only on the instance path, so that the
            // owner rule is one rule — an instance's canonical name has never
            // been a special kind of declaration, and making it one to avoid
            // this line would be the first time it was.
            if !self.names_a_carrier(owner) {
                return err(
                    format!(
                        "`{owner}` is not a type or a type former in scope, so `{}` \
                         attaches to nothing — a member declaration is \
                         `fn <Type>::{base}(…)` and the type must be declared (or be a \
                         kernel type) before it",
                        decl.name
                    ),
                    decl.span,
                );
            }
            if base.is_empty() {
                return err("a member needs a name after `::`", decl.span);
            }
        }
        // Reserve the goal prefix *before* anything is elaborated: the
        // telescope and result type are elaborated first and their types end
        // up embedded in the emitted term, so they must live in the same
        // (shifted) world as the body.
        self.goal_base = count_holes(decl);
        self.refresh_delta_psi();
        // Elaborate the parameter telescope. Type parameters come first and
        // are ordinary kernel binders at `Ty 0` — level-0 parametric
        // polymorphism, Tarski-style, so a *use* of one in type position is
        // `El A` (docs/surface-polymorphism.md §2). They are registered in
        // `cx.tyvars`, the same table an `inductive`'s parameters use while
        // its fields are lowered; the difference is only that these survive
        // into the kernel term.
        let mut cx = Cx::empty();
        cx.index_ambiguity = ambiguous;
        // The constraint slots' symbols, checked against each other on the way
        // in: §5.2's uniqueness rule runs over the symbol namespace by any mix
        // of slots and `as` (issues/binder-symbol-as-notation.md), and one loop
        // over one table is the whole of it.
        for s in symbols {
            Self::check_symbol_free(&cx.op_locals, &s.0, decl.span)?;
            cx.op_locals.push(s);
        }
        let mut param_info: Vec<(Type, Level)> = Vec::new();
        for (i, tv) in decl.tyvars.iter().enumerate() {
            let name = &tv.name;
            if decl.tyvars[..i].iter().any(|o| o.name == *name) {
                return err(format!("duplicate type parameter `{name}`"), decl.span);
            }
            if decl.params.iter().any(|p| p.name == *name) {
                return err(
                    format!("`{name}` is both a type parameter and a parameter of `{}`", decl.name),
                    decl.span,
                );
            }
            // `<A: Type<n>>`, defaulting to `Type<0>` — the binder is at
            // `Ty n`, which is itself a type at level `n + 1`
            // (docs/surface-universe.md §2).
            let level = Level::constant(tv.level);
            let (ty, lvl) = (Type::Ty(level.clone()), Level::constant(tv.level + 1));
            cx.push(name.clone(), ty.clone(), lvl.clone());
            // `El^n A`, scoped at the binder just pushed. `lower_named`
            // weakens by `names.len() - depth`, so recording the depth *after*
            // the push makes `Var(0)` correct here and correct everywhere
            // deeper — the device `Alias` and the inductive `TyVar` both use.
            cx.tyvars.push(TyVar {
                name: name.clone(),
                ty: Type::El { level: level.clone(), tm: Rc::new(Term::Var(LocalVar(0))) },
                level,
                depth: cx.names.len(),
            });
            param_info.push((ty, lvl));
        }
        for p in &decl.params {
            // `<A: Monoid>` — the inline constraint form. Its class is checked
            // before its type is elaborated, so `<A: Nat>` complains about the
            // annotation the user wrote and not about `Nat<A>`.
            self.check_constraint_param(p)?;
            let (ty, lvl) = self.elab_ty(&cx, &p.ty)?;
            // A binder of a class type at a written index is what fills a value
            // slot that unification left open (§5's ladder step 2), for the dot
            // sugars here and for a call's goal in `apply_implicit`.
            if let Some(r) = self.class_ref_of_ty(&p.ty)
                && !r.index.is_empty()
                && !r.args.is_empty()
            {
                cx.dicts.push(Rc::new(DictBinder {
                    name: p.name.clone(),
                    class: r.name,
                    carrier: r.args[0].clone(),
                    index: r.index,
                }));
            }
            cx.push_skel(p.name.clone(), ty.clone(), lvl.clone(), skel_of_ty(&p.ty));
            // `op as ∙` — the binder's **body** spelling, installed for the
            // rest of its scope: the remaining telescope, the result type (so a
            // theorem's *statement* may use it), and the body
            // (issues/binder-symbol-as-notation.md). This is exactly the
            // installation the constraint symbol slot performs
            // (docs/operators-onto-classes-design.md §5(b)) into exactly the
            // same table, which is the point — `as` adds a place to *write* a
            // symbol and never a second way to resolve one. The identifier is
            // untouched: `op` still binds the parameter, so the constraint
            // slot, the call sites and every diagnostic go on as before.
            if let Some(sym) = &p.symbol {
                Self::check_symbol_free(&cx.op_locals, sym, p.span)?;
                cx.op_locals.push((sym.clone(), p.name.clone()));
            }
            // An ordinary parameter *at a universe* — `(A: Type<n>, x: A)` —
            // is usable as a type for the rest of the telescope, by exactly
            // the machinery a declaration's `<A>` uses. That generalization is
            // the round: a type name is any binder whose type is `Type<n>`,
            // not only one bound by `<…>` (docs/surface-universe.md §2).
            if let Type::Ty(level) = &ty {
                cx.tyvars.push(TyVar {
                    name: p.name.clone(),
                    ty: Type::El { level: level.clone(), tm: Rc::new(Term::Var(LocalVar(0))) },
                    level: level.clone(),
                    depth: cx.names.len(),
                });
            }
            param_info.push((ty, lvl));
        }
        // Result type and body (checked against it). The declaration's own
        // name goes into scope for the body only: a self-call guarded by a
        // `match` on one of these parameters *is* the induction hypothesis
        // (issues/match-recursion.md), and the lowering constructs the
        // recursor, so there is no fixpoint and nothing new for the kernel.
        //
        // A result-position implicit mark has no consumer this round —
        // callers of `f()` get a computed head with no skeleton — and is
        // refused rather than dropped (docs/implicit-binders-design.md §3.4;
        // result-position skeletons on `GlobalInfo` are the named follow-on).
        if has_implicit_mark(&decl.result) {
            return err(IMPLICIT_MARK_REFUSED, decl.result.span);
        }
        let (res_ty, res_lvl) = self.elab_ty(&cx, &decl.result)?;
        cx.selfref = Some(Rc::new(SelfRef {
            // A member recurses under its **base** name: inside `fn List::nth`
            // the recursive call is `nth(t)`, not `List::nth(t)`. The self-name
            // is checked before globals in `resolve`, so this shadows an
            // ambient `nth` for the body only — which is the same scoping the
            // name has always had.
            name: member.map_or_else(|| decl.name.clone(), |(_, base)| base.to_string()),
            // Type parameters are part of the telescope, so they are part of
            // the positional bookkeeping a guarded self-call does — as
            // *implicit* parameters, which is what keeps them out of the
            // argument list `map(f, tail)` has to match
            // (docs/surface-polymorphism.md §6.1).
            params: decl
                .tyvars
                .iter()
                .map(|t| (t.name.clone(), true))
                .chain(decl.params.iter().map(|p| (p.name.clone(), p.implicit)))
                .collect(),
            n_tyvars: decl.tyvars.len(),
        }));
        // `let` bindings, then the result expression.
        let cx = self.elab_stmts(&cx, &decl.body.stmts)?;
        let body = self.elab_check(&cx, &decl.body.result, &res_ty, &res_lvl)?;
        // Discharge every goal the block raised, then substitute them away.
        self.solve_goals(&decl.body.ons, &decl.name)?;
        let sigma = self.goal_subst();

        // Close over the telescope: statement = Π…, proof/body = λ….
        //
        // The binder and result types are **respelled** on the way out
        // (`docs/annotation-component-respell-design.md` §2.1): every
        // component that is a registered declaration's lowering becomes
        // `El (D#tycode^δ)`, in the Ψ statement and the body's outer λs both.
        // This runs *after* the body is elaborated — every structural read
        // during elaboration saw the inline types — and *before*
        // `apply_global`, so the references' goal padding is renumbered with
        // everything else. The payoff cascades: an `App` at a call site
        // copies its `dom`/`cod` annotations out of the callee's statement,
        // so respelling the statement once shrinks every later application
        // for free. References are minted against the empty context (the
        // statement's own) at each binder's depth.
        let empty_cx = Cx::empty();
        let n_params = param_info.len() as u32;
        let mut stmt = match self.respell_ty_deep(&empty_cx, &res_ty, n_params) {
            Some(r) => r,
            None => res_ty,
        };
        let mut stmt_lvl = res_lvl;
        let mut term = body;
        for (i, (dom, dom_lvl)) in param_info.into_iter().enumerate().rev() {
            let dom = match self.respell_ty_deep(&empty_cx, &dom, i as u32) {
                Some(r) => r,
                None => dom,
            };
            term = Term::Lam {
                dom_level: dom_lvl.clone(),
                cod_level: stmt_lvl.clone(),
                dom: Rc::new(dom.clone()),
                body: Rc::new(term),
            };
            stmt = Type::Pi {
                dom_level: dom_lvl.clone(),
                cod_level: stmt_lvl.clone(),
                dom: Rc::new(dom),
                cod: Rc::new(stmt),
            };
            stmt_lvl = Level::max(dom_lvl, stmt_lvl);
        }

        // One global substitution fills every goal and renumbers the committed
        // globals back down out of the goal world (`GlobalSubst`'s
        // instantiation semantics). With no holes it is the identity.
        let term = term.apply_global(&sigma);
        let stmt = stmt.apply_global(&sigma);

        // The kernel is the gate: check the statement, then the term.
        // `stats::time_kernel` attributes exactly this to the kernel half of
        // the frontend suite's phase split (crates/elab/src/stats.rs).
        //
        // An installed gate oracle (`gate.rs`) may vouch for the declaration
        // instead, in which case neither call runs. Nothing installs one by
        // default; `heather check --cache` is the only caller today.
        let empty = LocalCtx::nil();
        {
            let item = gate::GateItem {
                name: &decl.name,
                ctx: &empty,
                ty: &stmt,
                level: &stmt_lvl,
                body: &term,
                opaque: matches!(decl.kind, DeclKind::Theorem),
                layer: Layer::Code,
                lands_in_psi: true,
            };
            if !self.gate.as_ref().is_some_and(|g| g.admits(&self.psi, &item)) {
                stats::time_kernel(|| {
                    typing::check_type(
                        &self.psi, 0, Layer::Prog, &empty, &stmt, &stmt_lvl, self.fuel,
                    )
                })
                .map_err(|e| ElabError::Kernel {
                    decl: decl.name.clone(),
                    span: decl.span,
                    err: e,
                    note: self.operator_fallback_note(),
                })?;
                stats::time_kernel(|| {
                    typing::check_term(
                        &self.psi, 0, Layer::Code, &empty, &term, &stmt, &stmt_lvl, self.fuel,
                    )
                })
                .map_err(|e| ElabError::Kernel {
                    decl: decl.name.clone(),
                    span: decl.span,
                    err: e,
                    note: self.operator_fallback_note(),
                })?;
                if let Some(g) = self.gate.as_ref() {
                    g.accepted(&self.psi, &item);
                }
            }
        }

        let params = Rc::new(
            decl.tyvars
                .iter()
                .map(|t| ParamMeta {
                    name: t.name.clone(),
                    implicit: true,
                    is_type: true,
                    is_self: false,
                    skel: None,
                    solver: None,
                })
                .chain(decl.params.iter().map(|p| ParamMeta {
                    name: p.name.clone(),
                    implicit: p.implicit,
                    is_type: false,
                    is_self: p.is_self,
                    // The parameter's own domain skeleton — what argument
                    // lambdas are checked against and what suppresses
                    // bare-reference insertion at this argument (§5.3/§6.1).
                    skel: skel_of_ty(&p.ty),
                    solver: p.solver.map(|_| Rc::new(p.ty.clone())),
                }))
                .collect::<Vec<_>>(),
        );
        // Both kinds bind a closed `Trm_c` global; the `fn` is the one that
        // keeps its body, so later declarations reference it as `u^δ` and
        // conversion δ-unfolds it at p when — and only when — running it is
        // what the comparison needs.
        //
        // A `theorem` stays opaque even though its proof is right here:
        // proofs are transported, never evaluated, and a transparent proof
        // would put the whole proof term back into every conversion that
        // mentions the theorem.
        let abs = self.psi.bindings.len() as u32;
        self.psi.push(GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(stmt),
            level: stmt_lvl,
            body: match decl.kind {
                DeclKind::Fn => Some(Rc::new(term)),
                DeclKind::Theorem => None,
            },
        });
        self.globals.insert(qkey(&self.scope.module, &decl.name), GlobalInfo { abs, params });
        self.add_name(&decl.name, NameKind::Global);
        if let Some((_, base)) = member {
            self.member_bases.insert(base.to_string());
        }
        self.refresh_delta_psi();
        Ok(())
    }

    // -- goals --------------------------------------------------------------

    /// Raise a goal for a hole, returning its occurrence `u^{id_Γ}`.
    fn new_goal(
        &self,
        cx: &Cx,
        name: Option<&str>,
        hint: Option<(&str, &str)>,
        ty: Type,
        level: Level,
        span: Span,
    ) -> R<Term> {
        if self.frozen.get() {
            return err(
                "a hole may not appear in an `on` right-hand side — give it its own `on`",
                span,
            );
        }
        let mut goals = self.goals.borrow_mut();
        let mut spans = self.goal_spans.borrow_mut();
        let k = match spans.get(&(span.start, span.end)) {
            // Re-elaboration of the same syntactic hole (motive synthesis,
            // `calc`'s cloned spine): the same goal, so long as it is the same
            // context — the occurrence's `id_Γ` is what the payload lands in.
            Some(&k) => {
                if goals[k].cx.gamma.entries.len() != cx.gamma.entries.len() {
                    return err("internal: a hole was re-elaborated in a different context", span);
                }
                k
            }
            None => {
                let k = goals.len();
                if k as u32 >= self.goal_base {
                    return err("internal: more goals than the pre-count reserved", span);
                }
                // A goal payload is a `Trm` entry, so a context *variable* base
                // would substitute a term for a `Ctx` binding (subst.rs).
                // Nothing can build one today; assert rather than discover it.
                debug_assert!(
                    matches!(cx.gamma.base, CtxBase::Nil),
                    "a goal context must be closed"
                );
                let name = match name {
                    Some(n) => {
                        if goals.iter().any(|g| g.name == n) {
                            return err(
                                format!(
                                    "hole `?{n}` is already used in this block; \
                                     each named hole is a distinct goal"
                                ),
                                span,
                            );
                        }
                        n.to_string()
                    }
                    // An anonymous hole takes the callee's parameter name,
                    // deduplicated with an ordinal (`bound`, `bound.1`, …);
                    // with no callee to name it after, a positional fallback.
                    None => {
                        let base = match hint {
                            Some((_, param)) => param.to_string(),
                            None => format!("g{}", k + 1),
                        };
                        let mut candidate = base.clone();
                        let mut ordinal = 0;
                        while goals.iter().any(|g| g.name == candidate) {
                            ordinal += 1;
                            candidate = format!("{base}.{ordinal}");
                        }
                        candidate
                    }
                };
                let origin =
                    hint.map(|(callee, param)| (callee.to_string(), param.to_string()));
                goals.push(Goal {
                    name,
                    cx: cx.clone(),
                    ty,
                    level,
                    span,
                    origin,
                    solution: None,
                });
                spans.insert((span.start, span.end), k);
                k
            }
        };
        Ok(Term::GlobalTm {
            var: GlobalVar(self.goal_base - 1 - k as u32),
            subst: LocalSubst::id(&cx.gamma),
        })
    }

    /// Run the block's `on` statements, then require that every goal is
    /// discharged.
    fn solve_goals(&self, ons: &[OnStmt], decl: &str) -> R<()> {
        // No new goals from here on: `on` right-hand sides are elaborated in
        // the goal world but their solutions are strengthened out of it.
        self.frozen.set(true);
        for on in ons {
            match &on.target {
                OnTarget::Name(name) => {
                    let (cx, ty, lvl) = {
                        let goals = self.goals.borrow();
                        let Some(g) = goals.iter().find(|g| g.name == *name) else {
                            let known: Vec<&str> =
                                goals.iter().map(|g| g.name.as_str()).collect();
                            return err(
                                if known.is_empty() {
                                    format!("no goal `?{name}` — this block raises none")
                                } else {
                                    format!(
                                        "no goal `?{name}` in this block; it raises: ?{}",
                                        known.join(", ?")
                                    )
                                },
                                on.span,
                            );
                        };
                        if g.solution.is_some() {
                            return err(format!("goal `?{name}` is discharged twice"), on.span);
                        }
                        (g.cx.clone(), g.ty.clone(), g.level.clone())
                    };
                    // In the goal's *own* context, not the one at the `on`.
                    let t = self.elab_check(&cx, &on.expr, &ty, &lvl)?;
                    let t = strengthen_global(&t, self.goal_base);
                    let mut goals = self.goals.borrow_mut();
                    let g = goals.iter_mut().find(|g| g.name == *name).expect("found above");
                    g.solution = Some(Rc::new(t));
                }
                // `on _: P := e;` — discharge *every* goal whose statement is
                // `P` (docs/sketches/surface-v2.md §2: one bound proof feeding
                // many sites). `P` is elaborated per goal, in that goal's own
                // context, since that is where its statement lives.
                OnTarget::Stmt(pat) => {
                    let psi = self.goal_psi();
                    let candidates: Vec<(usize, Cx, Type, Level)> = self
                        .goals
                        .borrow()
                        .iter()
                        .enumerate()
                        .filter(|(_, g)| g.solution.is_none())
                        .map(|(k, g)| (k, g.cx.clone(), g.ty.clone(), g.level.clone()))
                        .collect();
                    let mut matched = Vec::new();
                    for (k, cx, ty, lvl) in candidates {
                        // Not well-formed in this goal's context just means
                        // "not this goal" — a statement need not mention names
                        // every goal has.
                        let Ok((pat_ty, pat_lvl)) = self.elab_ty(&cx, pat) else {
                            continue;
                        };
                        if conv_type(&psi, &cx.gamma, Layer::Prog, &pat_ty, &ty, &pat_lvl, self.fuel)
                            .is_ok()
                        {
                            matched.push((k, cx, ty, lvl));
                        }
                    }
                    if matched.is_empty() {
                        return err(
                            "no outstanding goal has this statement".to_string(),
                            on.span,
                        );
                    }
                    for (k, cx, ty, lvl) in matched {
                        let t = self.elab_check(&cx, &on.expr, &ty, &lvl)?;
                        let t = strengthen_global(&t, self.goal_base);
                        self.goals.borrow_mut()[k].solution = Some(Rc::new(t));
                    }
                }
                // A `split` arm, consumed by the parser into an `Arm`
                // (docs/match-equation-split-design.md §6); one that reaches a
                // block's `ons` is a parse error, not an elaboration one.
                OnTarget::Ctor { ctor, .. } => {
                    return err(
                        format!("internal: `on {ctor}(…)` reached the elaborator"),
                        on.span,
                    )
                }
            }
        }
        let goals = self.goals.borrow();
        let unsolved: Vec<GoalReport> = goals
            .iter()
            .filter(|g| g.solution.is_none())
            .map(|g| GoalReport {
                name: g.name.clone(),
                statement: self.display_type(&g.cx, &g.ty),
                context: g
                    .cx
                    .names
                    .iter()
                    .zip(&g.cx.gamma.entries)
                    // `#`-prefixed binders are the elaborator's own (a `match`
                    // arm's hidden ih); they are unspellable, so listing them
                    // would only mislead.
                    .filter(|(n, _)| !n.starts_with('#'))
                    .map(|(n, e)| (n.clone(), self.display_type(&g.cx, &e.ty)))
                    .chain(
                        g.cx.aliases
                            .iter()
                            .map(|a| (a.name.clone(), self.display_type(&g.cx, &a.ty))),
                    )
                    .collect(),
                origin: g
                    .origin
                    .as_ref()
                    .map(|(callee, param)| format!("the `{param}` parameter of `{callee}`")),
                span: g.span,
            })
            .collect();
        if unsolved.is_empty() {
            Ok(())
        } else {
            Err(ElabError::UnsolvedGoals { decl: decl.to_string(), goals: unsolved })
        }
    }

    /// Ψ as the goal world sees it: the committed bindings, then one `Trm`
    /// binding per goal in creation order, padded out to `goal_base`. With
    /// `L = |Ψ| + goal_base`, `GlobalVar(v)` is `bindings[L - 1 - v]`, so goal
    /// `k` at `GlobalVar(goal_base - 1 - k)` lands immediately after the
    /// committed ones. Well-scoped precisely because goals are numbered in
    /// creation order: goal `k`'s statement can only mention goals before it.
    ///
    /// Needed only where the kernel must read a global's *statement* —
    /// conversion. Reduction reads a global's body instead, and a goal never
    /// has one, so the term path is served by the cheaper padded
    /// [`Self::delta_psi`] and goals still need no real binding for the rest
    /// of elaboration.
    fn goal_psi(&self) -> GlobalCtx {
        // Inside a `meta fn` (goals are refused there, so the two paddings
        // never combine): the meta binders, same reasoning as `oracle_psi`.
        {
            let mp = self.meta_pushed.borrow();
            if !mp.is_empty() {
                let mut bindings = (*self.psi.bindings).clone();
                bindings.extend(mp.iter().cloned());
                return GlobalCtx::new(bindings);
            }
        }
        // No goals in flight: Ψ itself already is the goal world, and
        // sharing its `Rc` beats rebuilding the list.
        if self.goal_base == 0 {
            return self.psi.clone();
        }
        let goals = self.goals.borrow();
        let mut bindings = (*self.psi.bindings).clone();
        for k in 0..self.goal_base as usize {
            bindings.push(match goals.get(k) {
                Some(g) => GlobalBinding::Tm {
                    ctx: g.cx.gamma.clone(),
                    layer: Layer::Code,
                    ty: Rc::new(g.ty.clone()),
                    level: g.level.clone(),
                    body: None,
                },
                // A reserved-but-unused slot (the pre-count is an upper
                // bound). Nothing refers to it.
                None => GlobalBinding::Tm {
                    ctx: LocalCtx::nil(),
                    layer: Layer::Code,
                    ty: Rc::new(Type::Nat),
                    level: Level::Zero,
                    body: None,
                },
            });
        }
        GlobalCtx::new(bindings)
    }

    /// The substitution discharging the whole goal block: `entries[k]` is the
    /// payload for goal `k` at `GlobalVar(goal_base - 1 - k)`, matching
    /// `apply_global`'s convention. Reserved-but-unused slots (the pre-count
    /// is an upper bound) get a payload nothing can reach.
    fn goal_subst(&self) -> GlobalSubst {
        let goals = self.goals.borrow();
        let entries = (0..self.goal_base as usize)
            .map(|k| {
                GlobalEntry::Tm(match goals.get(k).and_then(|g| g.solution.clone()) {
                    Some(t) => t,
                    None => Rc::new(Term::Zero),
                })
            })
            .collect();
        GlobalSubst { entries }
    }

    // -- types --------------------------------------------------------------

    /// Push a block's statements onto a **clone** of `cx` as aliases, and
    /// return the extended context.
    ///
    /// Shared by a declaration body and [`ExprKind::Block`]
    /// (docs/let-and-blocks-design.md §4.4), so the two cannot disagree about
    /// what a `let` means. A `let` is an inlined **alias** — the same doctrine
    /// as a `fn` definition — not a kernel binder, which is what makes a block
    /// in a `match` arm free: it perturbs no `Case`/`ElimNat` telescope and no
    /// motive, and its scope dies with the clone.
    fn elab_stmts(&self, cx: &Cx, stmts: &[Stmt]) -> R<Cx> {
        let mut cx = cx.clone();
        for stmt in stmts {
            // `let { unit, op } = m;` — each name aliased to its projection
            // (docs/surface-records.md §5). Sugar over `m.unit` / `m.op`, and
            // it shares their code: a partial pattern simply binds fewer.
            let (name, ty, expr) = match stmt {
                Stmt::Let { name, ty, expr, .. } => (name, ty, expr),
                Stmt::LetCode { span, .. } => {
                    return err(
                        "`let code` is meta-layer syntax: it binds code inside a \
                         `meta fn` body (docs/in-language-map-design.md §3)",
                        *span,
                    )
                }
                Stmt::LetRecord { fields, expr, span } => {
                    let (t, rty, _) = self.elab_infer(&cx, expr)?;
                    // `record_of_at`, not `record_of`: the right-hand side may
                    // have arrived through a `Nat -> Type` function value, and
                    // then its type is `El` of a β-redex rather than of a code
                    // (docs/record-type-values.md §4). Same reader as
                    // `resolve_dot`'s, so the same fallback.
                    let Some(ind) = self.record_of_at(&cx, &rty, *span) else {
                        return err(
                            "a `let { … }` pattern needs a record on the right",
                            *span,
                        );
                    };
                    let value = Rc::new(t);
                    for (f, fsp) in fields {
                        let Some(idx) = ind.field_index(f) else {
                            return err(
                                format!("`{}` has no field `{f}`", ind.name),
                                *fsp,
                            );
                        };
                        let (term, ty, level) = self.project_field(
                            &cx,
                            &ind,
                            &rty,
                            Rc::clone(&value),
                            idx,
                            *fsp,
                        )?;
                        cx.aliases.push(Rc::new(Alias {
                            // The projected field's skeleton travels onto
                            // the alias (docs/implicit-binders-design.md
                            // §3.1) — same source as `resolve_dot`'s.
                            skel: skel_of_ty(&ind.ctors[0].fields[idx].1),
                            name: f.clone(),
                            depth: cx.names.len(),
                            term: Rc::new(term),
                            ty,
                            level,
                        }));
                    }
                    continue;
                }
            };
            let annot = ty.clone();
            let (term, ty, level, skel) = match ty {
                Some(t) => {
                    let (ty, lvl) = self.elab_ty(&cx, t).map_err(|e| self.let_ty_hint(&cx, t, e))?;
                    // The annotation's skeleton is both the expected
                    // skeleton the RHS is checked at (§6.1's second site)
                    // and the alias's own (§3.1).
                    let skel = skel_of_ty(t);
                    let tm =
                        self.elab_check_skel(&cx, expr, &ty, &lvl, None, skel.as_deref())?;
                    (tm, ty, lvl, skel)
                }
                // The `let`-RHS harvest (docs/implicit-binders-design.md
                // §6.3): an implicit lambda infers here (all binders
                // annotated, as inference already requires) and the alias
                // records the skeleton read off the written marks.
                None => match &expr.kind {
                    ExprKind::Lam { binders, body } => {
                        let (tm, ty, lvl) = self.elab_lam_infer(&cx, binders, body, true)?;
                        (tm, ty, lvl, skel_of_lam_binders(binders))
                    }
                    _ => {
                        let (tm, ty, lvl) = self.elab_infer(&cx, expr)?;
                        (tm, ty, lvl, None)
                    }
                },
            };
            // A `let`-bound dictionary at a written index: the local-override
            // case of the value-slot ladder's step 2
            // (docs/operation-indexed-classes-design.md §5).
            if let Some(t) = &annot
                && let Some(r) = self.class_ref_of_ty(t)
                && !r.index.is_empty()
                && !r.args.is_empty()
            {
                cx.dicts.push(Rc::new(DictBinder {
                    name: name.clone(),
                    class: r.name,
                    carrier: r.args[0].clone(),
                    index: r.index,
                }));
            }
            cx.aliases.push(Rc::new(Alias {
                skel,
                name: name.clone(),
                depth: cx.names.len(),
                term: Rc::new(term),
                ty,
                level,
            }));
        }
        Ok(cx)
    }

    fn elab_ty(&self, cx: &Cx, ty: &Ty) -> R<(Type, Level)> {
        match &ty.kind {
            TyKind::Nat => Ok((Type::Nat, Level::Zero)),
            // `Type<n>` is the kernel's `Ty n`, itself a type at level `n + 1`
            // (`typing.rs:457-460`). This is the whole lowering
            // (docs/surface-universe.md §2).
            TyKind::Univ { level } => {
                Ok((Type::Ty(Level::constant(*level)), Level::constant(level + 1)))
            }
            // An expression in type position: infer it, require its type to be
            // a universe, and decode (docs/surface-universe.md §4). `El` is the
            // kernel's own decoding, so nothing here is a coercion — the term
            // *is* a code, and `El ⌜T⌝ ⇝ T` makes a written type and a decoded
            // one convertible rather than merely equal-looking.
            TyKind::OfExpr(e) => {
                // An operator in **type** position — `n <= m`, and `x + A.unit`
                // as an equation's endpoint. The symbol resolves to a name
                // here exactly as it does in a term
                // (docs/operators-onto-classes-design.md §4), and then every
                // reading below applies to what it named: `Le(n, m)` is the
                // record-at-its-value-parameters road it always was.
                if let Some(rewritten) = self.op_rewrite(cx, e, None)? {
                    let ty = Ty { kind: TyKind::OfExpr(Box::new(rewritten)), span: ty.span };
                    return self.elab_ty(cx, &ty);
                }
                // `Vec<A>(n)` — an indexed family applied to its index
                // (docs/inductive-indexed-lowering.md §2), delivered here by
                // the parser's applied-type-is-never-called backtracking.
                if let Some(r) = self.try_indexed_ty(cx, e, ty.span)? {
                    return Ok(r);
                }
                // `Converges(p, env, ir, vs)` — a record applied to its *value*
                // parameters (docs/surface-value-parameters.md §3). Same road,
                // same reason: the parser cannot tell formation from a call,
                // and only the declaration can.
                if let Some(r) = self.try_valparam_ty(cx, e, ty.span)? {
                    return Ok(r);
                }
                let (tm, tm_ty, _) = self.elab_infer(cx, e)?;
                let Type::Ty(level) = self.whnf(cx, &tm_ty, ty.span)? else {
                    return err(
                        "this is not a type: only an expression whose type is a \
                         universe (`Type<n>`) can be used where a type is expected",
                        ty.span,
                    );
                };
                Ok((Type::El { level: level.clone(), tm: Rc::new(tm) }, level))
            }
            TyKind::Named { name, args } => {
                // A `D<…>` type argument's lowering stores kernel types and
                // re-lowers in contexts with no skeleton slot, so a mark in
                // one has no consumer and is refused (§3.4).
                if let Some(a) = args.iter().find(|a| has_implicit_mark(a)) {
                    return err(IMPLICIT_MARK_REFUSED, a.span);
                }
                self.lower_named(cx, name, args, ty.span)
            }
            // `[T; n]` — the kernel's `Type::Vec` directly. A primitive
            // indexed type: no fording, no encoding
            // (docs/container-fields.md §2.1).
            TyKind::Vec { elem, len } => {
                // A `[T; n]` element type has no skeleton slot (§3.4).
                if has_implicit_mark(elem) {
                    return err(IMPLICIT_MARK_REFUSED, elem.span);
                }
                let (elem_t, level) = self.elab_ty(cx, elem)?;
                let len_t = self.elab_check(cx, len, &Type::Nat, &Level::Zero)?;
                Ok((
                    Type::Vec {
                        level: level.clone(),
                        elem: Rc::new(elem_t),
                        len: Rc::new(len_t),
                    },
                    level,
                ))
            }
            // `Fin(n)` — the kernel's `Type::Fin` directly
            // (docs/surface-fin-indexing-design.md §2.3). The level is
            // `Zero` **unconditionally**: `Fin` is the one extension former
            // that carries no level (`term.rs:153`), so there is no `Fin` at
            // level 1 to write and no way to ask for one.
            TyKind::Fin(len) => {
                let len_t = self.elab_check(cx, len, &Type::Nat, &Level::Zero)?;
                Ok((Type::Fin { len: Rc::new(len_t) }, Level::Zero))
            }
            // `(x: A) -> B` / `A -> B`. The level rule is `max(dom, cod)`,
            // the same one `elab_decl_inner` uses to close a declaration's
            // telescope — a written function type and a `fn`'s own type must
            // not compute levels differently
            // (docs/surface-function-types.md §5.1).
            TyKind::Fn { binder, dom, cod, .. } => {
                let (dom_t, dom_level) = self.elab_ty(cx, dom)?;
                let mut inner = cx.clone();
                // `#` marks an elaborator-introduced binder: unspellable, and
                // filtered out of the goal listing.
                let name = binder.clone().unwrap_or_else(|| "#arrow".to_string());
                // The binder pushed for the codomain carries the *domain's*
                // skeleton — this one line is what makes insertion work
                // inside any written dependent type: a statement
                // `(f: {A: Type<0>} -> A -> A) -> f(0) = 0` has `f`'s uses
                // in the codomain inferring with no further plumbing
                // (docs/implicit-binders-design.md §3.1).
                inner.push_skel(name.clone(), dom_t.clone(), dom_level.clone(), skel_of_ty(dom));
                // A binder at a universe is usable as a type in the codomain
                // (`(A: Type<0>) -> A -> A`) — the registration the telescope
                // loop and `elab_lam_check` make, at the third binding form.
                if let Type::Ty(level) = &dom_t {
                    inner.tyvars.push(TyVar {
                        name,
                        ty: Type::El {
                            level: level.clone(),
                            tm: Rc::new(Term::Var(LocalVar(0))),
                        },
                        level: level.clone(),
                        depth: inner.names.len(),
                    });
                }
                let (cod_t, cod_level) = self.elab_ty(&inner, cod)?;
                Ok((
                    Type::Pi {
                        dom_level: dom_level.clone(),
                        cod_level: cod_level.clone(),
                        dom: Rc::new(dom_t),
                        cod: Rc::new(cod_t),
                    },
                    Level::max(dom_level, cod_level),
                ))
            }
            // The modal types (docs/in-language-map-design.md §3): meaningful
            // only in a `meta fn` signature, which elaborates them itself
            // (`elab_meta_decl`) before this general path could see them.
            TyKind::Ctx | TyKind::TyCode { .. } | TyKind::Code { .. } => err(
                "`Ctx`/`TyCode`/`Code` are meta-layer types: they belong in a \
                 `meta fn` signature (docs/in-language-map-design.md §3)",
                ty.span,
            ),
            // `$a` for a `TyCode` binder: its global type variable, valid at
            // the code scope (a `meta fn` signature's payload types and quote
            // payloads — anywhere `cx.meta` is present).
            TyKind::Splice { name } => self.elab_ty_splice(cx, name, ty.span),
            TyKind::Eq(lhs, rhs) => {
                let (lhs_t, lhs_ty, lvl) = self.elab_infer(cx, lhs)?;
                let rhs_t = self.elab_check(cx, rhs, &lhs_ty, &lvl)?;
                Ok((
                    Type::Id {
                        level: lvl.clone(),
                        ty: Rc::new(lhs_ty),
                        lhs: Rc::new(lhs_t),
                        rhs: Rc::new(rhs_t),
                    },
                    lvl,
                ))
            }
        }
    }

    // -- terms --------------------------------------------------------------

    /// Checking mode. Structural only where the expected type is genuinely
    /// needed (`refl`, motive-less `match`); everything else infers, and
    /// the mismatch (if any) is caught by the kernel's final check of the
    /// declaration — the kernel converts at every application/eliminator
    /// premise, so errors cannot slip through, only be reported later.
    fn elab_check(&self, cx: &Cx, e: &Expr, expected: &Type, lvl: &Level) -> R<Term> {
        self.elab_check_hinted(cx, e, expected, lvl, None)
    }

    /// [`Self::elab_check`] plus, where the caller knows it, the `(callee,
    /// parameter)` this expression is an argument for — the provenance and
    /// default name of any goal raised inside it.
    fn elab_check_hinted(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
        lvl: &Level,
        hint: Option<(&str, &str)>,
    ) -> R<Term> {
        self.elab_check_skel(cx, e, expected, lvl, hint, None)
    }

    /// [`Self::elab_check_hinted`] plus, where the caller has one, the
    /// expected type's implicitness *skeleton*
    /// (docs/implicit-binders-design.md §6.1). Three caller classes supply
    /// it: argument checking in `apply_explicit`/`apply_implicit` (the
    /// callee parameter's own skeleton), an annotated `let`, and
    /// record-literal field checking. It is read by exactly two arms — a
    /// lambda (the §6.2 coherence rule) and the bare-reference suppression
    /// in the inference fallback (§5.3); everything else ignores it.
    fn elab_check_skel(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
        lvl: &Level,
        hint: Option<(&str, &str)>,
        skel: Option<&Skel>,
    ) -> R<Term> {
        // Checking position, so rung 2 has its second source: a bare symbol
        // resolves at the carrier this type's first domain names
        // (docs/bare-symbol-checking-carrier-design.md §3.1). The expected type
        // is already in hand one line above the rewrite, and has been since the
        // operators round — nothing is plumbed from a call site.
        if let Some(rewritten) = self.op_rewrite(cx, e, Some(expected))? {
            return self.elab_check_skel(cx, &rewritten, expected, lvl, hint, skel);
        }
        match &e.kind {
            // The expected type *is* the goal's statement, which is why holes
            // are checking-only (issues/goal-holes.md).
            ExprKind::Hole(name) => {
                self.new_goal(cx, name.as_deref(), hint, expected.clone(), lvl.clone(), e.span)
            }
            // **Rule 2** (docs/let-and-blocks-design.md §5.2): `refl` is a
            // *nullary* special form, so its node carries no name to
            // re-derive and the parser cannot buy the name back with a
            // lookahead — but the elaborator can, with exactly the guard
            // `Fin`, `absurd` and `inj` already use. Without it
            // `let refl = n; refl` elaborated the **use** as the form and
            // died at "`refl` needs an `=` expected type", one of the two
            // *silent* binder traps (§5.1). A down payment on
            // `issues/special-forms-as-declarations.md`, not a stopgap: when
            // `refl` becomes a declaration this arm is deleted and no program
            // changes behaviour.
            ExprKind::Refl if self.shadowed(cx, "refl") => self.elab_check_skel(
                cx,
                &Expr { kind: ExprKind::Var("refl".to_string()), span: e.span },
                expected,
                lvl,
                hint,
                skel,
            ),
            ExprKind::Refl => {
                let head = self.whnf(cx, expected, e.span)?;
                let Type::Id { level, ty, lhs, .. } = head else {
                    return err("`refl` needs an `=` expected type", e.span);
                };
                Ok(Term::Refl { level, ty, tm: lhs })
            }
            // `{}` — one speculative `refl`, kept iff the kernel accepts it
            // (issues/auto-refl-empty-block.md). The conversion is run *here*
            // rather than left to the declaration's final `check_term`,
            // because a guess that fails there would surface as a kernel error
            // about a term nobody wrote. A guess that fails here is an open
            // goal instead — the same object a `?` raises, so it is listed
            // with its statement and context and an `on` can still discharge
            // it.
            ExprKind::AutoRefl => {
                if let Ok(Type::Id { level, ty, lhs, rhs }) = self.whnf(cx, expected, e.span)
                    && conv_term(
                        &self.goal_psi(),
                        &cx.gamma,
                        Layer::Prog,
                        &lhs,
                        &rhs,
                        &ty,
                        &level,
                        self.fuel,
                    )
                    .is_ok()
                {
                    return Ok(Term::Refl { level, ty, tm: lhs });
                }
                self.new_goal(cx, None, hint, expected.clone(), lvl.clone(), e.span)
            }
            // `{ let x = e; … result }` — **checking**-transparent, which is
            // the property that makes the form useful: a block in a `match`
            // arm under a dependent motive is checked at the arm's type rather
            // than inferred and then converted
            // (docs/let-and-blocks-design.md §4.4). The hint travels with it,
            // so a hole in the result of a block in argument position still
            // reports the callee and parameter it belongs to.
            ExprKind::Block(b) => {
                let cx = self.elab_stmts(cx, &b.stmts)?;
                self.elab_check_skel(&cx, &b.result, expected, lvl, hint, skel)
            }
            // A quote against its `Code(g |- T)` type — checking-only, like
            // the kernel's `BoxTm` (docs/in-language-map-design.md §5).
            ExprKind::Quote(payload) => self.elab_quote(cx, payload, expected, e.span),
            ExprKind::Match { form, motive: None, scrut, arms, eqbind, generated } => {
                // Stage-2 motive synthesis (issues/elab-stage2-metas.md): when
                // the scrutinee is a local variable, abstract it out of the
                // expected type so the motive is genuinely dependent; otherwise
                // fall back to the non-dependent motive (expected under `z`).
                let (scrut_t, scrut_ty, scrut_lvl) = self.elab_infer(cx, scrut)?;
                let motive = self.synth_motive(cx, &scrut_t, &scrut_ty, &scrut_lvl, expected);
                let Some(h) = eqbind else {
                    return self.elab_match(
                        cx, *form, *generated, arms, scrut_t, &scrut_ty, &scrut_lvl, motive,
                        lvl.clone(), e.span,
                    );
                };
                self.elab_convoy(
                    cx, *form, *generated, h, arms, scrut_t, &scrut_ty, &scrut_lvl, motive, lvl,
                    expected, e.span,
                )
            }
            // `absurd(p)`: from an equation between distinct constructors,
            // anything — so it needs the expected type
            // (docs/inductive-tier0-lowering.md §6.1).
            ExprKind::App { .. }
                if matches!(e.as_named(), Some((n, _, _))
                            if n == "absurd" && !self.shadowed(cx, n)) =>
            {
                let (_, args, _) = e.as_named().expect("just checked");
                let [arg] = args else {
                    return err("`absurd` takes exactly one argument", e.span);
                };
                self.build_absurd(cx, arg, expected, lvl, e.span)
            }
            // A vector literal against an expected `Vec(T; k)`. Checking-only
            // like `refl`, and the length must be a *literal*: matching a
            // literal's own length against a neutral one is unification, not
            // a check (docs/container-fields.md §2.2).
            ExprKind::VecLit(elems) => self.elab_vec_lit(cx, elems, expected, e.span),
            // `FZ` / `FS(j)` against an expected `Fin`. Checking-only, like
            // `refl` and a vector literal: `FZ` inhabits `Fin(Succ k)` for
            // *every* `k`, and nothing in the term names one
            // (docs/surface-fin-indexing-design.md §3.1). Keyed on the
            // expected type and never on the name, so a user inductive with a
            // constructor called `FZ`/`FS` is untouched — hence the
            // `ctor_here` guard.
            ExprKind::Var(name)
                if name == "FZ"
                    && !self.shadowed(cx, name)
                    && self.ctor_here_expected(cx, name, expected).is_none() =>
            {
                self.elab_fin_index(cx, None, expected, e.span)
            }
            // `trivial` — the canonical inhabitant of `True`, i.e. the kernel's
            // `⟨⟩^l : Unit^l` (`issues/true-prop-trivial-hypotheses.md`). A
            // *bare* name and not a `True::intro` path, because bare is what
            // this surface already does for every inhabitant of a kernel type
            // with no declaration (`Zero`, `Succ`, `refl`, `FZ`/`FS`), and
            // because `A::b` is one lexer token whose owner is a module or an
            // applied obligation owner — `True` is neither.
            //
            // Checking takes the level from the expected type, so a `Unit` at
            // a level the surface cannot write is still inhabited by it; the
            // shadowing guards are `FZ`'s, so a user `trivial` wins.
            ExprKind::Var(name)
                if name == "trivial"
                    && !self.shadowed(cx, name)
                    && self.ctor_here_expected(cx, name, expected).is_none() =>
            {
                match self.whnf(cx, expected, e.span)? {
                    Type::Unit { level } => Ok(Term::Triv { level }),
                    _ => err(
                        format!(
                            "`trivial` proves `True`, but `{}` is expected here",
                            self.display_type(cx, expected)
                        ),
                        e.span,
                    ),
                }
            }
            ExprKind::App { args, .. }
                if matches!(e.as_named(), Some(("FS", _, false)))
                    && !self.shadowed(cx, "FS")
                    && self.ctor_here_expected(cx, "FS", expected).is_none() =>
            {
                let [j] = args.as_slice() else {
                    return err("`FS` takes exactly one argument, an index", e.span);
                };
                self.elab_fin_index(cx, Some(j), expected, e.span)
            }
            // A numeral at a `Fin` type is the iterated index (§3.3): `xs[2]`
            // is the spelling anybody reaches for first, and without this it
            // means `xs[FS(FS(FZ))]`. Falls through to the ordinary `Nat`
            // reading at every other expected type.
            ExprKind::Num(t) => self.elab_num_check(cx, *t, e, expected, e.span),
            // A lambda against an expected Π: the *expected* domain is what
            // the binder is pushed with, so the emitted annotation always
            // matches the type it is checked against. A written annotation is
            // a readability aid and must be convertible with it
            // (docs/surface-function-types.md §5.2).
            ExprKind::Lam { binders, body } => {
                self.elab_lam_check(cx, binders, body, expected, lvl, skel, e.span)
            }
            // A universe as the expected type: a *type* has been written where
            // a term is expected, so read it as one and quote it
            // (docs/surface-universe.md §4).
            _ if matches!(expected, Type::Ty(_)) => {
                self.elab_at_universe(cx, e, expected, e.span)
            }
            // A constructor in checking position: the expected type *is* the
            // encoding, so every annotation of the injection and the field
            // tuple is read off it (docs/inductive-tier0-lowering.md §4).
            // Unsaturated against an expected `Π`, it η-expands into a function
            // value (docs/constructor-function-values.md §2).
            // The name is read with the expected type as evidence
            // ([`Self::ctor_here_expected`]), so a bare constructor the name
            // layer left ambiguous is settled by the type that is checking it.
            ExprKind::Var(name) if self.ctor_here_expected(cx, name, expected).is_some() => {
                let (ind, i) =
                    self.ctor_here_expected(cx, name, expected).expect("just checked");
                self.build_ctor_value(cx, &ind, i, &[], expected, lvl, e.span)
            }
            ExprKind::App { .. } if self.ctor_spine_expected(cx, e, expected).is_some() => {
                let (ind, i, args) =
                    self.ctor_spine_expected(cx, e, expected).expect("just checked");
                self.build_ctor_value(cx, &ind, i, &args, expected, lvl, e.span)
            }
            // A record literal *is* a constructor application once its fields
            // are put in declaration order, so checking mode is the tier-0
            // constructor path — which is what lets the expected type supply
            // the instantiation and no annotation be written
            // (docs/surface-records.md §6).
            ExprKind::RecordLit { name, tyargs, fields } if tyargs.is_empty() => {
                let args = self.record_lit_args(name, fields, e.span)?;
                let Some(ind) = self.lookup_inductive(name).cloned() else {
                    return Err(self.name_miss(name, format!("unknown type `{name}`"), e.span));
                };
                self.build_ctor_value(cx, &ind, 0, &args, expected, lvl, e.span)
            }
            // `.f` resolution has to exist in *both* modes: a projection
            // synthesizes, but the method fallback may be checking-only
            // (`p.absurd()`), and routing it through inference would break it.
            ExprKind::Dot { recv, name, args } => {
                match self.resolve_dot(cx, recv, name, args, e.span)? {
                    DotResolution::Project(t, ty, l, fskel) => match args {
                        // A bare skeletal projection in checking position:
                        // the §5.2 route with the field's skeleton, under the
                        // same two suppressions the `Var` arm composes — the
                        // expected skeleton's leading implicit (§5.3) and the
                        // erased universe-domain check.
                        None => {
                            if let Some(fskel) = &fskel {
                                let prefix = fskel.leading_implicit();
                                let suppress = skel
                                    .is_some_and(|s| s.params.first().is_some_and(|b| b.implicit))
                                    || matches!(
                                        self.whnf(cx, expected, e.span)?,
                                        Type::Pi { dom, .. } if matches!(*dom, Type::Ty(_))
                                    );
                                if prefix > 0 && !suppress {
                                    let mask = vec![true; prefix];
                                    let (t, _, _) = self.apply_implicit(
                                        cx,
                                        name,
                                        skel_params(fskel),
                                        true,
                                        0,
                                        true,
                                        t,
                                        ty,
                                        l,
                                        &[],
                                        &mask,
                                        Some(expected),
                                        e.span,
                                    )?;
                                    return Ok(t);
                                }
                            }
                            Ok(t)
                        }
                        Some(args) => {
                            let (t, _, _) = self.apply_projection(
                                cx,
                                name,
                                t,
                                ty,
                                l,
                                fskel,
                                args,
                                Some(expected),
                                e.span,
                            )?;
                            Ok(t)
                        }
                    },
                    // Dispatch is a projection with its own arguments, so it
                    // takes the applied route unconditionally — there is no
                    // bare form (§4 rule 7).
                    DotResolution::Dispatch(t, ty, l, fskel, dargs) => {
                        let (t, _, _) = self.apply_projection(
                            cx,
                            name,
                            t,
                            ty,
                            l,
                            fskel,
                            &dargs,
                            Some(expected),
                            e.span,
                        )?;
                        Ok(t)
                    }
                    DotResolution::Method(m) => {
                        self.elab_check_skel(cx, &m, expected, lvl, hint, skel)
                    }
                }
            }
            _ => {
                // The universe arm above matches a *syntactic* `Ty`, but a
                // universe can hide under `El` of a quoted code — an indexed
                // family's field components arrive exactly so
                // (docs/inductive-indexed-lowering.md §4: the branch spine is
                // quoted and decoded, so a `Type`-valued field reads back as
                // `El (TmTy …)`). Reduce before giving up on the
                // type-position reading; `elab_at_universe` still falls
                // through to ordinary inference when the expression is not a
                // type by shape.
                let head = self.whnf(cx, expected, e.span)?;
                if matches!(head, Type::Ty(_)) {
                    return self.elab_at_universe(cx, e, &head, e.span);
                }
                // Inference is the fallback, but the expected type is *not*
                // discarded on the way: an implicit-inserting call (or a bare
                // reference to a polymorphic declaration) with something
                // still unsolved consults it — the anti-unification hook and
                // the general expected-type harvest both live behind this
                // line (issues/congruence-by-anti-unification.md decision 7;
                // docs/unifier-completeness-design.md §5). Nothing else reads
                // the hint, so every other expression elaborates exactly as
                // before.
                //
                // The §5.3 suppression rule (docs/implicit-binders-design.md):
                // a *bare reference* met where the expected type's own
                // skeleton opens with an implicit binder is passed verbatim —
                // the parameter asked for the implicit function itself, and
                // instantiating it here could only mis-teach (the probe-5
                // regression, one level up). Withholding the expected type is
                // exactly verbatim resolution: the bare-reference routes run
                // only in checking position. This composes with the
                // erased-type universe check inside the `Var` arm
                // (issues/elab-unifier-completeness.md, 2026-08-06), which
                // stays as the fallback for skeleton-less expected types.
                let suppress = matches!(&e.kind, ExprKind::Var(_))
                    && skel.is_some_and(|s| s.params.first().is_some_and(|b| b.implicit));
                let (t, _, _) =
                    self.elab_infer_at(cx, e, if suppress { None } else { Some(&head) })?;
                Ok(t)
            }
        }
    }

    /// An expression in a position whose expected type is a universe — a
    /// *type* written where a term is expected. Read it as a type, elaborate
    /// it, and quote it into its code (docs/surface-universe.md §4).
    ///
    /// This restores the coercion `docs/surface-polymorphism.md` §5 retired.
    /// The retirement was right *then*: `<…>`/`@` between them left no position
    /// with expected type `Ty l`, so the arm was dead code and a message was
    /// all it could be. A `Type`-valued binder creates the position for a real
    /// reason — it is stated by a declaration rather than conjured by a
    /// spelling — so the coercion has a customer again.
    /// The bridge is **not** a claim that every expression here is a type: a
    /// universe is an ordinary type, so `g(A)` and a variable at `Ty n` reach
    /// this position too. Only a reading that succeeds *as a type* is taken;
    /// anything else falls through to ordinary inference, which is what the
    /// position meant before universes were writable.
    fn elab_at_universe(&self, cx: &Cx, e: &Expr, expected: &Type, span: Span) -> R<Term> {
        if let Type::Ty(want) = expected {
            // `Boxed(v)` at `Type`: a declared type applied to its value
            // arguments, written where a *term* is expected
            // (docs/record-type-values.md). This is the only reading that can
            // be well-typed — no constructor inhabits a universe — so it is
            // **committed**: an error here is reported, not retried as a call,
            // which is what keeps the arity diagnostic pointed at the value
            // parameter telescope instead of at the constructor.
            if let Some(ty) = self.type_former_app(cx, e)? {
                let (elaborated, level) = self.elab_ty(cx, &ty)?;
                return self.quote_type_at(&elaborated, &level, want, span);
            }
            if let Some(ty) = expr_as_ty(e)
                && let Ok((elaborated, level)) = self.elab_ty(cx, &ty)
            {
                return self.quote_type_at(&elaborated, &level, want, span);
            }
        }
        let (t, _, _) = self.elab_infer(cx, e)?;
        Ok(t)
    }

    /// A lowered type quoted into its code at the universe that was expected.
    fn quote_type_at(
        &self,
        elaborated: &Type,
        level: &Level,
        want: &Level,
        span: Span,
    ) -> R<Term> {
        // Non-cumulative: levels compare by `≈`, never `≤`, and there
        // is no lift (docs/surface-universe.md §6).
        if !level.equiv(want) {
            return err(
                format!(
                    "this type is at level {}, but a `Type<{}>` is expected \
                     here — universes in this system are non-cumulative, so a \
                     type does not also inhabit the universes above its own, \
                     and there is no lift",
                    show_level(level),
                    show_level(want),
                ),
                span,
            );
        }
        // `El` is the identity on codes (`code.rs`), so a `Type`-valued
        // binder quotes back to the variable itself.
        match code::code_of(elaborated) {
            Some(code) => Ok(code),
            None => err(
                "this type has no code, so it cannot be written where a term is \
                 expected (docs/surface-universe.md §7)",
                span,
            ),
        }
    }

    /// `D<ā>(v̄)` in **expression** position, where `D` is a declared record or
    /// inductive: the applied *type former*, read as the type-position
    /// [`TyKind::OfExpr`] it would be one syntactic slot over. There is no
    /// second lowering here — `elab_ty` runs `try_indexed_ty` /
    /// `try_valparam_ty` / the generic decode exactly as it does for a type
    /// annotation (docs/record-type-values.md §2).
    ///
    /// `None` for anything that is not a declared type's name, and for a name a
    /// local binder or global shadows, so every existing spelling reaches its
    /// old handler. The one case answered here rather than deferred is a
    /// declaration with *no* value parameters and no index: `OfExpr`'s generic
    /// path would try to *call* it and report the constructor's problem, which
    /// is the misdirected diagnostic this round exists to remove.
    fn type_former_app(&self, cx: &Cx, e: &Expr) -> R<Option<Ty>> {
        let ExprKind::App { head, args, .. } = &e.kind else { return Ok(None) };
        let Some((name, _)) = inductive::named_head(head) else { return Ok(None) };
        if self.shadowed(cx, name) {
            return Ok(None);
        }
        let Some(ind) = self.lookup_inductive(name) else { return Ok(None) };
        // A non-empty telescope (and an index) reach their own handlers inside
        // `elab_ty`, and those already diagnose arity against the declaration.
        // An *empty* telescope has no handler there — `try_valparam_ty`
        // declines — so the mismatch is said here rather than left to
        // `OfExpr`'s generic path, which would try to call `D`.
        if ind.index.is_none() && ind.valparams.is_empty() {
            return err(
                format!(
                    "`{name}` takes 0 value argument(s), found {} — where a `Type` is \
                     expected, `{name}` names the type itself, so write it bare",
                    args.len()
                ),
                e.span,
            );
        }
        Ok(Some(Ty { kind: TyKind::OfExpr(Box::new(e.clone())), span: e.span }))
    }

    /// Inference mode: returns the elaborated term with its canonical type
    /// and level.
    fn elab_infer(&self, cx: &Cx, e: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer_at(cx, e, None)
    }

    /// [`Self::elab_infer`] plus, when the caller is in **checking** position
    /// and inference is the fallback, the expected type it would otherwise
    /// discard (already whnf'd).
    ///
    /// One consumer: [`Self::apply_implicit`], which uses it to solve
    /// implicits that no argument's type mentions — the congruence rule of
    /// `issues/congruence-by-anti-unification.md`, whose whole premise is
    /// that the information is in the expected type and nowhere else. Every
    /// other arm ignores it; inference stays inference, and this is a hint
    /// for one hook rather than a second checking mode.
    fn elab_infer_at(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: Option<&Type>,
    ) -> R<(Term, Type, Level)> {
        // An operator symbol resolves to a name *first*, and then this whole
        // function is the path the written name already took
        // (docs/operators-onto-classes-design.md §4).
        //
        // `None`, deliberately, and not this function's `expected`: that one is
        // the expected type of a *call's result*, reached only from
        // `elab_check_skel`'s inference fallback — i.e. only after the rewrite
        // at the top of `elab_check_skel` has already run. A symbol arrives
        // here unrewritten exactly when the position is genuinely inference,
        // which is the whole of what "a bare symbol has no carrier" still means
        // (docs/bare-symbol-checking-carrier-design.md §5).
        if let Some(rewritten) = self.op_rewrite(cx, e, None)? {
            return self.elab_infer_at(cx, &rewritten, expected);
        }
        match &e.kind {
            // `{ let x = e; … result }` — the block's statements extend a
            // clone of `cx`, and its result is inferred there
            // (docs/let-and-blocks-design.md §4.4). Inference-transparent:
            // the block contributes no term of its own, because a `let` is an
            // alias.
            ExprKind::Block(b) => {
                let cx = self.elab_stmts(cx, &b.stmts)?;
                self.elab_infer(&cx, &b.result)
            }
            // `a = b` as a term: it is a *type*, so the term is its code
            // `TmId : Ty l` (docs/surface-universe.md §13). Elaborated through
            // the type path so the two spellings cannot diverge.
            ExprKind::Eq(..) | ExprKind::TyLit(..) => {
                let ty = expr_as_ty(e).expect("an equation reads as a type");
                let (t, level) = self.elab_ty(cx, &ty)?;
                match code::code_of(&t) {
                    Some(code) => Ok((code, Type::Ty(level.clone()), Level::succ(level))),
                    None => err("this equation has no code", e.span),
                }
            }
            // Intensional analysis: the result type is written, so unlike a
            // quote this one *infers*
            // (docs/certgen-transcriber-in-language-design.md §3).
            ExprKind::MatchCode { scrut, motive, arms } => {
                self.elab_match_code(cx, scrut, motive, arms, e.span)
            }
            // `Type<n>` as a term is the code `TmTy(n) : Ty (n+1)`
            // (`typing.rs:756-759`) — it infers, so it needs no bridge.
            ExprKind::Univ { level } => Ok((
                Term::TmTy(Level::constant(*level)),
                Type::Ty(Level::constant(level + 1)),
                Level::constant(level + 2),
            )),
            // A goal is its statement; with nothing to check against there is
            // no statement to defer, so holes are checking-only (like `refl`).
            ExprKind::Hole(_) => err(
                "a hole here has no expected type — annotate it (`let p: T = ?;`) \
                 or write the call fully explicitly (`@f(a, b, ?p)`)",
                e.span,
            ),
            ExprKind::Num(n) => {
                let mut t = Term::Zero;
                for _ in 0..*n {
                    t = Term::Succ(Rc::new(t));
                }
                Ok((t, Type::Nat, Level::Zero))
            }
            // `FZ` cannot infer: it inhabits `Fin(Succ k)` for every `k`
            // (docs/surface-fin-indexing-design.md §3.1). Said only where the
            // name is neither shadowed nor some declaration's constructor.
            ExprKind::Var(name)
                if name == "FZ"
                    && !self.shadowed(cx, name)
                    && self.ctor_here(cx, name).is_none() =>
            {
                err(
                    "`FZ` needs an expected `Fin` type (checking position, or an \
                     annotated `let`)",
                    e.span,
                )
            }
            // `trivial` **infers**, unlike `FZ` and `refl`: the surface spells
            // exactly one `True` and it is `Unit^0`, so there is no level to
            // recover and nothing the expected type could tell this term
            // (`issues/true-prop-trivial-hypotheses.md`).
            ExprKind::Var(name)
                if name == "trivial"
                    && !self.shadowed(cx, name)
                    && self.ctor_here(cx, name).is_none() =>
            {
                Ok((
                    Term::Triv { level: Level::Zero },
                    Type::Unit { level: Level::Zero },
                    Level::Zero,
                ))
            }
            // A bare reference to a polymorphic declaration, met in
            // *checking* position, is the zero-explicit-argument case of
            // expected-type-directed instantiation
            // (docs/unifier-completeness-design.md §5.3): `app1(id, n)` at
            // `app1(f: Nat -> Nat, n: Nat)` dies as a bare kernel
            // `LevelMismatch` without it, because the polymorphic value's
            // leading `Π (A : Ty 0)` fails the Π–Π `dom_level` comparison
            // before the domains are even looked at. Inference position is
            // unchanged: with nothing to solve from, the reference still
            // resolves to the polymorphic value verbatim.
            //
            // Insertion is *suppressed* when the expected type itself still
            // quantifies over a type (a Π with a universe domain): the
            // parameter asked for the polymorphic function, and instantiating
            // the reference's type parameters can only mis-teach — `El ?A ≟
            // Ty 0` "solves" `?A := ⌜Type 0⌝` and the kernel rejects a term
            // nobody wrote. Passing verbatim is exactly the pre-insertion
            // behavior, and the kernel judges it as before. This is the
            // erased-type approximation of the skeleton suppression rule
            // (docs/implicit-binders-design.md §5.3), which refines it once
            // implicitness travels with the type.
            ExprKind::Var(name) => {
                // Which bare-reference route (if either) is live: the global
                // one, or the value analog. Decided before the whnf so a
                // name with neither pays nothing.
                let global_prefix = if expected.is_some() {
                    self.bare_implicit_prefix(cx, name)
                } else {
                    None
                };
                let value_skel = if expected.is_some() && global_prefix.is_none() {
                    self.value_skel(cx, name).filter(|s| s.leading_implicit() > 0)
                } else {
                    None
                };
                if let Some(expected) = expected
                    && (global_prefix.is_some() || value_skel.is_some())
                    && !matches!(
                        self.whnf(cx, expected, e.span)?,
                        Type::Pi { dom, .. } if matches!(*dom, Type::Ty(_))
                    )
                {
                    if let Some(prefix) = global_prefix {
                        let (head, ty, lvl) = self.resolve(cx, name, e.span)?;
                        let mask = vec![true; prefix];
                        return self.apply_implicit(
                            cx,
                            name,
                            self.params_of(name),
                            false,
                            0,
                            true,
                            head,
                            ty,
                            lvl,
                            &[],
                            &mask,
                            Some(expected),
                            e.span,
                        );
                    }
                    // The value analog (docs/implicit-binders-design.md
                    // §5.2): a bare local/alias whose *skeleton* opens with
                    // an implicit prefix takes the same route, with the
                    // parameter table synthesized from the skeleton. The
                    // §5.3 skeleton suppression happens one level up (the
                    // checking fallback withholds `expected`), so reaching
                    // here means insertion is wanted.
                    if let Some(skel) = value_skel {
                        let prefix = skel.leading_implicit();
                        let (head, ty, lvl) = self.resolve(cx, name, e.span)?;
                        let mask = vec![true; prefix];
                        return self.apply_implicit(
                            cx,
                            name,
                            skel_params(&skel),
                            true,
                            0,
                            true,
                            head,
                            ty,
                            lvl,
                            &[],
                            &mask,
                            Some(expected),
                            e.span,
                        );
                    }
                }
                self.resolve(cx, name, e.span)
            }
            // `xs[i]` — infers, since the element type comes off the receiver
            // (docs/surface-fin-indexing-design.md §5.2).
            ExprKind::Index { recv, idx } => self.elab_vec_nth(cx, recv, idx, e.span),
            ExprKind::Dot { recv, name, args } => {
                match self.resolve_dot(cx, recv, name, args, e.span)? {
                    DotResolution::Project(t, ty, l, fskel) => match args {
                        None => Ok((t, ty, l)),
                        Some(args) => {
                            self.apply_projection(cx, name, t, ty, l, fskel, args, expected, e.span)
                        }
                    },
                    DotResolution::Dispatch(t, ty, l, fskel, dargs) => {
                        self.apply_projection(cx, name, t, ty, l, fskel, &dargs, expected, e.span)
                    }
                    DotResolution::Method(m) => self.elab_infer_at(cx, &m, expected),
                }
            }
            // A record literal in inference position: the fields are permuted
            // into declaration order and the instantiation is recovered from
            // them, exactly as for any constructor application
            // (docs/inductive-tier0-lowering.md §2).
            ExprKind::RecordLit { name, tyargs, fields } => {
                let args = self.record_lit_args(name, fields, e.span)?;
                let Some(ind) = self.lookup_inductive(name).cloned() else {
                    return Err(self.name_miss(name, format!("unknown type `{name}`"), e.span));
                };
                if tyargs.is_empty() {
                    self.infer_ctor(cx, &ind, 0, &args, e.span)
                } else {
                    let head = Expr { kind: ExprKind::Var(name.clone()), span: e.span };
                    self.ctor_at(cx, &head, tyargs, &args, e.span).unwrap_or_else(|| {
                        err(format!("unknown type `{name}`"), e.span)
                    })
                }
            }
            ExprKind::VecLit(_) => err(
                "a vector literal needs an expected type (it is checking-only, like \
                 `refl`): annotate it (`let xs: [T; 2] = [a, b];`) or use it as an \
                 argument",
                e.span,
            ),
            // A lambda in inference position needs every binder annotated:
            // with no expected type there is nothing else to take the domain
            // from (docs/surface-function-types.md §5.2).
            ExprKind::Lam { binders, body } => self.elab_lam_infer(cx, binders, body, false),
            // `f<T, …>` — explicit type application, with or without a call
            // after it (docs/surface-polymorphism.md §1).
            ExprKind::TyApp { head, args } => {
                if let Some(r) = self.ctor_at(cx, head, args, &[], e.span) {
                    return r;
                }
                let (name, t, ty, lvl, mask) = self.elab_ty_app(cx, head, args, e.span)?;
                // `f<A, B>` with nothing after it, where the parameters that
                // follow the type arguments start with a **solver** parameter:
                // the bare-reference route of
                // docs/unifier-completeness-design.md §5.3, one step along.
                // This is what makes an instance's assembled value work at
                // layer 2 — `op<A, B>` is the member with its `requires`
                // binders still to fill, and filling them is resolution's job
                // (docs/traits-layer2-design.md §9.3).
                //
                // Deliberately narrow: only a leading prefix that *contains a
                // solver parameter* takes it, so no call that elaborated
                // before this round changes shape.
                let params = self.params_of(&name);
                let prefix = mask.iter().take_while(|&&b| b).count();
                let solver_here = (0..prefix)
                    .any(|k| params.get(args.len() + k).is_some_and(|p| p.solver.is_some()));
                if expected.is_some() && solver_here {
                    return self.apply_implicit(
                        cx,
                        &name,
                        Rc::clone(&params),
                        false,
                        args.len(),
                        true,
                        t,
                        ty,
                        lvl,
                        &[],
                        &mask[..prefix],
                        expected,
                        e.span,
                    );
                }
                Ok((t, ty, lvl))
            }
            // `f<T, …>(a, b)` and `@f<T, …>(a, b)`. The type arguments are
            // applied first; what happens to the remaining `{}`-implicits is
            // `@`'s business and not `<…>`'s — the two are orthogonal knobs
            // (issues/at-and-type-arguments.md).
            ExprKind::App { head, args, explicit }
                if matches!(head.kind, ExprKind::TyApp { .. }) =>
            {
                let ExprKind::TyApp { head: callee, args: tyargs } = &head.kind else {
                    unreachable!("just matched")
                };
                // `Cons<Nat>(1, xs)` — a constructor at a written
                // instantiation. Not a Π-typed head, so it cannot go down the
                // application path at all; the type arguments *are* the
                // instantiation, which is what `infer_ctor` otherwise has to
                // guess (docs/surface-polymorphism.md §10.3).
                if let Some(r) = self.ctor_at(cx, callee, tyargs, args, e.span) {
                    return r;
                }
                // `map<A, B>(f, tail)` — the recursive call *with its type
                // arguments written* (issues/recursive-self-call-type-arguments.md).
                // The self-name is not a global yet, so `elab_ty_app` would
                // report that the declaration takes no type arguments, of a
                // declaration that visibly takes some.
                if let ExprKind::Var(n) = &callee.kind
                    && cx.selfref.as_ref().is_some_and(|s| s.name == *n)
                {
                    self.check_self_tyargs(cx, tyargs, head.span)?;
                    return self.elab_self_call(cx, args, *explicit, e.span);
                }
                let (name, t, ty, lvl, mask) =
                    self.elab_ty_app(cx, callee, tyargs, head.span)?;
                if !*explicit && mask.iter().any(|&b| b) {
                    self.apply_implicit(
                        cx,
                        &name,
                        self.params_of(&name),
                        false,
                        tyargs.len(),
                        false,
                        t,
                        ty,
                        lvl,
                        args,
                        &mask,
                        expected,
                        e.span,
                    )
                } else {
                    // The type arguments have consumed the leading parameters,
                    // so argument `i` is now parameter `i + |tyargs|` — which
                    // is what the offset keeps honest for goal-name hints.
                    self.apply_explicit(
                        cx,
                        Some(&name),
                        self.params_of(&name),
                        tyargs.len(),
                        t,
                        ty,
                        lvl,
                        args,
                    )
                }
            }
            // A constructor applied in the curried spelling — `Cons(1)(xs)`.
            // Re-associated into one saturated application, which is what lets
            // it infer: the head alone (`Cons(1)`) has no inferable type, but
            // the whole spine does (docs/constructor-function-values.md §3).
            ExprKind::App { .. } if e.as_named().is_none() && self.ctor_spine(cx, e).is_some() => {
                let (ind, i, args) = self.ctor_spine(cx, e).expect("just checked");
                self.infer_ctor(cx, &ind, i, &args, e.span)
            }
            // An application whose head is *not* a name: no parameter
            // metadata exists for it, so it is always explicit.
            ExprKind::App { head, args, explicit } if e.as_named().is_none() => {
                if *explicit {
                    return err(
                        "`@` suppresses implicit-argument insertion, which only applies \
                         to a named callee",
                        e.span,
                    );
                }
                let (h, hty, hlvl) = self.elab_infer(cx, head)?;
                self.apply_explicit(cx, None, Rc::new(Vec::new()), 0, h, hty, hlvl, args)
            }
            ExprKind::App { args, explicit, .. } => {
                let (name, _, _) = e.as_named().expect("head is a name");
                let name = &name.to_string();
                // `Nat::Monoid(add)` — a class at a type, at its index
                // (docs/operation-indexed-classes-design.md §5.1). Before the
                // ordinary application path, because an indexed class's
                // qualified name is not a callable global: `Bool::Monoid#or`
                // is, and this is what names it.
                if !self.shadowed(cx, name)
                    && name.contains("::")
                    && let Some(r) = self.class_at_type(cx, name, args, e.span)
                {
                    return r;
                }
                if name == "Succ" {
                    let [arg] = args.as_slice() else {
                        return err("`Succ` takes exactly one argument", e.span);
                    };
                    let arg = self.elab_check(cx, arg, &Type::Nat, &Level::Zero)?;
                    return Ok((Term::Succ(Rc::new(arg)), Type::Nat, Level::Zero));
                }
                // `Fin(n)` where a *term* is expected: the type's code,
                // `TmFin n : Ty 0` — which is what makes
                // `fn Idx(n: Nat) -> Type { Fin(n) }` an ordinary `fn`
                // (docs/surface-fin-indexing-design.md §2.3). Guarded by
                // shadowing, so a local binder or a global still wins *in
                // expression position*, as for `map`/`head`/`cons`; type
                // position is unguarded, and that asymmetry is deliberate.
                if name == "Fin" && !self.shadowed(cx, name) {
                    let [arg] = args.as_slice() else {
                        return err(
                            "`Fin` takes exactly one argument, a length at `Nat`",
                            e.span,
                        );
                    };
                    let len = self.elab_check(cx, arg, &Type::Nat, &Level::Zero)?;
                    return Ok((
                        Term::TmFin { len: Rc::new(len) },
                        Type::Ty(Level::Zero),
                        Level::constant(1),
                    ));
                }
                // `FS(j)` is checking-only, like `refl` and a vector literal:
                // it inhabits `Fin(Succ k)` for every `k`, and nothing in the
                // term names one (§3.1). Said only where `FS` is not some
                // other declaration's constructor and is not shadowed, so a
                // user `FS` still resolves.
                if name == "FS"
                    && !self.shadowed(cx, name)
                    && self.ctor_here(cx, name).is_none()
                {
                    return err(
                        "`FS` needs an expected `Fin` type (checking position, or an \
                         annotated `let`)",
                        e.span,
                    );
                }
                // `xs.map(f)` / `xs.fold(z, f)` — the vector eliminators
                // (docs/container-fields.md §4.2). These are Rust rather than
                // declarations, so they have no `self` to write and take the
                // default subject position: the receiver arrives *first*, as
                // `map(xs, f)` and `fold(xs, z, f)`, which is also how the
                // direct spelling reads best
                // (issues/method-receiver-position.md).
                if name == "map" && !self.shadowed(cx, name) {
                    let [xs, f] = args.as_slice() else {
                        return self.vec_method_arity_err(cx, args, name, "`(f)`", e.span);
                    };
                    return self.elab_vec_map(cx, f, xs, e.span);
                }
                // `head(v)` / `tail(v)` / `cons(h, t)` — the vector at a
                // successor length *is* a `Σ` (`Vec` computes on its length),
                // so these are its projections and pairing, annotated from
                // the receiver's element type (docs/in-language-map-design.md
                // — the payload of the first in-language artifact is what
                // wanted spellings for them).
                if (name == "head" || name == "tail") && !self.shadowed(cx, name) {
                    let [v] = args.as_slice() else {
                        return self.vec_method_arity_err(cx, args, name, "no arguments", e.span);
                    };
                    return self.elab_vec_head_tail(cx, v, name == "head", e.span);
                }
                if name == "cons" && !self.shadowed(cx, name) {
                    let [h, t] = args.as_slice() else {
                        return err("`cons` takes `(head, tail)`", e.span);
                    };
                    return self.elab_vec_cons(cx, h, t, e.span);
                }
                // `xs.cong(self)` — the phase-3 lifting
                // (docs/container-proofs.md §6). Recognized by its *self-name*
                // argument rather than by the name `cong`, so a user-defined
                // `cong` theorem still resolves for the ordinary `p.cong(f)`:
                // the self-name is not a value, so it can never be an argument
                // to one (issues/match-recursion.md).
                if name == "cong"
                    && let [xs, f] = args.as_slice()
                    && let ExprKind::Var(f_name) = &f.kind
                    && cx.selfref.as_ref().is_some_and(|s| s.name == *f_name)
                {
                    let (xs_t, xs_ty, _) = self.elab_infer(cx, xs)?;
                    // Decoded, as in `elab_vec_map`: a coded `Vec` is one.
                    if !matches!(*crate::inductive::decoded(&xs_ty), Type::Vec { .. }) {
                        return err("`cong`'s receiver has to be a vector", e.span);
                    }
                    return self.elab_container_ih(cx, f_name, &xs_t, true, e.span);
                }
                if name == "fold" && !self.shadowed(cx, name) {
                    let [xs, z, f] = args.as_slice() else {
                        return self.vec_method_arity_err(cx, args, name, "`(init, f)`", e.span);
                    };
                    return self.elab_vec_fold(cx, z, f, xs, e.span);
                }
                // `inj(p)` / `inj(p, k)`: the field equations of an equation
                // between the same constructor (§6.2). The field index is a
                // literal, so `p.inj(1)` reads as the second field's equation.
                // The proof comes first in the direct spelling too, so the two
                // spellings are one order rather than two
                // (issues/method-receiver-position.md).
                if name == "inj" && !self.shadowed(cx, name) {
                    let (k, arg) = match args.as_slice() {
                        [arg] => (0, arg),
                        [arg, k] => match k.kind {
                            ExprKind::Num(k) => (k as usize, arg),
                            _ => return err("`inj`'s field index must be a numeral", k.span),
                        },
                        _ => return err("`inj` takes `(proof)` or `(proof, field)`", e.span),
                    };
                    return self.build_inj(cx, k, arg, e.span);
                }
                if name == "absurd" && !self.shadowed(cx, name) {
                    return err(
                        "`absurd` needs an expected type: use it in checking position \
                         (a `theorem` body, an annotated `let`, or an argument)",
                        e.span,
                    );
                }
                if let Some((ind, i)) = self.ctor_here(cx, name) {
                    return self.infer_ctor(cx, &ind, i, args, e.span);
                }
                if cx.selfref.as_ref().is_some_and(|s| s.name == *name) {
                    return self.elab_self_call(cx, args, *explicit, e.span);
                }
                // A *value* head — a local, or an alias. With a skeleton it
                // applies with skeleton-directed insertion
                // (docs/implicit-binders-design.md §5.1): same machinery as
                // a named global, with the parameter table synthesized from
                // the skeleton and `param_offset = 0` (a value has no
                // consumed type-argument prefix). `@f(…)` clears the whole
                // mask (§7.1): a value has no `f<…>` spelling, so narrowing
                // to type parameters would leave no complete escape.
                // Without one it is today's explicit application — and never
                // a same-named *global*'s mask or hint table, which is the
                // §4.2 params-passed-not-recovered rule (a local `f` must
                // not borrow a global `f`'s metadata).
                if cx.names.iter().any(|n| n == name)
                    || cx.aliases.iter().any(|a| a.name == *name)
                {
                    let (head, ty, lvl) = self.resolve(cx, name, e.span)?;
                    let skel = self.value_skel(cx, name);
                    let params = skel.as_deref().map_or_else(|| Rc::new(Vec::new()), skel_params);
                    let implicit = skel
                        .as_deref()
                        .filter(|s| !*explicit && s.params.iter().any(|b| b.implicit));
                    let Some(skel) = implicit else {
                        return self.apply_explicit(
                            cx, Some(name), params, 0, head, ty, lvl, args,
                        );
                    };
                    let mask: Vec<bool> = skel.params.iter().map(|b| b.implicit).collect();
                    return self.apply_implicit(
                        cx, name, params, true, 0, false, head, ty, lvl, args, &mask,
                        expected, e.span,
                    );
                }
                let mask = self.implicit_mask(name);
                let (head, ty, lvl) = self.resolve(cx, name, e.span)?;
                // `@f(…)` makes the **value** implicits positional and leaves
                // the *type* parameters inferred; `f<T, …>(…)` is the knob for
                // those, and the two compose
                // (issues/at-and-type-arguments.md). So `@` narrows the mask
                // rather than clearing it: without that, adding `<A>` to a
                // declaration would break every `@`-call to it, at the call
                // sites rather than at the declaration.
                let mask = if *explicit {
                    self.params_of(name)
                        .iter()
                        .map(|p| p.implicit && p.is_type)
                        .collect()
                } else {
                    mask
                };
                if !mask.iter().any(|&b| b) {
                    self.apply_explicit(
                        cx, Some(name), self.params_of(name), 0, head, ty, lvl, args,
                    )
                } else {
                    self.apply_implicit(
                        cx,
                        name,
                        self.params_of(name),
                        false,
                        0,
                        false,
                        head,
                        ty,
                        lvl,
                        args,
                        &mask,
                        expected,
                        e.span,
                    )
                }
            }
            ExprKind::Match { form, motive: Some(m), scrut, arms, eqbind, generated } => {
                let (scrut_t, scrut_ty, scrut_lvl) = self.elab_infer(cx, scrut)?;
                // An indexed scrutinee's motive binds the index too
                // (docs/inductive-indexed-lowering.md §6.1).
                // Route 2b's forded family (docs/inductive-fording-lowering.md
                // §12.1): the same two-binder motive rule as route 1's, over
                // the Σ+`sEq` form instead of the eliminator's.
                if let Some((ind, fam)) = self.forded_of_at(cx, &scrut_ty) {
                    let (binders, body) =
                        motive_lam(m, 2, "write `as \u{3bb} n z => T` (index, then value)")?;
                    let mut mcx = cx.clone();
                    mcx.push(binders[0].clone(), fam.ity.clone(), fam.ilvl.clone());
                    mcx.push(
                        binders[1].clone(),
                        fam.ty_at(Term::Var(LocalVar(0)), 1),
                        fam.lvl(),
                    );
                    let (motive2, mlvl) = self.elab_ty(&mcx, &body)?;
                    let result = motive2.apply_local(
                        &LocalSubst::id(&cx.gamma)
                            .extended(Rc::clone(&fam.idx))
                            .extended(Rc::new(scrut_t.clone())),
                    );
                    // §9: the two direct entries into a family lowering need
                    // the preprocessing too — otherwise a `_` arm reaches it
                    // as an unknown constructor. The motive here binds *two*
                    // things (index, then value), so non-dependence is a shift
                    // by two (docs/nested-match-patterns-design.md §5.1).
                    let indep = motive2 == result.shift_local(2);
                    let prepared = self.prepare_arms(
                        cx, *form, *generated, arms, &scrut_t, &scrut_ty, &result, indep, &mlvl,
                        e.span,
                    )?;
                    let (acx, arms) = match &prepared {
                        Some((c, a)) => (c, a.as_slice()),
                        None => (cx, arms.as_slice()),
                    };
                    let t = self.elab_match_forded(
                        acx, *form, &ind, &fam, arms, scrut_t, motive2, mlvl.clone(), e.span,
                    )?;
                    return Ok((t, result, mlvl));
                }
                if let Some((ind, fam)) = self.indexed_of_at(cx, &scrut_ty) {
                    let (binders, body) =
                        motive_lam(m, 2, "write `as \u{3bb} n z => T` (index, then value)")?;
                    let (ity, ilvl) = self.index_type_of(cx, &ind, e.span)?;
                    let mut mcx = cx.clone();
                    mcx.push(binders[0].clone(), ity, ilvl);
                    mcx.push(
                        binders[1].clone(),
                        fam.el_at(Term::Var(LocalVar(0)), 1),
                        fam.level.clone(),
                    );
                    let (motive2, mlvl) = self.elab_ty(&mcx, &body)?;
                    let result = motive2.apply_local(
                        &LocalSubst::id(&cx.gamma)
                            .extended(Rc::clone(&fam.idx))
                            .extended(Rc::new(scrut_t.clone())),
                    );
                    let indep = motive2 == result.shift_local(2);
                    let prepared = self.prepare_arms(
                        cx, *form, *generated, arms, &scrut_t, &scrut_ty, &result, indep, &mlvl,
                        e.span,
                    )?;
                    let (acx, arms) = match &prepared {
                        Some((c, a)) => (c, a.as_slice()),
                        None => (cx, arms.as_slice()),
                    };
                    let t = self.elab_match_indexed(
                        acx, *form, &ind, &fam, arms, scrut_t, motive2, mlvl.clone(), e.span,
                    )?;
                    return Ok((t, result, mlvl));
                }
                let (binders, body) = motive_lam(m, 1, "write `as \u{3bb} z => T`")?;
                let mut mcx = cx.clone();
                mcx.push(binders[0].clone(), scrut_ty.clone(), scrut_lvl.clone());
                let (motive, mlvl) = self.elab_ty(&mcx, &body)?;
                let result = motive.apply_local(
                    &LocalSubst::id(&cx.gamma).extended(Rc::new(scrut_t.clone())),
                );
                // `match h : e as \u{3bb} z => M { … }`: the equation decorates the
                // *user's* motive rather than replacing it, and the result type
                // is unchanged — the convoy is type-transparent
                // (docs/match-equation-split-design.md \u{a7}3.3).
                if let Some(h) = eqbind {
                    let t = self.elab_convoy(
                        cx, *form, *generated, h, arms, scrut_t, &scrut_ty, &scrut_lvl, motive,
                        &mlvl, &result, e.span,
                    )?;
                    return Ok((t, result, mlvl));
                }
                let t = self.elab_match(
                    cx, *form, *generated, arms, scrut_t, &scrut_ty, &scrut_lvl, motive,
                    mlvl.clone(), e.span,
                )?;
                Ok((t, result, mlvl))
            }
            // A motive-less `match` whose branches do not depend on the
            // scrutinee: one arm names the type, and the motive is that type,
            // constant (issues/match-arg-of-polymorphic-callee-needs-motive.md).
            // Tried before the message below, and only ever *replaced* by it —
            // a synthesis that does not go through leaves no trace.
            ExprKind::Match { form, motive: None, scrut, arms, eqbind: None, generated } => {
                if let Some(r) =
                    self.infer_match_constant_motive(cx, *form, scrut, arms, *generated, e.span)
                {
                    return r;
                }
                err(
                    format!(
                        "`{}` in inference position needs a motive: `{}`",
                        form.keyword(),
                        match form {
                            MatchForm::Match => "match e as \u{3bb} z => T { … }",
                            MatchForm::Split => "split e as \u{3bb} z => T;",
                        }
                    ),
                    e.span,
                )
            }
            // Both the form and the *suggested spelling* are the written
            // one: `match e as \u{3bb} z => T { … }` is not a thing a writer who
            // typed `split` can paste (issues/diagnostics-name-the-written-form.md).
            ExprKind::Match { form, motive: None, .. } => err(
                format!(
                    "`{}` in inference position needs a motive: `{}`",
                    form.keyword(),
                    match form {
                        MatchForm::Match => "match e as \u{3bb} z => T { … }",
                        MatchForm::Split => "split e as \u{3bb} z => T;",
                    }
                ),
                e.span,
            ),
            ExprKind::J { proof, motive, case } => {
                let (mbinders, mbody) =
                    motive_lam(motive, 2, "write `j(p, \u{3bb} y q => T, case)`")?;
                let (y, p) = (&mbinders[0], &mbinders[1]);
                let (proof_t, proof_ty, _) = self.elab_infer(cx, proof)?;
                let head = self.whnf(cx, &proof_ty, proof.span)?;
                let Type::Id { level, ty, lhs, rhs } = head else {
                    return err("`j` needs a proof of an `=` type", proof.span);
                };
                // Motive context: Γ, y : S, p : Id(S, a, y).
                let mut mcx = cx.clone();
                mcx.push(y.clone(), (*ty).clone(), level.clone());
                let p_ty = Type::Id {
                    level: level.clone(),
                    ty: Rc::new(ty.shift_local(1)),
                    lhs: Rc::new(lhs.shift_local(1)),
                    rhs: Rc::new(Term::Var(LocalVar(0))),
                };
                mcx.push(p.clone(), p_ty, level.clone());
                let (motive_t, mlvl) = self.elab_ty(&mcx, &mbody)?;
                // case : M[a/y, refl/p]
                let refl = Term::Refl {
                    level: level.clone(),
                    ty: Rc::clone(&ty),
                    tm: Rc::clone(&lhs),
                };
                let case_ty = motive_t.apply_local(
                    &LocalSubst::id(&cx.gamma)
                        .extended(Rc::clone(&lhs))
                        .extended(Rc::new(refl)),
                );
                let case_t = self.elab_check(cx, case, &case_ty, &mlvl)?;
                // result : M[b/y, proof/p]
                let proof_rc = Rc::new(proof_t);
                let result = motive_t.apply_local(
                    &LocalSubst::id(&cx.gamma)
                        .extended(Rc::clone(&rhs))
                        .extended(Rc::clone(&proof_rc)),
                );
                let t = Term::J {
                    ty_level: level.clone(),
                    motive_level: mlvl.clone(),
                    ty,
                    lhs,
                    motive: Rc::new(motive_t),
                    case: Rc::new(case_t),
                    rhs,
                    proof: proof_rc,
                };
                Ok((t, result, mlvl))
            }
            // Rule 2 again, in inference position: a bound `refl` is the
            // binding, and only an unbound one is the form.
            ExprKind::Refl if self.shadowed(cx, "refl") => self.elab_infer(
                cx,
                &Expr { kind: ExprKind::Var("refl".to_string()), span: e.span },
            ),
            ExprKind::Refl => err(
                "`refl` needs an expected type (checking position or `as` motive)",
                e.span,
            ),
            // Checking-only, like `refl` and for the same reason: with no
            // expected type there is no goal to close and nothing to guess.
            // This is where "ignored for values" falls out rather than being
            // enforced (issues/auto-refl-empty-block.md).
            ExprKind::AutoRefl => err(
                "an empty block `{}` needs an expected type: it is the one \
                 speculative `refl`, so it only means anything where a goal is \
                 known (a `theorem` body, an annotated `let`, an argument)",
                e.span,
            ),
            // Checking-only, mirroring the kernel: `BoxTm` is `NotInferable`
            // by design (docs/in-language-map-design.md §5). And a quote is
            // only meaningful at layer m, so outside a `meta fn` the pointer
            // is to the declaration form, not to an annotation.
            ExprKind::Quote(_) => err(
                "a `code { … }` quote needs an expected `Code(g |- T)` type, inside \
                 a `meta fn` (docs/in-language-map-design.md §3)",
                e.span,
            ),
            ExprKind::Splice(inner) => self.elab_splice(cx, inner, e.span),
            // Unreachable: [`Self::op_rewrite`] runs at the top of this
            // function and rewrites every symbol, bare or applied, to a name.
            ExprKind::OpSymbol(s) => {
                err(format!("`{s}` reached elaboration unresolved"), e.span)
            }
        }
    }

    /// `match h : e { … }` — the convoy, written for the user
    /// (docs/match-equation-split-design.md §3.3).
    ///
    /// Three mechanical steps over the *unconvoyed* elaboration, and nothing
    /// below [`Self::elab_match`] learns that any of them happened:
    ///
    /// 1. the motive `M` over `Γ, z` becomes `M' = Π (e = z). M`, so every arm
    ///    is checked at `Π fields. (e = C(fields)) -> M[C(fields)/z]`;
    /// 2. each arm's *surface* body `b` becomes `λ h => b`, unannotated — the
    ///    arm type supplies the domain, so no equation is written twice;
    /// 3. the eliminator is applied to `refl : e = e`, which is exactly `M'`
    ///    at `z := e` stripped back to `M[e/z]`.
    ///
    /// So the convoy is **type-transparent**: `result` is the type the
    /// unconvoyed `match` would have had, in both modes. The direction is
    /// `scrutinee = pattern` (§3.2): it is what the one live consumer wants,
    /// and it is the one `refl` inhabits without a `sym`.
    #[allow(clippy::too_many_arguments)]
    fn elab_convoy(
        &self,
        cx: &Cx,
        form: MatchForm,
        generated: bool,
        h: &str,
        arms: &[Arm],
        scrut_t: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        motive: Type,
        mlvl: &Level,
        result: &Type,
        span: Span,
    ) -> R<Term> {
        // §4: an indexed family's arms live at *different* indices, so `e = z`
        // would relate two values at two types. Homogeneous `Id` cannot say
        // that, and the thing that can is the family's inversion principle —
        // a library device, not a syntax (issues/surface-existential.md).
        if let Some(ind) = self
            .forded_of_at(cx, scrut_ty)
            .map(|(ind, _)| ind)
            .or_else(|| self.indexed_of_at(cx, scrut_ty).map(|(ind, _)| ind))
        {
            return err(
                format!(
                    "the equation binding is not available on the indexed family \
                     `{}`: an arm's index varies with its constructor, so \
                     `e = pat` would relate two values at different types. Case \
                     on the index first, or state the equation you want as an \
                     inversion lemma",
                    ind.name
                ),
                span,
            );
        }
        // `e = z` over `Γ, z` — every component weakened past `z`.
        let eq_under_z = Type::Id {
            level: scrut_lvl.clone(),
            ty: Rc::new(scrut_ty.shift_local(1)),
            lhs: Rc::new(scrut_t.shift_local(1)),
            rhs: Rc::new(Term::Var(LocalVar(0))),
        };
        let motive2 = Type::Pi {
            dom_level: scrut_lvl.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(eq_under_z),
            // `M` is over `Γ, z`; the codomain is over `Γ, z, h`.
            cod: Rc::new(motive.shift_local(1)),
        };
        let mlvl2 = Level::max(scrut_lvl.clone(), mlvl.clone());
        let arms: Vec<Arm> = arms
            .iter()
            .map(|a| Arm {
                ctor: a.ctor.clone(),
                default: a.default,
                binders: a.binders.clone(),
                body: Expr {
                    kind: ExprKind::Lam {
                        binders: vec![LamBinder {
                            name: h.to_string(),
                            ty: None,
                            implicit: false,
                            span: a.body.span,
                        }],
                        body: Box::new(a.body.clone()),
                    },
                    span: a.body.span,
                },
                span: a.span,
            })
            .collect();
        let elim = self.elab_match(
            cx,
            form,
            generated,
            &arms,
            scrut_t.clone(),
            scrut_ty,
            scrut_lvl,
            motive2,
            mlvl2,
            span,
        )?;
        let scrut_rc = Rc::new(scrut_t);
        let ty_rc = Rc::new(scrut_ty.clone());
        Ok(Term::App {
            fun: Rc::new(elim),
            dom_level: scrut_lvl.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(Type::Id {
                level: scrut_lvl.clone(),
                ty: Rc::clone(&ty_rc),
                lhs: Rc::clone(&scrut_rc),
                rhs: Rc::clone(&scrut_rc),
            }),
            // The Π is non-dependent, so the codomain is the result weakened
            // past the equation binder.
            cod: Rc::new(result.shift_local(1)),
            arg: Rc::new(Term::Refl {
                level: scrut_lvl.clone(),
                ty: ty_rc,
                tm: scrut_rc,
            }),
        })
    }

    /// Elaborate a `match` given its scrutinee and its (already elaborated)
    /// motive, scoped over one extra local `z` of the scrutinee's type.
    /// Dispatch is by the scrutinee's type: `Nat` is the kernel's own
    /// recursor, a declared inductive is the tier-0 case tree
    /// (docs/inductive-tier0-lowering.md §5).
    #[allow(clippy::too_many_arguments)]
    /// A motive-less `match` in **inference** position, read as one whose
    /// result type does not depend on the scrutinee: an arm names the type and
    /// the motive is that type, constant
    /// (`issues/match-arg-of-polymorphic-callee-needs-motive.md`).
    ///
    /// `None` means "not this shape" and the caller reports the message that
    /// asks for a motive — the synthesis never produces an error of its own,
    /// so a dependent `match` that always needed a written motive still gets
    /// told so rather than a mismatch inside an arm.
    ///
    /// Three properties make this a synthesis rather than a guess:
    ///
    ///  - **The naming arm binds nothing**, so its body is scoped in `Γ` and
    ///    its type is available with no branch context to build. Reading a
    ///    binding arm's type means reconstructing that arm's context, which is
    ///    per-lowering work (`elab_arm`'s Σ-walk, the case tree, the `Wf`
    ///    eliminator) and is not attempted here.
    ///  - **The other arms are checked, not joined.** Once one arm names `T`,
    ///    every arm — binding or not — goes through the ordinary path against
    ///    it. So this widens where a motive may be *omitted*, never what a
    ///    `match` may mean.
    ///  - **Speculation does not nest** ([`Self::motive_speculation`]), and a
    ///    failed attempt leaves no warnings behind.
    fn infer_match_constant_motive(
        &self,
        cx: &Cx,
        form: MatchForm,
        scrut: &Expr,
        arms: &[Arm],
        generated: bool,
        span: Span,
    ) -> Option<R<(Term, Type, Level)>> {
        if self.motive_speculation.get() {
            return None;
        }
        let warned = self.warnings.borrow().len();
        let goaled = self.goals.borrow().len();
        let rollback = || {
            self.warnings.borrow_mut().truncate(warned);
            self.goals.borrow_mut().truncate(goaled);
            self.goal_spans.borrow_mut().retain(|_, k| *k < goaled);
        };
        // *An* arm that binds nothing, not the first one: a non-binding arm
        // whose body does not infer either (`Nil` on its own, which is the
        // very ambiguity this is trying to resolve) teaches nothing and is
        // stepped over. Each candidate is elaborated at most once, so the
        // whole search is linear in the arms.
        self.motive_speculation.set(true);
        let named = arms
            .iter()
            .filter(|a| a.binders.is_empty())
            .find_map(|a| match self.elab_infer(cx, &a.body) {
                Ok((_, ty, lvl)) => Some((ty, lvl)),
                Err(_) => {
                    rollback();
                    None
                }
            });
        self.motive_speculation.set(false);
        let (ty, lvl) = named?;
        let attempt: R<(Term, Type, Level)> = (|| {
            let (scrut_t, scrut_ty, scrut_lvl) = self.elab_infer(cx, scrut)?;
            let t = self.elab_match(
                cx,
                form,
                generated,
                arms,
                scrut_t,
                &scrut_ty,
                &scrut_lvl,
                // Constant over the scrutinee binder: that *is* the reading.
                ty.shift_local(1),
                lvl.clone(),
                span,
            )?;
            Ok((t, ty, lvl))
        })();
        match attempt {
            Ok(r) => Some(Ok(r)),
            Err(_) => {
                // No trace: warnings raised inside the attempt, and any goal it
                // minted, are rolled back. The goals matter more than they
                // look — a hole is registered by *span*, and the attempt
                // elaborates the arm in `Γ` while the real pass elaborates it
                // inside the branch context, so a surviving registration would
                // meet the "re-elaborated in a different context" refusal in
                // [`Self::new_goal`] and turn a decline into an internal error.
                rollback();
                None
            }
        }
    }

    fn elab_match(
        &self,
        cx: &Cx,
        form: MatchForm,
        // Diagnostics only (`docs/diagnostic-warnings-design.md` §7.1):
        // whether the pattern compiler built this node.
        generated: bool,
        arms: &[Arm],
        scrut_t: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        // Deep patterns and the `_` arm, compiled away before the dispatch
        // below sees anything (docs/nested-match-patterns-design.md §9). The
        // pass is idempotent and its fast path is every `match` written
        // before it existed, so calling it here *and* at the two direct
        // `elab_infer` entry points costs nothing.
        let result = motive
            .apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(scrut_t.clone())));
        let independent = motive == result.shift_local(1);
        let prepared = self.prepare_arms(
            cx, form, generated, arms, &scrut_t, scrut_ty, &result, independent, &mlvl, span,
        )?;
        let (cx, arms) = match &prepared {
            Some((c, a)) => (c, a.as_slice()),
            None => (cx, arms),
        };
        let head = self.whnf(cx, scrut_ty, span)?;
        // An indexed family in family form (docs/inductive-indexed-lowering.md
        // §6) — checked on the *raw* type, since whnf at a literal index
        // reduces the family away, index and all. The `Empty` case wins
        // first: a family whose branch at this literal index is `Empty`
        // (`Fin(0)`) is matched as the empty type, arms and all.
        if let Some((ind, fam)) = self.forded_of_at(cx, scrut_ty) {
            let motive2 = self.generalize_index(cx, &motive, &fam.idx);
            return self
                .elab_match_forded(cx, form, &ind, &fam, arms, scrut_t, motive2, mlvl, span);
        }
        if !matches!(head, Type::Empty { .. })
            && let Some((ind, fam)) = self.indexed_of_at(cx, scrut_ty)
        {
            let motive2 = self.generalize_index(cx, &motive, &fam.idx);
            return self
                .elab_match_indexed(cx, form, &ind, &fam, arms, scrut_t, motive2, mlvl, span);
        }
        if let Some(ind) = self.tag_of(&head) {
            return self
                .elab_match_data(
                    cx, form, &ind, arms, scrut_t, &head, scrut_lvl, motive, mlvl, span,
                );
        }
        // `Fin(n)` (docs/surface-fin-indexing-design.md §4.2). Tested on the
        // **raw** scrutinee type for the same reason `indexed_of_at` is: the
        // whnf of `Fin(Succ k)` is a bare `Type::Sum`, which carries no hint
        // that its arms should be called `FZ`/`FS`. After the `tag_of` check,
        // so a declared inductive still wins, and before the `Nat`
        // fall-through.
        if let Type::Fin { len } = &*crate::inductive::decoded(scrut_ty) {
            let len_w = self.whnf_tm(cx, len, span)?;
            match &*len_w {
                // `Fin(0) ⇝ Empty⁰` is a whnf step, so `head` is already
                // `Type::Empty` and `match i { }` *is* `elim_Empty` — the arm
                // below, unchanged (§1.1 finding 1). Nothing to write here.
                Term::Zero => {}
                Term::Succ(k) => {
                    return self
                        .elab_match_fin(cx, form, arms, scrut_t, k, motive, mlvl, span);
                }
                // Permanent, not a gap: `Fin` has no eliminator of its own
                // (§1.2), so at an open length there is no canonical form to
                // case on. The message names the fix rather than the
                // limitation, and the fix is the shape `nth` itself has.
                _ => {
                    let here = match &*len_w {
                        Term::Var(LocalVar(i)) => cx
                            .names
                            .len()
                            .checked_sub(1 + *i as usize)
                            .and_then(|p| cx.names.get(p))
                            .map(|n| format!("; here it is `{n}`"))
                            .unwrap_or_default(),
                        _ => String::new(),
                    };
                    return err(
                        format!(
                            "`{}` on a `Fin` needs its length to reduce to `0` or a \
                             successor{here}. Recurse on the length first \
                             (`match n as \u{3bb} z => \u{2026}`), which is how the index \
                             becomes matchable",
                            form.keyword()
                        ),
                        span,
                    );
                }
            }
        }
        if let Type::Empty { level: empty_lvl } = &head {
            // An inductive with no constructors: absurdity elimination. All of
            // them share the kernel type `Empty` (§3.3), and none has an
            // inhabitant to confuse, so no tag is needed to dispatch.
            //
            // `Empty` is level-indexed, so the scrutinee's level comes off the
            // *type* and is independent of the motive's `mlvl`.
            if !arms.is_empty() {
                return err(
                    format!(
                        "this type has no constructors, so `{}` takes no arms",
                        form.keyword()
                    ),
                    span,
                );
            }
            return Ok(Term::ElimEmpty {
                level: mlvl,
                scrut_level: empty_lvl.clone(),
                motive: Rc::new(motive),
                scrut: Rc::new(scrut_t),
            });
        }
        if !matches!(head, Type::Nat) {
            return err(
                format!("`{}` needs a `Nat` or a declared inductive", form.keyword()),
                span,
            );
        }
        self.elab_match_nat(cx, form, arms, scrut_t, motive, mlvl, span)
    }

    /// `match` on `Nat`: the kernel's `elim_Nat`, with the arms named `Zero`
    /// and `Succ(k)` (or the low-level `Succ(k, ih)`).
    fn elab_match_nat(
        &self,
        cx: &Cx,
        form: MatchForm,
        arms: &[Arm],
        scrut_t: Term,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        let mut zero: Option<&Arm> = None;
        let mut succ: Option<&Arm> = None;
        for a in arms {
            let slot = match a.ctor.as_str() {
                "Zero" => &mut zero,
                "Succ" => &mut succ,
                other => {
                    return err(format!("`{other}` is not a constructor of `Nat`"), a.span)
                }
            };
            if slot.replace(a).is_some() {
                return err(format!("duplicate arm for `{}`", a.ctor), a.span);
            }
        }
        let (Some(zero), Some(succ)) = (zero, succ) else {
            return err(
                format!("`{}` on `Nat` needs both a `Zero` and a `Succ(k)` arm", form.keyword()),
                span,
            );
        };
        if !zero.binders.is_empty() {
            return err("`Zero` binds no fields", zero.span);
        }
        // `Succ(k)` is the unified form (ih = guarded self-call); `Succ(k, ih)`
        // stays as the low-level explicit fallback (issues/match-recursion.md).
        let (k, ih) = match succ.binders.as_slice() {
            [k] => (k.name().to_string(), None),
            [k, ih] => (k.name().to_string(), Some(ih.name().to_string())),
            _ => return err("`Succ` binds `(k)` or `(k, ih)`", succ.span),
        };
        let (zero, succ_body) = (&zero.body, &succ.body);
        let _ = span;
        // Does this match descend on one of the declaration's own parameters?
        // If so, self-calls in the arm become the ih. If not (a nested match on
        // some other term), the enclosing arm's guard — if any — still stands,
        // possibly *extended* by this match (§ course-of-values below).
        let dec = if ih.is_none() { self.descends_on_param(cx, &scrut_t) } else { None };
        // How many past values the arm reads. `1` is the ordinary recursion and
        // emits exactly the term it always did; more makes the recursor carry a
        // tuple (`cov_*` below, issues/recursion-at-deeper-subterms.md).
        let d = match dec {
            Some(dec) => self.cov_depth(cx, succ_body, &k, dec),
            None => 1,
        };
        // A nested `match` on the chain's end, with values below it still
        // uncollected: it must **convoy** them, or its arms cannot see that the
        // value one below `k` is the value at `l`
        // (docs/course-of-values-recursion-design.md §5).
        let convoy = if ih.is_none() && dec.is_none() {
            self.chain_convoy(cx, &scrut_t)
        } else {
            None
        };
        // The motive of the recursor actually emitted. Three shapes, and the
        // first is what every ordinary `match` on `Nat` has always emitted:
        //   d = 1, no convoy : M
        //   d > 1            : Σ(M[z], M[pred z], …)   — the carried window
        //   convoy           : T_outer(z) -> M[z]      — the window passed in
        let comps_z = cov_comps(&cx.gamma, &motive, d, 1, &Term::Var(LocalVar(0)));
        let (rec_motive, rec_lvl) = match &convoy {
            None => (cov_ty(&comps_z, &mlvl), mlvl.clone()),
            Some(c) => {
                let carried = cov_ty(
                    &cov_comps(&cx.gamma, &c.motive, c.d, 1, &c.anchor(Term::Var(LocalVar(0)))),
                    &c.lvl,
                );
                (
                    Type::Pi {
                        dom_level: c.lvl.clone(),
                        cod_level: mlvl.clone(),
                        dom: Rc::new(carried),
                        cod: Rc::new(motive.shift_local(1)),
                    },
                    Level::max(c.lvl.clone(), mlvl.clone()),
                )
            }
        };
        // base : M[Zero/z] — under the convoy binder where there is one, and
        // tupled where `d > 1`, since every component of F(0) is at the same
        // `Zero` (`pred 0` is `0`).
        let base_ty =
            motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Zero)));
        let base = match &convoy {
            None => self.elab_check(cx, zero, &base_ty, &mlvl)?,
            Some(c) => {
                let comps = cov_comps(&cx.gamma, &c.motive, c.d, 0, &c.anchor(Term::Zero));
                let dom = cov_ty(&comps, &c.lvl);
                let mut bcx = cx.clone();
                bcx.push("#cov".into(), dom.clone(), c.lvl.clone());
                bcx.guard = Some(c.guard_at(&comps, bcx.names.len(), None));
                let body = self.elab_check(&bcx, zero, &base_ty.shift_local(1), &mlvl)?;
                Term::Lam {
                    dom_level: c.lvl.clone(),
                    cod_level: mlvl.clone(),
                    dom: Rc::new(dom),
                    body: Rc::new(body),
                }
            }
        };
        // step context: Γ, k : Nat, ih : rec_motive[k/z].
        let mut scx = cx.clone();
        scx.push(k.clone(), Type::Nat, Level::Zero);
        let ih_ty = rec_motive.apply_local(&embed(&cx.gamma, 1).extended(Rc::new(Term::Var(LocalVar(0)))));
        // The unified arm `Succ(k)` binds the ih anyway — the recursor demands
        // it — but under a name the surface cannot spell, because it is
        // reached by a guarded self-call instead.
        scx.push(ih.clone().unwrap_or_else(|| "#ih".into()), ih_ty, rec_lvl.clone());
        // The window this arm carries, scoped in Γ, k, ih: the ih itself at
        // `d = 1`, its projections above that.
        let comps_ih: Vec<Type> = comps_z
            .iter()
            .map(|c| {
                c.apply_local(&embed(&cx.gamma, 2).extended(Rc::new(Term::Var(LocalVar(1)))))
            })
            .collect();
        let ih_at = |i: usize| {
            (cov_proj(&comps_ih, &mlvl, Term::Var(LocalVar(0)), i), comps_ih[i].clone(), mlvl.clone())
        };
        // step : M[Succ k/z] in Γ, k, ih (+ the convoy binder) — the arm the
        // writer wrote, whatever the recursor is carrying underneath it.
        let step_ty = motive.apply_local(
            &embed(&cx.gamma, 2)
                .extended(Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(1)))))),
        );
        let step = match &convoy {
            Some(c) => {
                // The convoyed window at `Succ k`, where `pred (Succ k) ⇝ k`
                // makes the component one below this arm's scrutinee *reduce*
                // to the motive at the variable the arm binds. That reduction
                // is the whole point of passing it in.
                let comps = cov_comps(
                    &cx.gamma,
                    &c.motive,
                    c.d,
                    2,
                    &c.anchor(Term::Succ(Rc::new(Term::Var(LocalVar(1))))),
                );
                let dom = cov_ty(&comps, &c.lvl);
                let mut bcx = scx.clone();
                bcx.push("#cov".into(), dom.clone(), c.lvl.clone());
                bcx.guard = Some(c.guard_at(&comps, bcx.names.len(), Some(cx.names.len())));
                let body = self.elab_check(&bcx, succ_body, &step_ty.shift_local(1), &mlvl)?;
                Term::Lam {
                    dom_level: c.lvl.clone(),
                    cod_level: mlvl.clone(),
                    dom: Rc::new(dom),
                    body: Rc::new(body),
                }
            }
            None => {
                if ih.is_none() {
                    scx.guard = dec
                        .map(|dec| {
                            Rc::new(Guard {
                                dec,
                                kind: GuardKind::Nat {
                                    preds: vec![cx.names.len()],
                                    depth: scx.names.len(),
                                    tuple: Term::Var(LocalVar(0)),
                                    comps: comps_ih.clone(),
                                    mlvl: mlvl.clone(),
                                    motive: Rc::new(motive.clone()),
                                    gamma: cx.gamma.clone(),
                                },
                                rebind: None,
                            })
                        })
                        .or_else(|| cx.guard.clone());
                }
                let step = self.elab_check(&scx, succ_body, &step_ty, &mlvl)?;
                if d == 1 {
                    step
                } else {
                    // F(Succ k) = (step, π₀ ih, …, π_{d-2} ih): the value just
                    // computed, then the window slid by one. Annotated at
                    // `Succ k`, where the kernel checks it; the shifted
                    // components differ from those annotations only by
                    // `pred (Succ k) ⇝ k`, which conversion does.
                    let comps_succ = cov_comps(
                        &cx.gamma,
                        &motive,
                        d,
                        2,
                        &Term::Succ(Rc::new(Term::Var(LocalVar(1)))),
                    );
                    let mut vals = vec![step];
                    vals.extend((0..d - 1).map(|i| ih_at(i).0));
                    cov_tuple(&comps_succ, &mlvl, vals)
                }
            }
        };
        // F(0) = (f(0), …, f(0)): the deeper components stand for values before
        // the start, which no arm can read — a call at depth `i` is only in
        // scope inside `i` nested `Succ` arms, so reaching one would need the
        // scrutinee to be at least `i`. The `Zero` arm's own value is the one
        // term of the right type already to hand.
        let base = if d == 1 {
            base
        } else {
            let comps_0 = cov_comps(&cx.gamma, &motive, d, 0, &Term::Zero);
            cov_tuple(&comps_0, &mlvl, vec![base; d])
        };
        let elim = Term::ElimNat {
            level: rec_lvl,
            motive: Rc::new(rec_motive),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::new(scrut_t.clone()),
        };
        if let Some(c) = &convoy {
            // …and the window goes in, which is what refines it.
            let comps = cov_comps(&cx.gamma, &c.motive, c.d, 0, &c.anchor(scrut_t.clone()));
            return Ok(Term::App {
                fun: Rc::new(elim),
                dom_level: c.lvl.clone(),
                cod_level: mlvl.clone(),
                dom: Rc::new(cov_ty(&comps, &c.lvl)),
                cod: Rc::new(
                    motive.apply_local(&embed(&cx.gamma, 1).extended(Rc::new(scrut_t.shift_local(1)))),
                ),
                arg: Rc::new(c.tuple.clone()),
            });
        }
        if d == 1 {
            return Ok(elim);
        }
        // The source's `match` is the *first* component of what the recursor
        // now computes, so the transformation stays local to this expression:
        // its type is still `M[scrut/z]`.
        let comps_at = cov_comps(&cx.gamma, &motive, d, 0, &scrut_t);
        Ok(cov_proj(&comps_at, &mlvl, elim, 0))
    }

    /// A nested `match` on the enclosing arm's predecessor continues the chain:
    /// inside `match n { Succ(k) => match k { Succ(l) => … } }` the variable
    /// `l` is the value two below `n`, and a self-call at it is guarded — but
    /// only if the values the enclosing recursion carries are *passed through*
    /// this match, since only then does the component one below `k` reduce, at
    /// the arm that knows `k` is `Succ l`, to the value at `l`.
    ///
    /// `None` when the enclosing recursion has nothing left to hand down —
    /// every ordinary one-step recursion, which therefore emits exactly the
    /// term it always did.
    fn chain_convoy(&self, cx: &Cx, scrut: &Term) -> Option<Convoy> {
        let g = cx.guard.clone()?;
        let GuardKind::Nat { preds, depth, tuple, comps, mlvl, motive, gamma } = &g.kind else {
            return None;
        };
        // Nothing below the chain's end is carried: this is the ordinary
        // recursion, and a nested `match` changes nothing about it.
        if comps.len() <= preds.len() {
            return None;
        }
        // By *binder*, never by name: an inner `k` that shadows the arm's own
        // is a different variable and does not continue the chain.
        let Term::Var(LocalVar(i)) = scrut else { return None };
        if cx.names.len() - 1 - *i as usize != *preds.last()? {
            return None;
        }
        let by = (cx.names.len() - depth) as u32;
        Some(Convoy {
            dec: g.dec,
            preds: preds.clone(),
            d: comps.len(),
            lvl: mlvl.clone(),
            motive: motive.apply_local(
                &embed(gamma, by + 1).extended(Rc::new(Term::Var(LocalVar(0)))),
            ),
            outer_motive: Rc::clone(motive),
            gamma: gamma.clone(),
            tuple: tuple.shift_local(by),
            lift: preds.len() - 1,
        })
    }

    /// How deep into the predecessor chain the arm's self-calls reach: `1` for
    /// `f(k)`, `2` for an `f(l)` under a nested `match k`, and so on
    /// (issues/recursion-at-deeper-subterms.md).
    ///
    /// **Syntactic, and deliberately only a sizing decision.** It reads names,
    /// so a shadowed binder can make it wrong in either direction — and
    /// neither direction can produce a wrong term. Too small, and the real
    /// check refuses the call for want of an ih (the same message as before
    /// this existed); too large, and the recursor carries a component nothing
    /// reads. What a call *lowers to* is decided by [`Self::elab_self_call`]
    /// comparing binder positions, which no spelling can fool.
    fn cov_depth(&self, cx: &Cx, body: &Expr, k: &str, dec: usize) -> usize {
        let Some(s) = cx.selfref.as_ref() else { return 1 };
        // name of a chain predecessor -> its depth, `k` being depth 1.
        let mut chain: Vec<(String, usize)> = vec![(k.to_string(), 1)];
        let mut found = 1usize;
        // Descend the chain first, then look for calls: the map has to be
        // complete before a call at `l` can be recognised as one.
        loop {
            let (cur, at) = chain.last().cloned().expect("seeded above");
            let mut next: Option<String> = None;
            walk_expr(body, &mut |e| {
                if let ExprKind::Match { scrut, arms, .. } = &e.kind
                    && matches!(&scrut.kind, ExprKind::Var(n) if *n == cur)
                    && let Some(a) = arms.iter().find(|a| a.ctor == "Succ")
                    && let [p] = a.binders.as_slice()
                {
                    next.get_or_insert_with(|| p.name().to_string());
                }
            });
            match next {
                Some(n) if !chain.iter().any(|(m, _)| *m == n) => chain.push((n, at + 1)),
                _ => break,
            }
        }
        walk_expr(body, &mut |e| {
            let ExprKind::App { head, args, explicit } = &e.kind else { return };
            let head = match &head.kind {
                ExprKind::TyApp { head, .. } => head,
                _ => head,
            };
            if !matches!(&head.kind, ExprKind::Var(n) if *n == s.name) {
                return;
            }
            let positions: Vec<usize> = (s.n_tyvars..s.params.len())
                .filter(|&j| *explicit || !s.params[j].1)
                .collect();
            let Some(slot) = positions.iter().position(|&j| j == dec) else { return };
            let Some(arg) = args.get(slot) else { return };
            if let ExprKind::Var(n) = &arg.kind
                && let Some((_, at)) = chain.iter().find(|(m, _)| m == n)
            {
                found = found.max(*at);
            }
        });
        found
    }

    /// `match` on `Fin(Succ k)`: the kernel's `Case` over the sum that
    /// `Fin(Succ k)` unfolds to, with the arms named `FZ` and `FS(j)`
    /// (docs/surface-fin-indexing-design.md §4.2).
    ///
    /// `Fin` has no eliminator of its own — it is a former whose whnf is
    /// `Unit⁰ + Fin(k)` — so the summands are written **unfolded** here while
    /// the scrutinee's own type stays the folded `Fin(Succ k)`, and conversion
    /// bridges the two. That is the same asymmetry `term::nth` lives with.
    #[allow(clippy::too_many_arguments)]
    fn elab_match_fin(
        &self,
        cx: &Cx,
        form: MatchForm,
        arms: &[Arm],
        scrut_t: Term,
        k: &Rc<Term>,
        motive: Type,
        mlvl: Level,
        span: Span,
    ) -> R<Term> {
        let mut fz: Option<&Arm> = None;
        let mut fs: Option<&Arm> = None;
        for a in arms {
            let slot = match a.ctor.as_str() {
                "FZ" => &mut fz,
                "FS" => &mut fs,
                other => {
                    return err(format!("`{other}` is not an index of a `Fin`"), a.span)
                }
            };
            if slot.replace(a).is_some() {
                return err(format!("duplicate arm for `{}`", a.ctor), a.span);
            }
        }
        let (Some(fz), Some(fs)) = (fz, fs) else {
            return err(
                format!(
                    "`{}` on a `Fin` needs both an `FZ` and an `FS(i)` arm",
                    form.keyword()
                ),
                span,
            );
        };
        if !fz.binders.is_empty() {
            return err("`FZ` binds no fields", fz.span);
        }
        let [j] = fs.binders.as_slice() else {
            return err("`FS` binds exactly one field, the predecessor index", fs.span)
        };
        let j = j.name().to_string();
        let (lhs, rhs) = (Type::Unit { level: Level::Zero }, Type::Fin { len: Rc::clone(k) });
        // The two arm types, as the kernel's `Case` rule states them:
        // `M[inl x/z]` in `Γ, x : Unit⁰` and `M[inr y/z]` in `Γ, y : Fin(k)`.
        let injected = |left: bool| {
            let (lhs, rhs) = (Rc::new(lhs.shift_local(1)), Rc::new(rhs.shift_local(1)));
            let val = Rc::new(Term::Var(LocalVar(0)));
            let (lhs_level, rhs_level) = (Level::Zero, Level::Zero);
            if left {
                Term::Inl { lhs_level, rhs_level, lhs, rhs, val }
            } else {
                Term::Inr { lhs_level, rhs_level, lhs, rhs, val }
            }
        };
        // The `FZ` arm binds nothing at the surface but the kernel's `case_l`
        // binds one local, so a `#`-prefixed dummy stands in — the convention
        // `build_absurd` already uses for `#y`/`#p`. Unspellable, and filtered
        // out of the goal listing.
        let mut lcx = cx.clone();
        lcx.push("#fz".to_string(), lhs.clone(), Level::Zero);
        let left_ty =
            motive.apply_local(&embed(&cx.gamma, 1).extended(Rc::new(injected(true))));
        let case_l = self.elab_check(&lcx, &fz.body, &left_ty, &mlvl)?;
        let mut rcx = cx.clone();
        rcx.push(j.clone(), rhs.clone(), Level::Zero);
        let right_ty =
            motive.apply_local(&embed(&cx.gamma, 1).extended(Rc::new(injected(false))));
        let case_r = self.elab_check(&rcx, &fs.body, &right_ty, &mlvl)?;
        Ok(Term::Case {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            motive_level: mlvl,
            lhs: Rc::new(lhs),
            rhs: Rc::new(rhs),
            motive: Rc::new(motive),
            case_l: Rc::new(case_l),
            case_r: Rc::new(case_r),
            scrut: Rc::new(scrut_t),
        })
    }

    /// `FZ` (`succ_of: None`) or `FS(j)` against an expected `Fin`
    /// (docs/surface-fin-indexing-design.md §3.2).
    ///
    /// `decoded` and not `whnf`, for exactly the reason `elab_vec_lit` gives:
    /// `Fin` *reduces on its length*, so the whnf of `Fin(Succ k)` is the sum
    /// this arm exists to recognise the folded form of. The length alone is
    /// reduced, and that is what the table dispatches on.
    fn elab_fin_index(
        &self,
        cx: &Cx,
        succ_of: Option<&Expr>,
        expected: &Type,
        span: Span,
    ) -> R<Term> {
        let what = if succ_of.is_some() { "FS" } else { "FZ" };
        let expected = &*crate::inductive::decoded(expected);
        let Type::Fin { len } = expected else {
            return err(format!("`{what}` needs an expected `Fin` type"), span);
        };
        let len_w = self.whnf_tm(cx, len, span)?;
        let Term::Succ(k) = &*len_w else {
            return if matches!(&*len_w, Term::Zero) {
                err("`Fin(0)` is empty, so it has no index", span)
            } else {
                err(
                    "the length has to reduce to a successor here; `Fin(n)` at an open \
                     `n` has no canonical index",
                    span,
                )
            };
        };
        // The annotations are written **folded** (`Fin(k)`, not its unfolded
        // sum): the kernel converts the two, and the folded form is what a
        // goal reads back as — the property `wf.rs`'s `fin_index` exists to
        // preserve.
        let (lhs_level, rhs_level) = (Level::Zero, Level::Zero);
        let lhs = Rc::new(Type::Unit { level: Level::Zero });
        let rhs = Rc::new(Type::Fin { len: Rc::clone(k) });
        match succ_of {
            None => Ok(Term::Inl {
                lhs_level,
                rhs_level,
                lhs,
                rhs,
                val: Rc::new(Term::Triv { level: Level::Zero }),
            }),
            Some(j) => {
                let j_t = self.elab_check(cx, j, &rhs, &Level::Zero)?;
                Ok(Term::Inr { lhs_level, rhs_level, lhs, rhs, val: Rc::new(j_t) })
            }
        }
    }

    /// A numeral in checking position. At a `Fin`-headed expected type it is
    /// the iterated index (docs/surface-fin-indexing-design.md §3.3);
    /// everywhere else it is the `Nat` it always was.
    ///
    /// The `Fin` case is a reuse and not new code: `wf::fin_index` already
    /// builds "index `t` of `Fin(Succ^m(base))`" with the folded annotations,
    /// and emitting *literally* the term it emits is free adequacy — the
    /// surface numeral and the elaborator's own container indices are the same
    /// syntax, so nothing can drift between them.
    fn elab_num_check(
        &self,
        cx: &Cx,
        t: u64,
        e: &Expr,
        expected: &Type,
        span: Span,
    ) -> R<Term> {
        if let Type::Fin { len } = &*crate::inductive::decoded(expected) {
            // Peel `t + 1` successors off the length; the residue is the base
            // `fin_index` annotates its tails with.
            let mut base = Rc::clone(len);
            for peeled in 0..=t {
                let w = self.whnf_tm(cx, &base, span)?;
                let Term::Succ(pred) = &*w else {
                    return err(
                        format!(
                            "`{t}` is not an index of this `Fin`: a numeral here needs the \
                             length to reduce to at least {} successor(s), and this one \
                             reduces to {peeled}",
                            t + 1
                        ),
                        span,
                    );
                };
                base = Rc::clone(pred);
            }
            let t = t as usize;
            return Ok(wf::fin_index(t, t + 1, &base));
        }
        let (num, _, _) = self.elab_infer(cx, e)?;
        Ok(num)
    }

    /// Is `scrut` (already elaborated) exactly one of the enclosing
    /// declaration's parameters? Returns its parameter index — the argument
    /// position the recursion descends on.
    fn descends_on_param(&self, cx: &Cx, scrut: &Term) -> Option<usize> {
        let s = cx.selfref.as_ref()?;
        let Term::Var(LocalVar(i)) = scrut else { return None };
        let pos = cx.names.len() - 1 - *i as usize;
        (pos < s.params.len()).then_some(pos)
    }

    /// A local variable by absolute position (outermost first), as
    /// [`Self::resolve`] would return it.
    fn local(&self, cx: &Cx, pos: usize) -> (Term, Type, Level) {
        let idx = (cx.names.len() - 1 - pos) as u32;
        let entry = &cx.gamma.entries[pos];
        (Term::Var(LocalVar(idx)), entry.ty.shift_local(idx + 1), entry.level.clone())
    }

    /// The written type arguments of a **self-call**
    /// (issues/recursive-self-call-type-arguments.md).
    ///
    /// A self-call is always at the declaration's *own* type parameters, and
    /// that is a fact about the lowering rather than a restriction chosen here:
    /// the recursion becomes an `elim` whose motive is fixed outside it, and the
    /// type parameters are λ-bound outside that — so there is no position in the
    /// emitted term where a second instantiation could go. Polymorphic recursion
    /// would need a fixpoint, which is exactly what
    /// `issues/match-recursion.md`'s discipline exists to avoid.
    ///
    /// So the written arguments are checked to *be* those parameters, in order,
    /// and then dropped. Accepting the spelling costs nothing and refusing it
    /// cost a reader the belief that the language has recursive polymorphic
    /// functions at all; what is not accepted is a different instantiation,
    /// which gets the honest answer instead of a puzzle about scope.
    fn check_self_tyargs(&self, cx: &Cx, tyargs: &[Ty], span: Span) -> R<()> {
        let s = cx.selfref.as_ref().expect("checked by the caller");
        let name = &s.name;
        let own: Vec<&str> = s.params[..s.n_tyvars].iter().map(|(n, _)| n.as_str()).collect();
        if tyargs.len() != s.n_tyvars {
            return err(
                if s.n_tyvars == 0 {
                    format!("`{name}` has no type parameters, so a recursive call takes none")
                } else {
                    format!(
                        "the recursive call to `{name}` writes {} type argument(s), and \
                         `{name}` has {} (`{}`)",
                        tyargs.len(),
                        s.n_tyvars,
                        own.join(", ")
                    )
                },
                span,
            );
        }
        for (a, want) in tyargs.iter().zip(&own) {
            let is_own = matches!(&a.kind, TyKind::Named { name, args }
                if args.is_empty() && name == want);
            if !is_own {
                return err(
                    format!(
                        "a recursive call to `{name}` is always at `{name}`'s own type \
                         parameter(s) `{}`, and `{}` is not `{want}`: recursing at a \
                         *different* instantiation is polymorphic recursion, which this \
                         lowering cannot express — the recursion becomes an `elim` whose \
                         type parameters are bound outside it, so there is nowhere for a \
                         second instantiation to go (issues/match-recursion.md). Writing \
                         `{}` is the same call and so is dropping the type arguments \
                         entirely",
                        own.join(", "),
                        crate::traits::render_ty(a),
                        own.join(", ")
                    ),
                    a.span,
                );
            }
        }
        Ok(())
    }

    /// Lower a call to the enclosing declaration's own name
    /// (issues/match-recursion.md). The termination analysis is deliberately
    /// strict: the call must sit inside a `match` arm that descends on one of
    /// the declaration's parameters, must be saturated, must pass the arm's
    /// predecessor in the decreasing position, and must pass every other
    /// parameter *unchanged*. Under exactly those conditions the recursive
    /// result is definitionally the arm's induction hypothesis, so the
    /// lowering is a variable — no motive surgery, no fixpoint.
    ///
    /// The analysis is untrusted: it can only *reject*. Anything it lets
    /// through still has to typecheck as an `elim_Nat` in the kernel.
    fn elab_self_call(
        &self,
        cx: &Cx,
        args: &[Expr],
        explicit: bool,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let s = Rc::clone(cx.selfref.as_ref().expect("self-call outside a declaration"));
        let name = &s.name;
        let Some(g) = cx.guard.clone() else {
            return err(
                format!(
                    "recursive call to `{name}` is not structurally guarded: it must occur \
                     inside a `match` on one of `{name}`'s own parameters"
                ),
                span,
            );
        };
        // Which parameter each surface argument fills: implicits are omitted
        // unless the call is `@`-marked.
        let positions: Vec<usize> = (s.n_tyvars..s.params.len())
            .filter(|&j| explicit || !s.params[j].1)
            .collect();
        if !positions.contains(&g.dec) {
            return err(
                format!(
                    "`{name}` recurses on its implicit parameter `{}`; pass it explicitly \
                     (`@{name}(…)`) to make the recursive call",
                    s.params[g.dec].0
                ),
                span,
            );
        }
        if args.len() < positions.len() {
            return err(
                format!(
                    "recursive call to `{name}` must pass all {} argument(s), found {}",
                    positions.len(),
                    args.len()
                ),
                span,
            );
        }
        // The ih is saturated at the declared parameters; anything beyond them
        // is a second spine on its *result*, exactly as at an ordinary call
        // site (issues/call-site-overapplication.md). This is the case that
        // matters most, because the curried-return workaround for a varying
        // argument (issues/ih-generalization.md) makes every use of such an ih
        // an over-application: `le_add(n2, m2, good)` for `le_add(n2)(m2, good)`
        // (`lib/std/nat.hthr`).
        let (args, spill) = args.split_at(positions.len());
        // Which descendant the call goes to, once the decreasing argument has
        // been matched: `Nat` has only one, a `Wf` arm has one per recursive
        // field, so this is set inside the loop below. The decreasing argument
        // is checked **first** — at a branching index constructor the ih's
        // index is the *descendant's own* pattern variable, so the rebind
        // check below has no answer until the descendant is known.
        let mut descendant = 0usize;
        // Which link of a `Nat` guard's predecessor chain the call descends to:
        // `0` is the immediate predecessor and anything beyond it is a
        // course-of-values call (issues/recursion-at-deeper-subterms.md).
        let mut cov_at = 0usize;
        let order = {
            let mut o: Vec<usize> = (0..args.len()).collect();
            if let Some(p) = positions.iter().position(|&j| j == g.dec) {
                o.swap(0, p);
            }
            o
        };
        for (arg, j) in order.iter().map(|&k| (&args[k], positions[k])) {
            // Compare by *binder* (`Nat`) or by *term* (`Wf`), never by name,
            // so shadowing cannot fake a guarded call.
            let (arg_t, _, _) = self.elab_infer(cx, arg)?;
            let ok = match (&g.kind, j == g.dec) {
                (GuardKind::Nat { preds, comps, .. }, true) => match arg_t {
                    Term::Var(LocalVar(i)) => {
                        let pos = cx.names.len() - 1 - i as usize;
                        match preds.iter().position(|&p| p == pos) {
                            // Deeper than the recursor was built for is not a
                            // descent it can serve; the message below says so.
                            Some(j) if j < comps.len() => {
                                cov_at = j;
                                true
                            }
                            _ => false,
                        }
                    }
                    _ => false,
                },
                (GuardKind::Wf { depth, children, .. }, true) => {
                    let by = (cx.names.len() - depth) as u32;
                    match children.iter().position(|(c, ..)| c.shift_local(by) == arg_t) {
                        Some(t) => {
                            descendant = t;
                            true
                        }
                        None => false,
                    }
                }
                (_, false) => {
                    let at = |pos: usize| {
                        matches!(arg_t, Term::Var(LocalVar(i))
                                 if cx.names.len() - 1 - i as usize == pos)
                    };
                    // An indexed match rebinds the index parameter to the
                    // arm's pattern variable — the ih is at that index, so
                    // the call must pass exactly it (§6). Compared by *term*,
                    // like a child: at a declared index the pattern variable
                    // is a projection (`nth(cs'; ι_t)`), not a binder.
                    at(j)
                        || g.rebind.as_ref().is_some_and(|(rj, terms)| {
                            let depth = match &g.kind {
                                GuardKind::Wf { depth, .. } => *depth,
                                GuardKind::Nat { .. } => return false,
                            };
                            let by = (cx.names.len() - depth) as u32;
                            *rj == j
                                && terms
                                    .get(descendant)
                                    .is_some_and(|t| t.shift_local(by) == arg_t)
                        })
                }
            };
            if ok {
                continue;
            }
            return if j == g.dec {
                // The message carries the *mechanism*, not just the rule,
                // because the commonest way to hit this is a call at a
                // genuinely smaller subterm — the predecessor's predecessor,
                // in a nested `match` — where the bare rule reads as a checker
                // being needlessly strict and sends the reader here to relax
                // the comparison above. That would only move the failure: the
                // arm is a recursor's step, its ih is the value at the
                // immediate descendant, and there is nothing else to emit.
                // See issues/recursion-at-deeper-subterms.md.
                let (what, why) = match &g.kind {
                    // The chain the enclosing `match`es bind, cut at the depth
                    // the recursor was actually built for: past that there is
                    // no ih to hand back, so naming it would be an offer the
                    // lowering cannot keep.
                    GuardKind::Nat { preds, comps, .. } => {
                        let usable = preds.len().min(comps.len());
                        let names: Vec<String> =
                            preds[..usable].iter().map(|p| format!("`{}`", cx.names[*p])).collect();
                        if usable == 1 {
                            (
                                format!("{}, the predecessor bound by", names[0]),
                                format!(
                                    ". A deeper subterm is refused too, even though it is \
                                     genuinely smaller: this `match` compiles to a recursor \
                                     whose induction hypothesis is the value at {} and at \
                                     nothing else, so a call anywhere else has no term to \
                                     elaborate to. Reaching further needs the recursion to \
                                     carry its earlier values \
                                     (issues/recursion-at-deeper-subterms.md), which happens \
                                     only where an arm scrutinizes its own predecessor",
                                    names[0]
                                ),
                            )
                        } else {
                            (
                                format!(
                                    "one of {}, the predecessors bound by",
                                    names.join(", ")
                                ),
                                format!(
                                    ". The recursion carries its last {usable} values, so \
                                     those are the subterms it can descend to; anything else \
                                     has no term to elaborate to, even when it is genuinely \
                                     smaller (issues/recursion-at-deeper-subterms.md)"
                                ),
                            )
                        }
                    }
                    GuardKind::Wf { .. } => (
                        "one of the recursive fields bound by".to_string(),
                        ". A deeper subterm is refused too, even though it is genuinely \
                         smaller: the induction hypothesis this `match` binds is the value \
                         at each recursive field and at nothing else, so a call anywhere \
                         else has no term to elaborate to"
                            .to_string(),
                    ),
                };
                err(
                    format!(
                        "recursive call to `{name}` must descend: argument `{}` has to be \
                         {what} the enclosing `match`{why}",
                        s.params[j].0
                    ),
                    arg.span,
                )
            } else {
                err(
                    format!(
                        "recursive call to `{name}` must pass `{}` unchanged: the induction \
                         hypothesis fixes every non-decreasing parameter (generalizing a \
                         varying argument into the motive is not supported yet)",
                        s.params[j].0
                    ),
                    arg.span,
                )
            };
        }
        let (t, ty, lvl) = match &g.kind {
            // The ih at the depth the argument descended to, shifted out to
            // wherever the call sits — a variable at depth 0, a projection out
            // of the carried tuple below it.
            GuardKind::Nat { tuple, comps, mlvl, depth, .. } => {
                let by = (cx.names.len() - depth) as u32;
                let t = cov_proj(comps, mlvl, tuple.clone(), cov_at);
                (t.shift_local(by), comps[cov_at].shift_local(by), mlvl.clone())
            }
            // `ih' ι_t` and its type, shifted out to wherever the call sits.
            GuardKind::Wf { depth, children, .. } => {
                let by = (cx.names.len() - depth) as u32;
                let (_, ih, ty, lvl) = &children[descendant];
                ((**ih).shift_local(by), ty.shift_local(by), lvl.clone())
            }
        };
        if spill.is_empty() {
            return Ok((t, ty, lvl));
        }
        self.apply_explicit(cx, Some(name), self.params_of(name), s.params.len(), t, ty, lvl, spill)
    }

    /// Synthesize the dependent motive for a motive-less `match` in checking
    /// position. If the scrutinee elaborates to a local variable `x`, the
    /// motive over `Γ, z : Nat` is the expected type with every occurrence of
    /// `x` abstracted to `z` (the "clear-and-generalize" move); otherwise the
    /// scrutinee is not a variable and no dependency can be recovered, so we
    /// fall back to the non-dependent motive (expected, weakened under `z`).
    ///
    /// Both branches are pure kernel substitutions — no metas. The abstraction
    /// is `expected↑¹` (weaken into `Γ, z`) composed with the swap
    /// `Var(x+1) ↦ z`; applying `[x/z]` to it recovers `expected`, which is
    /// exactly the eliminator's motive obligation `M[scrut/z] = expected`.
    fn synth_motive(
        &self,
        cx: &Cx,
        scrut_t: &Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        expected: &Type,
    ) -> Type {
        // Weaken the expected type into `Γ, z` (z = LocalVar 0, unused).
        let weak = expected.shift_local(1);
        let Term::Var(LocalVar(i)) = scrut_t else {
            return weak;
        };
        // Swap substitution over `Γ, z`: identity except the (shifted)
        // scrutinee `Var(i+1)` maps to `z = Var(0)`.
        let mut ext = cx.gamma.clone();
        ext.entries
            .push(CtxEntry { ty: Rc::new(scrut_ty.clone()), level: scrut_lvl.clone() });
        let mut swap = LocalSubst::id(&ext);
        // `id` puts the outermost entry at index 0: `Var(i+1)` sits at
        // position `|Γ| - 1 - i` (see LocalSubst::id).
        let g = cx.gamma.entries.len() as u32;
        swap.terms[(g - 1 - i) as usize] = Rc::new(Term::Var(LocalVar(0)));
        weak.apply_local(&swap)
    }

    // -- field access (docs/surface-records.md §4) ---------------------------

    /// Resolve `p.f` / `p.f(a, …)` against the receiver's type (§4.2).
    ///
    /// The order matters and is the whole design. The **cheap negative test**
    /// comes first: if `f` is nobody's record field, this is the method
    /// desugaring and the receiver is never inferred here — which is every use
    /// that predates records (`p.sym()`, `p.inj(1)`, `xs.map(f)`), so their
    /// elaboration is bit-for-bit what it was when the parser did this.
    ///
    /// Only if `f` *is* some record's field does the receiver get inferred,
    /// and only if the receiver's own type is a record carrying `f` does this
    /// become a projection. So a field name that shadows a global costs the
    /// global nothing at any other receiver type.
    fn resolve_dot(
        &self,
        cx: &Cx,
        recv: &Expr,
        name: &str,
        args: &Option<Vec<Expr>>,
        span: Span,
    ) -> R<DotResolution> {
        // A **type** subject, first: `A.unit`, `G.plus(x, y)`, `Nat.zero`
        // (docs/traits-type-projection-design.md). It is first because a type
        // is not a record and has no namespace member and is not a method
        // receiver, so nothing below could have read it — every reading it
        // takes was an error before this round, and every reading it declines
        // reaches its old handler untouched.
        if let Some(d) = self.type_projection(cx, recv, name, args, span)? {
            return Ok(d);
        }
        // The **index pseudo-projection** (`docs/operation-indexed-classes-
        // design.md` §5.2): `d.op` at `d: Monoid<A>(add)` is `add`, read off
        // the dictionary's type. Definitionally trivial, and it closes the
        // last "how do I refer to it" corner — anything that can name a
        // dictionary can name its index. Before the field path and harmless
        // there: a class cannot have a field named like its own index (the
        // record lowering refuses the collision), so the two never compete.
        if let ExprKind::Var(d) = &recv.kind
            && let Some(e) = self.index_of_dict(cx, d, name)
        {
            let (t, ty, lvl) = self.elab_infer(cx, &e)?;
            return Ok(DotResolution::Project(t, ty, lvl, None));
        }
        if self.record_fields.contains(name) {
            // Inference failure is not an error *here*: the fallback is what
            // handles a receiver whose type only the method call determines,
            // and reporting this failure would regress every such call.
            if let Ok((t, ty, lvl)) = self.elab_infer(cx, recv)
                && let Some(ind) = self.record_of_at(cx, &ty, span)
                && let Some(idx) = ind.field_index(name)
            {
                let (t, fty, flvl) =
                    self.project_field(cx, &ind, &ty, Rc::new(t), idx, span)?;
                let _ = lvl;
                let skel = skel_of_ty(&ind.ctors[0].fields[idx].1);
                return Ok(DotResolution::Project(t, fty, flvl, skel));
            }
        }
        let Some(args) = args else {
            // A bare `p.f` is never a method call — a call needs parentheses —
            // so there is nothing to fall back to. Name the receiver's actual
            // type, since the usual mistake is a receiver that is not the
            // record the writer had in mind.
            let what = match self.elab_infer(cx, recv) {
                Ok((_, ty, _)) => match self.record_of_at(cx, &ty, span) {
                    Some(ind) => format!("`{}` has no field `{name}`", ind.name),
                    None => format!("this is not a record, so it has no field `{name}`"),
                },
                // A failed **resolution** in the receiver is a diagnosis of
                // its own — the search, as data — and is better than anything
                // this branch could say about a field. `G::AddCommMonoid.f` at
                // a carrier with no instance is the spelling that produces one
                // (docs/traits-type-projection-design.md §5).
                Err(e @ ElabError::Resolution { .. }) => return Err(e),
                Err(_) => format!("no field `{name}` here (and the receiver's type \
                                   could not be inferred)"),
            };
            return err(what, span);
        };
        // The method desugaring: the receiver fills the callee's `self`
        // parameter, which defaults to the first explicit one
        // (issues/method-receiver-position.md). Implicit endpoints are still
        // inferred from it — insertion is name-directed and indifferent to
        // explicit-argument order, which is why the old receiver-last rule
        // was never doing the work its comment claimed.
        // Which name the call is to: the bare one, or a member of the
        // receiver's own type (issues/type-owned-members-receiver-slice.md).
        // The `member_bases` test comes first for the same reason the record
        // one does — no receiver is inferred for a name nobody attaches.
        let head = self.member_head(cx, recv, name, span)?;
        // Receiver dispatch through an instance
        // (docs/traits-receiver-dispatch-design.md §3). Last, so nothing that
        // resolved before this round can be reinterpreted by it: a class
        // member is only reached when the receiver's own type has no such
        // field and its namespace has no such member.
        //
        // `other` is what a *successful* dispatch would be racing (§4 rule 2)
        // and what a *failed* one falls back to (rule 5). The builtin list is
        // there because `map`/`fold`/… are Rust rather than declarations, so
        // `shadowed` cannot see them.
        let other: Option<(String, String)> = if head != name {
            Some((
                format!("`{head}`, a member of the receiver's own type"),
                format!("`{head}(…)`"),
            ))
        } else if self.shadowed(cx, name) || self.ctor_of(name).is_some() {
            Some((
                format!("`{name}`, a name in scope on its own"),
                format!("the bare call `{name}(…)` with the receiver as an argument"),
            ))
        } else if BUILTIN_METHODS.contains(&name) {
            Some((
                format!("`{name}`, a built-in method"),
                format!("the bare call `{name}(…)`"),
            ))
        } else {
            None
        };
        if let Some(d) = self.class_dispatch(cx, recv, name, other, args, span)? {
            return Ok(d);
        }
        let name = &head;
        let mut args = args.clone();
        let at = self.subject_index(name).min(args.len());
        args.insert(at, recv.clone());
        let head = Expr { kind: ExprKind::Var(name.to_string()), span };
        Ok(DotResolution::Method(Expr {
            kind: ExprKind::App { head: Box::new(head), args, explicit: false },
            span,
        }))
    }

    /// The callee of a method call, given the receiver: `name` itself, or
    /// `D::name` when the receiver's type `D` has a member by that name
    /// (issues/type-owned-members-receiver-slice.md).
    ///
    /// Evidence **shrinks** the candidate set and never races candidates. If
    /// both readings exist — an ambient `name` *and* a `D::name` at this
    /// receiver — the answer is an ambiguity naming both, not a preference.
    /// Preferring the member would mean that adding `D::name` to a library
    /// silently reinterprets an existing `t.name(…)`, which is the one thing
    /// the growth invariant forbids (docs/modules-design.md §4).
    fn member_head(&self, cx: &Cx, recv: &Expr, name: &str, span: Span) -> R<String> {
        if !self.member_bases.contains(name) {
            return Ok(name.to_string());
        }
        // Inference failure is not an error here, exactly as for a field: the
        // fallback is what handles a receiver whose type only the call fixes.
        let Ok((_, rty, _)) = self.elab_infer(cx, recv) else {
            return Ok(name.to_string());
        };
        let Some(owner) = self.type_namespace(cx, &rty, span) else {
            return Ok(name.to_string());
        };
        let qualified = format!("{owner}::{name}");
        match self.resolve_name(&qualified) {
            NameRes::Found(_) => {}
            // Two modules attaching the same member to the same type: the §4
            // regime's ambiguity, reported here rather than fallen back out
            // of — a receiver that *did* find candidates and cannot choose is
            // not a receiver that found none.
            NameRes::Ambiguous(_) => {
                return Err(self.name_miss(&qualified, String::new(), span))
            }
            // A restricted name falls back exactly as a missing one does: the
            // receiver's namespace is not where a generated member is
            // reached, and the field route above already ran
            // (docs/repr-access-spellings-design.md §3.2).
            NameRes::NotFound | NameRes::NoSuchQualifier(_) | NameRes::Restricted(_) => {
                return Ok(name.to_string())
            }
        }
        if self.shadowed(cx, name) {
            return err(
                format!(
                    "`{name}` here is both `{qualified}`, reached through the receiver's \
                     type, and a name in scope on its own — write one of them: \
                     `{qualified}(…)` for the member, or the bare call `{name}(…)` with \
                     the receiver as an argument"
                ),
                span,
            );
        }
        Ok(qualified)
    }

    /// `x.op(y)` where `op` is a class member and `x`'s type is a carrier with
    /// an instance (docs/traits-receiver-dispatch-design.md).
    ///
    /// One route for every carrier, because dispatch *is* a resolution goal:
    /// the goal `C<typeof(x)>` is built in kernel form (§2.1) and handed to
    /// layer 2's `resolve_goal`, so a concrete carrier is answered by the
    /// registry, a generic one by the `requires` binder in scope, and a
    /// derivable one by backchaining — with layer 2's own scope-beats-registry
    /// order inherited rather than re-decided.
    ///
    /// `None` is "this is not a dispatch", and every `None` leaves the method
    /// desugaring to run exactly as it did (§4 rule 5).
    fn class_dispatch(
        &self,
        cx: &Cx,
        recv: &Expr,
        name: &str,
        other: Option<(String, String)>,
        args: &[Expr],
        span: Span,
    ) -> R<Option<DotResolution>> {
        // The cheap negative test, before anything is inferred or resolved.
        if !self.class_members.contains(name) {
            return Ok(None);
        }
        // Inference failure is not an error here, exactly as for a field and
        // for a member: the fallback is what handles a receiver whose type
        // only the call fixes.
        let Ok((_, rty, rlvl)) = self.elab_infer(cx, recv) else {
            return Ok(None);
        };
        // Candidates: every class **visible here** (the ordinary §4 regime,
        // asked by resolving the class's own name) that **declares** this
        // field, with exactly one type parameter (§2.1), in sorted
        // canonical-name order — never `HashMap` order, and never declaration
        // order.
        //
        // *Declares*, and not "has": a class that merely inherits `name` never
        // said anything about it, so it is not a candidate at all — before any
        // instance is consulted (docs/traits-owner-dispatch-design.md §2). That
        // is what makes an inherited member dispatchable without a tiebreak,
        // and it leaves two *unrelated* declaring classes ambiguous, which is
        // the case §4 rule 3 exists for.
        let with_field = self.declaring_classes(name);
        let cands: Vec<(String, Rc<traits::ClassInfo>)> =
            with_field.iter().filter(|(_, i)| i.params.len() == 1).cloned().collect();
        if cands.is_empty() {
            // A multi-parameter class is refused *by name* rather than
            // mis-dispatched (§2.1): the receiver fixes the carrier and
            // nothing fixes the rest, and a goal with a meta in it is what
            // layer 2 §4 declines to resolve. Silent only when the call has
            // another reading to take (§4 rule 5).
            if let Some((_, info)) = with_field.first()
                && other.is_none()
            {
                return err(
                    format!(
                        "`{name}` is a member of `{}`, which takes {} type parameters: \
                         receiver dispatch builds its goal from the receiver alone, so it \
                         reaches a one-parameter class only — write the projection \
                         (`⟨instance⟩.{name}(…)`)",
                        info.name,
                        info.params.len()
                    ),
                    span,
                );
            }
            return Ok(None);
        }
        // What the trace calls the carrier. A display and never a key: an open
        // carrier has no nominal tag to name, and saying so beats rendering a
        // lowered type nothing can render totally (layer 2 §7).
        let carrier = self
            .type_namespace(cx, &rty, span)
            .unwrap_or_else(|| "the receiver's type".to_string());
        let mut trace: Vec<resolve::TraceLine> = Vec::new();
        let mut hits: Vec<(Rc<Inductive>, Type, Term, String, Upcast)> = Vec::new();
        let mut tried: Vec<String> = Vec::new();
        let mut unpinned: Option<ElabError> = None;
        for (_, info) in &cands {
            let Some(ind) = self.lookup_inductive(&info.name).cloned() else { continue };
            let targs = [(rty.clone(), rlvl.clone())];
            // An indexed class's goal has a value slot, and the ladder's step 2
            // is what fills it here (§5.1): scope, then refuse by name.
            let vargs = match self.index_vargs(cx, info, &ind, &targs, &carrier, span) {
                Ok(Some(v)) => v,
                Ok(None) => continue,
                Err(e) => {
                    unpinned.get_or_insert(e);
                    continue;
                }
            };
            let Ok((goal, glvl)) = self.lower_instance(cx, &ind, &targs, &vargs, span) else {
                continue;
            };
            let display = format!("{}<{carrier}>", info.name);
            tried.push(display.clone());
            let mut tr = Vec::new();
            // Every candidate is tried even once one has succeeded: the
            // ambiguity is the point, and a first hit would be a priority
            // (§4 rule 3).
            // `up` is the **upcast provenance** (`resolve_goal_from`): if this
            // goal is answered from a child dictionary, the child is what the
            // projection below reads from.
            let mut up = None;
            let found =
                self.resolve_goal_from(cx, &goal, &glvl, &display, span, &mut tr, &mut up);
            match found {
                Some(t) => hits.push((ind, goal, t, display, up)),
                None => trace.extend(tr),
            }
        }
        if hits.len() > 1 {
            let list = hits
                .iter()
                .map(|(_, _, _, d, _)| format!("`{d}`"))
                .collect::<Vec<_>>()
                .join(" and ");
            return err(
                format!(
                    "`{name}` at this receiver is a member of {list}, and each has an \
                     instance here — write the projection you meant \
                     (`⟨instance⟩.{name}(…)`) rather than letting the receiver choose"
                ),
                span,
            );
        }
        let Some((ind, goal, dict, display, up)) = hits.pop() else {
            // No candidate resolved. If the call has another reading, that
            // reading runs and this search is forgotten; if it has none, the
            // search *is* the diagnosis and is reported instead of the
            // "unknown name" the method desugaring would have produced.
            if other.is_some() {
                return Ok(None);
            }
            if let Some(e) = unpinned {
                return Err(e);
            }
            return Err(ElabError::Resolution {
                goal: tried.join("` or `"),
                span,
                trace,
            });
        };
        if let Some((desc, fix)) = other {
            return err(
                format!(
                    "`{name}` here is both a member of `{display}`, reached through the \
                     receiver's type, and {desc} — write one of them: \
                     `⟨instance⟩.{name}(…)` for the class member, or {fix} for the other"
                ),
                span,
            );
        }
        // An answer that came by **upcast** is read *through*: the field is the
        // child's own (docs/traits-named-upcast-design.md §2).
        let (ind, goal, dict) = self.through_upcast(ind, goal, dict, up, name);
        // Reported rather than asserted, though the candidate filter is what
        // just found this field: a library must not panic to say two of its own
        // tables disagree.
        let Some(idx) = ind.field_index(name) else {
            return err(
                format!("internal: `{}` has no field `{name}` after all", ind.name),
                span,
            );
        };
        let (t, fty, flvl) = self.project_field(cx, &ind, &goal, Rc::new(dict), idx, span)?;
        let skel = skel_of_ty(&ind.ctors[0].fields[idx].1);
        // The receiver is the field's **first explicit argument**: a class
        // field is a function type, not a declaration, so it has no `self`
        // marker to consult and takes the position `subject_index` defaults to
        // (issues/method-receiver-position.md).
        let mut all = Vec::with_capacity(args.len() + 1);
        all.push(recv.clone());
        all.extend(args.iter().cloned());
        Ok(Some(DotResolution::Dispatch(t, fty, flvl, skel, all)))
    }

    /// A dispatched projection reads **through** an upcast
    /// (`docs/traits-named-upcast-design.md` §2).
    ///
    /// Owner-keyed dispatch builds its goal at the class that *declares* the
    /// field, so at a child dictionary the resolver answers by step 1b with an
    /// assembled ancestor record and the projection would be
    /// `⟨C { f: d.f, … }⟩.f`. But that slot **is** `d.f` — it is what the
    /// assembly is made of — and the child has `f` in its own flattened field
    /// list at its own index (layer 1 §3). So the projection is taken from the
    /// child dictionary directly, and the assembled ancestor never enters the
    /// term.
    ///
    /// This is not a change to the *value*: the two are equal by β and
    /// projection, and the proposal has already passed the resolver's kernel
    /// gate (layer 2 §4.4) before it gets here. What it changes is the
    /// spelling the field's type is handed downstream in — the child's own
    /// components, rather than projections of a record literal that every later
    /// conversion has to reduce again. That residue *was* the cost
    /// `issues/upcast-assembly-cost-at-open-carriers.md` measured.
    ///
    /// A `None` provenance (every answer that is not an upcast) is the
    /// identity, which is what keeps this off every dispatch in the corpus that
    /// resolves exactly.
    fn through_upcast(
        &self,
        ind: Rc<Inductive>,
        goal: Type,
        dict: Term,
        up: Upcast,
        name: &str,
    ) -> (Rc<Inductive>, Type, Term) {
        // Reported by returning the input, not asserted: a child whose
        // flattened list has lost the field would mean the flattening and the
        // resolver disagree, and the identity is the answer that still checks.
        let Some((child_dict, child_ty)) = up else { return (ind, goal, dict) };
        let Some(child) = self.tag_of(&child_ty) else { return (ind, goal, dict) };
        if child.field_index(name).is_none() {
            return (ind, goal, dict);
        }
        (child, child_ty, child_dict)
    }

    /// The value-slot ladder's **step 2** at a goal the dot sugars are
    /// building (`docs/operation-indexed-classes-design.md` §5, §5.1): a
    /// binder in scope of the goal's class — or of a descendant, whose
    /// `extends` chain passes the index up unchanged — answers what the index
    /// is. Innermost first, exactly as the resolver's own scope pass.
    ///
    /// The index comes back as **surface** expressions at the goal's class, so
    /// the goal is built by the ordinary value-argument path and nothing here
    /// has to re-scope a kernel term. `None` is "no scope binder pins the
    /// slot", and its consumer refuses by name.
    fn scope_index(
        &self,
        cx: &Cx,
        target: &str,
        carrier: &Type,
        clvl: &Level,
    ) -> Option<Vec<Expr>> {
        let tkey = self.key_of(target)?;
        for d in cx.dicts.iter().rev() {
            let Some(dkey) = self.key_of(&d.class) else { continue };
            let Some(dinfo) = self.classes.get(&dkey) else { continue };
            let index = if dkey == tkey {
                d.index.clone()
            } else {
                // Not this binder's class and not one of its ancestors: try the
                // next binder out rather than giving up on the scope.
                let Some(anc) = dinfo
                    .ancestors
                    .iter()
                    .find(|r| self.key_of(&r.name).as_deref() == Some(tkey.as_str()))
                else {
                    continue;
                };
                // The ancestor's index is written in the child's own
                // value-parameter names (layer 1's `extends` restriction), so
                // instantiating it is the positional lookup.
                anc.index
                    .iter()
                    .map(|a| match &a.kind {
                        ExprKind::Var(n) => dinfo
                            .valparams
                            .iter()
                            .position(|p| p.name == *n)
                            .and_then(|i| d.index.get(i).cloned())
                            .unwrap_or_else(|| a.clone()),
                        _ => a.clone(),
                    })
                    .collect()
            };
            // The carrier has to be *this* one: a second class binder at an
            // unrelated type is not an answer.
            let Ok((dc, dlvl)) = self.elab_ty(cx, &d.carrier) else { continue };
            if !self.conv_types(cx, &dc, carrier, clvl) || dlvl != *clvl {
                continue;
            }
            return Some(index);
        }
        None
    }

    /// The value arguments of a dot sugar's goal
    /// (`docs/operation-indexed-classes-design.md` §5.1): empty at an
    /// unindexed class (every goal that predates this design), the scope
    /// binder's index at an indexed one, and the value-slot refusal where
    /// scope has no answer. `Ok(None)` is "this candidate cannot be built at
    /// all", which the caller skips as it always did.
    fn index_vargs(
        &self,
        cx: &Cx,
        info: &traits::ClassInfo,
        ind: &Inductive,
        targs: &[(Type, Level)],
        subject: &str,
        span: Span,
    ) -> Result<Option<Vec<(Term, Type, Level)>>, ElabError> {
        if info.valparams.is_empty() {
            return Ok(Some(Vec::new()));
        }
        let (carrier, clvl) = &targs[0];
        let Some(index) = self.scope_index(cx, &info.name, carrier, clvl) else {
            // The carrier's head where it has one: at `Bool` the refusal lists
            // the two Bool structures and not every instance of the class.
            let head = self.type_namespace(cx, carrier, span);
            return Err(self.value_slot_refusal(info, subject, head.as_deref(), span));
        };
        match self.valparam_args(cx, ind, targs, &index, span) {
            Ok(v) => Ok(Some(v)),
            Err(_) => Ok(None),
        }
    }

    /// Fill a blocked goal's **index slots** from a dictionary in scope
    /// (`docs/operation-indexed-classes-design.md` §5, ladder step 2).
    ///
    /// The goal's carrier is itself a scratch-world meta here, so the scope
    /// binder is chosen by class alone — innermost first, the goal's class or
    /// a descendant. That is a *proposal* and not a decision: the filled goal
    /// still has to resolve, and the answer still passes the kernel gate, so a
    /// wrong guess costs a refusal and never a wrong term.
    ///
    /// `true` when it filled at least one slot.
    fn fill_index_from_scope(
        &self,
        cx: &Cx,
        goal: Option<&Ty>,
        params: &[ParamMeta],
        slot_param: &[usize],
        sols: &mut [Sol],
    ) -> bool {
        let Some(r) = goal.and_then(|t| self.class_ref_of_ty(t)) else { return false };
        if r.index.is_empty() {
            return false;
        }
        let Some(tkey) = self.key_of(&r.name) else { return false };
        let mut filled = false;
        for a in &r.index {
            let ExprKind::Var(nm) = &a.kind else { continue };
            let Some(pi) = params.iter().position(|p| p.name == *nm) else { continue };
            let Some(slot) = slot_param.iter().position(|&s| s == pi) else { continue };
            if sols[slot].solved().is_some() || matches!(sols[slot], Sol::Withheld) {
                continue;
            }
            let Some(e) = self.scope_dict_index(cx, &tkey) else { continue };
            let Some(idx) = r.index.iter().position(|x| std::ptr::eq(x, a)) else { continue };
            let Some(e) = e.get(idx).cloned() else { continue };
            let Ok((t, _, _)) = self.elab_infer(cx, &e) else { continue };
            sols[slot] = Sol::Solved(Rc::new(t));
            filled = true;
        }
        filled
    }

    /// Fill a blocked goal's **index slots** from the designation table —
    /// the value-slot ladder's step 3
    /// (`docs/operation-indexed-classes-design.md` §5, built in
    /// `docs/operators-onto-classes-design.md` §5).
    ///
    /// This is what makes `sum_all(ns)` work at a caller who names no
    /// operation: `sum_all`'s constraint was written `<A: Monoid(+)>`, so its
    /// index binder carries the symbol `+`, the carrier is already pinned to
    /// `Nat` by the argument, and the table says `+` at `Nat` is `add`. The
    /// source is **named in the callee's signature** — this is not a search
    /// over instances and not a default: with no `(+)` written there is
    /// nothing here to consult.
    ///
    /// `true` when it filled at least one slot.
    fn fill_index_from_designation(
        &self,
        cx: &Cx,
        goal: Option<&Ty>,
        params: &[ParamMeta],
        slot_param: &[usize],
        sols: &mut [Sol],
        meta_doms: &[Type],
        n: u32,
        span: Span,
    ) -> bool {
        let Some(r) = goal.and_then(|t| self.class_ref_of_ty(t)) else { return false };
        if r.index.is_empty() {
            return false;
        }
        // Only a slot the callee designated is fillable, so decide that before
        // paying for the carrier.
        if !r.index.iter().any(|a| match &a.kind {
            ExprKind::Var(n) => traits::op_index_symbol(n).is_some(),
            _ => false,
        }) {
            return false;
        }
        let Some(head) = self.goal_carrier_head(cx, r.args.first(), params, slot_param, sols, span)
        else {
            return false;
        };
        let mut filled = false;
        for a in &r.index {
            let ExprKind::Var(nm) = &a.kind else { continue };
            let Some(sym) = traits::op_index_symbol(nm) else { continue };
            let Some(pi) = params.iter().position(|p| p.name == *nm) else { continue };
            let Some(slot) = slot_param.iter().position(|&s| s == pi) else { continue };
            if sols[slot].solved().is_some() || matches!(sols[slot], Sol::Withheld) {
                continue;
            }
            let Some(op) = self.designated(sym, &head) else { continue };
            // **Checked** against the slot's own domain, not inferred: the
            // designated operation is emitted bare (§3.2), so a generic one
            // — `append` at `List<B>` — has an element type that only the
            // domain can pin. The domain is the index binder's declared type
            // at the carrier this call solved, which is meta-free exactly
            // when the carrier is, and a failure here is a rung that did not
            // fire rather than an error.
            let Some(dom) = meta_doms.get(slot).and_then(|d| zonked(d, n, sols)) else { continue };
            let e = Expr { kind: ExprKind::Var(op), span };
            let Ok(t) = self.elab_check(cx, &e, &dom, &Level::Zero) else { continue };
            sols[slot] = Sol::Solved(Rc::new(t));
            filled = true;
        }
        filled
    }

    /// The head of a blocked goal's carrier, where the goal's *written* carrier
    /// is one of the callee's own type parameters and that parameter has
    /// already been solved. The one thing step 3 needs that scope's step 2 did
    /// not: a designation is keyed on the carrier, so the carrier has to be
    /// known before the table can be asked.
    ///
    /// A solved type-parameter slot holds the carrier's **code**, so `El` of it
    /// is the type and the kernel's own `El ⌜T⌝ ⇝ T` does the decoding — no
    /// second decoder, and nothing to drift.
    fn goal_carrier_head(
        &self,
        cx: &Cx,
        carrier: Option<&Ty>,
        params: &[ParamMeta],
        slot_param: &[usize],
        sols: &[Sol],
        span: Span,
    ) -> Option<String> {
        let TyKind::Named { name, args } = &carrier?.kind else { return None };
        if !args.is_empty() {
            return None;
        }
        // A carrier written concretely in the signature needs no lookup.
        if !params.iter().any(|p| p.name == *name) {
            return self.names_a_type(name).then(|| name.clone());
        }
        let pi = params.iter().position(|p| p.name == *name)?;
        let slot = slot_param.iter().position(|&s| s == pi)?;
        let code = sols[slot].solved()?;
        let ty = Type::El { level: Level::Zero, tm: Rc::clone(code) };
        self.type_namespace(cx, &ty, span)
    }

    /// The innermost dictionary in scope whose class is `tkey` or a descendant
    /// of it, with its index expressed **at that class**.
    fn scope_dict_index(&self, cx: &Cx, tkey: &str) -> Option<Vec<Expr>> {
        for d in cx.dicts.iter().rev() {
            let Some(dkey) = self.key_of(&d.class) else { continue };
            let Some(dinfo) = self.classes.get(&dkey) else { continue };
            if dkey == tkey {
                return Some(d.index.clone());
            }
            let Some(anc) =
                dinfo.ancestors.iter().find(|r| self.key_of(&r.name).as_deref() == Some(tkey))
            else {
                continue;
            };
            return Some(
                anc.index
                    .iter()
                    .map(|a| match &a.kind {
                        ExprKind::Var(nm) => dinfo
                            .valparams
                            .iter()
                            .position(|p| p.name == *nm)
                            .and_then(|i| d.index.get(i).cloned())
                            .unwrap_or_else(|| a.clone()),
                        _ => a.clone(),
                    })
                    .collect(),
            );
        }
        None
    }

    /// `d.op` — the index of a named dictionary in scope, as the expression
    /// its binder was written at (§5.2). `None` for every name that is not a
    /// dictionary binder and every `.f` that is not one of its class's
    /// indices, so an ordinary field projection is untouched.
    fn index_of_dict(&self, cx: &Cx, dict: &str, name: &str) -> Option<Expr> {
        let d = cx.dicts.iter().rev().find(|d| d.name == dict)?;
        let info = self.lookup_class(&d.class)?;
        let k = info.valparams.iter().position(|p| p.name == name)?;
        d.index.get(k).cloned()
    }

    /// The value-slot refusal (`docs/operation-indexed-classes-design.md` §5,
    /// §11): the slot, the class, and **every registered instance that would
    /// answer**, as data. This is the diagnostic the whole design leans on —
    /// at `Bool` it names both monoids with their indices, which is what makes
    /// refusing better than nominating.
    fn value_slot_refusal(
        &self,
        class: &traits::ClassInfo,
        subject: &str,
        head: Option<&str>,
        span: Span,
    ) -> ElabError {
        let Some(ckey) = self.key_of(&class.name) else {
            return ElabError::Elab { msg: format!("`{}` is not in scope", class.name), span };
        };
        let mut listed: Vec<String> = self
            .instances
            .iter()
            .filter(|((c, h, _), _)| *c == ckey && head.is_none_or(|k| h == k))
            .map(|(_, i)| format!("`{}`", i.written))
            .collect();
        listed.sort();
        let slots = class
            .valparams
            .iter()
            .map(|p| format!("`{}`", p.name))
            .collect::<Vec<_>>()
            .join(", ");
        // The designations at this carrier, where it has any
        // (docs/operators-onto-classes-design.md §6, §7). This is §11's polish
        // and it is the difference between a refusal reading as principled and
        // as obtuse: a designation cannot *fill* this slot — the dot sugar
        // names no symbol, and choosing among the symbols at a carrier would
        // be the nomination this whole design deletes — but naming the ones
        // that exist tells the reader, in one line, the binder that works.
        let desig = head.map(|h| self.designations_at(h)).unwrap_or_default();
        let fix = if desig.is_empty() {
            String::new()
        } else {
            format!(
                " Here {}: take the class as a constraint that names the symbol \
                 (`<A: {}({})>`), which is the spelling that pins the slot.",
                desig
                    .iter()
                    .map(|(s, op)| format!("`{s}` designates `{op}`"))
                    .collect::<Vec<_>>()
                    .join(" and "),
                class.name,
                desig[0].0
            )
        };
        ElabError::Elab {
            msg: format!(
                "the index {slots} of `{}` at `{subject}` is not pinned here: a value slot \
                 is filled by unification, by a binder in scope of the goal's class, or by \
                 a designation the binder names — and never by search, so nothing \
                 nominates and nothing guesses. Registered: {}.{fix} Write the dictionary \
                 you meant (`{subject}::{}(⟨index⟩).⟨field⟩`) or take the class as a \
                 constraint",
                class.name,
                if listed.is_empty() { "no instances".into() } else { listed.join(", ") },
                class.name
            ),
            span,
        }
    }

    // -- operator symbols ---------------------------------------------------

    /// The fixed name an operator symbol falls back to — the third rung of
    /// [`Self::resolve_op_name`] and the whole of what `+` meant before this
    /// round (docs/operators-onto-classes-design.md §4).
    ///
    /// This table *is* the parser desugaring it replaced, moved from
    /// `Parser::infix_op`'s first column to the resolver's last stop. That is
    /// the growth invariant, and it is structural rather than audited: a file
    /// with no designation for a symbol runs exactly this.
    fn op_fallback(sym: &str) -> Option<&'static str> {
        match sym {
            "+" => Some("add"),
            "*" => Some("mul"),
            "<=" => Some("Le"),
            // `Lt`, not `lt`: the row was written when nothing defined either
            // and the lowercase spelling was a guess. `std/nat` declares `Lt`
            // beside `Le`, and a relation is capitalized here for the same
            // reason `Le` is (issues/nat-order-kit.md, 2026-08-16).
            "<" => Some("Lt"),
            _ => None,
        }
    }

    /// §5.2's uniqueness rule, over the **symbol** namespace
    /// (docs/operators-onto-classes-design.md §5.1–§5.2, as
    /// issues/binder-symbol-as-notation.md amends them): a declaration installs
    /// each spelling once, by any mix of constraint symbol slots and `as`.
    ///
    /// Only the symbol half needs a new check. `as` mints no identifier — the
    /// binder keeps the name it would have had, which is the whole design — so
    /// the identifier half is the parameter-list checks that were already
    /// there, unchanged.
    fn check_symbol_free(installed: &[(String, String)], sym: &str, span: Span) -> R<()> {
        let Some((_, prev)) = installed.iter().find(|(s, _)| s == sym) else { return Ok(()) };
        // A constraint slot's binder is `#op∙@0_0` and unspellable, so it is
        // named by what wrote it rather than by the generated name.
        let by = match traits::op_index_symbol(prev) {
            Some(_) => format!("a constraint that named it (`<…: C({sym})>`)"),
            None => format!("`{prev} as {sym}`"),
        };
        err(
            format!(
                "`{sym}` is already this declaration's body spelling, installed by {by}: \
                 each spelling binds exactly one referent, so one declaration installs a \
                 symbol once — by a constraint's symbol slot or by `as`, not both \
                 (docs/operators-onto-classes-design.md §5.1). Pick a second symbol, or \
                 drop one of the two spellings"
            ),
            span,
        )
    }

    // The clause a diagnostic uses to say which of rung 2's two sources the
    // carrier came from (docs/bare-symbol-checking-carrier-design.md §6).
    const FROM_OPERAND: &'static str = "the carrier of its left operand";
    const FROM_EXPECTED: &'static str = "the carrier this position expects";

    /// The name an operator symbol means here — the three-rung ladder of
    /// docs/operators-onto-classes-design.md §4, as
    /// docs/bare-symbol-checking-carrier-design.md widens rung 2.
    ///
    /// `args` is the symbol's operand list, empty for a bare symbol between
    /// delimiters (`Monoid(+)`, `mconcat(++, xss)`). Rung 2 takes its carrier
    /// from the operand when there is one and from `expected` — the first
    /// domain of the type this **checking** position asks for — when there is
    /// not. Unapplied is not the same as carrier-less: in an *inference*
    /// position (`expected` is `None`) there is genuinely nothing to probe,
    /// and only rungs 1 and 3 can fire.
    fn resolve_op_name(
        &self,
        cx: &Cx,
        sym: &str,
        args: &[Expr],
        expected: Option<&Type>,
        span: Span,
    ) -> R<String> {
        // 1. A constraint binder that named the symbol. Innermost first, and
        //    before any type is looked at: inside `<A: Monoid(+)>` the `+` is
        //    the bound index and nothing else, at every carrier.
        if let Some((_, n)) = cx.op_locals.iter().rev().find(|(s, _)| s == sym) {
            return Ok(n.clone());
        }
        // 2. The designation at the carrier — the operand's, or the one this
        //    position expects. Probed only when the symbol has designations at
        //    all, so a file that declares none pays one failed lookup in a
        //    usually-empty map and no inference.
        //
        //    The two sources are exclusive, and this is the one place that
        //    says so: only a **bare** symbol reads the expected type. An
        //    applied one has an operand, which is the more specific evidence —
        //    the value the operation will be applied to, where the expected
        //    type is only what the surrounding position will accept — and
        //    admitting a second source there would put something new in the
        //    path of every operator expression that elaborates today
        //    (docs/bare-symbol-checking-carrier-design.md §4.2).
        let mut uncovered_carrier = None;
        if self.designations.keys().any(|(s, _)| s == sym) {
            let probed = if args.is_empty() {
                expected
                    .and_then(|t| self.expected_carrier_head(cx, t, span))
                    .map(|h| (h, Self::FROM_EXPECTED))
            } else {
                self.op_carrier_head(cx, args, span).map(|h| (h, Self::FROM_OPERAND))
            };
            if let Some((head, from)) = probed {
                if let Some(op) = self.designated(sym, &head) {
                    return Ok(op);
                }
                uncovered_carrier = Some((head, from));
            }
        }
        // 3. The symbol's fallback name, resolved as it always was. `&&`,
        //    `||` and `++` have no entry — they postdate the parser's fixed table, so
        //    there is no old desugaring for the growth invariant to preserve
        //    (issues/bool-operator-designations.md) — and refuse like a
        //    fallback whose name is missing, not like a symbol outside the
        //    grammar.
        let fb = Self::op_fallback(sym);
        if let Some(fb) = fb
            && (self.lookup_global(fb).is_some()
                || self.ctor_of(fb).is_some()
                || cx.names.iter().any(|n| n == fb)
                || cx.aliases.iter().any(|a| a.name == fb))
        {
            if let Some((head, from)) = &uncovered_carrier {
                let note = format!(
                    "`{sym}` has no designation at `{head}` ({from}), so it used its \
                     fallback name `{fb}`"
                );
                let mut notes = self.op_fallback_notes.borrow_mut();
                if !notes.contains(&note) {
                    notes.push(note);
                }
            }
            return Ok(fb.to_string());
        }
        // Reporting "unbound name `add`" would name something the writer
        // never typed. Say what *was* typed, and what would have to be
        // true for it to mean something.
        let mut known = self
            .designations
            .iter()
            .filter(|((s, _), _)| s == sym)
            .map(|((_, h), d)| format!("`{h}` (`{}`)", d.op))
            .collect::<Vec<_>>();
        known.sort();
        // The carrier rung 2 tried, where it got one from either source. Naming
        // it is the difference between "covers this carrier" — which names no
        // carrier at all — and a sentence the reader can check against the
        // table (docs/bare-symbol-checking-carrier-design.md §6).
        let tried = match &uncovered_carrier {
            Some((head, from)) => {
                format!("nothing designates `{sym}` at `{head}` — {from} —")
            }
            None => format!("no `designation {sym} at …` covers this carrier,"),
        };
        err(
            format!(
                "`{sym}` has no meaning here: no constraint binder named it \
                 (`<A: Monoid({sym})>`), {tried} and {}. {}",
                match fb {
                    Some(fb) => format!("its fallback name `{fb}` is not in scope"),
                    None => format!("`{sym}` has no fallback name"),
                },
                if known.is_empty() {
                    format!("`{sym}` designates nothing anywhere in this program")
                } else {
                    format!("`{sym}` designates something at {}", known.join(", "))
                }
            ),
            span,
        )
    }

    fn operator_fallback_note(&self) -> Option<String> {
        let notes = self.op_fallback_notes.borrow();
        (!notes.is_empty()).then(|| notes.join("; "))
    }

    /// The head of the carrier an operator application is at — rung 2's probe
    /// (docs/operators-onto-classes-design.md §4.1).
    ///
    /// Two rules, both load-bearing. It **descends the left spine** through
    /// operator applications to the leftmost non-operator leaf and infers that
    /// one: `a + b + c` is `(a + b) + c`, so naively inferring `args[0]` would
    /// re-infer the whole prefix at every rung and cost 2^d on a chain of
    /// length d, where the descent costs d. And it is a **proposal, never a
    /// decision**: a leaf that does not infer, or a head with no entry, falls
    /// through to the fallback rung, so a mis-probe costs a rung and never a
    /// wrong term. The speculative inference's goals are rolled back for the
    /// same reason.
    fn op_carrier_head(&self, cx: &Cx, args: &[Expr], span: Span) -> Option<String> {
        let mut leaf = args.first()?;
        loop {
            let ExprKind::App { head, args, .. } = &leaf.kind else { break };
            if !matches!(head.kind, ExprKind::OpSymbol(_)) {
                break;
            }
            match args.first() {
                Some(a) => leaf = a,
                None => break,
            }
        }
        if self.is_checking_only(cx, leaf) {
            return None;
        }
        let mark = self.goals.borrow().len();
        let inferred = self.elab_infer(cx, leaf);
        self.goals.borrow_mut().truncate(mark);
        let (_, ty, _) = inferred.ok()?;
        self.type_namespace(cx, &ty, span)
    }

    /// The head of the carrier a **checking position** is asking for — rung
    /// 2's second source (docs/bare-symbol-checking-carrier-design.md §3, §4).
    ///
    /// The expected type's **first domain**, which is where the left operand
    /// would have sat: at `A -> A -> A` with `A := List<B>` it is `List`. That
    /// is the same fact `op_carrier_head` gets by inferring an operand,
    /// arriving from the other side — and it costs no inference at all, since
    /// there is no operand to infer.
    ///
    /// A proposal like its applied twin, and declining is cheap: an expected
    /// type that is no `Π`, or a domain with no nominal head — a variable, a
    /// meta, `Type` — answers `None` through `type_namespace`, so a domain
    /// that still mentions an implicit needs no separate meta test, and the
    /// ladder simply goes on to the fallback rung.
    fn expected_carrier_head(&self, cx: &Cx, expected: &Type, span: Span) -> Option<String> {
        let Type::Pi { dom, .. } = self.whnf(cx, expected, span).ok()? else { return None };
        self.type_namespace(cx, &dom, span)
    }

    /// An operator symbol, bare or applied, rewritten to the ordinary
    /// application it means. `None` for every expression that is not one,
    /// which is every expression written before this round.
    ///
    /// A *rewrite* and not an elaboration arm on purpose: everything
    /// downstream — checking position, implicit insertion, spilling, the
    /// call diagnostics — is the path a written name already takes, and a
    /// symbol earns none of it separately. That is also what makes rung 2's
    /// checking-position source free of a second lesson: the name it produces
    /// is *checked* against `expected`, so a generic `append` gets its element
    /// type from the same domain the carrier came from
    /// (docs/operators-onto-classes-design.md §12.2).
    ///
    /// `expected` is the checking position's type where there is one, and
    /// `None` at the two inference sites.
    fn op_rewrite(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<Option<Expr>> {
        let (sym, args, explicit) = match &e.kind {
            ExprKind::OpSymbol(s) => (s, None, false),
            ExprKind::App { head, args, explicit } => match &head.kind {
                ExprKind::OpSymbol(s) => (s, Some(args), *explicit),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        let name =
            self.resolve_op_name(cx, sym, args.map_or(&[][..], |a| a), expected, e.span)?;
        let head = Expr { kind: ExprKind::Var(name), span: e.span };
        Ok(Some(match args {
            None => head,
            Some(args) => Expr {
                kind: ExprKind::App { head: Box::new(head), args: args.clone(), explicit },
                span: e.span,
            },
        }))
    }

    /// The classes that **declare** `name` — not the ones that merely inherit
    /// it — and are visible here, in sorted canonical-name order
    /// (docs/traits-owner-dispatch-design.md §2). Never `HashMap` order and
    /// never declaration order.
    ///
    /// "Visible here" is `key_of(C.name) == the key C is stored under`: the
    /// ordinary §4 name regime, asked by resolving the class's own name, and
    /// not a second visibility rule.
    fn declaring_classes(&self, name: &str) -> Vec<(String, Rc<traits::ClassInfo>)> {
        let mut with_field: Vec<(String, Rc<traits::ClassInfo>)> = self
            .classes
            .iter()
            .filter(|(k, info)| {
                info.fields
                    .iter()
                    .zip(&info.owner)
                    .any(|(f, o)| f.name.as_deref() == Some(name) && o.is_none())
                    && self.key_of(&info.name).as_deref() == Some(k.as_str())
            })
            .map(|(k, i)| (k.clone(), Rc::clone(i)))
            .collect();
        with_field.sort_by(|a, b| a.0.cmp(&b.0));
        with_field
    }

    /// The receiver read **as a type**, when it is one
    /// (docs/traits-type-projection-design.md §3.1). Two shapes, and they are
    /// exclusive by construction:
    ///
    /// - the receiver elaborates as a value whose type is a universe — a type
    ///   parameter `A`, or any binder at `Type<n>`; the carrier is `El` of
    ///   that code, which is what `lower_named` would have built for it;
    /// - the receiver does not elaborate as a value at all, but reads as a
    ///   type by shape (`Nat`, `Bool`, `Box<Z>`), through the same
    ///   [`expr_as_ty`] the universe round already uses.
    ///
    /// A value binder therefore **shadows** the type reading — `elab_infer`
    /// succeeds at a non-universe type and this answers `None` — which is what
    /// keeps a parameter named like a type from being reinterpreted.
    fn type_subject(&self, cx: &Cx, recv: &Expr, span: Span) -> Option<(Type, Level)> {
        match self.elab_infer(cx, recv) {
            Ok((tm, ty, _)) => {
                let Type::Ty(level) = self.whnf(cx, &ty, span).ok()? else { return None };
                Some((Type::El { level: level.clone(), tm: Rc::new(tm) }, level))
            }
            Err(_) => self.elab_ty(cx, &expr_as_ty(recv)?).ok(),
        }
    }

    /// `T.f` / `T.f(…)` where the subject is a **type**
    /// (docs/traits-type-projection-design.md): `A.unit`, `G.plus(x, G.zero)`,
    /// `Nat.zero`.
    ///
    /// The rule is receiver dispatch's with one word changed: the goal is
    /// built at the class that **declares** `f`, with the *subject itself* as
    /// the carrier rather than the subject's type, and the subject is
    /// therefore **not** an argument. So the emitted term is an ordinary field
    /// projection — the very term `⟨dictionary⟩.f` elaborates to — and a
    /// proof field (`A.unit_r(x)`) needs nothing of its own.
    ///
    /// `None` is "this is not a type projection", and every `None` leaves
    /// every older reading to run exactly as it did.
    fn type_projection(
        &self,
        cx: &Cx,
        recv: &Expr,
        name: &str,
        args: &Option<Vec<Expr>>,
        span: Span,
    ) -> R<Option<DotResolution>> {
        // The cheap negative test, before anything is inferred or lowered: a
        // `.f` where `f` is nobody's class field costs one hash lookup, which
        // is what keeps every program that predates classes at its old price.
        if !self.class_members.contains(name) {
            return Ok(None);
        }
        let Some((carrier, clvl)) = self.type_subject(cx, recv, span) else {
            return Ok(None);
        };
        let ns = self.type_namespace(cx, &carrier, span);
        let other = self.other_reading_of_a_type_subject(cx, &ns, name, args, span);
        let with_field = self.declaring_classes(name);
        let cands: Vec<(String, Rc<traits::ClassInfo>)> =
            with_field.iter().filter(|(_, i)| i.params.len() == 1).cloned().collect();
        if cands.is_empty() {
            // The multi-parameter refusal, verbatim from receiver dispatch
            // (§4 rule 7) and for the same reason: the subject fixes the
            // carrier and nothing fixes the rest.
            if let Some((_, info)) = with_field.first()
                && other.is_none()
            {
                return err(
                    format!(
                        "`{name}` is a member of `{}`, which takes {} type parameters: a type \
                         projection builds its goal from the subject alone, so it reaches a \
                         one-parameter class only — write the projection \
                         (`⟨instance⟩.{name}`)",
                        info.name,
                        info.params.len()
                    ),
                    span,
                );
            }
            return Ok(None);
        }
        // What the trace calls the subject: the text that was written, since
        // an open carrier has no nominal tag to name (layer 2 §7).
        let subject = subject_text(recv).or_else(|| ns.clone()).unwrap_or_else(|| "_".into());
        let mut trace: Vec<resolve::TraceLine> = Vec::new();
        let mut hits: Vec<(Rc<Inductive>, Type, Term, String, Upcast)> = Vec::new();
        let mut tried: Vec<String> = Vec::new();
        let mut unpinned: Option<ElabError> = None;
        for (_, info) in &cands {
            let Some(ind) = self.lookup_inductive(&info.name).cloned() else { continue };
            let targs = [(carrier.clone(), clvl.clone())];
            let vargs = match self.index_vargs(cx, info, &ind, &targs, &subject, span) {
                Ok(Some(v)) => v,
                Ok(None) => continue,
                Err(e) => {
                    unpinned.get_or_insert(e);
                    continue;
                }
            };
            let Ok((goal, glvl)) = self.lower_instance(cx, &ind, &targs, &vargs, span) else {
                continue;
            };
            let display = format!("{}<{subject}>", info.name);
            tried.push(display.clone());
            let mut tr = Vec::new();
            // Every candidate is tried even once one has succeeded: the
            // ambiguity is the point (§4 rule 3).
            let mut up = None;
            match self.resolve_goal_from(cx, &goal, &glvl, &display, span, &mut tr, &mut up) {
                Some(t) => hits.push((ind, goal, t, display, up)),
                None => trace.extend(tr),
            }
        }
        if hits.len() > 1 {
            let list =
                hits.iter().map(|(_, _, _, d, _)| format!("`{d}`")).collect::<Vec<_>>().join(" and ");
            return err(
                format!(
                    "`{name}` at `{subject}` is declared by {list}, and each has an instance \
                     here — write the class you meant (`{subject}::⟨class⟩.{name}`) rather \
                     than letting the type choose"
                ),
                span,
            );
        }
        let Some((ind, goal, dict, display, up)) = hits.pop() else {
            if other.is_some() {
                return Ok(None);
            }
            if let Some(e) = unpinned {
                return Err(e);
            }
            return Err(ElabError::Resolution { goal: tried.join("` or `"), span, trace });
        };
        if let Some((desc, fix)) = other {
            return err(
                format!(
                    "`{name}` here is both a member of `{display}`, reached through the type \
                     `{subject}`, and {desc} — write one of them: \
                     `{subject}::{}.{name}` for the class member, or {fix} for the other",
                    ind.name
                ),
                span,
            );
        }
        // As in receiver dispatch: an upcast answer is read through
        // (docs/traits-named-upcast-design.md §2).
        let (ind, goal, dict) = self.through_upcast(ind, goal, dict, up, name);
        let Some(idx) = ind.field_index(name) else {
            return err(format!("internal: `{}` has no field `{name}` after all", ind.name), span);
        };
        let skel = skel_of_ty(&ind.ctors[0].fields[idx].1);
        let (t, fty, flvl) = self.project_field(cx, &ind, &goal, Rc::new(dict), idx, span)?;
        Ok(Some(DotResolution::Project(t, fty, flvl, skel)))
    }

    /// What a `T.f(…)` would have meant if `T` were a value — the reading a
    /// successful type projection has to be named beside, and a failed one
    /// falls back to (docs/traits-type-projection-design.md §4).
    ///
    /// Two things make this narrower than receiver dispatch's `other`, and
    /// both are consequences of the subject being a **type**:
    ///
    /// - a **bare** `T.f` has no desugaring at all (a bare `p.f` is never a
    ///   method call), so it has no other reading, ever;
    /// - the desugaring puts the subject in the callee's *subject slot*, and a
    ///   type there is a reading only if that slot is **at a universe**. That
    ///   is read off the callee's own declared telescope — never by trying the
    ///   call — so this shrinks the candidate set the way owner-keying does
    ///   and is not a tiebreak. Undecidable (a builtin, a constructor, a
    ///   telescope that cannot be read) counts as a reading: the caution of
    ///   receiver-dispatch §7.2 belongs to exactly those.
    fn other_reading_of_a_type_subject(
        &self,
        cx: &Cx,
        ns: &Option<String>,
        name: &str,
        args: &Option<Vec<Expr>>,
        span: Span,
    ) -> Option<(String, String)> {
        args.as_ref()?;
        if let Some(t) = ns {
            let q = format!("{t}::{name}");
            if matches!(self.resolve_name(&q), NameRes::Found(_)) {
                return self.subject_slot_takes_a_type(cx, &q, span).then(|| {
                    (
                        format!("`{q}`, a member of `{t}`'s own namespace"),
                        format!("`{q}(…)`"),
                    )
                });
            }
        }
        if self.shadowed(cx, name) || self.ctor_of(name).is_some() {
            return self.subject_slot_takes_a_type(cx, name, span).then(|| {
                (
                    format!("`{name}`, a name in scope on its own"),
                    format!("the bare call `{name}(…)` with the type as an argument"),
                )
            });
        }
        BUILTIN_METHODS.contains(&name).then(|| {
            (format!("`{name}`, a built-in method"), format!("the bare call `{name}(…)`"))
        })
    }

    /// Can `name` take a **type** where the method desugaring would put the
    /// receiver? A purely syntactic walk of the callee's own Π-telescope to
    /// its subject slot: no elaboration, no trial call, no context of its own.
    ///
    /// `true` when the answer cannot be read off a declaration, which is the
    /// conservative direction — it makes the desugaring count as a reading and
    /// so makes the diagnostic name both.
    fn subject_slot_takes_a_type(&self, cx: &Cx, name: &str, span: Span) -> bool {
        let Ok((_, ty, _)) = self.resolve(cx, name, span) else { return true };
        let params = self.params_of(name);
        // Where the subject lands in *declaration* order. `subject_index`
        // counts explicit non-type parameters only, and the Π-telescope has
        // one domain per parameter in order, so this converts between the two.
        let mut pos = 0usize;
        if !params.is_empty() {
            let subj = self.subject_index(name);
            let mut seen = 0usize;
            let Some(i) = params.iter().position(|p| {
                if p.implicit || p.is_type {
                    return false;
                }
                let hit = seen == subj;
                seen += 1;
                hit
            }) else {
                // No such slot: the desugaring could not place the subject at
                // all, so it is not a reading.
                return false;
            };
            pos = i;
        }
        let mut cur = &ty;
        for _ in 0..pos {
            match cur {
                Type::Pi { cod, .. } => cur = cod,
                _ => return false,
            }
        }
        matches!(cur, Type::Pi { dom, .. } if matches!(**dom, Type::Ty(_)))
    }

    /// `G::AddCommMonoid` — the escape spelling: *the* `AddCommMonoid`
    /// dictionary at the type `G`, resolved rather than looked up
    /// (docs/traits-type-projection-design.md §5).
    ///
    /// Reached only from [`Self::resolve`]'s last stop, so it fires exactly
    /// where the answer would otherwise have been "unbound name". At a
    /// concrete carrier the qualified name is a registered global and never
    /// gets here, which is why `Nat::AddCommMonoid.plus` — the spelling the
    /// library already had — is untouched: this generalizes it to the carriers
    /// that have no global to name.
    /// `Nat::Monoid(add)` — the same spelling with the class's **index**
    /// (docs/operation-indexed-classes-design.md §5.1). An indexed class
    /// otherwise has no short dictionary spelling at a carrier with two
    /// structures, which is what discharges the projection round's
    /// "`T::C` takes no arguments" residue on `issues/traits.md`.
    fn class_at_type(
        &self,
        cx: &Cx,
        name: &str,
        index: &[Expr],
        span: Span,
    ) -> Option<R<(Term, Type, Level)>> {
        let (subject, class) = names::split_qual(name)?;
        let key = self.key_of(class)?;
        let info = Rc::clone(self.classes.get(&key)?);
        if info.params.len() != 1 || info.valparams.len() != index.len() {
            return None;
        }
        let ind = self.lookup_inductive(&info.name).cloned()?;
        let kind =
            if subject == "Nat" { TyKind::Nat } else { TyKind::Named { name: subject.into(), args: vec![] } };
        let (carrier, clvl) = self.elab_ty(cx, &Ty { kind, span }).ok()?;
        let targs = [(carrier, clvl)];
        // `Bool::Mon(+)` — the designation reference as a dictionary spelling
        // (docs/operation-indexed-classes-design.md §5.1, built in
        // docs/operators-onto-classes-design.md §4). This is the one argument
        // position where a bare symbol *does* have a carrier: the qualified
        // name wrote it. A symbol the table does not cover falls through to
        // the ordinary ladder, which reports it as written.
        let mut written: Vec<Expr> = Vec::with_capacity(index.len());
        for a in index {
            match &a.kind {
                ExprKind::OpSymbol(s) => match self.designated(s, subject) {
                    Some(op) => written.push(Expr { kind: ExprKind::Var(op), span: a.span }),
                    None => written.push(a.clone()),
                },
                _ => written.push(a.clone()),
            }
        }
        let vargs = match self.valparam_args(cx, &ind, &targs, &written, span) {
            Ok(v) => v,
            Err(e) => return Some(Err(e)),
        };
        let (goal, glvl) = self.lower_instance(cx, &ind, &targs, &vargs, span).ok()?;
        let display = format!(
            "{}<{subject}>{}",
            info.name,
            if index.is_empty() {
                String::new()
            } else {
                format!("({})", index.iter().map(traits::render_expr).collect::<Vec<_>>().join(", "))
            }
        );
        let mut tr = Vec::new();
        match self.resolve_goal(cx, &goal, &glvl, &display, span, &mut tr) {
            Some(t) => Some(Ok((t, goal, glvl))),
            None => Some(Err(ElabError::Resolution { goal: display, span, trace: tr })),
        }
    }

    /// A record literal (§6): permute the written fields into declaration
    /// order and hand the result to the ordinary tier-0 constructor path.
    /// Every diagnostic about *which* fields were written lives here, since
    /// the constructor path only ever sees a positional list.
    fn record_lit_args(
        &self,
        name: &str,
        fields: &[RecordLitField],
        span: Span,
    ) -> R<Vec<Expr>> {
        let Some(ind) = self.lookup_inductive(name) else {
            return Err(self.name_miss(name, format!("unknown type `{name}`"), span));
        };
        if !ind.is_record {
            return err(
                format!(
                    "`{name}` is an `inductive`, not a `record`: write a constructor \
                     application (`{}(…)`) rather than `{name} {{ … }}`",
                    ind.ctors.first().map(|c| c.name.as_str()).unwrap_or("…")
                ),
                span,
            );
        }
        let decl: Vec<&str> =
            ind.ctors[0].fields.iter().map(|(n, _)| n.as_deref().unwrap_or("_")).collect();
        let mut slots: Vec<Option<&Expr>> = vec![None; decl.len()];
        for f in fields {
            let Some(i) = decl.iter().position(|d| *d == f.name) else {
                return err(
                    format!("`{name}` has no field `{}` (it has: {})", f.name, decl.join(", ")),
                    f.span,
                );
            };
            if slots[i].is_some() {
                return err(format!("field `{}` is given twice", f.name), f.span);
            }
            slots[i] = Some(&f.expr);
        }
        let missing: Vec<&str> = decl
            .iter()
            .zip(&slots)
            .filter(|(_, s)| s.is_none())
            .map(|(d, _)| *d)
            .collect();
        if !missing.is_empty() {
            return err(
                format!("`{name}` literal is missing field(s): {}", missing.join(", ")),
                span,
            );
        }
        Ok(slots.into_iter().map(|s| s.expect("checked above").clone()).collect())
    }

    /// Explain a failed `let` annotation that turned out to name a **term**.
    ///
    /// `let p: a = b = pf;` used to parse as annotation `a = b`, binder `=`.
    /// The annotation position now suppresses the comparison rung
    /// (docs/let-and-blocks-design.md §3), so it parses as annotation `a`,
    /// binder `=`, value `b = pf` — and `a` is a term, whose only report from
    /// `elab_ty` is `unknown type \`a\``. That is diagnosable but says nothing
    /// about what actually happened, so this appends the spelling that works.
    /// Pass-through for every other failure.
    fn let_ty_hint(&self, cx: &Cx, t: &Ty, e: ElabError) -> ElabError {
        let TyKind::Named { name, args } = &t.kind else { return e };
        if !args.is_empty() || !self.shadowed(cx, name) {
            return e;
        }
        let ElabError::Elab { msg, span } = e else { return e };
        ElabError::Elab {
            msg: format!(
                "{msg} — `{name}` is a term, not a type. If this annotation was meant \
                 to be an equation, parenthesise it: `let p: ({name} = b) = pf;`, since \
                 an annotation does not extend across the `let`'s `=`"
            ),
            span,
        }
    }

    /// Is this name bound by something the user wrote? Builtins give way to
    /// locals, `let` aliases and declarations, so none of them is a keyword.
    fn shadowed(&self, cx: &Cx, name: &str) -> bool {
        cx.names.iter().any(|n| n == name)
            || cx.aliases.iter().any(|a| a.name == *name)
            || self.lookup_global(name).is_some()
            // The declaration's own name. It is not in `globals` until it is
            // checked, so without this a `fn map` could not recurse: its
            // self-call took the built-in vector-`map` path instead
            // (found writing docs/surface-polymorphism.md §9's headline test).
            || cx.selfref.as_ref().is_some_and(|s| s.name == name)
    }

    /// Does this name refer to a *type* here — a declared inductive/record, or
    /// a kernel type that has no declaration? Used only to check a member
    /// declaration's qualifier, so a false answer costs a rejection at the
    /// declaration and never a mis-resolution at a use.
    fn names_a_type(&self, name: &str) -> bool {
        // `True` for the same reason `Nat` is here: a kernel type (`Unit^0`)
        // claimed as a surface type name with no declaration behind it
        // (`inductive.rs`'s claim, issues/true-prop-trivial-hypotheses.md). A
        // file that declares its own `True` is answered by `lookup_inductive`
        // first, exactly as the claim itself is.
        self.lookup_inductive(name).is_some()
            || name == "Nat"
            || name == "Type"
            || name == "True"
    }

    /// Does this name refer to a **type former** — a global whose result, after
    /// every argument is supplied, is a universe? `Not : Π(P: Ty l). Ty l` and
    /// `Le : Π(n: Nat). Π(m: Nat). Ty 0` both answer yes.
    ///
    /// This is the *carrier-owner* half of an instance's canonical name
    /// (docs/traits-layer1-design.md §4.1, widened 2026-08-17). A carrier like
    /// `Le(n, m)` has a perfectly good head — `Le` — but `Le` names a `fn`
    /// rather than an inductive, so [`Self::names_a_type`] refused it and
    /// `Le::Decide` had nothing to attach to. The refusal was about the
    /// *namespace*, never about resolution: candidates are selected by trying
    /// each instance of the class against the goal (`resolve.rs`'s candidate
    /// loop), and the head never enters that search at all.
    ///
    /// Type formers and not merely *any* global, because the name has to keep
    /// meaning what it says: `Le::Decide` reads as "the `Decide` at `Le`", and
    /// that is only a sentence when `Le` is something a proposition can be *of*.
    /// A global returning `Nat` is not, and still refuses here.
    fn names_a_type_former(&self, name: &str) -> bool {
        let Some(info) = self.lookup_global(name) else { return false };
        let GlobalBinding::Tm { ty, .. } = &self.psi.bindings[info.abs as usize] else {
            return false;
        };
        // Peel arguments to the result. `UPi` is peeled too: a level-polymorphic
        // former is still a former, and its body is where the universe is.
        let mut t: &Type = ty;
        loop {
            match t {
                Type::Pi { cod, .. } => t = cod,
                Type::UPi { body, .. } => t = body,
                _ => return matches!(t, Type::Ty(_)),
            }
        }
    }

    /// The owner rule for a canonical instance name: a type, or a type former.
    /// One place, so `instance` and `designation` cannot drift apart on what a
    /// carrier is allowed to be.
    fn names_a_carrier(&self, name: &str) -> bool {
        self.names_a_type(name) || self.names_a_type_former(name)
    }

    /// The name of the declaration a lowered type belongs to — the type's own
    /// namespace, for a receiver-directed member lookup. `Nat` is a kernel
    /// type with no declaration and answers for itself; anything with no
    /// nominal tag has no namespace and answers `None`.
    fn type_namespace(&self, cx: &Cx, ty: &Type, span: Span) -> Option<String> {
        if matches!(ty, Type::Nat) {
            return Some("Nat".to_string());
        }
        if let Some(ind) = self.tag_of(ty) {
            return Some(ind.name.clone());
        }
        // Same fallback as `record_of_at`: a receiver whose type arrived
        // through a `Val -> Type` value is `El` of a redex, and the structural
        // read is deliberately context-free.
        let head = self.whnf(cx, ty, span).ok()?;
        if matches!(head, Type::Nat) {
            return Some("Nat".to_string());
        }
        self.tag_of(&head).map(|ind| ind.name.clone())
    }

    /// The constructor this name refers to *here* — `None` when it is not a
    /// constructor, or when a local binder or `let` alias shadows it.
    fn ctor_here(&self, cx: &Cx, name: &str) -> Option<(Rc<Inductive>, usize)> {
        if cx.names.iter().any(|n| n == name) || cx.aliases.iter().any(|a| a.name == *name) {
            return None;
        }
        self.ctor_of(name)
    }

    /// The declaration an expected type names, for the checking-position
    /// constructor route. A `Π` is peeled first: an **unsaturated**
    /// constructor is checked against the function type it η-expands into
    /// (docs/constructor-function-values.md §2), so the declaration is in the
    /// codomain, not the head.
    fn expected_ind(&self, expected: &Type) -> Option<Rc<Inductive>> {
        let mut ty = expected;
        while let Type::Pi { cod, .. } = ty {
            ty = cod;
        }
        self.tag_of(ty)
    }

    /// [`Self::ctor_here`], plus the **expected type** as evidence
    /// (docs/modules-design.md §4's follow-up, §8's one resolution judgment).
    ///
    /// In checking position the expected type already names the declaration,
    /// so a bare `None` at an expected `Option<A>` is that `Option`'s `None`
    /// whatever else is in scope — the same judgment a `match` arm already
    /// makes through the scrutinee ([`inductive::arm_ctor_index`], which this
    /// shares, so
    /// the `Option::None` spelling costs nothing extra here either).
    ///
    /// Strictly a **fallback**: the global reading is tried first, so a name
    /// that resolves today keeps resolving to the same declaration, and the
    /// expected type only ever *shrinks* a candidate set that the name layer
    /// left ambiguous — never reinterprets one it settled. That is §8's second
    /// invariant, and it is the reason this is sound to add to a library that
    /// is still growing: a new declaration can turn a bare constructor from
    /// unique into ambiguous, and here that is where it stops being an error,
    /// not where it starts meaning something else.
    ///
    /// The shadowing guard is repeated rather than inherited from the `None`
    /// branch above: a local binder beats a constructor at *any* expected
    /// type, and the type evidence must not buy that precedence back.
    ///
    /// [`Self::only_ctors_visible`] is the other half of "shrink, never
    /// reinterpret", and the reason this is not simply "ask the expected
    /// type when the name did not resolve": a name may fail to resolve *as a
    /// constructor* because it resolved to something else entirely, or
    /// because a **function** is one of the things it is ambiguous between —
    /// and a `fn None() -> Option<Nat>` is as admissible at an expected
    /// `Option<Nat>` as the constructor is, so the type is not evidence there
    /// at all. Those keep the reading they have today.
    fn ctor_here_expected(
        &self,
        cx: &Cx,
        name: &str,
        expected: &Type,
    ) -> Option<(Rc<Inductive>, usize)> {
        if let Some(hit) = self.ctor_here(cx, name) {
            return Some(hit);
        }
        if cx.names.iter().any(|n| n == name) || cx.aliases.iter().any(|a| a.name == *name) {
            return None;
        }
        if !self.only_ctors_visible(name) {
            return None;
        }
        // **Whnf first** (2026-08-16). The expected type reaches here in
        // whatever spelling its position had: a declared result type arrives
        // already structural, but a *parameter's* domain — which is what an
        // argument is checked against — can still be a reference that only
        // δ-unfolds to the lowering `tag_of` reads. Without this the route
        // fired for `theorem t(): Bool { False }` and stood down for
        // `idb(False)`, which is the same question asked twice
        // (issues/false-collides-with-bools-constructor.md). The cost is
        // confined to the fallback: this line is reached only after the
        // ordinary reading has already failed.
        // The span is only ever used for an out-of-fuel message, which this
        // discards along with every other failure — the route simply stands
        // down.
        let expected = self.whnf(cx, expected, Span { start: 0, end: 0 }).ok()?;
        let ind = self.expected_ind(&expected)?;
        let i = crate::inductive::arm_ctor_index(&ind, name)?;
        Some((ind, i))
    }

    /// Is every visible declaration of `name` a **constructor**?
    ///
    /// The precondition on the expected-type route. Reached only after the
    /// ordinary reading has already failed, so this is not asking "which
    /// declaration wins" — it is asking whether the type is allowed to be the
    /// tie-breaker at all, and it is allowed exactly when no candidate could
    /// have checked here *except* a constructor. One visible `fn` of the same
    /// name and the route stands down: that reading does not live in any
    /// declaration's constructor namespace and may well have the expected
    /// type, so picking the constructor over it would be a reinterpretation
    /// and not a shrink (docs/modules-design.md §8).
    ///
    /// **Amended 2026-08-16**: an `inductive`/`record` of the same name no
    /// longer stands the route down. See the body for the licence.
    ///
    /// Visibility is spelled out rather than taken from
    /// [`names::resolve`] because that function answers with *precedence*
    /// applied — a listed import or a local declaration hides the collision
    /// this has to see.
    fn only_ctors_visible(&self, name: &str) -> bool {
        let scopes = self.resolution_scopes.borrow();
        let scope = scopes.last().map(Rc::as_ref).unwrap_or(&self.scope);
        self.names.entries(name).iter().all(|e| {
            let visible = e.module == scope.module
                || scope.imports_module(&e.module)
                || e.module == names::PRELUDE_MODULE;
            // An `Inductive` candidate is admitted beside the constructors on
            // the same licence the whole route runs on. This function's caller
            // has already established that the expected type IS an inductive
            // (`expected_ind`), and a type *name* denotes a value whose type is
            // a universe — so that reading could never have checked here, and
            // dropping it is a shrink rather than a choice. A `Global` or a
            // `Meta` still stands the route down: a `fn` may perfectly well
            // return the expected type, so between it and a constructor there
            // is a real decision, and this route does not make those
            // (issues/false-collides-with-bools-constructor.md).
            !visible || matches!(e.kind, NameKind::Ctor | NameKind::Inductive)
        })
    }

    /// A constructor applied to its arguments, however the surface
    /// parenthesized them: `Cons(1, xs)` and `Cons(1)(xs)` flatten to the same
    /// `(declaration, index, arguments)`. Re-associating is sound because a
    /// constructor's function value *is* its η-expansion
    /// (docs/constructor-function-values.md §2), so the curried spelling is
    /// definitionally the saturated one — and flattening is what lets the
    /// curried spelling work in inference position, where the head alone
    /// (`Cons(1)`) has no type to infer.
    fn ctor_spine(&self, cx: &Cx, e: &Expr) -> Option<(Rc<Inductive>, usize, Vec<Expr>)> {
        let ExprKind::App { head, args, explicit } = &e.kind else { return None };
        if *explicit {
            return None;
        }
        match &head.kind {
            ExprKind::Var(name) => {
                let (ind, i) = self.ctor_here(cx, name)?;
                Some((ind, i, args.clone()))
            }
            ExprKind::App { .. } => {
                let (ind, i, mut prefix) = self.ctor_spine(cx, head)?;
                prefix.extend(args.iter().cloned());
                Some((ind, i, prefix))
            }
            _ => None,
        }
    }

    /// [`Self::ctor_spine`] with the expected type as evidence at the head,
    /// which is the only place a *name* appears: the arguments are checked
    /// against their field types downstream, and a curried spelling
    /// (`Cons(1)(xs)`) flattens before the head is read, so the expected type
    /// is the saturated result either way.
    fn ctor_spine_expected(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
    ) -> Option<(Rc<Inductive>, usize, Vec<Expr>)> {
        let ExprKind::App { head, args, explicit } = &e.kind else { return None };
        if *explicit {
            return None;
        }
        match &head.kind {
            ExprKind::Var(name) => {
                let (ind, i) = self.ctor_here_expected(cx, name, expected)?;
                Some((ind, i, args.clone()))
            }
            ExprKind::App { .. } => {
                let (ind, i, mut prefix) = self.ctor_spine_expected(cx, head, expected)?;
                prefix.extend(args.iter().cloned());
                Some((ind, i, prefix))
            }
            _ => None,
        }
    }

    /// A constructor used where nothing is checking it. Only possible when the
    /// declaration has no type parameters — otherwise there is nothing to
    /// determine the instantiation, and an annotation is required (§2:
    /// parameters are monomorphized, not inferred).
    fn infer_ctor(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        i: usize,
        args: &[Expr],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        // Type arguments are recovered only from a field whose type *is* a
        // parameter (`Some(A)`), by inferring that argument. Deliberately
        // narrow: anything deeper is unification, which belongs to
        // issues/elab-unifier-completeness.md, not here. A `None` on its own
        // is genuinely ambiguous and says so.
        // Value parameters are **not** inferred, by decision rather than by
        // omission (docs/surface-value-parameters.md §4, closing
        // `docs/surface-existential-investigation.md` §C.5): a parameter
        // appears only inside a *field type*, so recovering it from the
        // arguments is higher-order unification, not the narrow
        // field-type-is-a-parameter reading below. Checking position supplies
        // them; nothing else does.
        if !ind.valparams.is_empty() {
            return err(
                format!(
                    "cannot infer the value argument(s) of `{}` here — a value parameter \
                     appears only inside a field's type, so nothing in `{}(…)` determines \
                     it. Put the expression in a checking position: a `fn`/`theorem` \
                     body whose declared result is `{}(…)`, or an argument of a \
                     declaration that expects one",
                    ind.name, ind.name, ind.name
                ),
                span,
            );
        }
        let mut sols: Vec<Option<(Type, Level)>> = vec![None; ind.params.len()];
        for (f, arg) in self.ctor_fields(ind, i).iter().zip(args) {
            let TyKind::Named { name, args: targs } = &f.kind else { continue };
            if !targs.is_empty() {
                continue;
            }
            let Some(p) = ind.params.iter().position(|p| p == name) else { continue };
            if sols[p].is_none() {
                let (_, ty, lvl) = self.elab_infer(cx, arg)?;
                sols[p] = Some((ty, lvl));
            }
        }
        let mut targs = Vec::with_capacity(sols.len());
        for (p, sol) in ind.params.iter().zip(sols) {
            let Some(sol) = sol else {
                // A **child** argument determines the whole instance, and
                // determines it without recovering the instantiation at all:
                // its type *is* the family, at another index. `Node(n, m, l,
                // r)`'s `l : Tree<A>(n)` is `Σ(s : ⟦Skel<A>⟧). sEq(…)` with the
                // parameters already lowered into it, so re-indexing that type
                // is exactly the type `Node` builds
                // (docs/inductive-fording-lowering.md §14.7).
                //
                // Deliberately not the general case: a parameter that occurs
                // only *under* a field's type constructor (`xs: [A; n]`) still
                // needs unification, which is
                // issues/elab-unifier-completeness.md's and not this function's.
                if let Some(r) = self.ctor_from_child(cx, ind, i, args, span) {
                    return r;
                }
                return err(
                    format!(
                        "cannot infer the type argument `{p}` of `{}` here — no argument \
                         of `{}` determines it. Two ways out: put the expression in a \
                         checking position (a `fn`/`theorem` body whose declared result \
                         is `{}<…>(…)`, or an argument of a declaration that expects \
                         one), or write the type argument (`{}<…>(…)`)",
                        ind.name,
                        ind.ctors[i].name,
                        ind.name,
                        ind.ctors[i].name
                    ),
                    span,
                );
            };
            targs.push(sol);
        }
        let (ty, lvl) = if ind.skel.is_some() && args.len() == ind.ctors[i].fields.len() {
            // Route 2b: the index is the constructor's *written* result index
            // at the arguments it was given (docs/inductive-fording-lowering.md
            // §2), which is the whole widening.
            let (idx, _, _) = self.forded_ctor_index(cx, ind, i, args, span)?;
            self.lower_forded_instance(cx, ind, &targs, idx, span)?
        } else if ind.index.is_some() && args.len() == ind.ctors[i].fields.len() {
            // The result index comes from the pattern and the written index
            // argument (docs/inductive-indexed-lowering.md §5); the wrong-
            // arity case falls through to `build_ctor`'s arity message.
            let (idx, _, _) = self.indexed_ctor_index(cx, ind, i, args, span)?;
            self.lower_indexed_instance(cx, ind, &targs, idx, span)?
        } else {
            self.lower_instance(cx, ind, &targs, &[], span)?
        };
        let t = self.build_ctor(cx, ind, i, args, &ty, &lvl, span)?;
        Ok((t, ty, lvl))
    }

    /// A constructor of an **indexed** family whose type-parameter
    /// instantiation is determined by a *child* argument
    /// (`docs/inductive-fording-lowering.md` §14.7, and route 1's same gap).
    ///
    /// The child's inferred type is the family at the child's own index, and
    /// both routes keep the family in a form that can be re-applied at another
    /// index — `FordedFam::ty_at` and `IndexedFam::el_at`, which is what
    /// `match` uses to name `fam 0` and `fam (S m)` from one read-back type. So
    /// there is nothing to *solve*: the instance comes back whole and the
    /// written result index says where to put it. `None` when no argument is a
    /// child, or when the first child's type is not this family.
    fn ctor_from_child(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        i: usize,
        args: &[Expr],
        span: Span,
    ) -> Option<R<(Term, Type, Level)>> {
        if ind.index.is_none() || args.len() != ind.ctors[i].fields.len() {
            return None;
        }
        let k = ind.ctors[i].kind.iter().position(|f| *f == inductive::FieldKind::Plain)?;
        let (_, cty, _) = self.elab_infer(cx, &args[k]).ok()?;
        let (ty, lvl) = if ind.skel.is_some() {
            let (found, fam) = self.forded_of_at(cx, &cty)?;
            if found.tag != ind.tag {
                return None;
            }
            let idx = match self.forded_ctor_index(cx, ind, i, args, span) {
                Ok((idx, _, _)) => idx,
                Err(e) => return Some(Err(e)),
            };
            (fam.ty_at(idx, 0), fam.lvl())
        } else {
            let (found, fam) = self.indexed_of_at(cx, &cty)?;
            if found.tag != ind.tag {
                return None;
            }
            let idx = match self.indexed_ctor_index(cx, ind, i, args, span) {
                Ok((idx, _, _)) => idx,
                Err(e) => return Some(Err(e)),
            };
            (fam.el_at(idx, 0), fam.level.clone())
        };
        Some(
            self.build_ctor(cx, ind, i, args, &ty, &lvl, span)
                .map(|t| (t, ty, lvl)),
        )
    }

    // -- application (explicit + implicit spines) ---------------------------

    /// The implicit-parameter mask of a callable global (empty for locals,
    /// builtins, and unknown names — none of which take implicits).
    fn implicit_mask(&self, name: &str) -> Vec<bool> {
        self.params_of(name).iter().map(|p| p.implicit).collect()
    }

    /// Where a method call's receiver goes in the *explicit* argument list:
    /// the position of the `self`-marked parameter among the explicit,
    /// non-type-variable ones, or `0` when nothing is marked.
    ///
    /// Counting over explicit parameters only is the whole subtlety. The
    /// receiver is inserted into the surface argument list, which is what the
    /// writer typed — implicits are filled later, by the name-directed mask
    /// ([`Self::implicit_mask`]), and type arguments are never passed at all
    /// (issues/at-and-type-arguments.md). So a `self` sitting behind two
    /// `{}`-implicits is still explicit-index 0.
    ///
    /// Unmarked is `0` rather than "no method call", so every declaration
    /// that predates the marker keeps working and a one-premise lemma never
    /// has to write it (issues/method-receiver-position.md).
    fn subject_index(&self, name: &str) -> usize {
        self.params_of(name)
            .iter()
            .filter(|p| !p.implicit && !p.is_type)
            .position(|p| p.is_self)
            .unwrap_or(0)
    }

    /// The parameters of a callable global, for defaulting goal names.
    fn params_of(&self, name: &str) -> Rc<Vec<ParamMeta>> {
        match self.lookup_global(name) {
            Some(GlobalInfo { params, .. }) => Rc::clone(params),
            None => Rc::new(Vec::new()),
        }
    }

    /// The arity branch of a builtin vector method, which cannot say what it
    /// is about until it has looked at the receiver
    /// (issues/receiver-method-shadows-record-field.md).
    ///
    /// These builtins all open with `elab_infer` on the receiver, so a
    /// receiver whose type does not infer can never reach one of them — but
    /// the arity test runs *first*, and used to announce "on a vector
    /// receiver" about a receiver nobody had read. At a record with a field
    /// named `fold`, reached off a receiver that needs a motive, that made
    /// the elaborator assert something false in place of the one diagnostic
    /// the writer could act on.
    ///
    /// So the order here is the order the body would have taken anyway, and
    /// the wrong-arity message is uttered only where it is true. The receiver
    /// failing to infer is its own diagnosis and is returned as-is: it is
    /// exactly what the writer gets when the arity is *right*, so the two
    /// paths no longer disagree about the same receiver.
    fn vec_method_arity_err<T>(
        &self,
        cx: &Cx,
        args: &[Expr],
        name: &str,
        shape: &str,
        span: Span,
    ) -> R<T> {
        let [recv, ..] = args else {
            // No receiver at all — the direct spelling `fold()`, since the dot
            // always supplies one. Nothing to read, but nothing is being
            // guessed either: these builtins *are* the vector eliminators, so
            // what they require is a fact about them rather than a claim about
            // some receiver.
            return err(format!("`{name}` needs a vector receiver"), span);
        };
        let (_, ty, _) = self.elab_infer(cx, recv)?;
        if !matches!(*crate::inductive::decoded(&ty), Type::Vec { .. }) {
            return err(format!("`{name}`'s receiver has to be a vector"), span);
        }
        err(format!("`{name}` takes {shape} on a vector receiver"), span)
    }

    /// `xs.map(f)`. Two forms, and the split is what
    /// `docs/container-fields.md` §4.2 is about:
    ///
    /// - `f` is an ordinary function: the `elim_Nat` schema `vec::map`.
    /// - `f` is the **self-name** and `xs` the enclosing arm's container
    ///   binder: the induction hypothesis, *tabulated* over the container's
    ///   index range. It cannot be the first form, because the self-name is
    ///   not a value — there is no fixpoint, and the recursive call exists
    ///   only as the eliminator's ih (issues/match-recursion.md).
    fn elab_vec_map(
        &self,
        cx: &Cx,
        f: &Expr,
        xs: &Expr,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let (xs_t, xs_ty, _) = self.elab_infer(cx, xs)?;
        // `decoded`, not `whnf`: the receiver may be a vector *field* projected
        // out of a record that arrived as a code, in which case its type is
        // `El (TmVec …)` (docs/record-type-values.md §6). Reducing further
        // would unfold the `Vec` into its Σ-chain and lose the element type
        // and the length this reads off it — the same reason `elab_vec_lit`
        // decodes rather than normalizes.
        let xs_ty = &*crate::inductive::decoded(&xs_ty);
        let Type::Vec { level: al, elem: a_ty, len } = xs_ty else {
            return err("`map`'s receiver has to be a vector", span);
        };
        // The self-call form.
        if let ExprKind::Var(name) = &f.kind
            && cx.selfref.as_ref().is_some_and(|s| s.name == *name)
        {
            return self.elab_container_ih(cx, name, &xs_t, false, span);
        }
        let (f_t, f_ty, _) = self.elab_infer(cx, f)?;
        let Type::Pi { cod_level: bl, dom, cod, .. } = self.whnf(cx, &f_ty, span)? else {
            return err("`map`'s argument has to be a function", span);
        };
        let Some(b_ty) = vec::strengthen(&cod, &cx.gamma) else {
            return err(
                "`map`'s function must not have a dependent result type: the result \
                 is a vector, whose elements all have one type",
                span,
            );
        };
        let _ = dom;
        // The evaluation hook (docs/in-language-map-design.md §4): when a
        // template claims `vec.map`, the emitted term comes from evaluating it
        // — kernel computation mid-elaboration — and the Rust schema below
        // serves the instances the level-0 template declines, and every file
        // that declares no template at all. What this site knows is the slot
        // and the *names* of its ingredients; the Π order is the template's
        // own and lives in its signature
        // (docs/meta-def-registration-design.md §3).
        if let Some(t) = self.try_code_template(
            cx,
            Slot::VecMap,
            &[
                ("A", Ingredient::Type { level: al, ty: a_ty }),
                ("B", Ingredient::Type { level: &bl, ty: &b_ty }),
                ("f", Ingredient::Term(f_t.clone())),
                ("k", Ingredient::Term((**len).clone())),
                ("v", Ingredient::Term(xs_t.clone())),
            ],
            span,
        )? {
            return Ok((
                t,
                Type::Vec { level: bl.clone(), elem: Rc::new(b_ty), len: Rc::clone(len) },
                bl,
            ));
        }
        Ok((
            vec::map(al, &bl, a_ty, &b_ty, len, Rc::new(f_t), Rc::new(xs_t)),
            Type::Vec {
                level: bl.clone(),
                elem: Rc::new(b_ty),
                len: Rc::clone(len),
            },
            bl,
        ))
    }

    /// `head(v)` / `tail(v)` on a vector whose length reduces to a successor:
    /// the projections of the `Σ` that `Vec(A; S k)` computes to, annotated
    /// with its components. A neutral length is a diagnostic — there is no
    /// projection out of a vector that might be empty.
    fn elab_vec_head_tail(
        &self,
        cx: &Cx,
        v: &Expr,
        is_head: bool,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let (v_t, v_ty, _) = self.elab_infer(cx, v)?;
        // `decoded`, as in `elab_vec_map`: a coded `Vec` field is one.
        let v_ty = &*crate::inductive::decoded(&v_ty);
        let Type::Vec { level, elem, len } = v_ty else {
            let name = if is_head { "head" } else { "tail" };
            return err(format!("`{name}`'s receiver has to be a vector"), span);
        };
        let len_w = self.whnf_tm(cx, len, span)?;
        let Term::Succ(pred) = &*len_w else {
            let name = if is_head { "head" } else { "tail" };
            return err(
                format!(
                    "`{name}` needs a vector whose length reduces to a successor — \
                     this one's does not, so it might be empty"
                ),
                span,
            );
        };
        // `Vec(A; S k) ⇝ Σ(x: A). Vec(A↑; k↑)` — the Σ annotations, exactly
        // as `reduce.rs` spells the reduct.
        let snd_ty = Rc::new(Type::Vec {
            level: level.clone(),
            elem: Rc::new(elem.shift_local(1)),
            len: Rc::new(pred.shift_local(1)),
        });
        let (term, ty) = if is_head {
            (
                Term::Fst {
                    fst_level: level.clone(),
                    snd_level: level.clone(),
                    fst_ty: Rc::clone(elem),
                    snd_ty,
                    pair: Rc::new(v_t),
                },
                (**elem).clone(),
            )
        } else {
            (
                Term::Snd {
                    fst_level: level.clone(),
                    snd_level: level.clone(),
                    fst_ty: Rc::clone(elem),
                    snd_ty,
                    pair: Rc::new(v_t),
                },
                // `snd_ty[fst p/x]` — no dependence, so the unshifted spelling.
                Type::Vec {
                    level: level.clone(),
                    elem: Rc::clone(elem),
                    len: Rc::clone(pred),
                },
            )
        };
        Ok((term, ty, level.clone()))
    }

    /// `cons(h, t)`: the pair of the same `Σ`, inferring from the tail (which
    /// carries both the element type and the length).
    fn elab_vec_cons(&self, cx: &Cx, h: &Expr, t: &Expr, span: Span) -> R<(Term, Type, Level)> {
        let (t_t, t_ty, _) = self.elab_infer(cx, t)?;
        let t_ty = &*crate::inductive::decoded(&t_ty);
        let Type::Vec { level, elem, len } = t_ty else {
            return err("`cons`'s second argument has to be a vector (the tail)", span);
        };
        let h_t = self.elab_check(cx, h, elem, level)?;
        let snd_ty = Rc::new(Type::Vec {
            level: level.clone(),
            elem: Rc::new(elem.shift_local(1)),
            len: Rc::new(len.shift_local(1)),
        });
        Ok((
            Term::Pair {
                fst_level: level.clone(),
                snd_level: level.clone(),
                fst_ty: Rc::clone(elem),
                snd_ty,
                fst: Rc::new(h_t),
                snd: Rc::new(t_t),
            },
            Type::Vec {
                level: level.clone(),
                elem: Rc::clone(elem),
                len: Rc::new(Term::Succ(Rc::clone(len))),
            },
            level.clone(),
        ))
    }

    /// `xs.fold(init, f)` for `f : A → B → B`. A right fold: `[a, b]` folds to
    /// `f a (f b init)`, which is the direction that computes on a
    /// constructor form.
    fn elab_vec_fold(
        &self,
        cx: &Cx,
        z: &Expr,
        f: &Expr,
        xs: &Expr,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let (xs_t, xs_ty, _) = self.elab_infer(cx, xs)?;
        // As in `elab_vec_map`: decode a coded `Vec`, and no further.
        let xs_ty = &*crate::inductive::decoded(&xs_ty);
        let Type::Vec { level: al, elem: a_ty, len } = xs_ty else {
            return err("`fold`'s receiver has to be a vector", span);
        };
        let (z_t, b_ty, bl) = self.elab_infer(cx, z)?;
        let step_ty = Type::Pi {
            dom_level: al.clone(),
            cod_level: bl.clone(),
            dom: Rc::clone(a_ty),
            cod: Rc::new(Type::Pi {
                dom_level: bl.clone(),
                cod_level: bl.clone(),
                dom: Rc::new(b_ty.shift_local(1)),
                cod: Rc::new(b_ty.shift_local(2)),
            }),
        };
        let f_t = self.elab_check(cx, f, &step_ty, &Level::max(al.clone(), bl.clone()))?;
        // The evaluation hook, as in `elab_vec_map`: whichever template claims
        // `vec.fold` serves this use site, and the Rust schema below serves the
        // instances the level-0 template declines — and every file that
        // declares no template (issues/quotation-stage-artifacts.md).
        if let Some(t) = self.try_code_template(
            cx,
            Slot::VecFold,
            &[
                ("A", Ingredient::Type { level: al, ty: a_ty }),
                ("B", Ingredient::Type { level: &bl, ty: &b_ty }),
                ("z", Ingredient::Term(z_t.clone())),
                ("f", Ingredient::Term(f_t.clone())),
                ("k", Ingredient::Term((**len).clone())),
                ("v", Ingredient::Term(xs_t.clone())),
            ],
            span,
        )? {
            return Ok((t, b_ty, bl));
        }
        Ok((
            vec::fold(al, &bl, a_ty, &b_ty, len, Rc::new(z_t), Rc::new(f_t), Rc::new(xs_t)),
            b_ty,
            bl,
        ))
    }

    /// `xs[i]` — the kernel's `nth` schema
    /// (docs/surface-fin-indexing-design.md §5.2). Modelled on
    /// [`Self::elab_vec_fold`], and inferring rather than checking: the
    /// element type comes off the receiver.
    ///
    /// The index is **checked** at `Fin(len)` with the receiver's own length,
    /// which is what makes an index of the wrong vector's length a diagnostic
    /// rather than a silent coercion.
    fn elab_vec_nth(
        &self,
        cx: &Cx,
        recv: &Expr,
        idx: &Expr,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let (xs_t, xs_ty, _) = self.elab_infer(cx, recv)?;
        // As in `elab_vec_map`: decode a coded `Vec`, and no further.
        let xs_ty = &*crate::inductive::decoded(&xs_ty);
        let Type::Vec { level: vl, elem, len } = xs_ty else {
            return err("an index needs a vector receiver", span);
        };
        let idx_t =
            self.elab_check(cx, idx, &Type::Fin { len: Rc::clone(len) }, &Level::Zero)?;
        // The evaluation hook, as in `elab_vec_map`/`elab_vec_fold`:
        // `lib/vec_code.hthr`'s `nth_code` claims `vec.nth` when the lib is in
        // scope, and this declines silently when it is not. The kernel schema
        // stays the oracle and the fallback either way.
        if let Some(t) = self.try_code_template(
            cx,
            Slot::VecNth,
            &[
                ("A", Ingredient::Type { level: vl, ty: elem }),
                ("k", Ingredient::Term((**len).clone())),
                ("v", Ingredient::Term(xs_t.clone())),
                ("i", Ingredient::Term(idx_t.clone())),
            ],
            span,
        )? {
            return Ok((t, (**elem).clone(), vl.clone()));
        }
        Ok((
            nth(vl, elem, len, Rc::new(xs_t), Rc::new(idx_t)),
            (**elem).clone(),
            vl.clone(),
        ))
    }

    /// The self-call over a container binder: `tabulate(len, λ(i : Fin len).
    /// ih (inr^m i))` (`docs/container-fields.md` §4.2).
    ///
    /// The ih is indexed by `Fin (Succ^m len)` — `m` plain children first,
    /// then the container's — so the index map is `m` `inr`s.
    fn elab_container_ih(
        &self,
        cx: &Cx,
        name: &str,
        xs: &Term,
        as_eq: bool,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let Some(g) = cx.guard.clone() else {
            return err(
                format!(
                    "recursive call to `{name}` is not structurally guarded: it must occur \
                     inside a `match` on one of `{name}`'s own parameters"
                ),
                span,
            );
        };
        let GuardKind::Wf { depth, container: Some(c), .. } = &g.kind else {
            return err(
                format!("the enclosing `match` arm of `{name}` has no container field"),
                span,
            );
        };
        let by = (cx.names.len() - depth) as u32;
        if c.term.shift_local(by) != *xs {
            return err(
                format!(
                    "a recursive call to `{name}` over a vector has to be over the \
                     container field bound by the enclosing `match`"
                ),
                span,
            );
        }
        // The two spellings are not interchangeable: `.map` produces data and
        // `.cong` produces a proof, so each is rejected where the other belongs
        // (docs/container-proofs.md §6).
        if as_eq && c.result.is_some() {
            return err(
                format!(
                    "`{name}`'s result type does not depend on its argument, so a                      recursive call over a container produces a vector of results,                      not an equation between two: write `.map({name})`"
                ),
                span,
            );
        }
        if !as_eq && c.eq.is_some() {
            return err(
                format!(
                    "`{name}` proves an equation, so a recursive call over a container                      proves the two children vectors equal rather than producing one:                      write `.cong({name})` (docs/container-proofs.md §6)"
                ),
                span,
            );
        }
        if c.result.is_none() && c.eq.is_none() {
            return err(
                format!(
                    "recursing over a container field needs `{name}`'s result type to be \
                     independent of its argument, or else an equation `a = b` at a type \
                     that is (docs/container-proofs.md §7); a dependent result of any \
                     other shape is not supported yet"
                ),
                span,
            );
        }
        let len = c.len.shift_local(by);
        let len_rc = Rc::new(len.clone());
        let elem = c.elem.shift_local(by);
        let ih = c.ih.shift_local(by);
        // `h = λ(i : Fin len). ih (inr^m i)` — the index map, shared by both
        // phases: the ih is indexed by `Fin (Succ^m len)`, so the container's
        // own indices start at `m` (docs/container-fields.md §10.3). The
        // application is annotated with the ih's *own* Π type rather than a
        // rebuilt one, since phase 3's codomain is dependent.
        let unit = || Rc::new(Type::Unit { level: Level::Zero });
        let mut idx = Term::Var(LocalVar(0));
        for j in 0..c.plain {
            let mut inner = len.shift_local(1);
            for _ in 0..j {
                inner = Term::Succ(Rc::new(inner));
            }
            idx = Term::Inr {
                lhs_level: Level::Zero,
                rhs_level: Level::Zero,
                lhs: unit(),
                rhs: Rc::new(Type::Fin { len: Rc::new(inner) }),
                val: Rc::new(idx),
            };
        }
        let Type::Pi { dom: ih_dom, cod: ih_cod, .. } = c.ih_ty.shift_local(by + 1) else {
            unreachable!("a `Wf` arm's ih is a Π over its index")
        };
        let h = Term::Lam {
            dom_level: Level::Zero,
            cod_level: c.mlvl.clone(),
            dom: Rc::new(Type::Fin { len: Rc::clone(&len_rc) }),
            body: Rc::new(Term::App {
                fun: Rc::new(ih.shift_local(1)),
                dom_level: Level::Zero,
                cod_level: c.mlvl.clone(),
                dom: ih_dom,
                cod: ih_cod,
                arg: Rc::new(idx),
            }),
        };
        // Phase 2: an independent motive tabulates into a vector of results.
        if let Some(result) = &c.result {
            let result = result.shift_local(by);
            let ty = Type::Vec {
                level: c.mlvl.clone(),
                elem: Rc::new(result.clone()),
                len: Rc::clone(&len_rc),
            };
            // The evaluation hook, as in `elab_vec_map`/`elab_vec_fold` — the
            // call `docs/meta-def-registration-design.md` §9 says this site
            // gains once the surface can write `Fin` and its indices.
            // `lib/vec_code.hthr`'s `tabulate_code` claims `vec.tabulate` when
            // the lib is in scope; without it this declines silently and the
            // schema below runs unchanged.
            //
            // Phase 3's `tabulate`s below are deliberately *not* routed: they
            // build the two endpoints of an `Id` **type**, and a template's
            // output there would change what the proof is a proof of.
            if let Some(t) = self.try_code_template(
                cx,
                Slot::VecTabulate,
                &[
                    ("B", Ingredient::Type { level: &c.mlvl, ty: &result }),
                    ("k", Ingredient::Term((*len_rc).clone())),
                    ("f", Ingredient::Term(h.clone())),
                ],
                span,
            )? {
                return Ok((t, ty, c.mlvl.clone()));
            }
            return Ok((
                vec::tabulate(&c.mlvl, &result, &len_rc, Rc::new(h)),
                ty,
                c.mlvl.clone(),
            ));
        }
        // Phase 3: an equational motive proves the two children *vectors* equal
        // (docs/container-proofs.md §5). `f'`/`g'` are the endpoint functions
        // applied at each index; `h` proves them pointwise equal, verbatim.
        let e = c.eq.as_ref().expect("checked above");
        let (a_ty, kids) = (e.ty.shift_local(by), c.term.shift_local(by));
        let side = |f: &Rc<Term>| {
            let child = nth(
                &c.level,
                &Rc::new(elem.shift_local(1)),
                &Rc::new(len.shift_local(1)),
                Rc::new(kids.shift_local(1)),
                Rc::new(Term::Var(LocalVar(0))),
            );
            Rc::new(Term::Lam {
                dom_level: Level::Zero,
                cod_level: e.level.clone(),
                dom: Rc::new(Type::Fin { len: Rc::clone(&len_rc) }),
                body: Rc::new(Term::App {
                    fun: Rc::new(f.shift_local(by + 1)),
                    dom_level: c.level.clone(),
                    cod_level: e.level.clone(),
                    dom: Rc::new(elem.shift_local(1)),
                    cod: Rc::new(a_ty.shift_local(2)),
                    arg: Rc::new(child),
                }),
            })
        };
        let (f_side, g_side) = (side(&e.lhs), side(&e.rhs));
        Ok((
            vec::tab_cong(
                &e.level,
                &a_ty,
                &len_rc,
                Rc::clone(&f_side),
                Rc::clone(&g_side),
                Rc::new(h),
            ),
            Type::Id {
                level: e.level.clone(),
                ty: Rc::new(Type::Vec {
                    level: e.level.clone(),
                    elem: Rc::new(a_ty.clone()),
                    len: Rc::clone(&len_rc),
                }),
                lhs: Rc::new(vec::tabulate(&e.level, &a_ty, &len_rc, f_side)),
                rhs: Rc::new(vec::tabulate(&e.level, &a_ty, &len_rc, g_side)),
            },
            e.level.clone(),
        ))
    }

    /// `[a, b, c]` at an expected `Vec^l(T; k)`: the Σ-chain that `Vec`
    /// unfolds to, terminated by `⟨⟩ : Unit^l`
    /// (docs/container-fields.md §2.2). Shares its shape with
    /// `wf::build_children`, which builds the same chain for a constructor's
    /// children — the difference is only where the element type comes from.
    fn elab_vec_lit(
        &self,
        cx: &Cx,
        elems: &[Expr],
        expected: &Type,
        span: Span,
    ) -> R<Term> {
        // *Not* whnf'd: `Vec` reduces on its length, so the whnf of
        // `[T; 0]` is `Unit` and of `[T; 2]` a Σ-chain — the former is what
        // this arm exists to recognise.
        //
        // `decoded` and not `whnf` for exactly that reason. A `Vec` no longer
        // always arrives straight from `elab_ty`: a record whose field is a
        // vector, reached as a *code* (a type-valued `fn`, or a `Val -> Type`
        // value), hands `build_fields` a component that is `El (TmVec …)`
        // (docs/types-as-expressions.md §4 — the decode is lazy, so the
        // children stay wrapped). `decoded` strips that one canonical former
        // and stops; `whnf` would carry straight on into the Σ-chain and lose
        // the shape this arm exists to see.
        let expected = &*crate::inductive::decoded(expected);
        let Type::Vec { level, elem, len } = expected else {
            return err("a vector literal needs a `[T; n]` expected type", span);
        };
        let (level, elem) = (level.clone(), Rc::clone(elem));
        // The length has to be a literal — but only *after* reduction:
        // `Vec` itself reduces on the whnf of its length, and a container
        // field's expected length arrives as a projection out of the label
        // (docs/container-fields.md §3.4), which computes to a numeral rather
        // than being one.
        let len = whnf_term(len, &cx.gamma, self.fuel)
            .map_err(|_| ElabError::Elab {
                msg: "ran out of fuel reducing a vector literal's expected length".into(),
                span,
            })?;
        let Some(k) = crate::inductive::nat_value(&len) else {
            return err(
                "a vector literal needs a literal length here; a vector of a \
                 variable length has to come from a binder",
                span,
            );
        };
        if k != elems.len() {
            return err(
                format!(
                    "this vector literal has {} element(s) but {k} are expected",
                    elems.len()
                ),
                span,
            );
        }
        let mut acc = Term::Triv { level: level.clone() };
        for (j, e) in elems.iter().enumerate().rev() {
            let x = self.elab_check(cx, e, &elem, &level)?;
            acc = Term::Pair {
                fst_level: level.clone(),
                snd_level: level.clone(),
                fst_ty: Rc::clone(&elem),
                // A Σ's second component binds, so the tail type sits one
                // binder deeper (tier-1 §5's annotation caveat).
                snd_ty: Rc::new(Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(elem.shift_local(1)),
                    len: Rc::new(crate::inductive::nat_lit(elems.len() - 1 - j)),
                }),
                fst: Rc::new(x),
                snd: Rc::new(acc),
            };
        }
        Ok(acc)
    }

    /// A lambda against an expected type (docs/surface-function-types.md §5.2).
    /// One Π is peeled per binder; a written annotation must be convertible
    /// with the expected domain, but the *expected* domain is what gets
    /// pushed and emitted.
    fn elab_lam_check(
        &self,
        cx: &Cx,
        binders: &[LamBinder],
        body: &Expr,
        expected: &Type,
        lvl: &Level,
        // The expected type's skeleton, where the caller had one — positions
        // are consumed one per binder as the recursion descends the spine
        // (docs/implicit-binders-design.md §6.1).
        skel: Option<&Skel>,
        span: Span,
    ) -> R<Term> {
        self.lam_check_at(cx, binders, body, expected, lvl, skel.map(|s| s.params.as_slice()), span)
    }

    /// [`Self::elab_lam_check`] with the expected skeleton advanced to the
    /// current binder: `skel_at[0]` (if any) speaks for `binders[0]`.
    #[allow(clippy::too_many_arguments)]
    fn lam_check_at(
        &self,
        cx: &Cx,
        binders: &[LamBinder],
        body: &Expr,
        expected: &Type,
        lvl: &Level,
        skel_at: Option<&[SkelBinder]>,
        span: Span,
    ) -> R<Term> {
        let Some((b, rest)) = binders.split_first() else {
            return self.elab_check(cx, body, expected, lvl);
        };
        let head = self.whnf(cx, expected, span)?;
        let Type::Pi { dom_level, cod_level, dom, cod } = head else {
            return err(
                format!(
                    "a lambda needs a function type here, found `{}`",
                    self.display_type(cx, expected)
                ),
                span,
            );
        };
        // The §6.2 coherence rule: an implicit-marked binder requires the
        // expected position to be implicit — silently accepting would mean
        // the writer believes uses of the function will infer, and they will
        // not (stale intent, the §3.4 hazard at the term level). An
        // *explicit* binder is accepted at any position, including implicit
        // ones: insertion at uses is governed by the type's skeleton, not by
        // the argument's spelling.
        let pos = skel_at.and_then(|s| s.first());
        if b.implicit {
            match pos {
                Some(p) if p.implicit => {}
                Some(_) => {
                    return err(
                        "this binder is marked implicit, but the expected function \
                         type spells this parameter explicit — the two must agree \
                         position by position",
                        b.span,
                    )
                }
                None => {
                    return err(
                        "this binder is marked implicit, but the function type \
                         expected here carries no implicitness — it was computed, \
                         not written, and a computed type offers no implicit \
                         insertion (issues/implicit-binders-in-function-types.md)",
                        b.span,
                    )
                }
            }
        }
        if let Some(ann) = &b.ty {
            let (ann_t, _) = self.elab_ty(cx, ann)?;
            let psi = self.goal_psi();
            if conv_type(&psi, &cx.gamma, Layer::Prog, &ann_t, &dom, &dom_level, self.fuel)
                .is_err()
            {
                return err(
                    format!(
                        "`{}` is annotated with a type that is not the one expected here",
                        b.name
                    ),
                    ann.span,
                );
            }
        }
        let mut inner = cx.clone();
        // The binder carries the expected position's `dom` sub-skeleton, so
        // a callback bound by the lambda inserts at its own uses (§3.1);
        // the written annotation's marks are the fallback where the expected
        // type carried no skeleton — the annotation was just proved
        // convertible with the domain, so the pairing is with the same
        // erased spine.
        let bskel = pos
            .and_then(|p| p.dom.clone())
            .or_else(|| b.ty.as_ref().and_then(skel_of_ty));
        inner.push_skel(b.name.clone(), (*dom).clone(), dom_level.clone(), bskel);
        // A lambda binder *at a universe* is usable as a type in the body —
        // the same generalization the telescope loop makes for parameters
        // (docs/surface-universe.md §2: a type name is any binder whose type
        // is `Type<n>`). What forced it to lambdas: a generic code template
        // binds its element types inside the quote, `fun (A: Type<0>) => …`
        // (docs/in-language-map-design.md §3).
        if let Type::Ty(level) = &*dom {
            inner.tyvars.push(TyVar {
                name: b.name.clone(),
                ty: Type::El { level: level.clone(), tm: Rc::new(Term::Var(LocalVar(0))) },
                level: level.clone(),
                depth: inner.names.len(),
            });
        }
        let body_t = if rest.is_empty() {
            self.elab_check(&inner, body, &cod, &cod_level)?
        } else {
            let rest_skel = skel_at.map(|s| s.get(1..).unwrap_or(&[]));
            self.lam_check_at(&inner, rest, body, &cod, &cod_level, rest_skel, span)?
        };
        Ok(Term::Lam {
            dom_level,
            cod_level,
            dom,
            body: Rc::new(body_t),
        })
    }

    /// A lambda in inference position: every binder must be annotated.
    ///
    /// Implicit marks are **refused** here unless `harvest` — any other
    /// inference position would infer the type and *drop* the skeleton, the
    /// silent erasure §3.4 forbids. The one carve-out is the `let`-RHS
    /// caller in [`Self::elab_stmts`], which records the skeleton read off
    /// the written marks onto the alias (docs/implicit-binders-design.md
    /// §6.3).
    fn elab_lam_infer(
        &self,
        cx: &Cx,
        binders: &[LamBinder],
        body: &Expr,
        harvest: bool,
    ) -> R<(Term, Type, Level)> {
        let Some((b, rest)) = binders.split_first() else {
            return self.elab_infer(cx, body);
        };
        if b.implicit && !harvest {
            return err(
                "an implicit lambda binder needs a checking position, or a `let` — \
                 its implicitness has nowhere to go from here",
                b.span,
            );
        }
        let Some(ann) = &b.ty else {
            return err(
                format!(
                    "this lambda's binder `{}` needs a type annotation, or the lambda \
                     needs a checking position (`let f: A -> B = λ {} => …;`)",
                    b.name, b.name
                ),
                b.span,
            );
        };
        let (dom, dom_level) = self.elab_ty(cx, ann)?;
        let mut inner = cx.clone();
        // The annotation's own skeleton (docs/implicit-binders-design.md
        // §3.1): a callback parameter's uses in the body insert.
        inner.push_skel(b.name.clone(), dom.clone(), dom_level.clone(), skel_of_ty(ann));
        // A binder at a universe is usable as a type in the body — see
        // `elab_lam_check`, whose registration this mirrors.
        if let Type::Ty(level) = &dom {
            inner.tyvars.push(TyVar {
                name: b.name.clone(),
                ty: Type::El { level: level.clone(), tm: Rc::new(Term::Var(LocalVar(0))) },
                level: level.clone(),
                depth: inner.names.len(),
            });
        }
        let (body_t, cod, cod_level) = self.elab_lam_infer(&inner, rest, body, harvest)?;
        Ok((
            Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::new(dom.clone()),
                body: Rc::new(body_t),
            },
            Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::new(dom),
                cod: Rc::new(cod),
            },
            Level::max(dom_level, cod_level),
        ))
    }

    /// Positional application down the Π spine — the stage-1 behaviour, reused
    /// for `@`-marked calls and callees with no implicits. Supports partial
    /// application (fewer args than parameters yields a function value).
    #[allow(clippy::too_many_arguments)]
    fn apply_explicit(
        &self,
        cx: &Cx,
        name: Option<&str>,
        // The callee's parameter table, passed by the one caller that knows
        // it rather than recovered by name inside
        // (docs/implicit-binders-design.md §4.2): a *value* callee's table is
        // synthesized from its skeleton, and recovering by name here would
        // let a local `f` borrow a global `f`'s metadata.
        params: Rc<Vec<ParamMeta>>,
        // `param_offset`: how many leading parameters the head has already
        // consumed — the type arguments of an `f<T, …>(…)` call. Only the
        // goal-name hints depend on it, but a hint naming the wrong parameter
        // is user-visible, so it is threaded rather than approximated.
        param_offset: usize,
        head: Term,
        ty: Type,
        lvl: Level,
        args: &[Expr],
    ) -> R<(Term, Type, Level)> {
        let (mut t, mut ty, mut lvl) = (head, ty, lvl);
        // Positional, so argument `i` is parameter `i`: a hole here defaults
        // its name to that parameter's ("proof-parameter names are API").
        // A head that is not a name has no parameter metadata, hence no hints.
        let what = name.map_or_else(|| "this function".to_string(), |n| format!("`{n}`"));
        for (i, arg) in args.iter().enumerate() {
            let head = self.whnf(cx, &ty, arg.span)?;
            let Type::Pi { dom_level, cod_level, dom, cod } = head else {
                return err(format!("{what} is applied to too many arguments"), arg.span);
            };
            let p = params.get(i + param_offset);
            let hint = name.zip(p).map(|(n, p)| (n, p.name.as_str()));
            let skel = p.and_then(|p| p.skel.as_deref());
            let arg_t = self.elab_check_skel(cx, arg, &dom, &dom_level, hint, skel)?;
            let arg_rc = Rc::new(arg_t);
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg_rc)));
            lvl = cod_level.clone();
            t = Term::App { fun: Rc::new(t), dom_level, cod_level, dom, cod, arg: arg_rc };
        }
        Ok((t, ty, lvl))
    }

    /// A projected record field applied to arguments: `w.f(3)`. Routes to
    /// implicit insertion when the field's stored surface type carried marks
    /// (docs/implicit-binders-design.md §5.1), and to the explicit path —
    /// with the skeleton-synthesized hint table when there is one —
    /// otherwise. The field name is the display name; `@w.f(…)` stays out of
    /// the grammar this round (§7.1), so there is no explicit flag here.
    #[allow(clippy::too_many_arguments)]
    fn apply_projection(
        &self,
        cx: &Cx,
        name: &str,
        t: Term,
        ty: Type,
        lvl: Level,
        fskel: Option<Rc<Skel>>,
        args: &[Expr],
        expected: Option<&Type>,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        match fskel {
            Some(skel) if skel.params.iter().any(|b| b.implicit) => {
                let mask: Vec<bool> = skel.params.iter().map(|b| b.implicit).collect();
                self.apply_implicit(
                    cx,
                    name,
                    skel_params(&skel),
                    true,
                    0,
                    false,
                    t,
                    ty,
                    lvl,
                    args,
                    &mask,
                    expected,
                    span,
                )
            }
            Some(skel) => {
                self.apply_explicit(cx, Some(name), skel_params(&skel), 0, t, ty, lvl, args)
            }
            None => self.apply_explicit(cx, None, Rc::new(Vec::new()), 0, t, ty, lvl, args),
        }
    }

    /// `C<T, …>(a⃗)` — a constructor at a *written* instantiation. `None` when
    /// the head is not a constructor, so the caller falls through to the
    /// ordinary type-application path.
    ///
    /// This is the direct spelling of what `infer_ctor` can only recover
    /// narrowly (from a field whose type *is* a parameter) and otherwise
    /// refuses to guess: `Nil` alone is genuinely ambiguous, `Nil<Nat>` is not.
    fn ctor_at(
        &self,
        cx: &Cx,
        callee: &Expr,
        tyargs: &[Ty],
        args: &[Expr],
        span: Span,
    ) -> Option<R<(Term, Type, Level)>> {
        let ExprKind::Var(name) = &callee.kind else { return None };
        let (ind, i) = self.ctor_here(cx, name)?;
        Some((|| {
            if tyargs.len() != ind.params.len() {
                return err(
                    format!(
                        "`{}` is a constructor of `{}`, which takes {} type argument(s), \
                         found {}",
                        name,
                        ind.name,
                        ind.params.len(),
                        tyargs.len()
                    ),
                    span,
                );
            }
            let mut lowered = Vec::with_capacity(tyargs.len());
            for a in tyargs {
                // Same refusal as `elab_ty_app`'s: the instantiation stores
                // kernel types, so a mark in it has no consumer (§3.4).
                if has_implicit_mark(a) {
                    return err(IMPLICIT_MARK_REFUSED, a.span);
                }
                lowered.push(self.elab_ty(cx, a)?);
            }
            // `R<Nat>(a, b)` is not a spelling: the type arguments are
            // explicit here but the value arguments are still only recoverable
            // from the checking type (docs/surface-value-parameters.md §4).
            if !ind.valparams.is_empty() {
                return err(
                    format!(
                        "`{}` takes value parameters, which `<…>` cannot supply — they \
                         are read off the expected type. Put the expression where a \
                         `{}(…)` is expected instead",
                        ind.name, ind.name
                    ),
                    span,
                );
            }
            // An **indexed** family at a written instantiation: the index is
            // not written — it is the constructor's own result index at the
            // arguments it was given, exactly as in `infer_ctor`. This is the
            // second escape the "cannot infer the type argument" message names,
            // and the only one a nullary constructor like `Leaf<Nat>` has
            // (`docs/inductive-fording-lowering.md` §14.7).
            if ind.index.is_some() {
                if args.len() != ind.ctors[i].fields.len() {
                    return err(
                        format!(
                            "`{}` takes {} argument(s), found {} — a constructor of an \
                             indexed family cannot be partially applied at a written \
                             instantiation, because its index is read off its arguments",
                            name,
                            ind.ctors[i].fields.len(),
                            args.len()
                        ),
                        span,
                    );
                }
                let (ty, lvl) = if ind.skel.is_some() {
                    let (idx, _, _) = self.forded_ctor_index(cx, &ind, i, args, span)?;
                    self.lower_forded_instance(cx, &ind, &lowered, idx, span)?
                } else {
                    let (idx, _, _) = self.indexed_ctor_index(cx, &ind, i, args, span)?;
                    self.lower_indexed_instance(cx, &ind, &lowered, idx, span)?
                };
                let t = self.build_ctor(cx, &ind, i, args, &ty, &lvl, span)?;
                return Ok((t, ty, lvl));
            }
            let (ty, lvl) = self.lower_instance(cx, &ind, &lowered, &[], span)?;
            let t = self.build_ctor_value(cx, &ind, i, args, &ty, &lvl, span)?;
            Ok((t, ty, lvl))
        })())
    }

    /// `f<T, …>` — fill a declaration's leading type parameters with the
    /// codes of the written types (docs/surface-polymorphism.md §1).
    ///
    /// Returns the callee's name (for diagnostics downstream), the applied
    /// head with its type and level, and the implicit mask of the parameters
    /// that are *left* — so a call can still infer whatever `{}`-implicits
    /// follow the type arguments.
    fn elab_ty_app(
        &self,
        cx: &Cx,
        callee: &Expr,
        tyargs: &[Ty],
        span: Span,
    ) -> R<(String, Term, Type, Level, Vec<bool>)> {
        let ExprKind::Var(name) = &callee.kind else {
            return err(
                "type arguments need a named callee: write `f<T, …>(…)`, where `f` is a \
                 `fn` or `theorem` with type parameters",
                span,
            );
        };
        // The enclosing declaration's own name, with no call after it. A
        // *saturated* self-call at written type arguments is handled before
        // this function is reached; a bare `f<A>` is the self-name used as a
        // value, which it never is (it is the induction hypothesis). Said here
        // because `params_of` finds no global for a self-name and the arity
        // complaint below would otherwise deny a declaration the reader is
        // looking at (issues/recursive-self-call-type-arguments.md).
        if cx.selfref.as_ref().is_some_and(|s| s.name == *name) {
            return err(
                format!("`{name}` can only be used here as a saturated recursive call"),
                span,
            );
        }
        let params = self.params_of(name);
        let n_ty = params.iter().take_while(|p| p.is_type).count();
        if n_ty == 0 {
            return err(
                format!(
                    "`{name}` takes no type arguments (only a `fn` or `theorem` declared \
                     `{name}<A, …>` does)"
                ),
                span,
            );
        }
        if tyargs.len() != n_ty {
            return err(
                format!(
                    "`{name}` takes {n_ty} type argument(s), found {}",
                    tyargs.len()
                ),
                span,
            );
        }
        let (mut t, mut ty, mut lvl) = self.resolve(cx, name, span)?;
        for a in tyargs {
            // A written type argument becomes a code — a kernel value with
            // no skeleton slot — so a mark in one is refused (§3.4).
            if has_implicit_mark(a) {
                return err(IMPLICIT_MARK_REFUSED, a.span);
            }
            let (a_ty, _) = self.elab_ty(cx, a)?;
            let Some(c) = code::code_of(&a_ty) else {
                return err("this type cannot be a type argument", a.span);
            };
            let head = self.whnf(cx, &ty, span)?;
            let Type::Pi { dom_level, cod_level, dom, cod } = head else {
                return err(
                    format!("internal: `{name}`'s type parameter is not a `Π`"),
                    span,
                );
            };
            let arg = Rc::new(c);
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg)));
            lvl = cod_level.clone();
            t = Term::App { fun: Rc::new(t), dom_level, cod_level, dom, cod, arg };
        }
        let mask = params.iter().skip(n_ty).map(|p| p.implicit).collect();
        Ok((name.clone(), t, ty, lvl, mask))
    }

    /// Is `e` a form the elaborator can only *check*, never infer — the
    /// deferral trigger's syntactic half (docs/unifier-completeness-design.md
    /// §4.1)? The set is closed and enumerated by the refusing arms of
    /// [`Self::elab_infer_at`]/[`Self::elab_infer`]; deferring exactly these
    /// forms loses no solving power, because in inference mode they *error*
    /// rather than contribute a solution. Each variant, tied to its arm:
    ///
    /// - `Hole` — "a hole here has no expected type" (`elab_infer_at`).
    /// - `Refl`, when not shadowed — "`refl` needs an `=` expected type"
    ///   (the shadowed reading is a `Var` and infers).
    /// - `AutoRefl` — checking-only by construction (a speculative `refl`
    ///   against the expected `Id`).
    /// - `VecLit` — "a vector literal needs an expected type".
    /// - a `Lam` with any unannotated binder — nothing to take the domain
    ///   from (`elab_lam_infer` requires every annotation; `elab_lam_check`
    ///   reads the domain off the expected `Π`).
    /// - `FZ` / `FS(j)`, under their existing not-shadowed/not-a-ctor
    ///   guards — "needs an expected `Fin` type".
    /// - `absurd(p)`, when not shadowed — "needs an expected type".
    /// - a bare reference to a global with a leading implicit prefix
    ///   ([`Self::bare_implicit_prefix`]). This one *can* infer — but only at
    ///   its uninstantiated polymorphic Π, which against a meta-bearing
    ///   domain can just mis-teach (`El ?B ≟ Ty 0` "solves" `?B := ⌜Type 0⌝`
    ///   and the kernel rejects a term nobody meant). Checking position is
    ///   where its instantiation is decidable (the §5.3 route), so at a
    ///   meta-bearing domain it waits for one.
    /// - a **bare operator symbol** that no binder named and that some
    ///   designation covers ([`Self::symbol_needs_a_carrier`]). The same
    ///   sentence as the entry above, at the notation layer: `+` infers to
    ///   `add`, whose type would pin a `Bool` call's carrier to `Nat`, so at a
    ///   meta-bearing domain it waits for the carrier a later argument
    ///   produces (docs/bare-symbol-checking-carrier-design.md §3.2).
    ///
    /// `Num` is deliberately **excluded**: it infers at `Nat` today and that
    /// default is load-bearing for the suite (`xs[2]`'s `Fin` reading exists
    /// only in checking position, as before).
    fn is_checking_only(&self, cx: &Cx, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Hole(_) | ExprKind::AutoRefl | ExprKind::VecLit(_) => true,
            // A bare operator symbol that needs a carrier
            // (docs/bare-symbol-checking-carrier-design.md §3.2, §4.3). Same
            // sentence as the bare implicit prefix two arms down: it *can*
            // infer — `+` infers to `add` — but only at a shape that
            // mis-teaches, since `add`'s type would pin the call's carrier to
            // `Nat` at a call whose carrier is `Bool`. Checking position is
            // where its resolution is decidable, so at a meta-bearing domain it
            // waits for one, and the per-argument deferral is what hands it the
            // carrier a later argument produced.
            ExprKind::OpSymbol(sym) => self.symbol_needs_a_carrier(cx, sym),
            ExprKind::Refl => !self.shadowed(cx, "refl"),
            ExprKind::Lam { binders, .. } => binders.iter().any(|b| b.ty.is_none()),
            ExprKind::Var(name) => {
                (name == "FZ"
                    && !self.shadowed(cx, name)
                    && self.ctor_here(cx, name).is_none())
                    || self.bare_implicit_prefix(cx, name).is_some()
                    // The value analog (docs/implicit-binders-design.md
                    // §4.3): a bare local/alias whose skeleton has a leading
                    // implicit prefix is checking-only for the same reason
                    // the bare-global member is — it *can* infer, but only
                    // at its uninstantiated Π, which against a meta-bearing
                    // domain mis-teaches.
                    || self
                        .value_skel(cx, name)
                        .is_some_and(|s| s.leading_implicit() > 0)
            }
            ExprKind::App { .. } => match e.as_named() {
                Some(("absurd", _, _)) => !self.shadowed(cx, "absurd"),
                Some(("FS", _, false)) => {
                    !self.shadowed(cx, "FS") && self.ctor_here(cx, "FS").is_none()
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// A **bare** operator symbol whose meaning only a carrier can settle —
    /// the gate on [`Self::is_checking_only`]'s new arm
    /// (docs/bare-symbol-checking-carrier-design.md §4.3).
    ///
    /// Two conjuncts, both load-bearing.
    ///
    /// Rung 1 first, so a symbol this declaration's own binder named is never
    /// deferred: `sum_all`'s `mconcat(+, xs)` resolves without looking at a
    /// type and elaborates through exactly the code it did before.
    ///
    /// And the symbol must be designated *somewhere*, which is the growth
    /// invariant's guard and the very guard rung 2 already carries. Without it
    /// a file that declares no designation for a symbol would stop inferring
    /// it by the fallback — and the fallback's own type is sometimes what
    /// teaches the call its carrier — so a program written before this round
    /// could start refusing. With it, such a file runs byte-identical code.
    fn symbol_needs_a_carrier(&self, cx: &Cx, sym: &str) -> bool {
        !cx.op_locals.iter().any(|(s, _)| s == sym)
            && self.designations.keys().any(|(s, _)| s == sym)
    }

    /// Application with implicit-argument insertion
    /// (issues/elab-stage2-metas.md). Each implicit parameter becomes a fresh
    /// metavariable — represented, per the architecture, as an *innermost*
    /// Ψ-binding: occurrences are `?m^{id_Γ}` (`GlobalTm` at index `< n`),
    /// solutions are recorded by unifying each explicit argument's inferred
    /// type against the parameter's domain, and the whole meta block is
    /// discharged by one global substitution σ (`apply_global`) that also
    /// renumbers the committed globals back down. The kernel re-checks the
    /// zonked term, so a mis-solved meta is a rejection, never unsoundness.
    ///
    /// Unlike [`Self::apply_explicit`] this requires *saturating* the spine
    /// (every explicit parameter needs an argument): mixing partial
    /// application with implicit insertion is ambiguous, so it is refused —
    /// except that `mask` may cover only a *prefix* of the remaining
    /// parameters (the bare-reference route of
    /// docs/unifier-completeness-design.md §5.3), in which case the
    /// parameters past the mask are simply left unapplied.
    ///
    /// `param_offset` is how many leading parameters the head has already
    /// consumed (the type arguments of an `f<T, …>(…)` call) — passed rather
    /// than recovered from `all_params.len() - mask.len()`, which is only
    /// right when the mask is a suffix. `bare_ref` selects the §7.1 message
    /// flavor for the zero-argument checking-position route.
    #[allow(clippy::too_many_arguments)]
    fn apply_implicit(
        &self,
        cx: &Cx,
        name: &str,
        // The callee's parameter table, passed by the caller rather than
        // recovered by name here (docs/implicit-binders-design.md §4.2):
        // global sites pass `params_of`, value sites synthesize the table
        // from the head's skeleton — which is what keeps a local `f` from
        // borrowing a global `f`'s metadata, and what names goal hints and
        // per-slot messages after skeleton binders.
        params: Rc<Vec<ParamMeta>>,
        // A skeletal *value* head (a local, alias, or projection): its
        // messages must offer only the escapes that exist — `@name(…)` and
        // an annotated eta-expansion, never `name<…>` (§4.3).
        value_head: bool,
        param_offset: usize,
        bare_ref: bool,
        head: Term,
        callee_ty: Type,
        callee_lvl: Level,
        args: &[Expr],
        mask: &[bool],
        expected: Option<&Type>,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        // Scratch-world size, fixed up front (everything downstream of
        // `shift_global(n)` assumes it is static): one meta per implicit
        // parameter, plus one per explicit argument that is syntactically
        // checking-only (design §4.2) — those *may* be deferred behind a
        // stand-in meta. The second summand is an over-approximation: a
        // checking-only argument whose domain turns out meta-free is checked
        // inline exactly as before, and its pre-allocated slot is filled with
        // the checked term immediately.
        let n_impl = mask.iter().filter(|&&b| b).count();
        let n_expl = mask.len() - n_impl;
        let n_defer = args
            .iter()
            .take(n_expl)
            .filter(|a| self.is_checking_only(cx, a))
            .count();
        let n = (n_impl + n_defer) as u32;
        // Scratch world: the `n` metas take the innermost Ψ indices `[0, n)`;
        // committed globals shift up by `n` so nothing collides.
        let mut t = head.shift_global(n);
        let mut ty = callee_ty.shift_global(n);
        let mut lvl = callee_lvl;
        let mut sols: Vec<Sol> = vec![Sol::Unsolved; n as usize];
        // Each meta's *declared* parameter type, in meta order — the only
        // place a solution's domain can come from when no argument mentions
        // it (see [`Self::solve_from_expected`]).
        let mut meta_doms: Vec<Type> = Vec::with_capacity(n as usize);
        // Which parameter each slot came from, in slot order — for the
        // per-slot diagnostics at discharge.
        let mut slot_param: Vec<usize> = Vec::with_capacity(n as usize);
        // Deferred obligations (design §3.1): local to this activation. The
        // scratch world is the constraint store — an obligation's domain's
        // meta occurrences *are* its "blocked on" set, and [`zonked`] decides
        // readiness exactly.
        let mut deferred: Vec<DeferredArg<'_>> = Vec::new();
        // Resolution obligations (docs/traits-layer2-design.md §4): one per
        // **solver parameter**, discharged by the same retry-to-fixpoint loop
        // the deferred arguments use. A solver parameter's slot is minted
        // exactly like an implicit's; what differs is where its solution comes
        // from — search, once the goal is meta-free.
        let mut resolves: Vec<ResolveOb> = Vec::new();
        let mut next_meta = 0u32;
        let mut args = args.iter();
        let all_params = params;
        for (mi, &is_implicit) in mask.iter().enumerate() {
            let i = mi + param_offset;
            let params = &all_params;
            let head_ty = self.whnf(cx, &ty, span)?;
            let Type::Pi { dom_level, cod_level, dom, cod } = head_ty else {
                return err(format!("`{name}` is applied to too many arguments"), span);
            };
            let arg_rc = if is_implicit {
                // A fresh metavariable `?m^{id_Γ}` at Ψ-index `next_meta`.
                let m = Term::GlobalTm {
                    var: GlobalVar(next_meta),
                    subst: LocalSubst::id(&cx.gamma),
                };
                if all_params.get(i).is_some_and(|p| p.solver.is_some()) {
                    // A solver parameter: withheld, not unsolved. Nothing may
                    // learn a solution for it from an argument's type — its
                    // value is *searched for*, and a unifier-supplied one
                    // would be a different value at the same slot.
                    sols[next_meta as usize] = Sol::Withheld;
                    resolves.push(ResolveOb {
                        slot: next_meta as usize,
                        dom: (*dom).clone(),
                        dom_level: dom_level.clone(),
                        param: i,
                    });
                }
                meta_doms.push((*dom).clone());
                slot_param.push(i);
                next_meta += 1;
                Rc::new(m)
            } else {
                let arg = args.next().ok_or_else(|| ElabError::Elab {
                    msg: format!("`{name}` is applied to too few arguments"),
                    span,
                })?;
                // If every meta this domain mentions is *already* solved,
                // elaborate the argument in **checking** mode against the
                // zonked domain. That is what puts `refl`, a `?`-hole, an
                // unannotated lambda and a vector literal in a position that
                // supplies their expected type — they are checking-only.
                //
                // Load-bearing since `@` stopped clearing the mask
                // (issues/at-and-type-arguments.md): `@sym(a, b, ?p)` still
                // has one meta (the type parameter), so it comes through here
                // rather than through `apply_explicit`, and `a` solves the
                // meta before `p`'s domain is needed.
                match zonked(&dom, n, &sols) {
                    Some(real_dom) => {
                        let hint = params.get(i).map(|p| (name, p.name.as_str()));
                        let pskel = params.get(i).and_then(|p| p.skel.as_deref());
                        let arg_t = self
                            .elab_check_skel(cx, arg, &real_dom, &dom_level, hint, pskel)?;
                        if self.is_checking_only(cx, arg) {
                            // Counted into `n` up front, so the slot exists;
                            // fill it now (a solved slot is indistinguishable
                            // from an unused one at discharge) and keep the
                            // slot numbering aligned with the count.
                            sols[next_meta as usize] = Sol::Solved(Rc::new(arg_t.clone()));
                            meta_doms.push((*dom).clone());
                            slot_param.push(i);
                            next_meta += 1;
                        }
                        Rc::new(arg_t.shift_global(n))
                    }
                    // Per-argument deferral (design §4): a checking-only form
                    // cannot contribute a solution in inference mode — every
                    // such arm in `elab_infer_at` refuses it — so at a domain
                    // that still mentions metas it is *deferred*: its spine
                    // position is a fresh stand-in meta, its slot is
                    // withheld, and the obligation is retried after
                    // expected-type solving. Later arguments whose domains
                    // mention the deferred value see the meta and block or
                    // infer as their own trigger says.
                    None if self.is_checking_only(cx, arg) => {
                        let m = Term::GlobalTm {
                            var: GlobalVar(next_meta),
                            subst: LocalSubst::id(&cx.gamma),
                        };
                        sols[next_meta as usize] = Sol::Withheld;
                        deferred.push(DeferredArg {
                            slot: next_meta as usize,
                            expr: arg,
                            dom: (*dom).clone(),
                            dom_level: dom_level.clone(),
                            param: i,
                        });
                        meta_doms.push((*dom).clone());
                        slot_param.push(i);
                        next_meta += 1;
                        Rc::new(m)
                    }
                    None => {
                        let (arg_t, arg_ty, _) = self.elab_infer(cx, arg)?;
                        // Drive meta solutions from the argument's actual
                        // type, then splice it into the scratch world.
                        unify_ty(&cx.gamma, &dom, &arg_ty, n, 0, &mut sols);
                        Rc::new(arg_t.shift_global(n))
                    }
                }
            };
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg_rc)));
            lvl = cod_level.clone();
            t = Term::App { fun: Rc::new(t), dom_level, cod_level, dom, cod, arg: arg_rc };
        }
        // Arguments left over once every parameter has one are **not** partial
        // application: they are a second spine on the *result*, so they spill
        // into iterated application — `nth(t, k)` is `nth(t)(k)`
        // (issues/call-site-overapplication.md). Applied after the discharge
        // below, because only there is the head back in the committed world
        // that `apply_explicit` elaborates its arguments in.
        let mut spill: Vec<Expr> = args.cloned().collect();
        // …*unless* a meta is still unsolved, in which case the spine is not
        // over yet as far as inference is concerned. A declaration curried to
        // satisfy the termination guard (issues/ih-generalization.md) puts
        // real parameters in its result type — `zip<A, B>(xs: List<A>) ->
        // List<B> -> …` — and `B` occurs in no *declared* parameter, so
        // nothing above this line can solve it. The spilled argument's type is
        // the evidence, and it is evidence of exactly the kind the declared
        // arguments give (issues/curried-tail-type-arg-inference.md).
        //
        // Consumed here rather than in `apply_explicit` because a solution has
        // to land in `sols` *before* the discharge below. Three stopping
        // conditions keep this to the case that needs it, so a call that
        // elaborated before this existed takes the same path it did:
        //
        //  - every meta solved — nothing left to learn, so the rest spills;
        //  - a domain that is already meta-free — it teaches nothing, and
        //    `apply_explicit` is where an argument at a known type belongs;
        //  - a checking-only argument — it cannot contribute a solution in
        //    inference mode (design §4), the same rule the loop above obeys.
        //
        // Consuming the whole spill also makes `ty` the call's real result
        // type again, which is the condition the expected-type solving below
        // states for itself.
        if !spill.is_empty() && sols.iter().any(|s| s.solved().is_none()) {
            let mut taken = 0usize;
            while taken < spill.len() && sols.iter().any(|s| s.solved().is_none()) {
                let head_ty = self.whnf(cx, &ty, span)?;
                let Type::Pi { dom_level, cod_level, dom, cod } = head_ty else { break };
                let arg = &spill[taken];
                if zonked(&dom, n, &sols).is_some() || self.is_checking_only(cx, arg) {
                    break;
                }
                let (arg_t, arg_ty, _) = self.elab_infer(cx, arg)?;
                unify_ty(&cx.gamma, &dom, &arg_ty, n, 0, &mut sols);
                let arg_rc = Rc::new(arg_t.shift_global(n));
                ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg_rc)));
                lvl = cod_level.clone();
                t = Term::App { fun: Rc::new(t), dom_level, cod_level, dom, cod, arg: arg_rc };
                taken += 1;
            }
            spill.drain(..taken);
        }
        // Expected-type-directed solving (design §5): in checking position,
        // with an unspilled spine (so `ty` really is the call's result type),
        // the expected type is the remaining evidence. Run only when
        // something is still unfilled — so no call that elaborated before
        // reaches it.
        if let Some(expected) = expected
            && spill.is_empty()
            && sols.iter().any(|s| s.solved().is_none())
        {
            self.solve_from_expected(cx, &ty, expected, n, &mut sols, &meta_doms, span)?;
        }
        // Retry the deferred obligations, to fixpoint in argument order
        // (design §4.3): an obligation whose domain has become meta-free is
        // checked against it — the hole becomes an ordinary goal here, `refl`
        // gets its `Id`, the vector literal its `Vec`. The checked term is a
        // committed-world payload, the same convention the unifiers'
        // strengthened subjects follow. Checking-mode elaboration never
        // writes `sols`, so each pass either fills at least one slot or
        // stops: at most `k` passes for `k` obligations. The multi-pass
        // exists for an obligation whose domain mentions another deferred
        // argument's value, which a single ordered pass could misreport.
        loop {
            let mut progressed = false;
            let mut blocked = false;
            // Resolution obligations first: a resolved dictionary is
            // frequently what a deferred argument's domain was waiting on,
            // and the reverse never happens (a checked argument cannot
            // instantiate a solver parameter's goal — its slot is withheld).
            for ob in &resolves {
                if !matches!(sols[ob.slot], Sol::Withheld) {
                    continue;
                }
                let Some(goal) = zonked(&ob.dom, n, &sols) else {
                    // The value-slot ladder's step 2 at a *call*
                    // (docs/operation-indexed-classes-design.md §5): the goal
                    // is blocked on its index, and a binder in scope of the
                    // goal's class pins it. This is what lets a generic
                    // function call itself — `sum_all(t)` inside `sum_all`
                    // fills the index from the room rather than from search.
                    let written = all_params.get(ob.param).and_then(|p| p.solver.as_deref());
                    if self.fill_index_from_scope(
                        cx,
                        written,
                        &all_params,
                        &slot_param,
                        &mut sols,
                    ) || self.fill_index_from_designation(
                        // Step 3, after step 2: a binder in scope of the
                        // goal's class is the writer's own answer and always
                        // beats the table
                        // (docs/operators-onto-classes-design.md §5).
                        cx,
                        written,
                        &all_params,
                        &slot_param,
                        &mut sols,
                        &meta_doms,
                        n,
                        span,
                    ) {
                        // Progressed *and* still blocked: this obligation has
                        // not been discharged, only unblocked, so the loop has
                        // to come round again rather than fall out.
                        progressed = true;
                    }
                    blocked = true;
                    continue;
                };
                let display = all_params
                    .get(ob.param)
                    .and_then(|p| p.solver.as_deref())
                    .map(traits::render_ty)
                    .unwrap_or_else(|| "a solver parameter".to_string());
                let mut tr = Vec::new();
                match self.resolve_goal(cx, &goal, &ob.dom_level, &display, span, &mut tr) {
                    Some(t) => {
                        sols[ob.slot] = Sol::Solved(Rc::new(t));
                        progressed = true;
                    }
                    None => {
                        return Err(ElabError::Resolution {
                            goal: display,
                            span,
                            trace: tr,
                        })
                    }
                }
            }
            for ob in &deferred {
                if !matches!(sols[ob.slot], Sol::Withheld) {
                    continue;
                }
                let Some(dom) = zonked(&ob.dom, n, &sols) else {
                    blocked = true;
                    continue;
                };
                let hint = all_params.get(ob.param).map(|p| (name, p.name.as_str()));
                let pskel = all_params.get(ob.param).and_then(|p| p.skel.as_deref());
                let arg_t =
                    self.elab_check_skel(cx, ob.expr, &dom, &ob.dom_level, hint, pskel)?;
                sols[ob.slot] = Sol::Solved(Rc::new(arg_t));
                progressed = true;
            }
            if !progressed || !blocked {
                break;
            }
        }
        // A resolution obligation whose goal never became meta-free is
        // reported at the call, naming the parameter and what it waited on:
        // the goal is *unknown*, not absent, and saying "no instance" would
        // be a lie (docs/traits-layer2-design.md §4).
        for ob in &resolves {
            if matches!(sols[ob.slot], Sol::Withheld) {
                let p = all_params.get(ob.param).map(|p| p.name.as_str()).unwrap_or("?");
                // A goal blocked on a **value slot** is refused by name, with
                // every registered instance listed as data
                // (docs/operation-indexed-classes-design.md §5, §11): "no
                // instance" would be a lie and "could not infer" says nothing
                // about which structure was wanted.
                if let Some(t) = all_params.get(ob.param).and_then(|q| q.solver.as_deref())
                    && let Some(r) = self.class_ref_of_ty(t)
                    && let Some(class) = self.lookup_class(&r.name)
                    && !class.valparams.is_empty()
                {
                    return Err(self.value_slot_refusal(&class, name, None, span));
                }
                let goal = all_params
                    .get(ob.param)
                    .and_then(|q| q.solver.as_deref())
                    .map(traits::render_ty)
                    .unwrap_or_else(|| "a solver parameter".to_string());
                return err(
                    format!(
                        "the goal of `{p}` (`{goal}`) still mentions an implicit that \
                         could not be inferred here, so no search can run for it: give \
                         the type arguments (`{name}<…>(…)`) or pass `{p}` explicitly \
                         (`@{name}(…)`)"
                    ),
                    span,
                );
            }
        }
        // An obligation still blocked is reported at *its* argument, before
        // the generic unsolved-meta report — the user should see the
        // argument, not only the meta (design §7.2).
        for ob in &deferred {
            if matches!(sols[ob.slot], Sol::Withheld) {
                let p = all_params
                    .get(ob.param)
                    .map(|p| p.name.as_str())
                    .unwrap_or("?");
                // A value head has no `name<…>` spelling (§4.3), so its
                // message offers only the escapes that exist.
                let escape = if value_head {
                    format!("write the call fully explicitly (`@{name}(…)`)")
                } else {
                    format!(
                        "give the type arguments (`{name}<…>(…)`) or write \
                         the call fully explicitly (`@{name}(…)`)"
                    )
                };
                // A deferred bare symbol says why it wanted the type at all,
                // and names the spelling that does not
                // (docs/bare-symbol-checking-carrier-design.md §6(c)). The
                // generic message below is true of it but explains nothing:
                // the reader wrote a notation, not a hole.
                if let ExprKind::OpSymbol(sym) = &ob.expr.kind {
                    return err(
                        format!(
                            "`{sym}` is a bare operator symbol, so it needs the carrier \
                             this position expects — and the type of `{name}`'s \
                             parameter `{p}` still mentions an implicit that could not \
                             be inferred here. Name the operation instead of the \
                             symbol, or {escape}"
                        ),
                        ob.expr.span,
                    );
                }
                return err(
                    format!(
                        "this argument of `{name}` was deferred — the type of its \
                         parameter `{p}` still mentions an implicit that could not be \
                         inferred; {escape}"
                    ),
                    ob.expr.span,
                );
            }
        }
        // Discharge the meta block: `entries[k]` is the payload for Ψ-index
        // `n-1-k` (apply_global's convention), so it takes `sols[n-1-k]`.
        // Only an implicit's slot can still be `Unsolved` here — deferred
        // slots are `Solved` or already reported above, inline-checked ones
        // were filled at their turn.
        let mut entries = Vec::with_capacity(n as usize);
        for k in 0..n {
            let j = (n - 1 - k) as usize;
            let sol = sols[j].solved().cloned().ok_or_else(|| ElabError::Elab {
                msg: match slot_param.get(j).and_then(|&i| all_params.get(i)) {
                    // A value head's escapes are `@` and an annotated
                    // eta-expansion — `name<…>` does not exist for it
                    // (docs/implicit-binders-design.md §7.3).
                    Some(p) if value_head && bare_ref && p.is_type => format!(
                        "cannot infer the type argument `{}` of `{name}` from the \
                         expected type here — write the use fully explicitly \
                         (`@{name}(…)`) or eta-expand with the argument written \
                         (`λ … => {name}(T, …)`)",
                        p.name
                    ),
                    Some(p) if value_head && p.is_type => format!(
                        "cannot infer the type argument `{}` of `{name}` here — no \
                         argument's type mentions it; write the call fully \
                         explicitly (`@{name}(…)`) or eta-expand with the argument \
                         written (`λ … => {name}(T, …)`)",
                        p.name
                    ),
                    // The bare-reference route (design §7.1): there is no
                    // argument whose type could have mentioned anything, so
                    // the message names the only evidence that was consulted.
                    Some(p) if bare_ref && p.is_type => format!(
                        "cannot infer the type argument `{}` of `{name}` from the \
                         expected type here — write `{name}<…>` to give the type \
                         arguments",
                        p.name
                    ),
                    Some(p) if bare_ref => format!(
                        "could not infer the implicit argument `{}` of `{name}` from \
                         the expected type here",
                        p.name
                    ),
                    Some(p) if p.is_type => format!(
                        "cannot infer the type argument `{}` of `{name}` here — no \
                         argument's type mentions it; write `{name}<…>(…)` to give the \
                         type arguments",
                        p.name
                    ),
                    Some(p) => format!(
                        "could not infer the implicit argument `{}` of `{name}`",
                        p.name
                    ),
                    None => format!("could not infer an implicit argument of `{name}`"),
                },
                span,
            })?;
            entries.push(GlobalEntry::Tm(sol));
        }
        let sigma = GlobalSubst { entries };
        let (t, ty) = (t.apply_global(&sigma), ty.apply_global(&sigma));
        if spill.is_empty() {
            return Ok((t, ty, lvl));
        }
        // Past the end of the parameter list, so no goal-name hint can be
        // right: the offset is set beyond it rather than left at 0, which
        // would name the first parameter for an argument that is not it.
        let past = all_params.len();
        self.apply_explicit(cx, Some(name), all_params, past, t, ty, lvl, &spill)
    }

    /// Expected-type-directed solving (docs/unifier-completeness-design.md
    /// §5): the expected type, consulted for the implicits an argument's type
    /// cannot reach. Called from [`Self::apply_implicit`] with the call's
    /// scratch world (`n` metas, `sols` their solutions so far) just before
    /// the deferred-argument retry and the discharge.
    ///
    /// Two rules, the LGG trigger read first and keeping priority for its
    /// shape (design §5.2):
    ///
    /// - **The LGG hook** (issues/congruence-by-anti-unification.md, interim
    ///   round): when the result type is `?f(s) = ?f(t)` with the *same*
    ///   unsolved meta at both heads and `s`, `t` meta-free, and the expected
    ///   type whnf's to an `Id`, run the first-order harvest with `?f`
    ///   withheld, then solve `?f := λz. LGG(X, Y)` with every hole's witness
    ///   pair required to be exactly `(s, t)`. `?f(s) ≟ X` is outside the
    ///   Miller fragment, so no first-order rule may touch it — the
    ///   flex-head guard in [`unify_tm`] now enforces that at the source.
    ///   Once the trigger fires the outcome is **committed**: a mismatching
    ///   witness is reported here, not swallowed into "could not infer".
    ///   This half is still the documented throwaway: the LGG itself lives in
    ///   [`crate::lgg`] and outlives it, but the hook is deleted when a
    ///   layer-m goal solver can construct the call instead.
    ///
    /// - **The general harvest** (design §5.1), the else branch: unify the
    ///   scratch-world result type against the whnf'd expected type,
    ///   learn-only. This is the same call the LGG path makes as its step 1,
    ///   run also when the flex-`Id` trigger does not fire — the general rule
    ///   of which that harvest was the special case. It is what solves
    ///   `sym(?p)`'s endpoints and the bare polymorphic reference's type
    ///   argument (design D1/D2), and it can only *learn*: a wrong solution
    ///   is a kernel rejection, an absent one keeps the caller's message.
    #[allow(clippy::too_many_arguments)]
    fn solve_from_expected(
        &self,
        cx: &Cx,
        result_ty: &Type,
        expected: &Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        span: Span,
    ) -> R<()> {
        // The LGG trigger, read off the scratch-world result type.
        let flex = (|| {
            let Type::Id { lhs, rhs, .. } = result_ty else { return None };
            let (
                Term::App { fun: f_lhs, arg: s_raw, .. },
                Term::App { fun: f_rhs, arg: t_raw, .. },
            ) = (&**lhs, &**rhs)
            else {
                return None;
            };
            let Term::GlobalTm { var, subst } = &**f_lhs else { return None };
            // Unsolved, one of *this* call's metas, the same on both sides,
            // and at the identity substitution — a solution is scoped in Γ,
            // so anything else is not ours to solve.
            (f_lhs == f_rhs
                && var.0 < n
                && matches!(sols[var.0 as usize], Sol::Unsolved)
                && *subst == LocalSubst::id(&cx.gamma))
            .then(|| (var.0 as usize, Rc::clone(s_raw), Rc::clone(t_raw)))
        })();
        // The general harvest (design §5.1): the LGG's step 1 run on its own
        // whenever the flex-`Id` shape is not in play. This is the answer to
        // the old "nothing else gets to consult the expected type" comment —
        // solving result-only implicits in general *was*
        // elab-unifier-completeness's question, and this round answered it.
        let Some((m, s_raw, t_raw)) = flex else {
            let head = self.whnf(cx, expected, span)?;
            unify_ty(&cx.gamma, result_ty, &head, n, 0, sols);
            return Ok(());
        };
        // Step 1, with `?f` withheld (unsolved-but-untouchable — `unify_tm`
        // records only into `Unsolved`, and the flex-head guard skips the
        // spines it heads). The pattern is in the scratch world and the
        // subject in the committed one, exactly as at an argument's domain.
        sols[m] = Sol::Withheld;
        unify_ty(&cx.gamma, result_ty, expected, n, 0, sols);
        sols[m] = Sol::Unsolved;
        // `s` and `t` must be meta-*free* once the solved metas are
        // substituted away: the witnesses are compared with `==`, and an
        // unsolved meta is not a term (decision 2).
        let (Some(s), Some(t)) = (zonked_tm(&s_raw, n, sols), zonked_tm(&t_raw, n, sols)) else {
            return Ok(());
        };
        let Type::Id { lhs: x, rhs: y, .. } = self.whnf(cx, expected, span)? else {
            return Ok(());
        };
        // The abstraction's domain is `?f`'s *declared* parameter type — the
        // only place it can come from, since no argument has it. It is a `Π`
        // by construction of the trigger (a meta that is applied), and its
        // own metas are solved by now or the call could not have got here.
        let dom_ty = &meta_doms[m];
        let Some(dom_ty) = zonked(dom_ty, n, sols) else { return Ok(()) };
        let Type::Pi { dom_level, cod_level, dom, .. } = self.whnf(cx, &dom_ty, span)? else {
            return Ok(());
        };
        let body = lgg::lgg_body(&x, &y, &s, &t)
            .map_err(|msg| ElabError::Elab { msg, span })?;
        sols[m] = Sol::Solved(Rc::new(Term::Lam {
            dom_level,
            cod_level,
            dom,
            body: Rc::new(body),
        }));
        Ok(())
    }

    // -- names --------------------------------------------------------------

    /// Does a bare `name` in this context resolve to a **committed global**
    /// with a non-empty *leading implicit prefix* in its parameter list — the
    /// precondition of the bare-reference route
    /// (docs/unifier-completeness-design.md §5.3)? Returns the prefix length.
    ///
    /// The precedence checks replicate [`Self::resolve`]'s order exactly:
    /// locals, aliases and constructors keep their existing wins, `Zero`/
    /// `Succ` stay primitives, a `meta fn` slice stays pure quotation, and
    /// the enclosing declaration's own name stays a recursion marker. The
    /// route runs only when `resolve` would land on the global anyway.
    /// The implicitness skeleton a bare `name` offers as a *value* head: the
    /// local binder's `Cx` entry or the alias's, following [`Self::resolve`]'s
    /// precedence exactly (an alias bound at depth `d` shadows every binder
    /// at position `< d`), so a skeleton is consulted only for the entity the
    /// name resolves to (docs/implicit-binders-design.md §4.1). `None` for
    /// anything that is not a local or alias — a global's metadata is
    /// `ParamMeta`, not a skeleton.
    fn value_skel(&self, cx: &Cx, name: &str) -> Option<Rc<Skel>> {
        if name == "Zero" || name == "Succ" {
            return None;
        }
        let local_pos = cx.names.iter().rposition(|n| n == name);
        let alias = cx.aliases.iter().rev().find(|a| a.name == *name);
        match (local_pos, alias) {
            (Some(pos), Some(a)) if a.depth <= pos => cx.skels[pos].clone(),
            (_, Some(a)) => a.skel.clone(),
            (Some(pos), None) => cx.skels[pos].clone(),
            (None, None) => None,
        }
    }

    fn bare_implicit_prefix(&self, cx: &Cx, name: &str) -> Option<usize> {
        if name == "Zero" || name == "Succ" || cx.meta.is_some() {
            return None;
        }
        if cx.names.iter().any(|n| n == name)
            || cx.aliases.iter().any(|a| a.name == *name)
            || self.ctor_of(name).is_some()
            || cx.selfref.as_ref().is_some_and(|s| s.name == *name)
        {
            return None;
        }
        self.lookup_global(name)?;
        let prefix = self
            .params_of(name)
            .iter()
            .take_while(|p| p.implicit)
            .count();
        (prefix > 0).then_some(prefix)
    }

    fn resolve(&self, cx: &Cx, name: &str, span: Span) -> R<(Term, Type, Level)> {
        if name == "Zero" {
            return Ok((Term::Zero, Type::Nat, Level::Zero));
        }
        // `Succ` as a *value*: the kernel has it as a term former, not a
        // global, so there is nothing to pass and the η-expansion is built here
        // (docs/constructor-function-values.md §2.1). Unlike a declared
        // constructor this needs no expected type — its type is a constant —
        // which is what makes `p.cong(Succ)` work even though `cong`'s
        // implicits put the argument in *inference* position.
        //
        // Checked before locals, like `Zero`: `Succ(x)` in the application arm
        // already ignores shadowing, and the two must agree.
        if name == "Succ" {
            let nat = || Rc::new(Type::Nat);
            return Ok((
                Term::Lam {
                    dom_level: Level::Zero,
                    cod_level: Level::Zero,
                    dom: nat(),
                    body: Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0))))),
                },
                Type::Pi {
                    dom_level: Level::Zero,
                    cod_level: Level::Zero,
                    dom: nat(),
                    cod: nat(),
                },
                Level::Zero,
            ));
        }
        // Locals and `let` aliases, innermost first. An alias bound at depth
        // `d` shadows every binder at position `< d` and is shadowed by the
        // rest, which is what compares the two here.
        let local_pos = cx.names.iter().rposition(|n| n == name);
        let alias = cx.aliases.iter().rev().find(|a| a.name == *name);
        match (local_pos, alias) {
            (Some(pos), Some(a)) if a.depth <= pos => return Ok(self.local(cx, pos)),
            (_, Some(a)) => {
                // Inlined at the use site, shifted across the binders pushed
                // since it was bound (same as a `fn` definition's globals).
                let by = (cx.names.len() - a.depth) as u32;
                return Ok(((*a.term).shift_local(by), a.ty.shift_local(by), a.level.clone()));
            }
            (Some(pos), None) => return Ok(self.local(cx, pos)),
            (None, None) => {}
        }
        if let Some((ind, i)) = self.ctor_of(name) {
            return self.infer_ctor(cx, &ind, i, &[], span);
        }
        // The enclosing declaration's own name: only a saturated, guarded
        // *call* means anything (it is the induction hypothesis, not a value).
        if cx.selfref.as_ref().is_some_and(|s| s.name == name) {
            return err(
                format!("`{name}` can only be used here as a saturated recursive call"),
                span,
            );
        }
        match self.lookup_global(name) {
            Some(GlobalInfo { abs, .. }) => {
                let len = self.psi.bindings.len() as u32;
                // The goals sit innermost, so a committed binding is that much
                // further out — and so do a `meta fn`'s Ψ-extending binders
                // (its `Ctx` binder, each hoisted letbox global, a `match code`
                // branch telescope). A layer-m term *may* name a layer-c
                // global (`i' ≤ i`, typing.rs:756), which is what lets an
                // analyzer's arms call ordinary library functions
                // (docs/certgen-transcriber-in-language-design.md §4); the
                // index arithmetic is the only thing that ever stopped it.
                // The two paddings never combine: goals are refused inside a
                // `meta fn`.
                let meta_off = self.meta_pushed.borrow().len() as u32;
                let var = GlobalVar(len - 1 - abs + self.goal_base + meta_off);
                let GlobalBinding::Tm { ty, level, .. } =
                    &self.psi.bindings[*abs as usize]
                else {
                    unreachable!("global index points at a non-Trm binding");
                };
                // Stored scoped in its prefix of Ψ; rescope to the full Ψ
                // (the kernel's own lookup convention, typing.rs). This needs
                // no goal offset of its own: `var.0` already carries it.
                let ty = ty.shift_global(var.0 + 1);
                // The binding is closed (· ⊢), so the delayed substitution
                // is the empty map out of the current Γ.
                let subst = LocalSubst {
                    tail: SubstTail::Empty {
                        len: cx.gamma.entries.len() as u32,
                        base: cx.gamma.base,
                    },
                    terms: vec![],
                };
                // …and the *type* travels the same way: `T[δ]`, exactly the
                // kernel's own rule for `u^δ` (typing.rs, `tm_infer`). A
                // closed statement can still mention globals, and each such
                // occurrence carries a `·^k` tail recording the Γ it was
                // written in — `k = 0` here, so it must be re-tailed to this
                // Γ or the kernel rejects it as a `SubstMismatch`. Invisible
                // while `fn`s were inlined, because then a closed statement
                // really had nothing delayed inside it.
                let ty = ty.apply_local(&subst);
                Ok((Term::GlobalTm { var, subst }, ty, level.clone()))
            }
            // The last stop for every written name, so this is where an
            // ambiguity has to surface as an ambiguity rather than as an
            // absence (docs/modules-design.md §4).
            None => {
                // `G::AddCommMonoid` — a class **at a type**, resolved. Here
                // and not earlier: a registered instance is an ordinary global
                // and was found above, so this reaches only the carriers that
                // have none (docs/traits-type-projection-design.md §5).
                if let Some(r) = self.class_at_type(cx, name, &[], span) {
                    return r;
                }
                // A name the constraint list bound twice over binds nothing
                // (§5.2), and saying so names both constraints.
                if let Some((_, why)) = cx.index_ambiguity.iter().find(|(n, _)| n == name) {
                    return err(why.clone(), span);
                }
                Err(self.name_miss(name, format!("unbound name `{name}`"), span))
            }
        }
    }

    // -- kernel oracle ------------------------------------------------------

    /// [`Self::whnf`] for a term: δ against Ψ included, so a definition
    /// unfolds. Used where a *shape* has to be read off a computed term.
    pub(crate) fn whnf_tm(&self, cx: &Cx, t: &Term, span: Span) -> R<Rc<Term>> {
        let psi = self.oracle_psi();
        whnf_term_delta(t, &cx.gamma, Defs::transparent(&psi), self.fuel)
            .map(Rc::new)
            .map_err(|_| ElabError::Elab { msg: "out of fuel reducing a term".into(), span })
    }

    fn whnf(&self, cx: &Cx, ty: &Type, span: Span) -> R<Type> {
        // A reference to a registered lowering reduces back to the **registry's
        // own copy**, not to the kernel's lazy decode of it
        // (`docs/wf-shape-code-design.md` §3.3). The two are the same type; the
        // decode's spelling is `Wf(El ⌜S⌝). n` with every component still
        // `El`-wrapped, and the whole elaborator — every structural reader, and
        // every *guard* that hands out a reference — anchors on the inline
        // identity. Without this a value built at a respelled expected type
        // carries the decode's spelling into all its annotations, where no
        // respell can name it: measured at the constructor-value sites, half
        // of a value-heavy statement's mass was decoded copies nothing could
        // collapse. This is `unspell_ty_deep`'s doctrine (unfolding-for-
        // analysis at the boundary) applied one step earlier, at the one
        // choke point every structural read goes through.
        if let Some(inline) = self.unspell_here(ty) {
            return Ok(inline);
        }
        let psi = self.oracle_psi();
        whnf_type_delta(ty, &cx.gamma, Defs::transparent(&psi), self.fuel)
            .map_err(|_| ElabError::Elab { msg: "out of fuel reducing a type".into(), span })
    }

    /// Expose just enough of a lazy `El(code)` to give a human its decoded
    /// head. Keep this separate from checking: a hostile or merely long
    /// definition chain falls back to the original, budget-bounded `Debug`
    /// rendering instead of consuming elaboration fuel or changing the type.
    fn display_type(&self, cx: &Cx, ty: &Type) -> String {
        let raw = || dress_true(&format!("{ty:?}"));
        if !matches!(ty, Type::El { .. }) {
            return raw();
        }

        let psi = self.oracle_psi();
        let defs = Defs::transparent(&psi);
        let mut head = ty.clone();
        for _ in 0..DISPLAY_DECODE_STEPS {
            let Some(next) = step_type_delta(&head, &cx.gamma, defs) else {
                return raw();
            };
            head = next;
            if !matches!(head, Type::El { .. }) {
                return dress_true(&format!("{head:?}"));
            }
        }
        raw()
    }

    /// [`Self::delta_psi`], padded with the meta binders currently in scope
    /// (docs/in-language-map-design.md §5): during a `meta fn`'s elaboration
    /// the innermost `GlobalVar`s are its `Ctx`/`TyCode`/letbox binders, and
    /// δ-consultation with an unpadded Ψ would resolve them to the wrong
    /// bindings. Identical to `delta_psi` everywhere else.
    fn oracle_psi(&self) -> GlobalCtx {
        let mp = self.meta_pushed.borrow();
        if mp.is_empty() {
            return self.delta_psi.clone();
        }
        let mut bindings = (*self.delta_psi.bindings).clone();
        bindings.extend(mp.iter().cloned());
        GlobalCtx::new(bindings)
    }

    /// Rebuild [`Self::delta_psi`]. Called wherever Ψ or `goal_base` moves.
    fn refresh_delta_psi(&mut self) {
        if self.goal_base == 0 {
            self.delta_psi = self.psi.clone();
            return;
        }
        let mut bindings = (*self.psi.bindings).clone();
        bindings.resize(
            bindings.len() + self.goal_base as usize,
            GlobalBinding::Tm {
                ctx: LocalCtx::nil(),
                layer: Layer::Code,
                ty: Rc::new(Type::Nat),
                level: Level::Zero,
                body: None,
            },
        );
        self.delta_psi = GlobalCtx::new(bindings);
    }
}

/// The enclosing declaration, in scope throughout its own body so that a
/// structurally guarded self-call can lower to the induction hypothesis
/// (issues/match-recursion.md). Nothing else can reference it: the name is
/// only registered as a global once the declaration is checked.
struct SelfRef {
    name: String,
    /// `(parameter name, implicit?)` in declaration order. Parameter `j` is
    /// bound at position `j` of the body's `Cx` (the telescope goes first).
    params: Vec<(String, bool)>,
    /// How many leading entries of [`Self::params`] are `<A, …>` type
    /// parameters. They are never passed at a call site — neither implicitly
    /// nor under `@`, which now controls only the *value* implicits
    /// (issues/at-and-type-arguments.md) — so they are skipped wholesale
    /// rather than filtered by implicitness.
    n_tyvars: usize,
}

/// The enclosing recursion's window of past values, as a nested `match` on the
/// chain's end needs it — see [`Elaborator::chain_convoy`], which builds one,
/// and `docs/course-of-values-recursion-design.md` §5 for why passing it
/// through the `match` is what makes the deeper values usable.
struct Convoy {
    dec: usize,
    preds: Vec<usize>,
    /// How many values are carried.
    d: usize,
    lvl: Level,
    /// The recursion's motive reindexed into the context the nested `match`
    /// sits in, scoped in (that context, z).
    motive: Type,
    /// …and as it was written, for the guards this `match` hands to its arms:
    /// they must be able to reindex it again, deeper in.
    outer_motive: Rc<Type>,
    gamma: LocalCtx,
    /// The window itself, at the nested `match`'s context.
    tuple: Term,
    /// How far the window's **anchor** sits above this `match`'s scrutinee.
    ///
    /// The window always holds the values at the chain read from its head:
    /// component `i` is the value at `preds[i]`, so it is anchored at
    /// `preds[0]` however deep the nesting has gone. The first nested `match`
    /// scrutinizes that head and lifts by nothing; the second scrutinizes the
    /// value one below it, so its window is the same window at `Succ` of its
    /// own scrutinee — and so on down. Re-indexing at the scrutinee instead
    /// would slide every component by one and typecheck nowhere.
    lift: usize,
}

impl Convoy {
    /// `Succ^lift(t)` — where the window's head sits, seen from a term at this
    /// `match`'s scrutinee.
    fn anchor(&self, t: Term) -> Term {
        (0..self.lift).fold(t, |t, _| Term::Succ(Rc::new(t)))
    }

    /// The guard for one arm: the window is now the arm's own binder, and
    /// `new_pred` is the predecessor that arm binds — `None` for the `Zero`
    /// arm, which extends the chain by nothing.
    fn guard_at(&self, comps: &[Type], depth: usize, new_pred: Option<usize>) -> Rc<Guard> {
        let mut preds = self.preds.clone();
        preds.extend(new_pred);
        Rc::new(Guard {
            dec: self.dec,
            kind: GuardKind::Nat {
                preds,
                // Shifted past the convoy binder itself, which every caller
                // pushes immediately before asking for this.
                comps: comps.iter().map(|c| c.shift_local(1)).collect(),
                tuple: Term::Var(LocalVar(0)),
                mlvl: self.lvl.clone(),
                depth,
                motive: Rc::clone(&self.outer_motive),
                gamma: self.gamma.clone(),
            },
            rebind: None,
        })
    }
}

/// What a guarded self-call must look like inside a `match` arm, and what it
/// lowers to (issues/match-recursion.md).
struct Guard {
    /// Index of the parameter the recursion descends on.
    dec: usize,
    kind: GuardKind,
    /// An indexed `match`'s index parameter, *rebound* by the arm
    /// (docs/inductive-indexed-lowering.md §6): a self-call must pass the
    /// arm's pattern variable there, not the original parameter.
    ///
    /// `(parameter position, one index term per descendant)` — parallel to
    /// [`GuardKind::Wf`]'s `children` and scoped at the same `depth`, because
    /// a branching index constructor gives each recursive field its *own*
    /// pattern variable (`Bal(SNode(l, r))`), and the ih at descendant `t`
    /// lives at exactly that one. `None` for every non-indexed guard.
    rebind: Option<(usize, Vec<Rc<Term>>)>,
}

/// The two arm shapes a self-call can sit in. They differ in how many
/// descendants an arm has — one for `Nat`, `mᵢ` for a branching constructor —
/// and correspondingly in whether the ih is a variable or a function of the
/// index (`docs/inductive-tier1-wf-lowering.md` §6.4).
enum GuardKind {
    /// A `Succ(k)` arm. Positions are *absolute* (indices into `cx.names`,
    /// outermost first) so they stay valid as inner binders are pushed.
    Nat {
        /// The chain of predecessors this arm makes available, outermost
        /// first: `preds[0]` is the `k` the arm itself binds, `preds[1]` the
        /// `l` a nested `match k` binds, and so on
        /// (issues/recursion-at-deeper-subterms.md). A self-call descending to
        /// `preds[i]` lowers to the `i`-th component of [`Self::tuple`].
        ///
        /// One entry for the ordinary one-step recursion; the chain grows only
        /// where the arm's own body scrutinizes the predecessor again, and
        /// only by being convoyed through that `match`
        /// (docs/course-of-values-recursion-design.md §5).
        preds: Vec<usize>,
        /// The window of past values in scope: the ih binder itself for the
        /// ordinary recursion, a Σ-tuple of the last `comps.len()` values
        /// above that. Scoped at [`Self::depth`] binders, like
        /// [`GuardKind::Wf`]'s `children`, so a call from deeper inside the
        /// arm shifts it by the difference.
        tuple: Term,
        /// Its component types, at the same scope. `comps.len()` is the depth
        /// the recursion was *elaborated* for: a call below the chain's end
        /// but within it is what a nested `match` unlocks, and a call below
        /// `comps.len()` has no component to become — the refusal
        /// `elab_self_call` reports.
        comps: Vec<Type>,
        /// The level every component lives at.
        mlvl: Level,
        /// Binder count at the arm's ih — the scope [`Self::tuple`] lives in.
        depth: usize,
        /// The recursion's motive, scoped in ([`Self::gamma`], z), kept so a
        /// nested `match` can rebuild the window's type at *its* scrutinee.
        /// The pair travels together because reindexing a family needs the
        /// context it was written in, which a shift cannot recover.
        motive: Rc<Type>,
        gamma: LocalCtx,
    },
    /// A `Wf` arm: one entry per recursive field, as
    /// `(the child's term, `ih' ι_t`, its type, that type's level)`. All four
    /// are scoped at `depth` binders, so a call from deeper inside the arm
    /// shifts them by the difference.
    ///
    /// The match is on the *term*, not the name: an arm binder is an alias
    /// (tier 0 §5.1), not a kernel binder, so there is no position to compare,
    /// and comparing terms is what keeps shadowing from faking a guarded call.
    Wf {
        depth: usize,
        children: Vec<(Rc<Term>, Rc<Term>, Type, Level)>,
        /// The arm's *container* field, if it has one
        /// (`docs/container-fields.md` §4.2). A container is a group of
        /// children rather than one, so a self-call over it maps rather than
        /// descends — and the thing it maps to is the ih *tabulated* over the
        /// container's index range.
        container: Option<ContainerIh>,
    },
}

/// What a self-call over a container binder needs, gathered at the arm and
/// scoped like the rest of [`GuardKind::Wf`], at `depth` binders.
#[derive(Clone)]
struct ContainerIh {
    /// The container binder's own term (`snd^m cs`), matched against the
    /// call's elaborated argument exactly as a plain child's term is.
    term: Rc<Term>,
    /// Its length.
    len: Rc<Term>,
    /// The ih function `Π(i : Fin (Succ^m len)). M`, as a term.
    ih: Rc<Term>,
    /// `m`: how many plain children precede the container, and so how far the
    /// container's indices are offset inside `Fin (Succ^m len)`.
    plain: usize,
    /// The motive, *strengthened* — a self-call over a container maps to a
    /// `Vec` of results, which requires a motive independent of the scrutinee
    /// (`docs/container-fields.md` §4.3). `None` when it depends, in which case
    /// [`ContainerIh::eq`] decides whether this is phase 3 or a diagnostic.
    result: Option<Type>,
    /// The motive read as an **equation**, when it is one — phase 3
    /// (`docs/container-proofs.md` §5). Set only when `result` is `None`: a
    /// dependent motive `Id^l(A; lhs(z); rhs(z))` whose *type* `A` does not
    /// mention `z` still relates the two children vectors pointwise, which is
    /// what `vec::tab_cong` turns into an equation between them.
    eq: Option<EqSplit>,
    /// The ih's own Π type, so a call site annotates its application with the
    /// codomain the eliminator actually gave rather than rebuilding it — the
    /// rebuild is only correct for a strengthened motive, and phase 3's is not.
    ih_ty: Type,
    /// `⟦D⟧`, the container's element type, for `nth` at the call site.
    elem: Type,
    /// `l`: the declaration's level, which is `⟦D⟧`'s. Not `mlvl`, which is the
    /// motive's — `nth` and the endpoint applications need this one.
    level: Level,
    mlvl: Level,
}

/// A dependent motive that is an equation, split into its two endpoints
/// (`docs/container-proofs.md` §5).
#[derive(Clone)]
struct EqSplit {
    /// The level `Id^l` is at, which is `A`'s.
    level: Level,
    /// `A`, the type the equation is at — strengthened, so it may not mention
    /// the scrutinee. A heterogeneous motive is out of scope and diagnosed
    /// (`issues/dependent-field-injectivity.md` holds the transport question).
    ty: Type,
    /// `λ(z : ⟦D⟧). lhs` and `λ(z : ⟦D⟧). rhs`. Kept as *functions* rather than
    /// as open terms so that a call site can shift them like any other term and
    /// apply them to a child; the β-redex this leaves is what conversion is for.
    lhs: Rc<Term>,
    rhs: Rc<Term>,
}

/// Elaboration context: kernel Γ plus the parallel name list
/// (`names[j]` names `gamma.entries[j]`, outermost first).
#[derive(Clone)]
struct Cx {
    names: Vec<String>,
    gamma: LocalCtx,
    /// Parallel to `names`/`gamma.entries`: the implicitness skeleton of the
    /// binder's *written* type, where it had one
    /// (docs/implicit-binders-design.md §3.1). Maintained by [`Cx::push`]
    /// (defaulting `None`) and [`Cx::push_skel`] — one push path, so the
    /// vectors cannot desync. Nothing in a skeleton is subject to
    /// substitution or shifting (§3.2), so entries are never updated.
    skels: Vec<Option<Rc<Skel>>>,
    /// The declaration being elaborated, once its telescope is in scope.
    selfref: Option<Rc<SelfRef>>,
    /// Set inside a `Succ(k)` arm; `None` outside every such arm, where a
    /// self-call has no induction hypothesis to become.
    guard: Option<Rc<Guard>>,
    /// `let` bindings in scope, outermost first. Not kernel binders: an alias
    /// is inlined at each use, so `Γ` is unchanged.
    aliases: Vec<Rc<Alias>>,
    /// An `inductive`'s type parameters, while its field types are being
    /// lowered at an instantiation. Empty everywhere else: type parameters are
    /// monomorphized, so they never survive into a kernel term.
    tyvars: Vec<TyVar>,
    /// Class dictionaries in scope, outermost first, **as written**
    /// (docs/operation-indexed-classes-design.md §5, ladder step 2). A value
    /// index is never searched for; where it is not already ground it comes
    /// from a binder of the goal's class — or of a descendant — whose own index
    /// pins it, and that index is a surface expression valid in this very
    /// context. Empty for every declaration with no class binder, which is what
    /// keeps the whole mechanism off code that has nothing to do with classes.
    dicts: Vec<Rc<DictBinder>>,
    /// Index names that a *repeated* constraint left bound to nothing
    /// (`docs/operation-indexed-classes-design.md` §5.2), with the refusal
    /// each one owes. Consulted only where the answer would otherwise have
    /// been "unbound name".
    index_ambiguity: Vec<(String, String)>,
    /// Operator symbols a constraint binder **installed**, as (symbol, the
    /// index binder's generated name) — the first rung of a symbol's
    /// resolution (docs/operators-onto-classes-design.md §4, §5).
    ///
    /// `<A: Monoid(+)>` puts `("+", "#op+@0_0")` here for the whole
    /// declaration, signature and body alike, which is what makes
    /// `x + A.unit` in a *result type* the bound index rather than an ambient
    /// operator. Later entries shadow earlier ones. Empty for every
    /// declaration that names no symbol, which is every declaration written
    /// before this round.
    op_locals: Vec<(String, String)>,
    /// The meta-layer binder environment, present exactly while a `meta fn`'s
    /// body — or a quote payload inside it — elaborates
    /// (docs/in-language-map-design.md §5). `None` everywhere else, which is
    /// what keeps the entire quotation machinery inert for ordinary code.
    meta: Option<Rc<quote::MetaEnv>>,
}

/// One type parameter, bound to the type it is instantiated at
/// (`docs/inductive-tier0-lowering.md` §3.1).
///
/// `depth` is `names.len()` at the binding — the same device [`Alias`] uses,
/// and needed for the same reason. The instantiation is lowered in the
/// *ambient* context, and the constructor's field spine then pushes the
/// nominal tag and every earlier field on top of it, so a use in field `j`
/// sits `1 + j` binders deeper than where its type is scoped and must be
/// weakened by exactly that.
///
/// Getting this wrong is invisible for a *closed* instantiation, which is
/// every instantiation the suite had until 2026-07-26
/// (issues/tyvar-scoping-in-lowered-fields.md). The surface's one
/// context-dependent type is `=`, whose endpoints are terms.
#[derive(Clone)]
struct TyVar {
    name: String,
    ty: Type,
    level: Level,
    depth: usize,
}

/// A `let`-bound name: the elaborated right-hand side, inlined at every use
/// (the same doctrine as an inlined `fn`). `depth` is `names.len()` at the
/// binding, which is what decides shadowing against ordinary binders and how
/// far a use must be shifted.
struct Alias {
    name: String,
    depth: usize,
    term: Rc<Term>,
    ty: Type,
    level: Level,
    /// The alias's implicitness skeleton, when its `let` annotation, its
    /// RHS lambda's written marks, or the record field it projects carried
    /// one (docs/implicit-binders-design.md §3.1). `None` everywhere else.
    skel: Option<Rc<Skel>>,
}

impl Cx {
    fn empty() -> Cx {
        Cx {
            names: vec![],
            gamma: LocalCtx::nil(),
            skels: vec![],
            selfref: None,
            guard: None,
            aliases: vec![],
            tyvars: vec![],
            dicts: vec![],
            index_ambiguity: vec![],
            op_locals: vec![],
            meta: None,
        }
    }

    fn push(&mut self, name: String, ty: Type, level: Level) {
        self.push_skel(name, ty, level, None);
    }

    /// [`Cx::push`] for the sites that carry an implicitness skeleton: the
    /// declaration telescope loop, `elab_ty`'s `Fn` arm, and the lambda
    /// binder pushes (docs/implicit-binders-design.md §3.1).
    fn push_skel(&mut self, name: String, ty: Type, level: Level, skel: Option<Rc<Skel>>) {
        self.names.push(name);
        self.gamma.entries.push(CtxEntry { ty: Rc::new(ty), level });
        self.skels.push(skel);
    }
}

/// A class dictionary in scope, as the declaration wrote it
/// (`docs/operation-indexed-classes-design.md` §5). The carrier and the index
/// are **surface** and are re-elaborated in the context that consults them,
/// which is what keeps the index an ordinary expression of the use site rather
/// than a kernel term that would have to be re-scoped.
#[derive(Clone)]
struct DictBinder {
    /// The binder's own name, where it has a spellable one — what `d.op`
    /// looks itself up by. `#`-prefixed for an inline constraint, which
    /// deliberately offers no way to project the dictionary and therefore no
    /// way to reach this either.
    name: String,
    /// The class, as written — resolved through the ordinary name regime.
    class: String,
    carrier: Ty,
    index: Vec<Expr>,
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
            TyKind::OfExpr(e) => expr(e, n),
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
            | ExprKind::OpSymbol(_)
            | ExprKind::Num(_)
            | ExprKind::Refl
            | ExprKind::Univ { .. } => {}
            // The empty block's speculative `refl` may fail, and then it
            // raises a goal — so it must be counted. The pre-count is
            // documented as an upper bound, so counting one that turns out to
            // be discharged by `refl` costs a reserved-but-unused slot and
            // nothing else (issues/auto-refl-empty-block.md).
            ExprKind::AutoRefl => *n += 1,
            ExprKind::App { head, args, .. } => {
                expr(head, n);
                args.iter().for_each(|a| expr(a, n));
            }
            // A type argument can contain a hole (`f<a = ?p>(…)`), and the
            // pre-count is the one thing the goal mechanism cannot survive
            // under-counting (see this function's doc comment).
            ExprKind::TyApp { head, args } => {
                expr(head, n);
                args.iter().for_each(|t| ty(t, n));
            }
            ExprKind::Lam { binders, body } => {
                binders.iter().filter_map(|b| b.ty.as_ref()).for_each(|t| ty(t, n));
                expr(body, n);
            }
            ExprKind::VecLit(elems) => elems.iter().for_each(|x| expr(x, n)),
            ExprKind::Index { recv, idx } => {
                expr(recv, n);
                expr(idx, n);
            }
            // The receiver counts whether or not `.f` turns out to be a
            // projection: the method fallback re-elaborates it as an argument,
            // and a hole is keyed by span, so one syntactic hole stays one
            // goal either way.
            ExprKind::Dot { recv, args, .. } => {
                expr(recv, n);
                args.iter().flatten().for_each(|a| expr(a, n));
            }
            ExprKind::RecordLit { tyargs, fields, .. } => {
                tyargs.iter().for_each(|t| ty(t, n));
                fields.iter().for_each(|f| expr(&f.expr, n));
            }
            ExprKind::Match { scrut, motive, arms, eqbind: _, form: _, generated: _ } => {
                expr(scrut, n);
                if let Some(m) = motive {
                    expr(m, n);
                }
                arms.iter().for_each(|a| expr(&a.body, n));
            }
            ExprKind::MatchCode { scrut, motive, arms } => {
                expr(scrut, n);
                ty(motive, n);
                arms.iter().for_each(|a| expr(&a.body, n));
            }
            ExprKind::J { proof, motive, case, .. } => {
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

/// Syntactic upper bound on the goals a declaration can raise: every `?` in
/// it. An *upper* bound, not the count — `calc` clones sub-expressions into
/// its `@trans` spine (parser.rs) and the elaborator visits some expressions
/// twice — which is why goals are numbered in creation order and the unused
/// slots are padded. Under-counting is impossible: nothing invents a hole.
fn count_holes(decl: &Decl) -> u32 {
    use count_holes_impl::{expr, stmts, ty};
    let mut n = 0;
    for p in &decl.params {
        ty(&p.ty, &mut n);
    }
    ty(&decl.result, &mut n);
    stmts(&decl.body.stmts, &mut n);
    expr(&decl.body.result, &mut n);
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
fn strengthen_global(t: &Term, g: u32) -> Term {
    if g == 0 {
        return t.clone();
    }
    let entries = (0..g).map(|_| GlobalEntry::Tm(Rc::new(Term::Zero))).collect();
    t.apply_global(&GlobalSubst { entries })
}

/// Pre-order walk over an expression's subexpressions.
///
/// Total over the forms a *self-call* can hide in, which is what its one
/// caller ([`Elaborator::cov_depth`]) needs; a form missed here can only
/// under-count a depth, and an under-counted depth is the refusal that stood
/// before course-of-values existed, never a wrong term.
fn walk_expr(e: &Expr, f: &mut impl FnMut(&Expr)) {
    f(e);
    let mut go = |e: &Expr| walk_expr(e, f);
    match &e.kind {
        ExprKind::App { head, args, .. } => {
            go(head);
            args.iter().for_each(go);
        }
        ExprKind::TyApp { head, .. } => go(head),
        ExprKind::Lam { body, .. } => go(body),
        ExprKind::VecLit(xs) => xs.iter().for_each(go),
        ExprKind::Eq(a, b) => {
            go(a);
            go(b);
        }
        ExprKind::Match { scrut, arms, .. } | ExprKind::MatchCode { scrut, arms, .. } => {
            go(scrut);
            arms.iter().for_each(|a| go(&a.body));
        }
        ExprKind::Dot { recv, args, .. } => {
            go(recv);
            args.iter().flatten().for_each(go);
        }
        ExprKind::Index { recv, idx } => {
            go(recv);
            go(idx);
        }
        ExprKind::RecordLit { fields, .. } => fields.iter().for_each(|x| go(&x.expr)),
        ExprKind::Block(b) => {
            for s in &b.stmts {
                match s {
                    Stmt::Let { expr, .. } | Stmt::LetRecord { expr, .. } => go(expr),
                    _ => {}
                }
            }
            go(&b.result);
            b.ons.iter().for_each(|o| go(&o.expr));
        }
        ExprKind::Quote(x) | ExprKind::Splice(x) => go(x),
        _ => {}
    }
}

/// `pred(t)`, as the kernel spells it: `elim_Nat(λ _. Nat; 0; λ k ih. k; t)`.
/// Needed because a course-of-values tuple's `i`-th component is the motive at
/// `pred^i z` — and `pred (Succ k) ⇝ k` and `pred 0 ⇝ 0` by computation, which
/// is what makes the step's and the base's annotations line up
/// (issues/recursion-at-deeper-subterms.md).
fn pred_tm(t: Term) -> Term {
    Term::ElimNat {
        level: Level::Zero,
        motive: Rc::new(Type::Nat),
        base: Rc::new(Term::Zero),
        // Scoped in (Γ, k : Nat, ih : Nat): the predecessor, ignoring the ih.
        step: Rc::new(Term::Var(LocalVar(1))),
        scrut: Rc::new(t),
    }
}

/// The component types of the course-of-values tuple at `at`: `M[pred^i at/z]`
/// for `i < d`, scoped in `gamma` extended by `extra` binders (where `at`
/// lives). `d = 1` gives back the plain motive, which is why every caller can
/// use these unconditionally.
fn cov_comps(gamma: &LocalCtx, motive: &Type, d: usize, extra: u32, at: &Term) -> Vec<Type> {
    (0..d)
        .map(|i| {
            let mut t = at.clone();
            for _ in 0..i {
                t = pred_tm(t);
            }
            motive.apply_local(&embed(gamma, extra).extended(Rc::new(t)))
        })
        .collect()
}

/// `Σ(comps[0], Σ(comps[1], …))`, right-nested and non-dependent — the tuple
/// the recursor carries. One component is the motive itself, so the ordinary
/// recursion emits no `Σ` at all.
fn cov_ty(comps: &[Type], lvl: &Level) -> Type {
    let (last, rest) = comps.split_last().expect("a tuple has at least one component");
    rest.iter().rev().fold(last.clone(), |snd, fst| Type::Sigma {
        fst_level: lvl.clone(),
        snd_level: lvl.clone(),
        fst: Rc::new(fst.clone()),
        snd: Rc::new(snd.shift_local(1)),
    })
}

/// The tuple of `vals` at [`cov_ty`]'s type.
fn cov_tuple(comps: &[Type], lvl: &Level, vals: Vec<Term>) -> Term {
    debug_assert_eq!(comps.len(), vals.len());
    let mut vals = vals;
    let mut acc = vals.pop().expect("a tuple has at least one component");
    for (i, fst) in vals.into_iter().enumerate().rev() {
        acc = Term::Pair {
            fst_level: lvl.clone(),
            snd_level: lvl.clone(),
            fst_ty: Rc::new(comps[i].clone()),
            snd_ty: Rc::new(cov_ty(&comps[i + 1..], lvl).shift_local(1)),
            fst: Rc::new(fst),
            snd: Rc::new(acc),
        };
    }
    acc
}

/// `π_i p` — `snd` down to the `i`-th component and `fst` off it, except at the
/// last, which the nesting leaves bare.
fn cov_proj(comps: &[Type], lvl: &Level, p: Term, i: usize) -> Term {
    let ann = |at: usize| {
        (Rc::new(comps[at].clone()), Rc::new(cov_ty(&comps[at + 1..], lvl).shift_local(1)))
    };
    let mut cur = p;
    for at in 0..i {
        let (fst_ty, snd_ty) = ann(at);
        cur = Term::Snd {
            fst_level: lvl.clone(),
            snd_level: lvl.clone(),
            fst_ty,
            snd_ty,
            pair: Rc::new(cur),
        };
    }
    if i + 1 < comps.len() {
        let (fst_ty, snd_ty) = ann(i);
        cur = Term::Fst {
            fst_level: lvl.clone(),
            snd_level: lvl.clone(),
            fst_ty,
            snd_ty,
            pair: Rc::new(cur),
        };
    }
    cur
}

/// The identity substitution of `gamma`, weakened so its source is `gamma`
/// extended by `extra` fresh entries: maps a term scoped in `gamma, z` (once
/// `extended`) into `gamma` + the extra binders.
pub(crate) fn embed(gamma: &LocalCtx, extra: u32) -> LocalSubst {
    let m = gamma.entries.len() as u32;
    let tail = match gamma.base {
        CtxBase::Nil => SubstTail::Empty { len: m + extra, base: CtxBase::Nil },
        CtxBase::Var(g) => SubstTail::Wk { len: m + extra, ctx_var: g },
    };
    let terms = (0..m)
        .map(|j| Rc::new(Term::Var(LocalVar(m + extra - 1 - j))))
        .collect();
    LocalSubst { tail, terms }
}

/// A deferred explicit argument (docs/unifier-completeness-design.md §3.1):
/// **not** a first-class constraint in a queue on the [`Elaborator`], but a
/// record local to one [`Elaborator::apply_implicit`] activation. The scratch
/// world is the constraint store — the domain's meta occurrences *are* the
/// "blocked on" set, and [`zonked`] decides readiness exactly. Cross-call
/// postponement is deliberately not built: a nested call elaborates to
/// completion (or errors) inside its own world before the outer loop
/// continues, so there is nothing an inner call could leave pending that the
/// outer call could later unblock.
struct ResolveOb {
    /// The scratch slot standing for the argument.
    slot: usize,
    /// The parameter's declared domain, scratch world — the goal, once every
    /// meta it mentions is solved (docs/traits-layer2-design.md §4).
    dom: Type,
    dom_level: Level,
    /// Parameter index, for the hint and the message.
    param: usize,
}

struct DeferredArg<'a> {
    /// The withheld slot: the stand-in meta holding the argument's spine
    /// position.
    slot: usize,
    /// The unelaborated surface argument.
    expr: &'a Expr,
    /// Its declared domain, scratch world.
    dom: Type,
    dom_level: Level,
    /// Parameter index, for the goal-name hint and the §7.2 message.
    param: usize,
}

/// Per-slot state of one [`Elaborator::apply_implicit`] scratch world
/// (docs/unifier-completeness-design.md §3). Three states, because two
/// different "unsolved" populations exist and must not be conflated:
///
/// - `Unsolved` — nothing known yet; `unify_ty`/`unify_tm` may record a
///   solution here (and only here).
/// - `Withheld` — unsolved *and untouchable*: a deferred argument's stand-in
///   meta, or a flex-applied meta during the LGG's harvest. [`zonked`] treats
///   it as unsolved (its occurrences must keep blocking dependent domains),
///   while the unifiers refuse to write into it. This replaces the old
///   plant-a-`Term::Zero` placeholder, which made a withheld slot *look*
///   solved to `zonked` — a lie once deferred arguments joined the world.
/// - `Solved(t)` — `t` is a committed-world payload, the convention the
///   unifiers' strengthened subjects already follow.
///
/// Discharge requires `Solved` everywhere; anything else is a per-slot
/// diagnostic (design §7).
#[derive(Clone)]
enum Sol {
    Unsolved,
    Withheld,
    Solved(Rc<Term>),
}

impl Sol {
    fn solved(&self) -> Option<&Rc<Term>> {
        match self {
            Sol::Solved(t) => Some(t),
            _ => None,
        }
    }
}

/// Best-effort structural unification driving implicit-argument solutions
/// (issues/elab-stage2-metas.md). `pat` is a parameter domain in the scratch
/// world (metavariables at Ψ-indices `< n`); `subj` is an argument's inferred
/// type. Solving is deliberately incomplete: this mirrors the fragment of
/// `conv.rs` the Nat suite exercises (`Id`/`Nat` congruence), records a
/// solution whenever a meta meets a rigid subterm, and otherwise makes no
/// claim — an unsolved meta is reported by the caller, a *wrong* solution is
/// caught by the kernel's re-check. It never fails: it only ever *learns*.
/// Congruence through every type former the lowerings build, plus the one
/// rule that makes polymorphism inferable:
///
/// > `El ?A ≟ T` solves `?A := ⌜T⌝` (docs/surface-polymorphism.md §4).
///
/// `d` counts the binders crossed since `gamma` — a `Σ`'s second component, a
/// `Π`'s codomain, a `Wf`'s arity. A meta's solution is scoped in `gamma`, so
/// a candidate found under `d` binders is accepted only if it survives
/// [`strengthen_ty`]. Without that check `f(g)` at `g : (x : Nat) -> Vec(A;
/// x)` would happily solve a meta to a term mentioning `x`, which is
/// ill-scoped where it lands (the kernel would reject it, but a rejection is
/// a worse message than a refusal to guess).
fn unify_ty(
    gamma: &LocalCtx,
    pat: &Type,
    subj: &Type,
    n: u32,
    d: u32,
    sols: &mut [Sol],
) {
    // The `El` rule. Checked before the congruence so that `El ?A` meeting a
    // *decoded* `El t` still solves rather than descending into the code.
    if let Type::El { tm, .. } = pat
        && let Term::GlobalTm { var, subst } = &**tm
        && var.0 < n
    {
        // The Miller-pattern guard (docs/unifier-completeness-design.md §6):
        // the delayed substitution must be exactly the weakened identity
        // `embed(Γ, d)` — the one condition under which taking the
        // strengthened subject verbatim *is* the pattern inversion. Every
        // reachable renaming today is of this class (established structurally
        // and by an instrumented full run, design §6.1); anything else — a
        // non-variable payload, and the today-unreachable permuted or
        // dropping renamings — is declined, which learn-only always permits.
        if matches!(sols[var.0 as usize], Sol::Unsolved)
            && *subst == embed(gamma, d)
            && let Some(s) = strengthen_ty(gamma, subj, d)
            && let Some(c) = code::code_of(&s)
        {
            sols[var.0 as usize] = Sol::Solved(Rc::new(c));
        }
        return;
    }
    // The subject may be `El` of a canonical code rather than the former
    // itself — a record field read off a type that arrived through a
    // `Val -> Type` *value* is exactly that (docs/record-type-values.md §4).
    // `decoded` is the same context-free strip the structural readers of
    // `inductive.rs` use: canonical codes only, never a neutral, so this walk
    // still does no δ. Below the pattern's own `El` rule, which must keep
    // seeing an undecoded subject so `El ?A` solves whole.
    let subj = &*inductive::decoded(subj);
    match (pat, subj) {
        (
            Type::Id { ty: t1, lhs: a1, rhs: b1, .. },
            Type::Id { ty: t2, lhs: a2, rhs: b2, .. },
        ) => {
            unify_ty(gamma, t1, t2, n, d, sols);
            unify_tm(gamma, a1, a2, n, d, sols);
            unify_tm(gamma, b1, b2, n, d, sols);
        }
        // `Π`/`Σ`/`W` bind in their second component; `+` does not.
        (
            Type::Pi { dom: a1, cod: b1, .. },
            Type::Pi { dom: a2, cod: b2, .. },
        )
        | (
            Type::Sigma { fst: a1, snd: b1, .. },
            Type::Sigma { fst: a2, snd: b2, .. },
        )
        | (
            Type::W { shape: a1, pos: b1, .. },
            Type::W { shape: a2, pos: b2, .. },
        ) => {
            unify_ty(gamma, a1, a2, n, d, sols);
            unify_ty(gamma, b1, b2, n, d + 1, sols);
        }
        (Type::Sum { lhs: a1, rhs: b1, .. }, Type::Sum { lhs: a2, rhs: b2, .. }) => {
            unify_ty(gamma, a1, a2, n, d, sols);
            unify_ty(gamma, b1, b2, n, d, sols);
        }
        (Type::Vec { elem: e1, len: k1, .. }, Type::Vec { elem: e2, len: k2, .. }) => {
            unify_ty(gamma, e1, e2, n, d, sols);
            unify_tm(gamma, k1, k2, n, d, sols);
        }
        // A `Wf`'s arity is scoped under its shape binder — the same +1 a `Σ`
        // tail gets, and the reason this is not a flat structural walk.
        (
            Type::Wf { shape: s1, arity: a1, .. },
            Type::Wf { shape: s2, arity: a2, .. },
        ) => {
            unify_ty(gamma, s1, s2, n, d, sols);
            unify_tm(gamma, a1, a2, n, d + 1, sols);
        }
        (Type::Fin { len: k1 }, Type::Fin { len: k2 }) => {
            unify_tm(gamma, k1, k2, n, d, sols);
        }
        (Type::El { tm: t1, .. }, Type::El { tm: t2, .. }) => {
            unify_tm(gamma, t1, t2, n, d, sols);
        }
        // `Nat`/`Unit`/`Empty`/`Ty` and every mismatched pairing: nothing to
        // learn. A mismatch is not an error here — this function only ever
        // learns, and the kernel is what decides whether the call typechecks.
        _ => {}
    }
}

/// Term-level companion of [`unify_ty`]. When `pat` is an unsolved
/// metavariable under the weakened identity renaming `embed(Γ, d)` (the
/// Miller pattern condition, in the one class reachable today — design §6),
/// record the strengthened subject; otherwise recurse through matching heads
/// toward nested metas. For an occurrence `?m^{embed(Γ,d)}` and a subject `s`
/// with `strengthen_tm(Γ, s, d) = Some(s₀)`, the recorded `?m := s₀`
/// satisfies `s₀[embed(Γ,d)] = s₀.shift(d) = s` — the verbatim take plus the
/// strengthening that already runs *is* the inversion for this class.
/// How many arguments a spine applies. Used only by the equal-arity rule.
fn spine_len(mut t: &Term) -> usize {
    let mut k = 0;
    while let Term::App { fun, .. } = t {
        k += 1;
        t = fun;
    }
    k
}

/// Is this spine headed by a **committed** global — one outside this call's
/// scratch world? A meta head at either end is what the guard exists for.
fn rigid_global_head(mut t: &Term, n: u32) -> bool {
    while let Term::App { fun, .. } = t {
        t = fun;
    }
    matches!(t, Term::GlobalTm { var, .. } if var.0 >= n)
}

fn unify_tm(
    gamma: &LocalCtx,
    pat: &Term,
    subj: &Term,
    n: u32,
    d: u32,
    sols: &mut [Sol],
) {
    if let Term::GlobalTm { var, subst } = pat
        && var.0 < n
    {
        if matches!(sols[var.0 as usize], Sol::Unsolved)
            && *subst == embed(gamma, d)
            && let Some(s) = strengthen_tm(gamma, subj, d)
        {
            sols[var.0 as usize] = Sol::Solved(Rc::new(s));
        }
        return;
    }
    match (pat, subj) {
        (Term::Succ(a), Term::Succ(b)) => unify_tm(gamma, a, b, n, d, sols),
        (Term::App { fun: f1, arg: a1, .. }, Term::App { fun: f2, arg: a2, .. }) => {
            // The flex-head guard (design §5.4): a pattern application whose
            // spine head is one of this call's not-yet-solved metas learns
            // nothing here. The `App` congruence would otherwise "solve"
            // `?f(?a) ≟ add(a, a)` by peeling one argument — `?f := add(a)` —
            // satisfying this occurrence and contradicting the next. Flex
            // heads applied to arbitrary terms are outside the Miller
            // fragment; the only rule trusted for them is the LGG
            // ([`Elaborator::solve_from_expected`]), and this guard is what
            // keeps first-order guessing out of the position. Committed
            // globals sit at `var.0 >= n`, so `D#fam`-headed family spines
            // (the type-arg-inference-through-index walker) are untouched.
            let mut head = pat;
            while let Term::App { fun, .. } = head {
                head = fun;
            }
            //
            // The **equal-arity flex-rigid rule**
            // (docs/operation-indexed-classes-design.md §4.2): where the
            // subject's own spine is headed by a *committed global* and has
            // exactly as many arguments, the head is determined and the
            // decomposition is the inversion — `?op(x, u) ≟ add(x, 0)` gives
            // `?op := add` with `u ≟ 0` learned beside it, which is how a
            // law's corollary pins its operation. It dodges the guard's
            // recorded counterexample precisely: `?f(?a) ≟ add(a, a)` has
            // spine lengths 1 against 2, and the dangerous partial-application
            // peel *is* the unequal-length case, which stays refused. Same
            // license as every rule here — learn-only, the kernel judges.
            if let Term::GlobalTm { var, .. } = head
                && var.0 < n
                && sols[var.0 as usize].solved().is_none()
                && !(spine_len(pat) == spine_len(subj) && rigid_global_head(subj, n))
            {
                return;
            }
            unify_tm(gamma, f1, f2, n, d, sols);
            unify_tm(gamma, a1, a2, n, d, sols);
        }
        // A declared-index family's type is `El` of an **index recursion
        // choosing among quoted codes** — `elimN(M; z «Σ…+…»; s «…»; i)`
        // with the payload type a variable *inside* the code literals
        // (docs/inductive-indexed-lowering.md), so learning `A` from
        // `t: W3<A>(n)` means walking the eliminator and the code
        // constructors (issues/type-arg-inference-through-index.md). Same
        // license as every case here: learn-only, kernel judges. Depths are
        // each variant's own binding structure — motive and Π/Σ/W second
        // components bind one, a step binds two, `Wf`'s arity binds one,
        // `Vec`/`Fin`/`Id`/`sEq`/`+` bind nothing.
        (
            Term::ElimNat { motive: m1, base: b1, step: s1, scrut: t1, .. },
            Term::ElimNat { motive: m2, base: b2, step: s2, scrut: t2, .. },
        ) => {
            unify_ty(gamma, m1, m2, n, d + 1, sols);
            unify_tm(gamma, b1, b2, n, d, sols);
            unify_tm(gamma, s1, s2, n, d + 2, sols);
            unify_tm(gamma, t1, t2, n, d, sols);
        }
        (
            Term::TmPi { dom: a1, cod: b1, .. },
            Term::TmPi { dom: a2, cod: b2, .. },
        )
        | (
            Term::TmSigma { fst: a1, snd: b1, .. },
            Term::TmSigma { fst: a2, snd: b2, .. },
        )
        | (Term::TmW { shape: a1, pos: b1, .. }, Term::TmW { shape: a2, pos: b2, .. })
        | (
            Term::TmWf { shape: a1, arity: b1, .. },
            Term::TmWf { shape: a2, arity: b2, .. },
        ) => {
            unify_tm(gamma, a1, a2, n, d, sols);
            unify_tm(gamma, b1, b2, n, d + 1, sols);
        }
        (
            Term::TmSum { lhs: a1, rhs: b1, .. },
            Term::TmSum { lhs: a2, rhs: b2, .. },
        ) => {
            unify_tm(gamma, a1, a2, n, d, sols);
            unify_tm(gamma, b1, b2, n, d, sols);
        }
        (
            Term::TmVec { elem: e1, len: k1, .. },
            Term::TmVec { elem: e2, len: k2, .. },
        ) => {
            unify_tm(gamma, e1, e2, n, d, sols);
            unify_tm(gamma, k1, k2, n, d, sols);
        }
        (Term::TmFin { len: k1 }, Term::TmFin { len: k2 }) => {
            unify_tm(gamma, k1, k2, n, d, sols);
        }
        (
            Term::TmId { ty: t1, lhs: a1, rhs: b1, .. },
            Term::TmId { ty: t2, lhs: a2, rhs: b2, .. },
        )
        | (
            Term::TmSEq { ty: t1, lhs: a1, rhs: b1, .. },
            Term::TmSEq { ty: t2, lhs: a2, rhs: b2, .. },
        ) => {
            unify_tm(gamma, t1, t2, n, d, sols);
            unify_tm(gamma, a1, a2, n, d, sols);
            unify_tm(gamma, b1, b2, n, d, sols);
        }
        _ => {}
    }
}

/// A parameter domain with the meta block substituted away — `Some` exactly
/// when every metavariable it mentions is already solved, in which case the
/// result is scoped in the *real* Ψ (a `GlobalSubst` over the `n` metas also
/// renumbers the committed globals back down, as `strengthen_global` records).
///
/// "Mentions no unsolved meta" is decided by substituting **two different**
/// markers for the unsolved ones and comparing: an unsolved occurrence makes
/// the two results differ, and nothing else can. Same device as
/// [`strengthen_tm`] — an exact test that needs no traversal of `Term`/`Type`
/// and so cannot drift out of sync with the syntax.
fn zonked(dom: &Type, n: u32, sols: &[Sol]) -> Option<Type> {
    let with = |marker: Term| {
        let entries = (0..n)
            .map(|k| {
                GlobalEntry::Tm(match sols[(n - 1 - k) as usize].solved() {
                    Some(t) => Rc::clone(t),
                    // `Unsolved` and `Withheld` alike: a withheld slot must
                    // keep *blocking* — a deferred argument's occurrences in a
                    // dependent domain are exactly what its retry waits on.
                    None => Rc::new(marker.clone()),
                })
            })
            .collect();
        dom.apply_global(&GlobalSubst { entries })
    };
    let a = with(Term::Zero);
    (a == with(Term::Succ(Rc::new(Term::Zero)))).then_some(a)
}

/// [`zonked`] for a *term* — same two-marker test, same guarantee: `Some`
/// exactly when every metavariable the term mentions is already solved, in
/// which case the result is scoped in the committed Ψ. Used by the congruence
/// rule, whose witnesses are compared with `==` and so must be real terms.
fn zonked_tm(t: &Term, n: u32, sols: &[Sol]) -> Option<Term> {
    let with = |marker: Term| {
        let entries = (0..n)
            .map(|k| {
                GlobalEntry::Tm(match sols[(n - 1 - k) as usize].solved() {
                    Some(t) => Rc::clone(t),
                    None => Rc::new(marker.clone()),
                })
            })
            .collect();
        t.apply_global(&GlobalSubst { entries })
    };
    let a = with(Term::Zero);
    (a == with(Term::Succ(Rc::new(Term::Zero)))).then_some(a)
}

/// The substitution that drops the innermost `d` binders off `gamma`,
/// sending each to a marker. Used only by [`strengthen_ty`]/[`strengthen_tm`].
///
/// `terms` is indexed outermost-first over the *source* context `Γ, d`
/// (length `m + d`), so entry `k` is the image of `Var(m + d - 1 - k)`: the
/// first `m` are `Γ`'s own variables lowered by `d`, and the last `d` are the
/// binders being dropped.
fn drop_binders(gamma: &LocalCtx, d: u32) -> LocalSubst {
    let m = gamma.entries.len() as u32;
    let tail = match gamma.base {
        CtxBase::Nil => SubstTail::Empty { len: m, base: CtxBase::Nil },
        CtxBase::Var(g) => SubstTail::Wk { len: m, ctx_var: g },
    };
    let terms = (0..m)
        .map(|k| Rc::new(Term::Var(LocalVar(m - 1 - k))))
        .chain((0..d).map(|_| Rc::new(Term::Zero)))
        .collect();
    LocalSubst { tail, terms }
}

/// Is `t`, scoped in `Γ` plus `d` further binders, in fact scoped in `Γ`
/// alone — and if so, what is it there?
///
/// Drop the `d` binders to a marker, then shift back by `d` and compare. A
/// term that never mentioned them is restored exactly; one that did keeps a
/// marker where a variable was, and the comparison fails. That is the whole
/// test: no new traversal of `Term`/`Type` is needed, and it cannot drift out
/// of sync with the syntax the way a hand-written occurrence check would.
fn strengthen_tm(gamma: &LocalCtx, t: &Term, d: u32) -> Option<Term> {
    if d == 0 {
        return Some(t.clone());
    }
    let s = t.apply_local(&drop_binders(gamma, d));
    (s.shift_local(d) == *t).then_some(s)
}

/// [`strengthen_tm`] at the type level.
fn strengthen_ty(gamma: &LocalCtx, t: &Type, d: u32) -> Option<Type> {
    if d == 0 {
        return Some(t.clone());
    }
    let s = t.apply_local(&drop_binders(gamma, d));
    (s.shift_local(d) == *t).then_some(s)
}
