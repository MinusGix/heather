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
use heather_kernel::reduce::{whnf_term, whnf_term_delta, whnf_type_delta, Defs};
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{
    nth, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    SubstTail, Term, Type,
};
use heather_kernel::typing::{self, TypeError, DEFAULT_FUEL};
use heather_syntax::{
    parse_file, Arm, Decl, DeclKind, Expr, ExprKind, Item, LamBinder, OnStmt, OnTarget, ParseError,
    Span, Stmt, RecordLitField, Ty, TyKind,
};

pub mod certgen;
pub mod stats;
mod code;
mod names;
mod patterns;
mod forded;
mod gendefs;
mod indexed;
mod inductive;
mod lgg;
mod quote;
mod slots;
mod vec;
mod wf;

use inductive::Inductive;
use names::{
    miss_msg, qkey, resolve, split_qual, ImportSpec, NameIndex, NameKind, NameRes,
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
    Kernel { decl: String, span: Span, err: TypeError },
    /// Goals raised in a block that no `on` statement discharged
    /// (issues/goal-holes.md). Not one error per goal: the *listing* is the
    /// point — it is how the checker shows goal state.
    UnsolvedGoals { decl: String, goals: Vec<GoalReport> },
}

/// One entry of the unsolved-goal listing. Types are rendered eagerly with
/// the kernel's budget-bounded `Debug` (crates/kernel/src/fmt.rs), so no
/// kernel type escapes into the public error.
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

impl From<ParseError> for ElabError {
    fn from(e: ParseError) -> Self {
        ElabError::Parse(e)
    }
}

impl ElabError {
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
        let headed = |msg: &str, span: Span| {
            format!("error: {msg}\n  --> {}\n{}", loc(span), snippet(src, span))
        };
        match self {
            ElabError::Parse(e) => headed(&format!("parse error: {}", e.msg), e.span),
            ElabError::Elab { msg, span } => headed(msg, *span),
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
            ElabError::Kernel { decl, err, .. } => {
                write!(f, "the kernel rejected `{decl}`: {err:?}")
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

/// One parameter of a callable global, in declaration/telescope order.
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
    /// Every module elaborated into this accumulator, with the scope it was
    /// elaborated in. Its job today is existence: `import m;` requires that
    /// `m` already landed here, which is what the CLI's topological walk
    /// guarantees.
    ///
    /// **Known seam.** An inductive keeps its field types in *surface* form
    /// and re-lowers them at each use (§2 of docs/inductive-tier0-lowering.md),
    /// and that lowering resolves names in the **use site's** scope, not the
    /// declaring module's. Two visible declarations of `List` therefore make an
    /// imported `Cons`'s `tail: List<A>` field mean the wrong one. It is loud
    /// rather than silent — nominal tags differ, so the use fails to
    /// typecheck — but the honest fix is a resolution environment that travels
    /// with stored syntax (or closing that syntax over its scope at
    /// declaration time). Recorded for its own round.
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
    /// The slot this template claimed, if any. `None` is an ordinary meta
    /// definition: registered, never dispatched.
    #[allow(dead_code)]
    pub(crate) slot: Option<Slot>,
    pub(crate) order: Vec<usize>,
}

/// What a `p.f` turned out to be (docs/surface-records.md §4.2).
enum DotResolution {
    /// A record field: the projection, its type and level. Synthesized, since
    /// every annotation is read off the receiver's type.
    Project(Term, Type, Level),
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
            next_tag: 0,
            fuel: DEFAULT_FUEL,
            goal_base: 0,
            goals: RefCell::new(Vec::new()),
            goal_spans: RefCell::new(HashMap::new()),
            frozen: Cell::new(false),
            meta_defs: HashMap::new(),
            meta_slots: HashMap::new(),
            meta_pushed: RefCell::new(Vec::new()),
        }
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

    /// [`Self::elab_source`] into a named module. The elaborator does no file
    /// IO: an `import m;` here requires that `m` has *already* been elaborated
    /// into this same accumulator, which is exactly what the CLI's topological
    /// walk guarantees (docs/modules-design.md §3.2).
    pub fn elab_module_source(&mut self, module: &str, src: &str) -> R<()> {
        let file = parse_file(src)?;
        self.enter_module(module, &file)?;
        for item in &file.items {
            match item {
                Item::Decl(d) => self.elab_decl(d)?,
                Item::Inductive(i) => self.elab_inductive(i)?,
                Item::Import(_) => {}
            }
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
        resolve(&self.names, &self.scope, name, |m, ty, ctor| {
            self.inductives
                .get(&qkey(m, ty))
                .is_some_and(|i| i.ctors.iter().any(|c| c.name == ctor))
        })
    }

    /// The base half of a written name — `nat::sub` and `sub` both name `sub`.
    fn base_name(name: &str) -> &str {
        split_qual(name).map(|(_, b)| b).unwrap_or(name)
    }

    /// The qualified table key a written name resolves to, if it resolves.
    fn key_of(&self, name: &str) -> Option<String> {
        match self.resolve_name(name) {
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
        self.globals.get(&self.key_of(name)?)
    }

    pub(crate) fn lookup_inductive(&self, name: &str) -> Option<&Rc<Inductive>> {
        self.inductives.get(&self.key_of(name)?)
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
            let r = match item {
                Item::Decl(d) => self.elab_decl(d),
                Item::Inductive(i) => self.elab_inductive(i),
                Item::Import(_) => Ok(()),
            };
            if let Err(e) = r {
                errs.push(e);
            }
        }
        errs
    }

    /// The accumulated global context (theorem statements).
    pub fn psi(&self) -> &GlobalCtx {
        &self.psi
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
        let r = self.elab_decl_inner(decl);
        self.goal_base = 0;
        self.refresh_delta_psi();
        self.goals.borrow_mut().clear();
        self.goal_spans.borrow_mut().clear();
        self.frozen.set(false);
        r
    }

    fn elab_decl_inner(&mut self, decl: &Decl) -> R<()> {
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
            if !self.names_a_type(owner) {
                return err(
                    format!(
                        "`{owner}` is not a type in scope, so `{}` attaches to nothing — \
                         a member declaration is `fn <Type>::{base}(…)` and the type \
                         must be declared (or be a kernel type) before it",
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
            let (ty, lvl) = self.elab_ty(&cx, &p.ty)?;
            cx.push(p.name.clone(), ty.clone(), lvl.clone());
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
        let mut stmt = res_ty;
        let mut stmt_lvl = res_lvl;
        let mut term = body;
        for (dom, dom_lvl) in param_info.into_iter().rev() {
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
        let empty = LocalCtx { base: CtxBase::Nil, entries: vec![] };
        stats::time_kernel(|| {
            typing::check_type(&self.psi, 0, Layer::Prog, &empty, &stmt, &stmt_lvl, self.fuel)
        })
        .map_err(|e| ElabError::Kernel { decl: decl.name.clone(), span: decl.span, err: e })?;
        stats::time_kernel(|| {
            typing::check_term(&self.psi, 0, Layer::Code, &empty, &term, &stmt, &stmt_lvl, self.fuel)
        })
        .map_err(|e| ElabError::Kernel { decl: decl.name.clone(), span: decl.span, err: e })?;

        let params = Rc::new(
            decl.tyvars
                .iter()
                .map(|t| ParamMeta {
                    name: t.name.clone(),
                    implicit: true,
                    is_type: true,
                    is_self: false,
                })
                .chain(decl.params.iter().map(|p| ParamMeta {
                    name: p.name.clone(),
                    implicit: p.implicit,
                    is_type: false,
                    is_self: p.is_self,
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
            ctx: LocalCtx { base: CtxBase::Nil, entries: vec![] },
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
                statement: format!("{:?}", g.ty),
                context: g
                    .cx
                    .names
                    .iter()
                    .zip(&g.cx.gamma.entries)
                    // `#`-prefixed binders are the elaborator's own (a `match`
                    // arm's hidden ih); they are unspellable, so listing them
                    // would only mislead.
                    .filter(|(n, _)| !n.starts_with('#'))
                    .map(|(n, e)| (n.clone(), format!("{:?}", e.ty)))
                    .chain(g.cx.aliases.iter().map(|a| (a.name.clone(), format!("{:?}", a.ty))))
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
                    ctx: LocalCtx { base: CtxBase::Nil, entries: vec![] },
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
            let (term, ty, level) = match ty {
                Some(t) => {
                    let (ty, lvl) = self.elab_ty(&cx, t).map_err(|e| self.let_ty_hint(&cx, t, e))?;
                    let tm = self.elab_check(&cx, expr, &ty, &lvl)?;
                    (tm, ty, lvl)
                }
                None => self.elab_infer(&cx, expr)?,
            };
            cx.aliases.push(Rc::new(Alias {
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
            TyKind::Named { name, args } => self.lower_named(cx, name, args, ty.span),
            // `[T; n]` — the kernel's `Type::Vec` directly. A primitive
            // indexed type: no fording, no encoding
            // (docs/container-fields.md §2.1).
            TyKind::Vec { elem, len } => {
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
            TyKind::Fn { binder, dom, cod } => {
                let (dom_t, dom_level) = self.elab_ty(cx, dom)?;
                let mut inner = cx.clone();
                // `#` marks an elaborator-introduced binder: unspellable, and
                // filtered out of the goal listing.
                let name = binder.clone().unwrap_or_else(|| "#arrow".to_string());
                inner.push(name.clone(), dom_t.clone(), dom_level.clone());
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
            ExprKind::Refl if self.shadowed(cx, "refl") => self.elab_check_hinted(
                cx,
                &Expr { kind: ExprKind::Var("refl".to_string()), span: e.span },
                expected,
                lvl,
                hint,
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
                self.elab_check_hinted(&cx, &b.result, expected, lvl, hint)
            }
            // A quote against its `Code(g |- T)` type — checking-only, like
            // the kernel's `BoxTm` (docs/in-language-map-design.md §5).
            ExprKind::Quote(payload) => self.elab_quote(cx, payload, expected, e.span),
            ExprKind::Match { motive: None, scrut, arms, eqbind } => {
                // Stage-2 motive synthesis (issues/elab-stage2-metas.md): when
                // the scrutinee is a local variable, abstract it out of the
                // expected type so the motive is genuinely dependent; otherwise
                // fall back to the non-dependent motive (expected under `z`).
                let (scrut_t, scrut_ty, scrut_lvl) = self.elab_infer(cx, scrut)?;
                let motive = self.synth_motive(cx, &scrut_t, &scrut_ty, &scrut_lvl, expected);
                let Some(h) = eqbind else {
                    return self.elab_match(
                        cx, arms, scrut_t, &scrut_ty, &scrut_lvl, motive, lvl.clone(), e.span,
                    );
                };
                self.elab_convoy(
                    cx, h, arms, scrut_t, &scrut_ty, &scrut_lvl, motive, lvl, expected,
                    e.span,
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
                    && self.ctor_here(cx, name).is_none() =>
            {
                self.elab_fin_index(cx, None, expected, e.span)
            }
            ExprKind::App { args, .. }
                if matches!(e.as_named(), Some(("FS", _, false)))
                    && !self.shadowed(cx, "FS")
                    && self.ctor_here(cx, "FS").is_none() =>
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
                self.elab_lam_check(cx, binders, body, expected, lvl, e.span)
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
            ExprKind::Var(name) if self.ctor_here(cx, name).is_some() => {
                let (ind, i) = self.ctor_here(cx, name).expect("just checked");
                self.build_ctor_value(cx, &ind, i, &[], expected, lvl, e.span)
            }
            ExprKind::App { .. } if self.ctor_spine(cx, e).is_some() => {
                let (ind, i, args) = self.ctor_spine(cx, e).expect("just checked");
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
                    DotResolution::Project(t, ty, l) => match args {
                        None => Ok(t),
                        Some(args) => {
                            let (t, _, _) = self.apply_explicit(cx, None, 0, t, ty, l, args)?;
                            Ok(t)
                        }
                    },
                    DotResolution::Method(m) => self.elab_check_hinted(cx, &m, expected, lvl, hint),
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
                // discarded on the way: an implicit-inserting call whose last
                // unsolved implicit is a function only the goal mentions is
                // solved by anti-unification against it
                // (issues/congruence-by-anti-unification.md, decision 7 —
                // this line is the plumbing that decision names). Nothing
                // else reads the hint, so every other expression elaborates
                // exactly as before.
                let (t, _, _) = self.elab_infer_at(cx, e, Some(&head))?;
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
            ExprKind::Var(name) => self.resolve(cx, name, e.span),
            // `xs[i]` — infers, since the element type comes off the receiver
            // (docs/surface-fin-indexing-design.md §5.2).
            ExprKind::Index { recv, idx } => self.elab_vec_nth(cx, recv, idx, e.span),
            ExprKind::Dot { recv, name, args } => {
                match self.resolve_dot(cx, recv, name, args, e.span)? {
                    DotResolution::Project(t, ty, l) => match args {
                        None => Ok((t, ty, l)),
                        Some(args) => self.apply_explicit(cx, None, 0, t, ty, l, args),
                    },
                    DotResolution::Method(m) => self.elab_infer(cx, &m),
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
            ExprKind::Lam { binders, body } => self.elab_lam_infer(cx, binders, body),
            // `f<T, …>` — explicit type application, with or without a call
            // after it (docs/surface-polymorphism.md §1).
            ExprKind::TyApp { head, args } => {
                if let Some(r) = self.ctor_at(cx, head, args, &[], e.span) {
                    return r;
                }
                let (_, t, ty, lvl, _) = self.elab_ty_app(cx, head, args, e.span)?;
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
                let (name, t, ty, lvl, mask) =
                    self.elab_ty_app(cx, callee, tyargs, head.span)?;
                if !*explicit && mask.iter().any(|&b| b) {
                    self.apply_implicit(cx, &name, t, ty, lvl, args, &mask, expected, e.span)
                } else {
                    // The type arguments have consumed the leading parameters,
                    // so argument `i` is now parameter `i + |tyargs|` — which
                    // is what the offset keeps honest for goal-name hints.
                    self.apply_explicit(cx, Some(&name), tyargs.len(), t, ty, lvl, args)
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
                self.apply_explicit(cx, None, 0, h, hty, hlvl, args)
            }
            ExprKind::App { args, explicit, .. } => {
                let (name, _, _) = e.as_named().expect("head is a name");
                let name = &name.to_string();
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
                        return err("`map` takes `(f)` on a vector receiver", e.span);
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
                        return err(format!("`{name}` takes a vector receiver"), e.span);
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
                        return err("`fold` takes `(init, f)` on a vector receiver", e.span);
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
                    self.apply_explicit(cx, Some(name), 0, head, ty, lvl, args)
                } else {
                    self.apply_implicit(cx, name, head, ty, lvl, args, &mask, expected, e.span)
                }
            }
            ExprKind::Match { motive: Some(m), scrut, arms, eqbind } => {
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
                        cx, arms, &scrut_t, &scrut_ty, &result, indep, &mlvl, e.span,
                    )?;
                    let (acx, arms) = match &prepared {
                        Some((c, a)) => (c, a.as_slice()),
                        None => (cx, arms.as_slice()),
                    };
                    let t = self.elab_match_forded(
                        acx, &ind, &fam, arms, scrut_t, motive2, mlvl.clone(), e.span,
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
                        cx, arms, &scrut_t, &scrut_ty, &result, indep, &mlvl, e.span,
                    )?;
                    let (acx, arms) = match &prepared {
                        Some((c, a)) => (c, a.as_slice()),
                        None => (cx, arms.as_slice()),
                    };
                    let t = self.elab_match_indexed(
                        acx, &ind, &fam, arms, scrut_t, motive2, mlvl.clone(), e.span,
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
                        cx, h, arms, scrut_t, &scrut_ty, &scrut_lvl, motive, &mlvl, &result,
                        e.span,
                    )?;
                    return Ok((t, result, mlvl));
                }
                let t = self.elab_match(
                    cx, arms, scrut_t, &scrut_ty, &scrut_lvl, motive, mlvl.clone(), e.span,
                )?;
                Ok((t, result, mlvl))
            }
            ExprKind::Match { motive: None, .. } => err(
                "`match` in inference position needs a motive: `match e as \u{3bb} z => T { … }`",
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
    fn elab_match(
        &self,
        cx: &Cx,
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
            cx, arms, &scrut_t, scrut_ty, &result, independent, &mlvl, span,
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
                .elab_match_forded(cx, &ind, &fam, arms, scrut_t, motive2, mlvl, span);
        }
        if !matches!(head, Type::Empty { .. })
            && let Some((ind, fam)) = self.indexed_of_at(cx, scrut_ty)
        {
            let motive2 = self.generalize_index(cx, &motive, &fam.idx);
            return self
                .elab_match_indexed(cx, &ind, &fam, arms, scrut_t, motive2, mlvl, span);
        }
        if let Some(ind) = self.tag_of(&head) {
            return self
                .elab_match_data(cx, &ind, arms, scrut_t, &head, scrut_lvl, motive, mlvl, span);
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
                    return self.elab_match_fin(cx, arms, scrut_t, k, motive, mlvl, span);
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
                            "`match` on a `Fin` needs its length to reduce to `0` or a \
                             successor{here}. Recurse on the length first \
                             (`match n as \u{3bb} z => \u{2026}`), which is how the index \
                             becomes matchable"
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
                return err("this type has no constructors, so `match` takes no arms", span);
            }
            return Ok(Term::ElimEmpty {
                level: mlvl,
                scrut_level: empty_lvl.clone(),
                motive: Rc::new(motive),
                scrut: Rc::new(scrut_t),
            });
        }
        if !matches!(head, Type::Nat) {
            return err("`match` needs a `Nat` or a declared inductive", span);
        }
        self.elab_match_nat(cx, arms, scrut_t, motive, mlvl, span)
    }

    /// `match` on `Nat`: the kernel's `elim_Nat`, with the arms named `Zero`
    /// and `Succ(k)` (or the low-level `Succ(k, ih)`).
    fn elab_match_nat(
        &self,
        cx: &Cx,
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
            return err("`match` on `Nat` needs both a `Zero` and a `Succ(k)` arm", span);
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
        // base : M[Zero/z]
        let base_ty =
            motive.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Zero)));
        let base = self.elab_check(cx, zero, &base_ty, &mlvl)?;
        // step context: Γ, k : Nat, ih : M[k/z]  (M scoped in Γ,z).
        let mut scx = cx.clone();
        scx.push(k.clone(), Type::Nat, Level::Zero);
        let ih_ty = motive
            .apply_local(&embed(&cx.gamma, 1).extended(Rc::new(Term::Var(LocalVar(0)))));
        // The unified arm `Succ(k)` binds the ih anyway — the recursor demands
        // it — but under a name the surface cannot spell, because it is
        // reached by a guarded self-call instead.
        scx.push(ih.clone().unwrap_or_else(|| "#ih".into()), ih_ty, mlvl.clone());
        if ih.is_none() {
            // Does this match descend on one of the declaration's own
            // parameters? If so, self-calls in the arm become the ih. If not
            // (a nested match on some other term), the enclosing arm's guard —
            // if any — still stands.
            scx.guard = self
                .descends_on_param(cx, &scrut_t)
                .map(|dec| {
                    Rc::new(Guard {
                        dec,
                        kind: GuardKind::Nat {
                            pred_pos: cx.names.len(),
                            ih_pos: cx.names.len() + 1,
                        },
                        rebind: None,
                    })
                })
                .or_else(|| cx.guard.clone());
        }
        // step : M[Succ k/z] in Γ, k, ih.
        let step_ty = motive.apply_local(
            &embed(&cx.gamma, 2)
                .extended(Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(1)))))),
        );
        let step = self.elab_check(&scx, succ_body, &step_ty, &mlvl)?;
        Ok(Term::ElimNat {
            level: mlvl,
            motive: Rc::new(motive),
            base: Rc::new(base),
            step: Rc::new(step),
            scrut: Rc::new(scrut_t),
        })
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
            return err("`match` on a `Fin` needs both an `FZ` and an `FS(i)` arm", span);
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
        // an over-application: `leb_false_flip(k, l, p)` for
        // `leb_false_flip(k)(l, p)`.
        let (args, spill) = args.split_at(positions.len());
        // Which descendant the call goes to, once the decreasing argument has
        // been matched: `Nat` has only one, a `Wf` arm has one per recursive
        // field, so this is set inside the loop below. The decreasing argument
        // is checked **first** — at a branching index constructor the ih's
        // index is the *descendant's own* pattern variable, so the rebind
        // check below has no answer until the descendant is known.
        let mut descendant = 0usize;
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
                (GuardKind::Nat { pred_pos, .. }, true) => {
                    matches!(arg_t, Term::Var(LocalVar(i))
                             if cx.names.len() - 1 - i as usize == *pred_pos)
                }
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
                let what = match &g.kind {
                    GuardKind::Nat { pred_pos, .. } => {
                        format!("`{}`, the predecessor bound by", cx.names[*pred_pos])
                    }
                    GuardKind::Wf { .. } => {
                        "one of the recursive fields bound by".to_string()
                    }
                };
                err(
                    format!(
                        "recursive call to `{name}` must descend: argument `{}` has to be \
                         {what} the enclosing `match`",
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
            GuardKind::Nat { ih_pos, .. } => self.local(cx, *ih_pos),
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
        self.apply_explicit(cx, Some(name), s.params.len(), t, ty, lvl, spill)
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
                return Ok(DotResolution::Project(t, fty, flvl));
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
        let name = &self.member_head(cx, recv, name, span)?;
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
            NameRes::NotFound | NameRes::NoSuchQualifier(_) => {
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
        self.lookup_inductive(name).is_some() || name == "Nat" || name == "Type"
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
        span: Span,
    ) -> R<Term> {
        let Some((b, rest)) = binders.split_first() else {
            return self.elab_check(cx, body, expected, lvl);
        };
        let head = self.whnf(cx, expected, span)?;
        let Type::Pi { dom_level, cod_level, dom, cod } = head else {
            return err(
                format!("a lambda needs a function type here, found `{expected:?}`"),
                span,
            );
        };
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
        inner.push(b.name.clone(), (*dom).clone(), dom_level.clone());
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
            self.elab_lam_check(&inner, rest, body, &cod, &cod_level, span)?
        };
        Ok(Term::Lam {
            dom_level,
            cod_level,
            dom,
            body: Rc::new(body_t),
        })
    }

    /// A lambda in inference position: every binder must be annotated.
    fn elab_lam_infer(
        &self,
        cx: &Cx,
        binders: &[LamBinder],
        body: &Expr,
    ) -> R<(Term, Type, Level)> {
        let Some((b, rest)) = binders.split_first() else {
            return self.elab_infer(cx, body);
        };
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
        inner.push(b.name.clone(), dom.clone(), dom_level.clone());
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
        let (body_t, cod, cod_level) = self.elab_lam_infer(&inner, rest, body)?;
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
        let params = name.map(|n| self.params_of(n)).unwrap_or_default();
        let what = name.map_or_else(|| "this function".to_string(), |n| format!("`{n}`"));
        for (i, arg) in args.iter().enumerate() {
            let head = self.whnf(cx, &ty, arg.span)?;
            let Type::Pi { dom_level, cod_level, dom, cod } = head else {
                return err(format!("{what} is applied to too many arguments"), arg.span);
            };
            let hint = name.zip(params.get(i + param_offset)).map(|(n, p)| (n, p.name.as_str()));
            let arg_t = self.elab_check_hinted(cx, arg, &dom, &dom_level, hint)?;
            let arg_rc = Rc::new(arg_t);
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg_rc)));
            lvl = cod_level.clone();
            t = Term::App { fun: Rc::new(t), dom_level, cod_level, dom, cod, arg: arg_rc };
        }
        Ok((t, ty, lvl))
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
    /// application with implicit insertion is ambiguous, so it is refused.
    #[allow(clippy::too_many_arguments)]
    fn apply_implicit(
        &self,
        cx: &Cx,
        name: &str,
        head: Term,
        callee_ty: Type,
        callee_lvl: Level,
        args: &[Expr],
        mask: &[bool],
        expected: Option<&Type>,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let n = mask.iter().filter(|&&b| b).count() as u32;
        // Scratch world: the `n` metas take the innermost Ψ indices `[0, n)`;
        // committed globals shift up by `n` so nothing collides.
        let mut t = head.shift_global(n);
        let mut ty = callee_ty.shift_global(n);
        let mut lvl = callee_lvl;
        let mut sols: Vec<Option<Rc<Term>>> = vec![None; n as usize];
        // Each meta's *declared* parameter type, in meta order — the only
        // place a solution's domain can come from when no argument mentions
        // it (see [`Self::solve_by_lgg`]).
        let mut meta_doms: Vec<Type> = Vec::with_capacity(n as usize);
        let mut next_meta = 0u32;
        let mut args = args.iter();
        // Parameter metadata for goal-name hints. `mask` may be a suffix of
        // the parameter list (`f<T>(…)` has already consumed the leading type
        // parameters), so index from the same offset.
        let all_params = self.params_of(name);
        let offset = all_params.len().saturating_sub(mask.len());
        for (mi, &is_implicit) in mask.iter().enumerate() {
            let i = mi + offset;
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
                meta_doms.push((*dom).clone());
                next_meta += 1;
                Rc::new(m)
            } else {
                let arg = args.next().ok_or_else(|| ElabError::Elab {
                    msg: format!("`{name}` is applied to too few arguments"),
                    span,
                })?;
                if matches!(arg.kind, ExprKind::Lam { .. }) {
                    // An explicit argument is *inferred* here, and an
                    // unannotated lambda has nothing to infer from. Harmless
                    // before polymorphism (a monomorphic callee's domain was
                    // never needed to elaborate the argument); now it is the
                    // first thing anyone hits, so it says what to do
                    // (docs/surface-polymorphism.md §4.1).
                    let unannotated = matches!(&arg.kind,
                        ExprKind::Lam { binders, .. } if binders.iter().any(|b| b.ty.is_none()));
                    if unannotated {
                        return err(
                            format!(
                                "`{name}` has implicit arguments, so this lambda is \
                                 elaborated before they are known: annotate its binders \
                                 (`λ (x: A) => …`), or give the type arguments \
                                 (`{name}<T, …>(…)`)"
                            ),
                            arg.span,
                        );
                    }
                }
                // If every meta this domain mentions is *already* solved,
                // elaborate the argument in **checking** mode against the
                // zonked domain. That is what puts `refl`, a `?`-hole and a
                // vector literal back in a position that supplies their
                // expected type — they are checking-only, and before this
                // every argument of an implicit-taking callee was inferred.
                //
                // Load-bearing since `@` stopped clearing the mask
                // (issues/at-and-type-arguments.md): `@sym(a, b, ?p)` still
                // has one meta (the type parameter), so it comes through here
                // rather than through `apply_explicit`, and `a` solves the
                // meta before `p`'s domain is needed.
                match zonked(&dom, n, &sols) {
                    Some(real_dom) => {
                        let hint = params.get(i).map(|p| (name, p.name.as_str()));
                        let arg_t =
                            self.elab_check_hinted(cx, arg, &real_dom, &dom_level, hint)?;
                        Rc::new(arg_t.shift_global(n))
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
        // that `apply_explicit` elaborates its arguments in; the price is that
        // a spilled argument cannot solve a meta, which is also true of the
        // parenthesized spelling this is sugar for.
        let spill: Vec<Expr> = args.cloned().collect();
        // Last chance for an implicit no argument's type mentions: in
        // *checking* position the expected type is the remaining evidence,
        // and recovering a congruence's function from it is anti-unification
        // (issues/congruence-by-anti-unification.md, interim design).
        //
        // Run only when something is still unsolved — so no call that
        // elaborated before reaches it — and only on an unspilled spine,
        // where `ty` really is the call's result type.
        if let Some(expected) = expected
            && spill.is_empty()
            && sols.iter().any(|s| s.is_none())
        {
            self.solve_by_lgg(cx, &ty, expected, n, &mut sols, &meta_doms, span)?;
        }
        // Discharge the meta block: `entries[k]` is the payload for Ψ-index
        // `n-1-k` (apply_global's convention), so it takes `sols[n-1-k]`.
        let mut entries = Vec::with_capacity(n as usize);
        // Which parameter each meta came from, in meta order — for the
        // message below. `mask` may be a *suffix* of the parameter list when
        // the call already gave its type arguments (`f<T>(…)`), so the offset
        // is recovered rather than assumed to be zero.
        let all = self.params_of(name);
        let skip = all.len().saturating_sub(mask.len());
        let meta_params: Vec<&ParamMeta> =
            all.iter().skip(skip).zip(mask).filter(|&(_, &m)| m).map(|(p, _)| p).collect();
        for k in 0..n {
            let j = (n - 1 - k) as usize;
            let sol = sols[j].clone().ok_or_else(|| ElabError::Elab {
                msg: match meta_params.get(j) {
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
        let past = self.params_of(name).len();
        self.apply_explicit(cx, Some(name), past, t, ty, lvl, &spill)
    }

    /// The congruence rule of `issues/congruence-by-anti-unification.md`: the
    /// expected type, consulted for the implicits an argument's type cannot
    /// reach. Called from [`Self::apply_implicit`] with the call's scratch
    /// world (`n` metas, `sols` their solutions so far) just before an
    /// unsolved meta would be reported.
    ///
    /// Two steps, both behind one structural trigger and no name
    /// (decision 1): the result type is `?f(s) = ?f(t)` with the *same*
    /// unsolved meta at both heads and `s`, `t` meta-free, and the expected
    /// type whnf's to an `Id`.
    ///
    /// 1. **First-order harvest.** `unify_ty` against the result type is what
    ///    solves the *other* implicits the same call needs and no argument
    ///    mentions — `cong`'s codomain `B` is exactly that. It never fails
    ///    and only ever learns.
    /// 2. **Anti-unification**: `?f := λz. LGG(X, Y)`, every hole's witness
    ///    pair required to be exactly `(s, t)`.
    ///
    /// The trigger is read off **before** the harvest, and `?f` is *withheld*
    /// from it. That order is load-bearing rather than tidy: `unify_ty`'s
    /// `App`-congruence happily solves `?f(?a) ≟ add(a, a)` by peeling one
    /// argument — `?f := add(a)` — which satisfies the left endpoint and
    /// contradicts the right, and reaches the kernel as `NotConvertible` on a
    /// term nobody wrote. Flex heads applied to arbitrary arguments are §2's
    /// out-of-pattern case; the *only* rule this round trusts for them is the
    /// LGG, so first-order guessing is denied the position it would otherwise
    /// take first.
    ///
    /// Once the trigger fires the outcome is **committed**: a mismatching
    /// witness is reported here, not swallowed into "could not infer". A
    /// shape that does not match is simply left alone, and the caller's
    /// existing message stands.
    ///
    /// This hook is the throwaway half of the interim round (§5): the LGG
    /// itself lives in [`crate::lgg`] and outlives it, but *this* function is
    /// deleted when a layer-m goal solver can construct the call instead.
    #[allow(clippy::too_many_arguments)]
    fn solve_by_lgg(
        &self,
        cx: &Cx,
        result_ty: &Type,
        expected: &Type,
        n: u32,
        sols: &mut [Option<Rc<Term>>],
        meta_doms: &[Type],
        span: Span,
    ) -> R<()> {
        // The trigger, read off the scratch-world result type.
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
                && sols[var.0 as usize].is_none()
                && *subst == LocalSubst::id(&cx.gamma))
            .then(|| (var.0 as usize, Rc::clone(s_raw), Rc::clone(t_raw)))
        })();
        // Nothing else gets to consult the expected type: an implicit that no
        // argument mentions stays a "could not infer" everywhere but here.
        // That is deliberate — solving result-only implicits *in general* is
        // [[elab-unifier-completeness]]'s question and a much wider change
        // (it would silently retire diagnostics like "cannot infer the type
        // argument", which exist to send people to `f<T>(…)`). This round
        // buys one shape.
        let Some((m, s_raw, t_raw)) = flex else { return Ok(()) };
        // Step 1, with `?f` withheld (see above): a placeholder makes the
        // meta look solved to `unify_tm`, which never overwrites, and is
        // taken back out before anything reads a solution. The pattern is in
        // the scratch world and the subject in the committed one, exactly as
        // at an argument's domain.
        sols[m] = Some(Rc::new(Term::Zero));
        unify_ty(&cx.gamma, result_ty, expected, n, 0, sols);
        sols[m] = None;
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
        sols[m] = Some(Rc::new(Term::Lam {
            dom_level,
            cod_level,
            dom,
            body: Rc::new(body),
        }));
        Ok(())
    }

    // -- names --------------------------------------------------------------

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
        // Inside a `meta fn`, nothing beyond locals, aliases and the Nat
        // primitives resolves: a committed global would be referenced by a
        // `GlobalVar` whose index the meta binders above it have shifted, and
        // the slice is pure quotation anyway (docs/in-language-map-design.md
        // §5 — the expressiveness verdict's opaque-globals blocker gates
        // exactly this).
        if cx.meta.is_some() {
            return err(
                format!(
                    "`{name}` is not in scope inside a `meta fn`: the slice is pure \
                     quotation — parameters, splices, `let code` names, and the Nat \
                     primitives only"
                ),
                span,
            );
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
                // further out.
                let var = GlobalVar(len - 1 - abs + self.goal_base);
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
            None => Err(self.name_miss(name, format!("unbound name `{name}`"), span)),
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
        let psi = self.oracle_psi();
        whnf_type_delta(ty, &cx.gamma, Defs::transparent(&psi), self.fuel)
            .map_err(|_| ElabError::Elab { msg: "out of fuel reducing a type".into(), span })
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
                ctx: LocalCtx { base: CtxBase::Nil, entries: vec![] },
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
        /// Position of the predecessor `k` bound by the arm.
        pred_pos: usize,
        /// Position of the arm's (hidden) induction-hypothesis binder.
        ih_pos: usize,
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
}

impl Cx {
    fn empty() -> Cx {
        Cx {
            names: vec![],
            gamma: LocalCtx { base: CtxBase::Nil, entries: vec![] },
            selfref: None,
            guard: None,
            aliases: vec![],
            tyvars: vec![],
            meta: None,
        }
    }

    fn push(&mut self, name: String, ty: Type, level: Level) {
        self.names.push(name);
        self.gamma.entries.push(CtxEntry { ty: Rc::new(ty), level });
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
            ExprKind::Match { scrut, motive, arms, eqbind: _ } => {
                expr(scrut, n);
                if let Some(m) = motive {
                    expr(m, n);
                }
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
    sols: &mut [Option<Rc<Term>>],
) {
    // The `El` rule. Checked before the congruence so that `El ?A` meeting a
    // *decoded* `El t` still solves rather than descending into the code.
    if let Type::El { tm, .. } = pat
        && let Term::GlobalTm { var, subst } = &**tm
        && var.0 < n
    {
        if sols[var.0 as usize].is_none()
            && subst.terms.iter().all(|t| matches!(**t, Term::Var(_)))
            && let Some(s) = strengthen_ty(gamma, subj, d)
            && let Some(c) = code::code_of(&s)
        {
            sols[var.0 as usize] = Some(Rc::new(c));
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
/// metavariable under a variable renaming (the Miller pattern condition —
/// here always the identity `id_Γ`, so the solution is the subject verbatim),
/// record it; otherwise recurse through matching heads toward nested metas.
fn unify_tm(
    gamma: &LocalCtx,
    pat: &Term,
    subj: &Term,
    n: u32,
    d: u32,
    sols: &mut [Option<Rc<Term>>],
) {
    if let Term::GlobalTm { var, subst } = pat
        && var.0 < n
    {
        let is_pattern = subst.terms.iter().all(|t| matches!(**t, Term::Var(_)));
        if is_pattern
            && sols[var.0 as usize].is_none()
            && let Some(s) = strengthen_tm(gamma, subj, d)
        {
            sols[var.0 as usize] = Some(Rc::new(s));
        }
        return;
    }
    match (pat, subj) {
        (Term::Succ(a), Term::Succ(b)) => unify_tm(gamma, a, b, n, d, sols),
        (Term::App { fun: f1, arg: a1, .. }, Term::App { fun: f2, arg: a2, .. }) => {
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
fn zonked(dom: &Type, n: u32, sols: &[Option<Rc<Term>>]) -> Option<Type> {
    let with = |marker: Term| {
        let entries = (0..n)
            .map(|k| {
                GlobalEntry::Tm(match &sols[(n - 1 - k) as usize] {
                    Some(t) => Rc::clone(t),
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
fn zonked_tm(t: &Term, n: u32, sols: &[Option<Rc<Term>>]) -> Option<Term> {
    let with = |marker: Term| {
        let entries = (0..n)
            .map(|k| {
                GlobalEntry::Tm(match &sols[(n - 1 - k) as usize] {
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

