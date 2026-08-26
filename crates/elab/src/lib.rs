//! The stage-1 elaborator: surface AST → fully explicit kernel core.
//!
//! Scope (issues/elaborator-design.md, order of attack, stage 1): name
//! resolution into the kernel's namespaces and bidirectional
//! annotation-filling — no metavariables, no level inference (everything in
//! stage 1 lives at level 0, though levels are tracked honestly), no modal
//! layer. The kernel remains the gate: every definition and theorem is
//! re-checked from scratch by `heather_kernel::typing`; an explicit axiom's
//! statement is checked as a type and its assumption status is recorded.
//!
//! Definition story (elaborator-design; revised 2026-07-31 by
//! issues/simulate-conversion-cost.md). All three ordinary kinds bind a closed Ψ-global
//! `u : Trm_c(· ⊢ Stmt @ l)` and are referenced by name as `u^δ` (ch. 04
//! admits referencing a layer-c global from any layer ≥ c: `i' ≤ i`,
//! typing.rs). Definitions and proved theorems differ in one binding field:
//! - `fn` (computes): the binding carries the elaborated term as its
//!   **body**, so conversion δ-unfolds it at layer p exactly when running
//!   it is what a comparison needs. Previously a `fn` was **inlined** at
//!   every use, which put a copy of the whole body into every statement and
//!   every induction hypothesis that mentioned it.
//! - `theorem` (never computes): the proof is kernel-checked against the
//!   statement, then discarded — the binding stays **opaque**. Later proofs
//!   refer to it as a neutral; proofs are transported, never evaluated.
//! - `axiom` (explicit assumption): the statement is checked for
//!   well-formedness and committed opaque with no proof. Its trust status and
//!   transitive provenance live elaborator-side (`provenance.rs`).
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
use std::collections::HashMap;
use std::rc::Rc;

use heather_kernel::conv::ConvError;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::subst::GlobalSubst;
use heather_kernel::term::{
    GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    SubstTail, Term, Type,
};
use heather_kernel::typing::{self, TypeError, DEFAULT_FUEL};
use heather_kernel::value::{ValueArena, ValueMetrics, ValueMetricsSnapshot};
use heather_syntax::{
    parse_file, Arm, Decl, DeclKind, Expr, ExprKind, InstanceDecl, Item, LamBinder, MatchForm,
    OnStmt, OnTarget, NamedArg, ParseError, Span, Ty, TyKind,
};

mod access;
mod application;
mod attempt;
pub mod arith;
pub mod omega;
pub mod certgen;
pub mod gate;
pub mod stats;
mod code;
mod context;
mod constructor;
mod datarepr;
mod diagnostics;
mod dispatch;
mod display;
mod expr;
pub use datarepr::{Obligation, Provenance};
pub mod reprgen;
mod names;
mod oracle;
mod patterns;
mod provenance;
pub use provenance::{AssumptionKind, AxiomReport, AxiomUse};
mod forded;
mod gendefs;
mod goals;
mod indexed;
mod inductive;
mod lgg;
mod lint;
pub use lint::{Lint, LintProfile};
mod matching;
mod metaprograms;
mod quote;
mod recursion;
pub mod resolve;
mod representations;
mod session;
mod slots;
mod statements;
mod surface;
mod traits;
mod types;
mod unification;
mod vec;
mod wf;

use attempt::DeclAttempt;
pub(crate) use application::{
    ParamMeta, Skel, has_implicit_mark, skel_of_lam_binders, skel_of_ty, skel_params,
};
use inductive::Inductive;
use metaprograms::{MetaDef, MetaPrograms};
use names::{
    miss_msg, qkey, split_qual, GlobalInfo, GlobalRegistration, ImportSpec,
    NameKind, NameRes, Names, Scope, DEFAULT_MODULE,
};
pub(crate) use context::{Alias, Cx, DictBinder, TyVar};
use representations::Representations;
use recursion::SelfRef;
use slots::{Ingredient, Slot};
use surface::{
    expression_as_type, expression_left_leaf_is_numeral, for_each_free_slot, has_free_slots,
    lower_argument_slots, slot_profile,
};
use traits::Traits;
use types::Types;
use unification::{ResolveOb, Sol, unify_ty, zonked, zonked_tm};
pub(crate) use surface::{count_holes, count_holes_expr, strengthen_global};
pub(crate) use unification::{embed, mentions_binder, strengthen_tm, strengthen_ty};

/// The stage-1 prelude: `sym`/`trans`/`cong`/`cong_succ`, monomorphic at
/// `Nat` where the equation's type is not a parameter.
/// (The universe-polymorphic versions are layer-m `Λ ℓ⃗` territory — later
/// stage; the Nat suite only ever congs by `Succ`.)
pub const PRELUDE: &str = include_str!("prelude.hthr");

/// The prelude's module name: an implicit import of every module
/// (docs/modules-design.md §3.2). Public so a loader can skip resolving it to
/// a file — there is no `prelude.hthr` on disk to find.
pub const PRELUDE_MODULE: &str = names::PRELUDE_MODULE;

pub use diagnostics::{
    ElabError, GoalReport, GoalSource, IndexedRoute, LintFix, Warning,
};

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
            ElabError::ArgSlotEscape { .. } =>
                "an argument slot needs an enclosing checking position with a function type"
                    .into(),
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
            ElabError::ArgSlotEscape { span } => format!(
                "{}: an argument slot needs an enclosing checking position with a function type",
                at(*span)
            ),
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
            ElabError::ArgSlotEscape { span } => headed(
                "an argument slot needs an enclosing checking position with a function type",
                *span,
            ),
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
            ElabError::ArgSlotEscape { .. } => write!(
                f,
                "an argument slot needs an enclosing checking position with a function type"
            ),
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

fn err<T>(msg: impl Into<String>, span: Span) -> R<T> {
    Err(ElabError::Elab { msg: msg.into(), span })
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

/// Where a resolved dictionary came from, when it came by **upcast**: the
/// *child* dictionary and its class type ([`Elaborator::resolve_goal_from`],
/// `docs/traits-named-upcast-design.md` §2.1). `None` for every other answer,
/// which is every answer already at the goal's own class.
type Upcast = Option<(Term, Type)>;

#[derive(Clone)]
struct OperatorFallbackUse {
    symbol: String,
    fallback: String,
    carrier: String,
    from: &'static str,
    span: Span,
}

/// A kernel-checked ordinary declaration which has not entered the session.
///
/// Construction is the entire fallible half of declaration elaboration.
/// Committing one only assigns its absolute Ψ position and updates the lookup
/// registries; it performs no elaboration and cannot fail.
struct PendingDecl {
    binding: GlobalBinding,
    registration: GlobalRegistration,
    is_axiom: bool,
    direct_dependencies: Vec<String>,
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
    /// Module scopes, committed ordinary declarations, and every index that
    /// makes them nameable (`names.rs`).
    names: Names,
    /// Committed nominal declarations and every index or generated definition
    /// belonging to them (`types.rs`).
    types: Types,
    /// Committed classes, instances, designations, and derived dictionaries
    /// (`traits.rs`).
    traits: Traits,
    /// Committed representation declarations, implementations, obligations,
    /// monomorph names, and designed access paths (`representations.rs`).
    representations: Representations,
    /// Direct declaration edges and their transitive assumption paths.
    provenance: provenance::Provenance,
    /// Nesting depth of generated-source elaboration. This is execution mode,
    /// not representation registry state; zero means user source.
    generated_depth: usize,
    /// Set while a `:= derive()` route elaborates the transfer generator's
    /// emission, so that the `impl` block *inside* that emission records
    /// `Derived` rather than what its own clauses look like. `None` everywhere
    /// else, which makes the mechanism inert.
    impl_provenance: Option<datarepr::Provenance>,
    /// Scratch state with exactly one ordinary declaration's lifetime.
    attempt: DeclAttempt,
    /// While an `instance` block is being elaborated: the members that have
    /// already landed, as (written name, full name). An unqualified reference
    /// to one of them resolves to its global, which is the whole of "later
    /// members use earlier members by name" (docs/traits-layer1-design.md
    /// §4.2). Empty outside a block, which makes the mechanism inert.
    instance_scope: Vec<(String, String)>,
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
    /// Project-local style policy for written-source lints. General lints run
    /// under every profile; the CLI selects `Stdlib` only for `lib/std`.
    lint_profile: LintProfile,
    /// Backchaining depth, for the recursion cap. A `Cell` because resolution
    /// recurses *through* `elab_check` — the nested obligation is discovered
    /// by `apply_implicit`, not passed down.
    resolve_depth: Cell<usize>,
    fuel: u64,
    /// Optional explicit collector for evaluator-region activity. Clones
    /// share it so speculative and generated checking contribute to the same
    /// requested measurement; ordinary elaborators leave it absent.
    value_metrics: Option<Rc<ValueMetrics>>,
    /// Successful arithmetic reconstructions in source order. This is the
    /// certifying solver's audit surface: callers can see certificate size
    /// and the exact library lemmas it selected. Failed declarations truncate
    /// reports alongside warnings in [`Self::elab_module_source`].
    arith_reports: RefCell<Vec<arith::ArithReport>>,
    /// Meta-layer definitions and the slots claimed by their `for` clauses
    /// (`metaprograms.rs`). Kept elaborator-side because layer-m terms cannot
    /// enter Ψ; both lookup views commit together after validation.
    meta_programs: MetaPrograms,
    /// The Ψ-extending binders of the `meta fn` currently elaborating (its
    /// `Ctx`/`TyCode` binders, plus letbox-bound code globals during quote
    /// assembly). The whnf/conv oracles append these to Ψ so meta-bound
    /// `GlobalVar`s resolve to the right bindings — the goal machinery's
    /// padding trick, one layer up. Empty outside a `meta fn`.
    meta_pushed: RefCell<Vec<GlobalBinding>>,
    /// Memo for the telescope walk in
    /// [`Elaborator::call_defers_for_result_only`], keyed by the global's absolute
    /// Ψ position. That test is asked at **every explicit argument of every
    /// call**, and its answer depends only on the callee's declared type,
    /// which never changes once the global is committed — so it is computed
    /// once per declaration rather than once per argument. Nothing here is
    /// semantic: dropping the memo changes only how long elaboration takes.
    result_only_memo: RefCell<HashMap<u32, bool>>,
    /// The oracle consulted at the kernel gate (`gate.rs`), if any. `None` —
    /// the default, and what every test and the unflagged CLI use — means the
    /// kernel runs on every declaration, exactly as it always has.
    gate: Option<Rc<dyn gate::KernelGate>>,
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

impl expr::StructuralTypeElab for Elaborator {
    fn lower_type(&self, cx: &Cx, ty: &Ty) -> R<(Type, Level)> {
        self.elab_ty(cx, ty)
    }

    fn infer_type_endpoint(&self, cx: &Cx, expression: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, expression)
    }

    fn lower_named_type(
        &self,
        cx: &Cx,
        name: &str,
        arguments: &[Ty],
        span: Span,
    ) -> R<(Type, Level)> {
        self.lower_named(cx, name, arguments, span)
    }

    fn check_type_endpoint(
        &self,
        cx: &Cx,
        expression: &Expr,
        expected: &Type,
        level: &Level,
    ) -> R<Term> {
        self.elab_check(cx, expression, expected, level)
    }
}

impl expr::UniverseElab for Elaborator {
    fn rewrite_type_operator(&self, cx: &Cx, expression: &Expr) -> R<Option<Expr>> {
        self.op_rewrite(cx, expression, None)
    }

    fn lower_declared_expression_type(
        &self,
        cx: &Cx,
        expression: &Expr,
        span: Span,
    ) -> R<Option<(Type, Level)>> {
        if let Some(lowered) = self.try_indexed_ty(cx, expression, span)? {
            return Ok(Some(lowered));
        }
        self.try_valparam_ty(cx, expression, span)
    }

    fn read_inferred_type(&self, cx: &Cx, inferred: &Type, span: Span) -> R<Type> {
        self.whnf(cx, inferred, span)
    }

    fn visible_type_former(&self, cx: &Cx, name: &str) -> Option<expr::TypeFormerShape> {
        if self.shadowed(cx, name) {
            return None;
        }
        let ind = self.lookup_inductive(name)?;
        Some(expr::TypeFormerShape {
            indexed: ind.index.is_some(),
            value_parameters: ind.valparams.len(),
        })
    }
}

impl expr::ExpectedTypeElab for Elaborator {
    fn read_expected_type(&self, cx: &Cx, expected: &Type, span: Span) -> R<Type> {
        self.whnf(cx, expected, span)
    }
}

impl expr::EqualityCheckingElab for Elaborator {
    fn goal_endpoints_convert(
        &self,
        cx: &Cx,
        lhs: &Term,
        rhs: &Term,
        ty: &Type,
        level: &Level,
    ) -> bool {
        self.goal_oracle()
            .convert_term(&cx.gamma, Layer::Prog, lhs, rhs, ty, level)
            .is_ok()
    }
}

impl expr::ExpectedTypeDiagnosticsElab for Elaborator {
    fn display_expected_type(&self, cx: &Cx, expected: &Type) -> String {
        self.display_type(cx, expected)
    }
}

impl expr::RecursiveCheckingElab for Elaborator {
    fn check_expression(
        &self,
        cx: &Cx,
        expression: &Expr,
        expected: &Type,
        level: &Level,
    ) -> R<Term> {
        self.elab_check(cx, expression, expected, level)
    }
}

impl expr::LambdaBinderElab for Elaborator {
    fn lower_lambda_annotation(&self, cx: &Cx, annotation: &Ty) -> R<(Type, Level)> {
        self.elab_ty(cx, annotation)
    }
}

impl expr::LambdaCheckingElab for Elaborator {
    fn lambda_domains_convert(
        &self,
        cx: &Cx,
        annotation: &Type,
        expected: &Type,
        level: &Level,
    ) -> bool {
        self.goal_oracle()
            .convert_type(&cx.gamma, Layer::Prog, annotation, expected, level)
            .is_ok()
    }
}

impl expr::LambdaInferenceElab for Elaborator {
    fn infer_lambda_body(&self, cx: &Cx, body: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, body)
    }
}

impl statements::StatementElab for Elaborator {
    fn lower_let_annotation(&self, cx: &Cx, annotation: &Ty) -> R<(Type, Level)> {
        self.elab_ty(cx, annotation)
            .map_err(|error| self.let_ty_hint(cx, annotation, error))
    }

    fn check_let_value(
        &self,
        cx: &Cx,
        expression: &Expr,
        expected: &Type,
        level: &Level,
        skeleton: Option<&Skel>,
    ) -> R<Term> {
        self.elab_check_skel(cx, expression, expected, level, None, skeleton)
    }

    fn infer_statement_expression(
        &self,
        cx: &Cx,
        expression: &Expr,
    ) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, expression)
    }

    fn infer_let_lambda(
        &self,
        cx: &Cx,
        binders: &[LamBinder],
        body: &Expr,
    ) -> R<(Term, Type, Level)> {
        self.expr_elab().infer_lambda(
            self,
            cx,
            binders,
            body,
            expr::LambdaInferenceMode::LetSkeletonHarvest,
        )
    }

    fn dictionary_alias(&self, name: &str, annotation: &Ty) -> Option<DictBinder> {
        let reference = self.class_ref_of_ty(annotation)?;
        if reference.index.is_empty() || reference.args.is_empty() {
            return None;
        }
        Some(DictBinder {
            name: name.to_string(),
            class: reference.name,
            carrier: reference.args[0].clone(),
            index: reference.index,
        })
    }

    fn record_for_destructuring(
        &self,
        cx: &Cx,
        record_type: &Type,
        span: Span,
    ) -> Option<Rc<Inductive>> {
        self.record_of_at(cx, record_type, span)
    }

    fn project_destructured_field(
        &self,
        cx: &Cx,
        record: &Inductive,
        record_type: &Type,
        value: Rc<Term>,
        index: usize,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        self.project_field(cx, record, record_type, value, index, span)
    }
}

impl statements::BlockCheckingElab for Elaborator {
    fn check_block_result(
        &self,
        cx: &Cx,
        result: &Expr,
        expected: &Type,
        level: &Level,
        hint: Option<(&str, &str)>,
        skeleton: Option<&Skel>,
        capture_slots: bool,
    ) -> R<Term> {
        self.elab_check_skel_slots(
            cx,
            result,
            expected,
            level,
            hint,
            skeleton,
            capture_slots,
        )
    }
}

impl matching::MotiveSynthesisElab for Elaborator {
    fn read_motive_type(&self, cx: &Cx, ty: &Type, span: Span) -> Option<Type> {
        self.whnf(cx, ty, span).ok()
    }

    fn read_motive_term(&self, cx: &Cx, term: &Term, span: Span) -> Option<Rc<Term>> {
        self.whnf_tm(cx, term, span).ok()
    }

    fn motive_candidate_converts(
        &self,
        cx: &Cx,
        candidate: &Term,
        scrutinee: &Term,
        scrutinee_type: &Type,
        scrutinee_level: &Level,
    ) -> bool {
        self.goal_oracle()
            .convert_term(
                &cx.gamma,
                Layer::Prog,
                candidate,
                scrutinee,
                scrutinee_type,
                scrutinee_level,
            )
            .is_ok()
    }
}

impl matching::MatchSpeculationState for Elaborator {
    type Mark = (usize, usize);

    fn mark_match_state(&self) -> Self::Mark {
        (self.warnings.borrow().len(), self.attempt.goal_arena.mark())
    }

    fn rollback_match_state(&self, mark: Self::Mark) {
        self.warnings.borrow_mut().truncate(mark.0);
        self.attempt.goal_arena.rollback(mark.1);
    }

    fn motive_probe_active(&self) -> bool {
        self.attempt.motive_speculation.get()
    }

    fn set_motive_probe_active(&self, active: bool) {
        self.attempt.motive_speculation.set(active);
    }
}

impl matching::ConstantMotiveElab for Elaborator {
    fn infer_motive_expr(&self, cx: &Cx, expr: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, expr)
    }

    fn lower_if_condition(&self, cx: &Cx, condition: &Ty) -> R<(Type, Level)> {
        self.elab_ty(cx, condition)
    }

    fn lower_constant_match(
        &self,
        cx: &Cx,
        form: MatchForm,
        generated: bool,
        arms: &[Arm],
        scrutinee: Term,
        scrutinee_type: &Type,
        scrutinee_level: &Level,
        motive: Type,
        motive_level: Level,
        span: Span,
    ) -> R<Term> {
        self.elab_match(
            cx,
            form,
            generated,
            arms,
            scrutinee,
            scrutinee_type,
            scrutinee_level,
            motive,
            motive_level,
            span,
        )
    }
}

impl application::ExplicitArgElab for Elaborator {
    fn whnf_for_application(&self, cx: &Cx, ty: &Type, span: Span) -> R<Type> {
        self.whnf(cx, ty, span)
    }

    fn check_explicit_argument(
        &self,
        cx: &Cx,
        arg: &Expr,
        expected: &Type,
        level: &Level,
        hint: Option<(&str, &str)>,
        skel: Option<&Skel>,
    ) -> R<Term> {
        self.elab_check_skel(cx, arg, expected, level, hint, skel)
    }
}

impl recursion::SelfCallElab for Elaborator {
    fn infer_self_call_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, argument)
    }

    fn self_call_application_params(&self, name: &str) -> Rc<Vec<ParamMeta>> {
        self.params_of(name)
    }
}

impl vec::SurfaceVecElab for Elaborator {
    fn infer_vector_expr(&self, cx: &Cx, expression: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, expression)
    }

    fn check_vector_expr(
        &self,
        cx: &Cx,
        expression: &Expr,
        expected: &Type,
        level: &Level,
    ) -> R<Term> {
        self.elab_check(cx, expression, expected, level)
    }

    fn whnf_vector_type(&self, cx: &Cx, ty: &Type, span: Span) -> R<Type> {
        self.whnf(cx, ty, span)
    }

    fn whnf_vector_term(&self, cx: &Cx, term: &Term, span: Span) -> R<Rc<Term>> {
        self.whnf_tm(cx, term, span)
    }

    fn try_vector_template(
        &self,
        cx: &Cx,
        slot: Slot,
        ingredients: &[(&'static str, Ingredient<'_>)],
        span: Span,
    ) -> R<Option<Term>> {
        self.try_code_template(cx, slot, ingredients, span)
    }
}

impl application::ImplicitApplicationElab for Elaborator {
    fn classify_application_argument(
        &self,
        cx: &Cx,
        argument: &Expr,
    ) -> application::ArgumentClass {
        application::ArgumentClass {
            checking_only: self.is_checking_only(cx, argument),
            fallback_infer: self.deferral_can_fall_back(cx, argument),
        }
    }

    fn infer_application_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, argument)
    }

    fn unify_application_argument_type(
        &self,
        cx: &Cx,
        parameter: &Type,
        argument: &Type,
        n: u32,
        sols: &mut [Sol],
        span: Span,
    ) {
        self.unify_arg_ty(cx, parameter, argument, n, sols, span)
    }

    fn solve_application_from_expected(
        &self,
        cx: &Cx,
        result: &Type,
        expected: &Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        span: Span,
    ) -> R<()> {
        self.solve_from_expected(cx, result, expected, n, sols, meta_doms, span)
    }

    fn resolve_application_obligation(
        &self,
        cx: &Cx,
        _name: &str,
        params: &[ParamMeta],
        slot_param: &[usize],
        meta_doms: &[Type],
        n: u32,
        sols: &mut [Sol],
        obligation: &ResolveOb,
        span: Span,
    ) -> R<application::ObligationProgress> {
        let Some(goal) = zonked(&obligation.dom, n, sols) else {
            // A blocked indexed goal first consults the matching dictionary
            // binder, then an operator designation. Either may fill an index
            // slot without yet solving this obligation.
            let written = params.get(obligation.param).and_then(|p| p.solver.as_deref());
            let changed = self.fill_index_from_scope(cx, written, params, slot_param, sols)
                || self.fill_index_from_designation(
                    cx, written, params, slot_param, sols, meta_doms, n, span,
                );
            return Ok(if changed {
                application::ObligationProgress::Unblocked
            } else {
                application::ObligationProgress::Blocked
            });
        };
        let display = params
            .get(obligation.param)
            .and_then(|p| p.solver.as_deref())
            .map(traits::render_ty)
            .unwrap_or_else(|| "a solver parameter".to_string());
        let mut trace = Vec::new();
        match self.resolve_goal(
            cx,
            &goal,
            &obligation.dom_level,
            &display,
            span,
            &mut trace,
        ) {
            Some(term) => {
                sols[obligation.slot] = Sol::Solved(Rc::new(term));
                Ok(application::ObligationProgress::Solved)
            }
            None => Err(ElabError::Resolution { goal: display, span, trace }),
        }
    }

    fn promote_application_goals(
        &self,
        cx: &Cx,
        name: &str,
        params: &[ParamMeta],
        slot_param: &[usize],
        meta_doms: &[Type],
        meta_lvls: &[Level],
        n: u32,
        sols: &mut [Sol],
        span: Span,
    ) -> R<()> {
        let promoted: Vec<usize> = sols
            .iter()
            .enumerate()
            .filter_map(|(slot, sol)| matches!(sol, Sol::Unsolved).then_some(slot))
            .collect();
        match self.attempt.goal_arena.reserve_promoted(promoted.len() as u32) {
            goals::PromotionCapacity::Disabled => return Ok(()),
            goals::PromotionCapacity::Ready => {}
            goals::PromotionCapacity::Restart => {
                return err(
                    "internal: restarting declaration to reserve promoted apply goals",
                    span,
                );
            }
        }
        for slot in promoted {
            // Telescope order means earlier implicit parameters have already
            // been inferred or promoted. A remaining blocked domain belongs
            // to a solver/deferred value and is left for its own diagnostic.
            let Some(dom) = zonked(&meta_doms[slot], n, sols) else { continue };
            let parameter = slot_param[slot];
            let param = params.get(parameter).map(|p| p.name.as_str()).unwrap_or("?");
            let key = format!("apply:{name}:{parameter}");
            let goal = self.new_goal_key(
                cx,
                None,
                Some((name, param)),
                dom,
                meta_lvls[slot].clone(),
                span,
                Some(&key),
                Some(parameter),
            )?;
            sols[slot] = Sol::Solved(Rc::new(goal));
        }
        Ok(())
    }

    fn blocked_solver_error(
        &self,
        name: &str,
        params: &[ParamMeta],
        obligation: &ResolveOb,
        span: Span,
    ) -> ElabError {
        let parameter = params
            .get(obligation.param)
            .map(|parameter| parameter.name.as_str())
            .unwrap_or("?");
        if let Some(solver) = params
            .get(obligation.param)
            .and_then(|parameter| parameter.solver.as_deref())
            && let Some(reference) = self.class_ref_of_ty(solver)
            && let Some(class) = self.lookup_class(&reference.name)
            && !class.valparams.is_empty()
        {
            return self.value_slot_refusal(&class, name, None, span);
        }
        let goal = params
            .get(obligation.param)
            .and_then(|parameter| parameter.solver.as_deref())
            .map(traits::render_ty)
            .unwrap_or_else(|| "a solver parameter".to_string());
        ElabError::Elab {
            msg: format!(
                "the goal of `{parameter}` (`{goal}`) still mentions an implicit that \
                 could not be inferred here, so no search can run for it: give the type \
                 arguments (`{name}<…>(…)`) or pass `{parameter}` explicitly \
                 (`@{name}(…)`)"
            ),
            span,
        }
    }
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
            names: Names::new(DEFAULT_MODULE),
            types: Types::default(),
            traits: Traits::default(),
            representations: Representations::default(),
            provenance: provenance::Provenance::default(),
            generated_depth: 0,
            impl_provenance: None,
            attempt: DeclAttempt::default(),
            instance_scope: Vec::new(),
            pending_derived: RefCell::new(Vec::new()),
            warnings: RefCell::new(Vec::new()),
            lint_profile: LintProfile::Default,
            resolve_depth: Cell::new(0),
            fuel: DEFAULT_FUEL,
            value_metrics: None,
            arith_reports: RefCell::new(Vec::new()),
            meta_programs: MetaPrograms::default(),
            meta_pushed: RefCell::new(Vec::new()),
            result_only_memo: RefCell::new(HashMap::new()),
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

    /// Select project-local source conventions without changing what syntax
    /// the language accepts. Intended for drivers before they check a module.
    pub fn set_lint_profile(&mut self, profile: LintProfile) {
        self.lint_profile = profile;
    }

    /// Begin aggregating value-machine allocation and cache activity across
    /// kernel gates and in-language analyzer evaluation.
    pub fn enable_value_metrics(&mut self) {
        self.value_metrics = Some(Rc::new(ValueMetrics::default()));
    }

    /// Reset the active collector without changing whether instrumentation is
    /// enabled. Useful for measuring one source fragment after its imports;
    /// call only between checks, when no profiled arena is still active.
    pub fn reset_value_metrics(&self) {
        if let Some(metrics) = &self.value_metrics {
            metrics.reset();
        }
    }

    pub fn value_metrics(&self) -> Option<ValueMetricsSnapshot> {
        self.value_metrics.as_ref().map(|metrics| metrics.snapshot())
    }

    /// Drain the audit reports produced by successful `arith` uses.
    pub fn take_arith_reports(&self) -> Vec<arith::ArithReport> {
        self.arith_reports.borrow_mut().drain(..).collect()
    }

    pub(crate) fn profiled_value_arena(&self) -> ValueArena<'_> {
        self.value_metrics
            .as_deref()
            .map_or_else(ValueArena::new, ValueArena::profiled)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn kernel_check_type(
        &self,
        psi: &GlobalCtx,
        layer: Layer,
        gamma: &LocalCtx,
        ty: &Type,
        level: &Level,
    ) -> Result<(), TypeError> {
        match self.value_metrics.as_deref() {
            Some(metrics) => typing::check_type_profiled(
                psi, 0, layer, gamma, ty, level, self.fuel, metrics,
            ),
            None => typing::check_type(psi, 0, layer, gamma, ty, level, self.fuel),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn kernel_check_term(
        &self,
        psi: &GlobalCtx,
        layer: Layer,
        gamma: &LocalCtx,
        term: &Term,
        ty: &Type,
        level: &Level,
    ) -> Result<(), TypeError> {
        match self.value_metrics.as_deref() {
            Some(metrics) => typing::check_term_profiled(
                psi, 0, layer, gamma, term, ty, level, self.fuel, metrics,
            ),
            None => typing::check_term(psi, 0, layer, gamma, term, ty, level, self.fuel),
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
        self.session_transaction(|me| me.generated_mode(|me| me.elab_source(src)))
    }

    /// [`Self::elab_source`] into a named module. The elaborator does no file
    /// IO: an `import m;` here requires that `m` has *already* been elaborated
    /// into this same accumulator, which is exactly what the CLI's topological
    /// walk guarantees (docs/modules-design.md §3.2).
    pub fn elab_module_source(&mut self, module: &str, src: &str) -> R<()> {
        let file = parse_file(src)?;
        let lint_source = lint::Source::new(src, self.lint_profile);
        self.enter_module(module, &file)?;
        for item in &file.items {
            let warn_mark = self.warnings.borrow().len();
            let arith_mark = self.arith_reports.borrow().len();
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
                self.arith_reports.borrow_mut().truncate(arith_mark);
            } else {
                self.mint_pending();
                self.run_source_lints(item, &lint_source);
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
            self.names.module_scope(module).cloned().unwrap_or_else(|| Scope::new(module));
        let mut written: Vec<&str> = Vec::new();
        for item in &file.items {
            let Item::Import(imp) = item else { continue };
            if imp.module == module {
                return err(format!("a module cannot import itself (`{module}`)"), imp.span);
            }
            if imp.module != PRELUDE_MODULE && !self.names.has_module(&imp.module) {
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
        self.names.enter_scope(scope);
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
        self.names.resolve_kinds(name, kinds, |m, ty, ctor| {
            self.types
                .inductive(&qkey(m, ty))
                .is_some_and(|i| i.ctors.iter().any(|c| c.name == ctor))
        })
    }

    /// Install the declaration scope for one read of stored inductive syntax.
    /// The guard restores the caller's scope on every return path.
    fn use_inductive_scope<'a>(
        &'a self,
        ind: &inductive::Inductive,
    ) -> names::ResolutionScope<'a> {
        self.names.use_scope(Rc::clone(&ind.scope))
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
        self.names.global(&self.key_of(self.instance_alias(name))?)
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
        self.types.inductive(&self.key_of_kinds(name, &[NameKind::Inductive])?)
    }

    pub(crate) fn lookup_ctor(&self, name: &str) -> Option<(Rc<Inductive>, usize)> {
        // `Option::None` resolves through the *type*, so the key is the
        // constructor's own name in the type's module.
        let key = self.key_of(name)?;
        self.types.constructor(&key).map(|(i, k)| (Rc::clone(i), *k))
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
        self.names.declares_as(self.names.module(), name, kinds)
    }

    /// The one collision the regime turns into an error at the *declaration*:
    /// a local name that an import listed by name. (An unlisted collision is
    /// fine — locals win.) Checked before anything is registered, since a
    /// failed declaration must register nothing.
    fn check_declarable(&self, name: &str, span: Span) -> R<()> {
        if let Some(m) = self
            .names
            .scope()
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
        self.names.insert_current(name, kind);
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
    pub(crate) fn emit_lint(&self, lint: Lint, msg: impl Into<String>, span: Span) {
        self.emit_lint_with_fix(lint, msg, span, None);
    }

    fn emit_lint_with_fix(
        &self,
        lint: Lint,
        msg: impl Into<String>,
        span: Span,
        fix: Option<LintFix>,
    ) {
        // §4.1: a span into *generated* text does not index into any file a
        // reader has, and a `datarepr`'s emission is elaborated inside an
        // ordinary `check` of the declaration that owns it. Rendering such a
        // span against the user's source would point a caret at an unrelated
        // line. Generated code is the generator's problem, so it is dropped
        // here rather than filtered by whoever renders.
        if self.in_generated() {
            return;
        }
        let mut warnings = self.warnings.borrow_mut();
        if warnings.iter().any(|w| w.lint == lint && w.span == span) {
            return;
        }
        warnings.push(Warning { lint, msg: msg.into(), span, fix });
    }

    fn run_source_lints(&self, item: &Item, source: &lint::Source<'_>) {
        for warning in self
            .warnings
            .borrow_mut()
            .iter_mut()
            .filter(|w| w.lint == Lint::RedundantMatchMotive)
        {
            if let Some(fix) = &mut warning.fix
                && let Some(span) = source.complete_motive_fix(item, fix.span)
            {
                fix.span = span;
                fix.replacement = " ".into();
            }
        }
        for finding in lint::check_item(item, source) {
            // A dead arm's body is deliberately never checked. Its dedicated
            // semantic warning already says so; piling lexical unused-binder
            // findings onto names in that body would pretend we had analyzed
            // code that cannot run.
            if finding.lint == Lint::UnusedPatternBinder
                && self.warnings.borrow().iter().any(|w| {
                    w.lint == Lint::UnreachableMatchArm
                        && w.span.start <= finding.span.start
                        && finding.span.end <= w.span.end
                })
            {
                continue;
            }
            if !self.in_generated() {
                self.warnings.borrow_mut().push(Warning {
                    lint: finding.lint,
                    msg: finding.msg,
                    span: finding.span,
                    fix: finding.fix,
                });
            }
        }
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
        let lint_source = lint::Source::new(src, self.lint_profile);
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
                self.run_source_lints(item, &lint_source);
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
        self.traits.derived().iter().map(|d| d.name.as_str()).collect()
    }

    /// Assumptions reachable from one declaration, resolved by the same name
    /// judgment as an ordinary source reference.
    pub fn axiom_report(&self, name: &str) -> Result<AxiomReport, String> {
        let key = self
            .key_of_kinds(name, &[NameKind::Global])
            .ok_or_else(|| format!("no visible declaration named `{name}`"))?;
        self.provenance
            .report(&key)
            .ok_or_else(|| format!("`{name}` has no provenance record"))
    }

    /// Every non-axiom declaration whose proof or body reaches an axiom.
    /// Sorted by resolved declaration identity.
    pub fn axiom_violations(&self) -> Vec<AxiomReport> {
        self.provenance.tainted()
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
    /// `GlobalVar`s to callee names. The name registry maintains this reverse
    /// index when the declaration commits.
    pub(crate) fn global_name_at(&self, abs: usize) -> Option<String> {
        let key = self.names.global_name_at(abs as u32)?;
        Some(key.rsplit("::").next().unwrap_or(key).to_string())
    }

    /// The absolute Ψ index a `GlobalVar` *occurring in a term being
    /// displayed* refers to. Same inversion as [`Self::gen_def_of`]'s, and for
    /// the same reason: the index counts from the innermost end of the padded
    /// Ψ, so the goal region and a `meta fn`'s pushed binders both shift it.
    /// Fully checked — a `GlobalVar` reaching here can be anything the term it
    /// came out of contains, including one that is out of scope.
    pub(crate) fn global_abs_of(&self, var: GlobalVar) -> Option<usize> {
        let len = self.psi.bindings.len() as u32;
        let abs = len
            .checked_add(self.attempt.goal_arena.base())?
            .checked_add(self.meta_pushed.borrow().len() as u32)?
            .checked_sub(var.0.checked_add(1)?)?;
        Some(abs as usize)
    }

    /// The parameter table of the binding at absolute Ψ index `abs`, empty for
    /// a binding that has none. The by-index companion of [`Self::params_of`].
    pub(crate) fn params_at(&self, abs: usize) -> Rc<Vec<ParamMeta>> {
        self.names.params_at(abs as u32).unwrap_or_else(|| Rc::new(Vec::new()))
    }

    /// The `meta fn` claiming an analyzer slot, with the arity of its Π spine
    /// fixed by the slot's own signature
    /// (docs/certgen-transcriber-in-language-design.md §6). `None` is the
    /// honest decline every caller falls back from: no template claimed it.
    pub(crate) fn analyzer_def(&self, slot: Slot) -> Option<&MetaDef> {
        self.meta_programs.for_slot(slot).map(|(_, definition)| definition)
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
            names::qkey(self.names.module(), name)
        };
        let ind = self.types.inductive(&key)?;
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
        let warn_mark = self.warnings.borrow().len();
        let mut reserved = 0;
        self.attempt.goal_arena.enable_restarts();
        let r = loop {
            self.attempt.prepare();
            self.pending_derived.borrow_mut().clear();
            let r = self.check_decl(decl, reserved);
            let requested = self.attempt.goal_arena.take_requested_base();
            if requested <= reserved {
                break r;
            }
            // Nothing in an ordinary declaration is registered before its
            // kernel gate. Goal-capacity discovery is therefore speculative:
            // discard its diagnostics and goal arena, enlarge the stable Ψ
            // prefix, and elaborate the declaration again from its source.
            self.warnings.borrow_mut().truncate(warn_mark);
            self.attempt.clear_goals();
            reserved = requested;
        };
        self.attempt.finish();
        self.refresh_delta_psi();
        match r {
            Ok(pending) => {
                self.commit_decl(pending);
                for used in self.attempt.op_fallback_uses.borrow_mut().drain(..) {
                    self.emit_lint(
                        Lint::OperatorFallback,
                        format!(
                            "`{}` has no designation at `{}` ({}), so this notation resolved through the compatibility fallback `{}`; install or import `designation {} at {} := {}` to make the meaning explicit",
                            used.symbol,
                            used.carrier,
                            used.from,
                            used.fallback,
                            used.symbol,
                            used.carrier,
                            used.fallback,
                        ),
                        used.span,
                    );
                }
                Ok(())
            }
            Err(error) => {
                self.attempt.op_fallback_uses.borrow_mut().clear();
                Err(error)
            }
        }
    }

    /// The sole commit point for a checked ordinary declaration.
    ///
    /// Every operation here is infallible. In particular, no declaration can
    /// become visible to later source unless `check_decl` returned a complete
    /// value after the kernel gate.
    fn commit_decl(&mut self, pending: PendingDecl) {
        let PendingDecl { binding, registration, is_axiom, direct_dependencies } = pending;
        let key = registration.key.clone();
        let abs = self.psi.bindings.len() as u32;
        self.psi.push(binding);
        self.names.commit_global(abs, registration);
        self.provenance.commit(key, is_axiom, direct_dependencies);
        self.refresh_delta_psi();
    }

    /// The binders available in an instance's **head**, for declaration-time
    /// inspection that must elaborate the carrier before the generated
    /// instance declarations exist. Equality carriers need this to infer the
    /// endpoints' type and use its resolved declaration as their registry key
    /// (issues/decidable-equation-carrier.md).
    ///
    /// This is the prefix of [`Self::check_decl`]'s telescope builder:
    /// type parameters, then value parameters. `requires` dictionaries do not
    /// occur in an instance head and therefore deliberately are not in scope.
    fn instance_head_cx(&self, decl: &InstanceDecl) -> R<Cx> {
        let mut cx = Cx::empty();
        for (i, tv) in decl.tyvars.iter().enumerate() {
            if decl.tyvars[..i].iter().any(|other| other.name == tv.name) {
                return err(format!("duplicate type parameter `{}`", tv.name), tv.span);
            }
            let level = Level::constant(tv.level);
            cx.push(tv.name.clone(), Type::Ty(level.clone()), Level::constant(tv.level + 1));
            cx.tyvars.push(TyVar {
                name: tv.name.clone(),
                ty: Type::El {
                    level: level.clone(),
                    tm: Rc::new(Term::Var(LocalVar(0))),
                },
                level,
                depth: cx.names.len(),
            });
        }
        for p in &decl.valparams {
            let (ty, lvl) = self.elab_ty(&cx, &p.ty)?;
            cx.push_skel(p.name.clone(), ty.clone(), lvl, skel_of_ty(&p.ty));
            if let Type::Ty(level) = &ty {
                cx.tyvars.push(TyVar {
                    name: p.name.clone(),
                    ty: Type::El {
                        level: level.clone(),
                        tm: Rc::new(Term::Var(LocalVar(0))),
                    },
                    level: level.clone(),
                    depth: cx.names.len(),
                });
            }
        }
        Ok(cx)
    }

    fn check_decl(&mut self, decl: &Decl, reserved_goals: u32) -> R<PendingDecl> {
        // Keep the writer's declaration, not the constraint-expanded working
        // copy: representation obligations later restate the surface API.
        let surface = decl.clone();
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
        self.attempt.goal_arena.configure(count_holes(decl), reserved_goals);
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
        // The graph records what the checked proof/body references, not names
        // appearing only in its public statement (issues/axiom-provenance.md).
        self.attempt.direct_dependencies.borrow_mut().clear();
        if decl.kind != DeclKind::Axiom {
            cx.selfref = Some(Rc::new(SelfRef {
                // A member recurses under its **base** name: inside
                // `fn List::nth` the recursive call is `nth(t)`, not
                // `List::nth(t)`. The self-name is checked before globals in
                // `resolve`, so this shadows an ambient `nth` for the body.
                name: member.map_or_else(|| decl.name.clone(), |(_, base)| base.to_string()),
                // Type parameters participate in guarded-call bookkeeping as
                // implicit parameters (docs/surface-polymorphism.md §6.1).
                params: decl
                    .tyvars
                    .iter()
                    .map(|t| (t.name.clone(), true))
                    .chain(decl.params.iter().map(|p| (p.name.clone(), p.implicit)))
                    .collect(),
                n_tyvars: decl.tyvars.len(),
            }));
        }
        // An axiom has no term to check. Ordinary definitions and theorems
        // elaborate their block exactly as before.
        let body = if decl.kind == DeclKind::Axiom {
            self.solve_goals(&[], &decl.name)?;
            None
        } else {
            let cx = statements::elaborate(self, &cx, &decl.body.stmts)?;
            let body = self.elab_check(&cx, &decl.body.result, &res_ty, &res_lvl)?;
            self.solve_goals(&decl.body.ons, &decl.name)?;
            Some(body)
        };
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
            term = term.map(|term| Term::Lam {
                dom_level: dom_lvl.clone(),
                cod_level: stmt_lvl.clone(),
                dom: Rc::new(dom.clone()),
                body: Rc::new(term),
            });
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
        let term = term.map(|term| term.apply_global(&sigma));
        let stmt = stmt.apply_global(&sigma);

        // The kernel is the gate: check the statement, then the term.
        // `stats::time_kernel` attributes exactly this to the kernel half of
        // the frontend suite's phase split (crates/elab/src/stats.rs).
        //
        // An installed gate oracle (`gate.rs`) may vouch for the declaration
        // instead, in which case neither call runs. Nothing installs one by
        // default; `heather check --cache` is the only caller today.
        let empty = LocalCtx::nil();
        if let Some(term) = term.as_ref() {
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
                    self.kernel_check_type(
                        &self.psi, Layer::Prog, &empty, &stmt, &stmt_lvl,
                    )
                })
                .map_err(|e| self.kernel_error(&decl.name, decl.span, e))?;
                stats::time_kernel(|| {
                    self.kernel_check_term(
                        &self.psi, Layer::Code, &empty, &term, &stmt, &stmt_lvl,
                    )
                })
                .map_err(|e| self.kernel_error(&decl.name, decl.span, e))?;
                if let Some(g) = self.gate.as_ref() {
                    g.accepted(&self.psi, &item);
                }
            }
        } else {
            // Axioms extend the trusted assumptions, but their statements are
            // still required to be well-formed kernel types.
            stats::time_kernel(|| {
                self.kernel_check_type(&self.psi, Layer::Prog, &empty, &stmt, &stmt_lvl)
            })
            .map_err(|e| self.kernel_error(&decl.name, decl.span, e))?;
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
        // All three kinds bind a closed `Trm_c` global; the `fn` is the one that
        // keeps its body, so later declarations reference it as `u^δ` and
        // conversion δ-unfolds it at p when — and only when — running it is
        // what the comparison needs.
        //
        // A `theorem` stays opaque even though its proof is right here:
        // proofs are transported, never evaluated, and a transparent proof
        // would put the whole proof term back into every conversion that
        // mentions the theorem.
        let binding = GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(stmt),
            level: stmt_lvl,
            body: match decl.kind {
                DeclKind::Fn => Some(Rc::new(term.expect("a function has a body"))),
                DeclKind::Theorem | DeclKind::Axiom => None,
            },
        };
        if decl.kind == DeclKind::Axiom
            && let Some(gate) = self.gate.as_ref()
        {
            gate.assumption(&self.psi, &decl.name, &binding);
        }
        let direct_dependencies = self
            .attempt
            .direct_dependencies
            .borrow()
            .iter()
            .cloned()
            .collect();
        Ok(PendingDecl {
            binding,
            is_axiom: decl.kind == DeclKind::Axiom,
            direct_dependencies,
            registration: GlobalRegistration {
                name: decl.name.clone(),
                key: qkey(self.names.module(), &decl.name),
                params,
                member_base: member.map(|(_, base)| base.to_string()),
                surface,
            },
        })
    }

    // -- goals --------------------------------------------------------------

    /// Raise a goal with a stable discriminator for several synthesized goals
    /// at one shared source span. Written holes use [`goals::GoalAllocator`];
    /// promoted implicit parameters additionally need this key and index.
    fn new_goal_key(
        &self,
        cx: &Cx,
        name: Option<&str>,
        hint: Option<(&str, &str)>,
        ty: Type,
        level: Level,
        span: Span,
        key: Option<&str>,
        promoted_parameter: Option<usize>,
    ) -> R<Term> {
        self.attempt.goal_arena.allocate(
            cx,
            name,
            hint,
            ty,
            level,
            span,
            key,
            promoted_parameter,
        )
    }

    /// Run the block's `on` statements, then require that every goal is
    /// discharged.
    fn solve_goals(&self, ons: &[OnStmt], decl: &str) -> R<()> {
        // No new goals from here on: `on` right-hand sides are elaborated in
        // the goal world but their solutions are strengthened out of it.
        self.attempt.goal_arena.freeze();
        for on in ons {
            match &on.target {
                OnTarget::Name(name) => {
                    let (cx, ty, lvl) = self.attempt.goal_arena.named(name, on.span)?;
                    // In the goal's *own* context, not the one at the `on`.
                    let t = self.elab_check(&cx, &on.expr, &ty, &lvl)?;
                    let t = strengthen_global(&t, self.attempt.goal_arena.base());
                    self.attempt.goal_arena.solve_named(name, t);
                }
                // `on _: P := e;` — discharge *every* goal whose statement is
                // `P` (docs/sketches/surface-v2.md §2: one bound proof feeding
                // many sites). `P` is elaborated per goal, in that goal's own
                // context, since that is where its statement lives.
                OnTarget::Stmt(pat) => {
                    let oracle = self.goal_oracle();
                    let candidates = self.attempt.goal_arena.outstanding();
                    let mut matched = Vec::new();
                    for (k, cx, ty, lvl) in candidates {
                        // Not well-formed in this goal's context just means
                        // "not this goal" — a statement need not mention names
                        // every goal has.
                        let Ok((pat_ty, pat_lvl)) = self.elab_ty(&cx, pat) else {
                            continue;
                        };
                        if oracle
                            .convert_type(&cx.gamma, Layer::Prog, &pat_ty, &ty, &pat_lvl)
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
                        let t = strengthen_global(&t, self.attempt.goal_arena.base());
                        self.attempt.goal_arena.solve(k, t);
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
        let unsolved = self
            .attempt
            .goal_arena
            .reports(|cx, ty| self.display_type(cx, ty));
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
        self.attempt
            .goal_arena
            .world(&self.psi, &self.meta_pushed.borrow())
    }

    /// The substitution discharging the whole goal block: `entries[k]` is the
    /// payload for goal `k` at `GlobalVar(goal_base - 1 - k)`, matching
    /// `apply_global`'s convention. Reserved-but-unused slots (the pre-count
    /// is an upper bound) get a payload nothing can reach.
    fn goal_subst(&self) -> GlobalSubst {
        self.attempt.goal_arena.substitution()
    }

    // -- types --------------------------------------------------------------

    fn elab_ty(&self, cx: &Cx, ty: &Ty) -> R<(Type, Level)> {
        match &ty.kind {
            // An expression in type position: infer it, require its type to be
            // a universe, and decode (docs/surface-universe.md §4). `El` is the
            // kernel's own decoding, so nothing here is a coercion — the term
            // *is* a code, and `El ⌜T⌝ ⇝ T` makes a written type and a decoded
            // one convertible rather than merely equal-looking.
            TyKind::OfExpr(e) => self.expr_elab().lower_expression_type(self, cx, e, ty.span),
            _ => self
                .expr_elab()
                .type_form(self, cx, ty)
                .expect("every structural type form is classified by ExprElab"),
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
        self.elab_check_skel_slots(cx, e, expected, lvl, hint, skel, true)
    }

    /// Checking with control over whether THIS boundary may capture argument
    /// slots. A capture-enabled boundary first probes a clone with itself
    /// disabled: nested checking positions remain enabled and therefore win.
    /// Only a slot that escapes all of them causes this boundary to lower the
    /// free section to ordinary lambdas. The clone makes the probe incapable
    /// of leaking goals, derived instances, warnings, or mismatch notes.
    #[allow(clippy::too_many_arguments)]
    fn elab_check_skel_slots(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
        lvl: &Level,
        hint: Option<(&str, &str)>,
        skel: Option<&Skel>,
        capture_slots: bool,
    ) -> R<Term> {
        if capture_slots && has_free_slots(e) {
            let probe = self.clone();
            match probe.elab_check_skel_slots(cx, e, expected, lvl, hint, skel, false) {
                Ok(_) => {
                    // Every slot found a smaller function-typed checking
                    // position. Repeat on the real elaborator; the probe's
                    // state is deliberately discarded.
                    return self
                        .elab_check_skel_slots(cx, e, expected, lvl, hint, skel, false);
                }
                Err(ElabError::ArgSlotEscape { span }) => {
                    if !matches!(self.whnf(cx, expected, span)?, Type::Pi { .. }) {
                        return Err(ElabError::ArgSlotEscape { span });
                    }
                    // The first escaping slot may precede smaller sections in
                    // source order. Probe every slot independently, masking
                    // its siblings with disposable neutrals, so ownership is
                    // structural rather than an accident of traversal order.
                    let mut slots = Vec::new();
                    for_each_free_slot(e, &mut |_, span| slots.push(span));
                    let mut nested = Vec::new();
                    for target in slots {
                        let targeted = self.clone();
                        targeted.attempt.slot_probe_target.set(Some(target));
                        match targeted
                            .elab_check_skel_slots(cx, e, expected, lvl, hint, skel, false)
                        {
                            Ok(_) => nested.push(target),
                            Err(ElabError::ArgSlotEscape { span }) if span == target => {}
                            Err(other) => return Err(other),
                        }
                    }
                    let profile = slot_profile(e, &nested)?
                        .expect("an escaping slot remains after nested captures");
                    let lowered = lower_argument_slots(e, profile, &nested);
                    return self.elab_check_skel_slots(
                        cx, &lowered, expected, lvl, hint, skel, false,
                    );
                }
                Err(other) => return Err(other),
            }
        }
        // A written motive in checking position has a mechanically testable
        // redundancy criterion: clone the elaborator, remove just the motive,
        // and ask the ordinary goal-derived route to check the same match
        // against the same expected type. The clone makes goals, warnings,
        // fallback provenance, derived instances, and fuel bookkeeping
        // transactional; no declaration or kernel gate is duplicated.
        if let ExprKind::Match {
            generated: false,
            scrut,
            motive: Some(motive),
            eqbind: None,
            ..
        } = &e.kind
        {
            let mut omitted = e.clone();
            let ExprKind::Match { motive: omitted_motive, .. } = &mut omitted.kind else {
                unreachable!()
            };
            *omitted_motive = None;
            let probe = self.clone();
            if let Ok(term) = probe.elab_check_skel_slots(
                    cx,
                    &omitted,
                    expected,
                    lvl,
                    hint,
                    skel,
                    capture_slots,
                )
                && probe
                    .kernel_check_term(
                        &probe.goal_psi(), Layer::Prog, &cx.gamma, &term, expected, lvl,
                    )
                .is_ok()
            {
                self.emit_lint_with_fix(
                    Lint::RedundantMatchMotive,
                    format!(
                        "this explicit `{}` motive is redundant: the same match checks against its expected type without it",
                        match &e.kind {
                            ExprKind::Match { form, .. } => form.keyword(),
                            _ => unreachable!(),
                        }
                    ),
                    motive.span,
                    Some(LintFix {
                        span: Span { start: scrut.span.end, end: motive.span.end },
                        replacement: String::new(),
                    }),
                );
            }
        }
        // Checking position, so rung 2 has its second source: a bare symbol
        // resolves at the carrier this type's first domain names
        // (docs/bare-symbol-checking-carrier-design.md §3.1). The expected type
        // is already in hand one line above the rewrite, and has been since the
        // operators round — nothing is plumbed from a call site.
        if let Some(rewritten) = self.op_rewrite(cx, e, Some(expected))? {
            return self.elab_check_skel_slots(
                cx,
                &rewritten,
                expected,
                lvl,
                hint,
                skel,
                capture_slots,
            );
        }
        if let ExprKind::App { head, args, named, explicit: false, goal_oriented: false } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "squash")
            && args.len() == 1
            && named.is_empty()
            && !self.shadowed(cx, "squash")
        {
            let head_ty = self.whnf(cx, expected, e.span)?;
            if let Type::Squash { level, ty } = head_ty {
                let payload = self.elab_check(cx, &args[0], &ty, &level)?;
                return Ok(Term::Squash { level, ty, tm: Rc::new(payload) });
            }
        }
        match &e.kind {
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
            ExprKind::Refl if self.shadowed(cx, "refl") => self.elab_check_skel_slots(
                cx,
                &Expr { kind: ExprKind::Var("refl".to_string()), span: e.span },
                expected,
                lvl,
                hint,
                skel,
                capture_slots,
            ),
            ExprKind::ArgSlot(_)
            | ExprKind::Hole(_)
            | ExprKind::Refl
            | ExprKind::AutoRefl => self
                .expr_elab()
                .check_form(self, cx, e, expected, lvl, hint)
                .expect("classified as an ExprElab checking form"),
            // `{ let x = e; … result }` — **checking**-transparent, which is
            // the property that makes the form useful: a block in a `match`
            // arm under a dependent motive is checked at the arm's type rather
            // than inferred and then converted
            // (docs/let-and-blocks-design.md §4.4). The hint travels with it,
            // so a hole in the result of a block in argument position still
            // reports the callee and parameter it belongs to.
            ExprKind::Block(block) => statements::check_block(
                self,
                cx,
                block,
                expected,
                lvl,
                hint,
                skel,
                capture_slots,
            ),
            // A quote against its `Code(g |- T)` type — checking-only, like
            // the kernel's `BoxTm` (docs/in-language-map-design.md §5).
            ExprKind::Quote(payload) => self.elab_quote(cx, payload, expected, e.span),
            ExprKind::Match { form, motive: None, scrut, arms, eqbind, generated } => {
                // Stage-2 motive synthesis (issues/elab-stage2-metas.md,
                // docs/goal-motive-synthesis-design.md): abstract the
                // scrutinee out of the expected type so the motive is
                // genuinely dependent; the non-dependent motive (expected
                // under `z`) is what "no occurrence anywhere" falls back to.
                let (scrut_t, scrut_ty, scrut_lvl) = self
                    .elab_infer(cx, scrut)
                    .map_err(|error| matching::if_resolution_error(*form, scrut, error))?;
                let motive = matching::synthesize_motive(
                    self,
                    cx,
                    &scrut_t,
                    &scrut_ty,
                    &scrut_lvl,
                    expected,
                    e.span,
                );
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
            ExprKind::VecLit(_) => self
                .expr_elab()
                .check_indexed_form(self, cx, e, expected)
                .expect("classified as an ExprElab indexed checking form"),
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
                self.expr_elab()
                    .check_indexed_form(self, cx, e, expected)
                    .expect("classified as an ExprElab indexed checking form")
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
                self.expr_elab().check_unit_form(self, cx, expected, e.span)
            }
            // Private leaves of the Boolean tree. The marker contains a NUL
            // and cannot be written by the surface lexer; it exists only in
            // `arith`'s generated AST. Each candidate is tried transactionally;
            // the selected term becomes part of the completed declaration and
            // therefore crosses its ordinary kernel gate.
            ExprKind::Var(name) if name == arith::BOOLEAN_LEAF => {
                let head = self.whnf(cx, expected, e.span)?;
                if let Type::Id { level, ty, lhs, rhs } = &head
                    && expr::EqualityCheckingElab::goal_endpoints_convert(
                        self, cx, lhs, rhs, ty, level,
                    )
                {
                    self.arith_reports.borrow_mut().push(arith::ArithReport {
                        atoms: 0,
                        adjacent_swaps: 0,
                        boolean_splits: 0,
                        branches: 1,
                        order_reifications: 0,
                        candidate_probes: 0,
                        used_lemmas: Vec::new(),
                    });
                    Ok(Term::Refl {
                        level: level.clone(),
                        ty: Rc::clone(ty),
                        tm: Rc::clone(lhs),
                    })
                } else if let Ok(cert) = arith::reconstruct(self, cx, &head) {
                    let term = self.elab_check(cx, &cert.expr, expected, lvl)?;
                    self.arith_reports.borrow_mut().push(cert.report);
                    Ok(term)
                } else {
                    let direct_failure = match arith::reconstruct_order(self, cx, &head, e.span) {
                        Ok(cert) => {
                            let term = self.elab_check(cx, &cert.expr, expected, lvl)?;
                            self.arith_reports.borrow_mut().push(arith::ArithReport {
                                atoms: 0,
                                adjacent_swaps: 0,
                                boolean_splits: 0,
                                branches: 1,
                                order_reifications: 1,
                                candidate_probes: 0,
                                used_lemmas: vec![cert.lemma],
                            });
                            return Ok(term);
                        }
                        Err(detail) => detail,
                    };
                    let candidates = arith::order_candidates(cx, e.span);
                    let mut selected = None;
                    let mut candidate_probes = 0;
                    for (lemma, candidate) in candidates {
                        candidate_probes += 1;
                        let probe = self.clone();
                        let Ok((_term, got, got_lvl)) = probe.elab_infer(cx, &candidate) else {
                            continue;
                        };
                        // Search needs only decide whether the inferred result
                        // type matches this leaf. Rechecking the complete
                        // theorem application here duplicated the work of the
                        // enclosing declaration gate; conversion is enough to
                        // select a candidate, and the final gate remains the
                        // authority on the selected proof term itself.
                        if &got_lvl != lvl
                            || probe
                                .goal_oracle()
                                .convert_type(&cx.gamma, Layer::Prog, &got, expected, lvl)
                                .is_err()
                        {
                            continue;
                        }
                        selected = Some((lemma, candidate));
                        break;
                    }
                    let Some((lemma, candidate)) = selected else {
                        return err(
                            format!("`arith` exhausted its Boolean leaf candidates: conversion, additive equality, and the structural doubling-order kit all failed\n  direct order reification: {direct_failure}"),
                            e.span,
                        );
                    };
                    let term = self.elab_check(cx, &candidate, expected, lvl)?;
                    self.arith_reports.borrow_mut().push(arith::ArithReport {
                        atoms: 0,
                        adjacent_swaps: 0,
                        boolean_splits: 0,
                        branches: 1,
                        order_reifications: 0,
                        candidate_probes,
                        used_lemmas: vec![lemma],
                    });
                    Ok(term)
                }
            }
            // `arith` is an untrusted, checking-only proof reconstructor. It
            // reads the elaborated goal and produces an ordinary Heather
            // expression from the `Nat` lemma kit; this recursive call takes
            // that expression through the same elaboration and final kernel
            // gate as a handwritten proof. Like every bare special form, a
            // local, declaration, or expected constructor with this name
            // wins (crates/elab/src/arith.rs).
            ExprKind::Var(name)
                if name == "arith"
                    && !self.shadowed(cx, name)
                    && self.ctor_here_expected(cx, name, expected).is_none() =>
            {
                let head = self.whnf(cx, expected, e.span)?;
                if let Type::Id { level, ty, lhs, rhs } = &head
                    && expr::EqualityCheckingElab::goal_endpoints_convert(
                        self, cx, lhs, rhs, ty, level,
                    )
                {
                    self.arith_reports.borrow_mut().push(arith::ArithReport {
                        atoms: 0,
                        adjacent_swaps: 0,
                        boolean_splits: 0,
                        branches: 1,
                        order_reifications: 0,
                        candidate_probes: 0,
                        used_lemmas: Vec::new(),
                    });
                    return Ok(Term::Refl {
                        level: level.clone(),
                        ty: Rc::clone(ty),
                        tm: Rc::clone(lhs),
                    });
                }
                match arith::reconstruct(self, cx, &head) {
                    Ok(cert) => {
                        let term = self.elab_check(cx, &cert.expr, expected, lvl)?;
                        self.arith_reports.borrow_mut().push(cert.report);
                        Ok(term)
                    }
                    Err(direct) => {
                        let split = arith::split_booleans(self, cx, e.span)
                            .map_err(|detail| ElabError::Elab {
                                msg: format!("{direct}\n  Boolean split: {detail}"),
                                span: e.span,
                            })?;
                        let Some(split) = split else {
                            return Err(ElabError::Elab {
                                msg: direct.to_string(),
                                span: e.span,
                            });
                        };
                        let mark = self.arith_reports.borrow().len();
                        let term = self.elab_check(cx, &split.expr, expected, lvl)?;
                        let leaves: Vec<arith::ArithReport> =
                            self.arith_reports.borrow_mut().drain(mark..).collect();
                        let mut used_lemmas = Vec::new();
                        for report in &leaves {
                            for &lemma in &report.used_lemmas {
                                if !used_lemmas.contains(&lemma) {
                                    used_lemmas.push(lemma);
                                }
                            }
                        }
                        self.arith_reports.borrow_mut().push(arith::ArithReport {
                            atoms: leaves.iter().map(|r| r.atoms).sum(),
                            adjacent_swaps: leaves.iter().map(|r| r.adjacent_swaps).sum(),
                            boolean_splits: split.splits,
                            branches: leaves.len(),
                            order_reifications: leaves
                                .iter()
                                .map(|r| r.order_reifications)
                                .sum(),
                            candidate_probes: leaves.iter().map(|r| r.candidate_probes).sum(),
                            used_lemmas,
                        });
                        Ok(term)
                    }
                }
            }
            ExprKind::App { .. }
                if matches!(e.as_named(), Some(("FS", _, false)))
                    && !self.shadowed(cx, "FS")
                    && self.ctor_here_expected(cx, "FS", expected).is_none() =>
            {
                self.expr_elab()
                    .check_indexed_form(self, cx, e, expected)
                    .expect("classified as an ExprElab indexed checking form")
            }
            // A numeral at a `Fin` type is the iterated index (§3.3): `xs[2]`
            // is the spelling anybody reaches for first, and without this it
            // means `xs[FS(FS(FZ))]`. Falls through to the ordinary `Nat`
            // reading at every other expected type.
            ExprKind::Num(t) => match self
                .expr_elab()
                .check_builtin_numeral(cx, *t, expected, e.span)
            {
                Some(result) => result,
                None => self.elab_overloaded_num_check(cx, e, expected, lvl, e.span),
            },
            // A lambda against an expected Π: the *expected* domain is what
            // the binder is pushed with, so the emitted annotation always
            // matches the type it is checked against. A written annotation is
            // a readability aid and must be convertible with it
            // (docs/surface-function-types.md §5.2).
            ExprKind::Lam { binders, body } => {
                self.expr_elab()
                    .check_lambda(self, cx, binders, body, expected, lvl, skel, e.span)
            }
            // A universe as the expected type: a *type* has been written where
            // a term is expected, so read it as one and quote it
            // (docs/surface-universe.md §4).
            _ if matches!(expected, Type::Ty(_)) => {
                let Type::Ty(want) = expected else { unreachable!() };
                self.expr_elab().check_at_universe(self, cx, e, want, e.span)
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
                let (ind, i, args, named) =
                    self.ctor_spine_expected(cx, e, expected).expect("just checked");
                let permuted = application::resolve_constructor_arguments(
                    &ind, i, &args, &named, e.span,
                )?;
                let args = permuted.unwrap_or(args);
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
            ExprKind::Dot { recv, name, args, named } => {
                match self.resolve_dot(cx, recv, name, args, named, e.span)? {
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
                                    let (t, _, _) = application::apply_implicit(
                                        self,
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
                                        false,
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
                                named,
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
                            named,
                            Some(expected),
                            e.span,
                        )?;
                        Ok(t)
                    }
                    DotResolution::Method(m) => {
                        self.elab_check_skel_slots(
                            cx,
                            &m,
                            expected,
                            lvl,
                            hint,
                            skel,
                            capture_slots,
                        )
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
                // type-position reading; the universe bridge still falls
                // through to ordinary inference when the expression is not a
                // type by shape.
                let head = self.whnf(cx, expected, e.span)?;
                if let Type::Ty(want) = &head {
                    return self.expr_elab().check_at_universe(self, cx, e, want, e.span);
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
                let (t, got, _) =
                    self.elab_infer_at(cx, e, if suppress { None } else { Some(&head) })?;
                // The inferred type is *not* thrown away any more
                // (`issues/check-fallback-discards-expected-type.md`): it is
                // compared with what was expected, and a disagreement is
                // recorded for the gate to report at this span. Recorded rather
                // than raised — see [`Self::note_check_mismatch`] — so the
                // elaborator says what it saw without becoming the judge.
                //
                // The cost was measured rather than assumed, because this arm
                // is on every checking path: on the frontend suite the added
                // conversion moves total time by less than the run-to-run noise
                // of the suite itself (the issue's 2026-08-17 log), so the
                // cheap variants the issue proposed — leaves only, whnf'd types
                // only — buy nothing worth the narrowing.
                self.note_check_mismatch(cx, &got, &head, lvl, e.span);
                Ok(t)
            }
        }
    }

    /// Notice what the kernel is going to reject, and where
    /// (`issues/check-fallback-discards-expected-type.md`). Checking that ends
    /// in inference holds an inferred type and used to drop it, so the simplest
    /// type error in the language — a literal at the wrong type — was
    /// discovered by the decl-final gate: at the declaration, with no span and
    /// no types, as a bare `NotConvertible`.
    ///
    /// The kernel stays the judge, and this method does not even raise an error:
    /// it fills [`DeclAttempt::pending_mismatch`], which only the gate reads and only
    /// when the gate itself rejects. `Layer::Prog` against
    /// [`Self::goal_psi`] is [[auto-refl-empty-block]]'s gate, for its reason
    /// (a type mentioning an outstanding goal must still be well-scoped).
    ///
    /// **One outcome is silence rather than an error**, and it is the
    /// difference between reporting and judging: out of fuel is *inconclusive*
    /// — the gate has a fresh budget and may well succeed, and a message about
    /// two types that might yet convert is worse than no message. Only
    /// `NotConvertible`, which is the decided answer, is reported.
    fn note_check_mismatch(
        &self,
        cx: &Cx,
        got: &Type,
        expected: &Type,
        lvl: &Level,
        span: Span,
    ) {
        if self
            .goal_oracle()
            .convert_type(&cx.gamma, Layer::Prog, got, expected, lvl)
            != Err(ConvError::NotConvertible)
        {
            return;
        }
        // **Readable or silent.** This message makes a claim about two types,
        // and a claim the reader cannot check is worse than no claim: below the
        // bar, the gate's crisp `NotConvertible` at the declaration says less
        // but says it honestly. So both types must spell *entirely* in surface
        // — no raw node anywhere — and they must not spell **alike**. The
        // look-alike case is real and is where the display's own limit shows:
        // `And<…>` against `And<…>`, whose type arguments are the whole
        // difference ([[display-inductive-type-arguments]]). Both filters are
        // silence, not error: the declaration is still rejected, by the gate.
        let Some(got_s) = self.display_type_clean(cx, got) else { return };
        let Some(want_s) = self.display_type_clean(cx, expected) else { return };
        if got_s == want_s {
            return;
        }
        // Recorded, not raised: see [`DeclAttempt::pending_mismatch`]. The gate is
        // still the judge, and a more specific diagnostic downstream still
        // wins the message.
        let mut slot = self.attempt.pending_mismatch.borrow_mut();
        if slot.is_none() {
            *slot = Some((
                format!("this has type `{got_s}`, but `{want_s}` is expected here"),
                span,
            ));
        }
    }

    /// Inference mode: returns the elaborated term with its canonical type
    /// and level.
    fn elab_infer(&self, cx: &Cx, e: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer_at(cx, e, None)
    }

    fn elab_squash_ind(
        &self,
        cx: &Cx,
        scrut: &Expr,
        motive: &Expr,
        case: &Expr,
    ) -> R<(Term, Type, Level)> {
        let (mbinders, mbody) = matching::motive_lam(
            motive,
            1,
            "write `squash_ind(q, λ z => B, λ x => b)`",
        )?;
        let (scrut_t, scrut_ty, _) = self.elab_infer(cx, scrut)?;
        let head = self.whnf(cx, &scrut_ty, scrut.span)?;
        let squash_ty = head.clone();
        let Type::Squash { level: src_level, ty: src_ty } = head else {
            return err("`squash_ind` needs a scrutinee of type `∥A∥`", scrut.span);
        };
        let mut mcx = cx.clone();
        mcx.push(mbinders[0].clone(), squash_ty, src_level.clone());
        let (motive_t, dst_level) = self.elab_ty(&mcx, &mbody)?;

        let ExprKind::Lam { binders, body } = &case.kind else {
            return err("the `squash_ind` case is a lambda: write `λ x => b`", case.span);
        };
        if binders.len() != 1 || binders[0].ty.is_some() {
            return err(
                "the `squash_ind` case binds one unannotated witness: `λ x => b`",
                case.span,
            );
        }
        let mut bcx = cx.clone();
        bcx.push(binders[0].name.clone(), (*src_ty).clone(), src_level.clone());
        let packed = Rc::new(Term::Squash {
            level: src_level.clone(),
            ty: Rc::new(src_ty.shift_local(1)),
            tm: Rc::new(Term::Var(LocalVar(0))),
        });
        let inner = motive_t.apply_local(
            &LocalSubst::id(&cx.gamma).shift_local(1).extended(packed),
        );
        let branch_ty = Type::Squash { level: dst_level.clone(), ty: Rc::new(inner) };
        let case_t = self.elab_check(&bcx, body, &branch_ty, &dst_level)?;
        let scrut_t = Rc::new(scrut_t);
        let result_inner = motive_t.apply_local(
            &LocalSubst::id(&cx.gamma).extended(Rc::clone(&scrut_t)),
        );
        let result = Type::Squash { level: dst_level.clone(), ty: Rc::new(result_inner) };
        Ok((
            Term::ElimSquash {
                src_level,
                dst_level: dst_level.clone(),
                src_ty,
                motive: Rc::new(motive_t),
                case: Rc::new(case_t),
                scrut: scrut_t,
            },
            result,
            dst_level,
        ))
    }

    /// [`Self::elab_infer`] plus, when the caller is in **checking** position
    /// and inference is the fallback, the expected type it would otherwise
    /// discard (already whnf'd).
    ///
    /// One consumer: [`application::apply_implicit`], which uses it to solve
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
        if let ExprKind::App { head, args, named, explicit: false, goal_oriented: false } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "squash")
            && args.len() == 1
            && named.is_empty()
            && !self.shadowed(cx, "squash")
        {
            let (tm, ty, level) = self.elab_infer(cx, &args[0])?;
            return Ok((
                Term::Squash {
                    level: level.clone(),
                    ty: Rc::new(ty.clone()),
                    tm: Rc::new(tm),
                },
                Type::Squash { level: level.clone(), ty: Rc::new(ty) },
                level,
            ));
        }
        if let ExprKind::App { head, args, named, explicit: false, goal_oriented: false } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "squash_ind")
            && args.len() == 3
            && named.is_empty()
            && !self.shadowed(cx, "squash_ind")
        {
            return self.elab_squash_ind(cx, &args[0], &args[1], &args[2]);
        }
        match &e.kind {
            ExprKind::ArgSlot(_)
            | ExprKind::Univ { .. }
            | ExprKind::Hole(_)
            | ExprKind::Num(_)
            | ExprKind::Eq(..)
            | ExprKind::TyLit(..)
            | ExprKind::VecLit(_) => self
                .expr_elab()
                .infer_form(self, cx, e)
                .expect("classified as an ExprElab inference form"),
            // `{ let x = e; … result }` — the block's statements extend a
            // clone of `cx`, and its result is inferred there
            // (docs/let-and-blocks-design.md §4.4). Inference-transparent:
            // the block contributes no term of its own, because a `let` is an
            // alias.
            ExprKind::Block(block) => statements::infer_block(self, cx, block),
            // Intensional analysis: the result type is written, so unlike a
            // quote this one *infers*
            // (docs/certgen-transcriber-in-language-design.md §3).
            ExprKind::MatchCode { scrut, motive, arms } => {
                self.elab_match_code(cx, scrut, motive, arms, e.span)
            }
            // `FZ` cannot infer: it inhabits `Fin(Succ k)` for every `k`
            // (docs/surface-fin-indexing-design.md §3.1). Said only where the
            // name is neither shadowed nor some declaration's constructor.
            ExprKind::Var(name)
                if name == "FZ"
                    && !self.shadowed(cx, name)
                    && self.ctor_here(cx, name).is_none() =>
            {
                self.expr_elab()
                    .infer_form(self, cx, e)
                    .expect("classified as an ExprElab inference form")
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
                self.expr_elab()
                    .infer_form(self, cx, e)
                    .expect("classified as an ExprElab inference form")
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
                        return application::apply_implicit(
                            self,
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
                            false,
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
                        return application::apply_implicit(
                            self,
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
                            false,
                            e.span,
                        );
                    }
                }
                self.resolve(cx, name, e.span)
            }
            // `xs[i]` — infers, since the element type comes off the receiver
            // (docs/surface-fin-indexing-design.md §5.2).
            ExprKind::Index { recv, idx } => vec::elab_nth(self, cx, recv, idx, e.span),
            ExprKind::Dot { recv, name, args, named } => {
                match self.resolve_dot(cx, recv, name, args, named, e.span)? {
                    DotResolution::Project(t, ty, l, fskel) => match args {
                        None => Ok((t, ty, l)),
                        Some(args) => self.apply_projection(
                            cx, name, t, ty, l, fskel, args, named, expected, e.span,
                        ),
                    },
                    DotResolution::Dispatch(t, ty, l, fskel, dargs) => self.apply_projection(
                        cx, name, t, ty, l, fskel, &dargs, named, expected, e.span,
                    ),
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
            // A lambda in inference position needs every binder annotated:
            // with no expected type there is nothing else to take the domain
            // from (docs/surface-function-types.md §5.2).
            ExprKind::Lam { binders, body } => self.expr_elab().infer_lambda(
                self,
                cx,
                binders,
                body,
                expr::LambdaInferenceMode::Ordinary,
            ),
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
                    return application::apply_implicit(
                        self,
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
                        false,
                        e.span,
                    );
                }
                Ok((t, ty, lvl))
            }
            // `f<T, …>(a, b)` and `@f<T, …>(a, b)`. The type arguments are
            // applied first; what happens to the remaining `{}`-implicits is
            // `@`'s business and not `<…>`'s — the two are orthogonal knobs
            // (issues/at-and-type-arguments.md).
            ExprKind::App { head, args, named, explicit, goal_oriented }
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
                if let ExprKind::Var(cn) = &callee.kind
                    && let Some((ind, ci)) = self.ctor_here(cx, cn)
                {
                    let permuted = application::resolve_constructor_arguments(
                        &ind, ci, args, named, e.span,
                    )?;
                    let args = permuted.as_deref().unwrap_or(args);
                    if let Some(r) = self.ctor_at(cx, callee, tyargs, args, e.span) {
                        return r;
                    }
                } else if let Some(r) = self.ctor_at(cx, callee, tyargs, args, e.span) {
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
                    recursion::check_self_tyargs(cx, tyargs, head.span)?;
                    application::refuse_named(
                        &format!("a recursive call to `{n}`"),
                        "the termination guard reads *which position* decreases, so a                          self-call's arguments stay where the declaration put them",
                        named,
                    )?;
                    return recursion::elab_self_call(self, cx, args, *explicit, e.span);
                }
                let (name, t, ty, lvl, mask) =
                    self.elab_ty_app(cx, callee, tyargs, head.span)?;
                let params = self.params_of(&name);
                let flat;
                let full = if !*explicit && mask.iter().any(|&b| b) {
                    &mask[..]
                } else {
                    flat = vec![false; mask.len()];
                    &flat[..]
                };
                let r = application::resolve_named(
                    &name, false, &params, tyargs.len(), full, args, named, e.span,
                )?;
                let (args, mask): (&[Expr], &[bool]) = match &r {
                    Some((a, m)) => (&a[..], &m[..]),
                    None => (&args[..], &mask[..]),
                };
                if !*explicit && mask.iter().any(|&b| b) {
                    application::apply_implicit(
                        self,
                        cx,
                        &name,
                        Rc::clone(&params),
                        false,
                        tyargs.len(),
                        false,
                        t,
                        ty,
                        lvl,
                        args,
                        mask,
                        expected,
                        *goal_oriented,
                        e.span,
                    )
                } else {
                    // The type arguments have consumed the leading parameters,
                    // so argument `i` is now parameter `i + |tyargs|` — which
                    // is what the offset keeps honest for goal-name hints.
                    application::apply_explicit(
                        self,
                        cx,
                        Some(&name),
                        params,
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
                let (ind, i, args, named) = self.ctor_spine(cx, e).expect("just checked");
                let permuted = application::resolve_constructor_arguments(
                    &ind, i, &args, &named, e.span,
                )?;
                let args = permuted.unwrap_or(args);
                self.infer_ctor(cx, &ind, i, &args, e.span)
            }
            // An application whose head is *not* a name: no parameter
            // metadata exists for it, so it is always explicit.
            ExprKind::App { head, args, named, explicit, .. } if e.as_named().is_none() => {
                application::refuse_named(
                    "a call whose head is an expression",
                    "named arguments need a callee whose parameters have names, and only a                      *name* has a parameter table here (docs/named-arguments-design.md §7)",
                    named,
                )?;
                if *explicit {
                    return err(
                        "`@` suppresses implicit-argument insertion, which only applies \
                         to a named callee",
                        e.span,
                    );
                }
                let (h, hty, hlvl) = self.elab_infer(cx, head)?;
                application::apply_explicit(
                    self,
                    cx,
                    None,
                    Rc::new(Vec::new()),
                    0,
                    h,
                    hty,
                    hlvl,
                    args,
                )
            }
            ExprKind::App { args, named, explicit, goal_oriented, .. } => {
                let (name, _, _) = e.as_named().expect("head is a name");
                let name = &name.to_string();
                // Named arguments (docs/named-arguments-design.md §8.2). Only
                // four of this arm's paths have a parameter table — a
                // constructor, a value head, a global, and the self-call — and
                // everything else in it is a *builtin*: an elaborator form
                // rather than a declaration, with no names to be called by.
                // The test is `shadowed`'s own, which is exactly the guard
                // every builtin arm below already carries, so the two cannot
                // drift apart.
                if !named.is_empty() {
                    if cx.selfref.as_ref().is_some_and(|s| s.name == *name) {
                        return err(
                            format!(
                                "a recursive call to `{name}` takes positional arguments only:                                  the termination guard reads *which position* decreases, so a                                  self-call's arguments stay where the declaration put them"
                            ),
                            named[0].name_span,
                        );
                    }
                    if !self.shadowed(cx, name) && self.ctor_here(cx, name).is_none() {
                        return err(
                            format!(
                                "`{name}` is a built-in form rather than a declaration, so it                                  has no parameter names: write its arguments positionally"
                            ),
                            named[0].name_span,
                        );
                    }
                }
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
                        return vec::method_arity_error(self, cx, args, name, "`(f)`", e.span);
                    };
                    return vec::elab_map(self, cx, f, xs, e.span);
                }
                // `head(v)` / `tail(v)` / `cons(h, t)` — the vector at a
                // successor length *is* a `Σ` (`Vec` computes on its length),
                // so these are its projections and pairing, annotated from
                // the receiver's element type (docs/in-language-map-design.md
                // — the payload of the first in-language artifact is what
                // wanted spellings for them).
                if (name == "head" || name == "tail") && !self.shadowed(cx, name) {
                    let [v] = args.as_slice() else {
                        return vec::method_arity_error(
                            self, cx, args, name, "no arguments", e.span,
                        );
                    };
                    return vec::elab_head_tail(self, cx, v, name == "head", e.span);
                }
                if name == "cons" && !self.shadowed(cx, name) {
                    let [h, t] = args.as_slice() else {
                        return err("`cons` takes `(head, tail)`", e.span);
                    };
                    return vec::elab_cons(self, cx, h, t, e.span);
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
                    // Decoded, as in `vec::elab_map`: a coded `Vec` is one.
                    if !matches!(*crate::inductive::decoded(&xs_ty), Type::Vec { .. }) {
                        return err("`cong`'s receiver has to be a vector", e.span);
                    }
                    return vec::elab_container_ih(self, cx, f_name, &xs_t, true, e.span);
                }
                if name == "fold" && !self.shadowed(cx, name) {
                    let [xs, z, f] = args.as_slice() else {
                        return vec::method_arity_error(
                            self, cx, args, name, "`(init, f)`", e.span,
                        );
                    };
                    return vec::elab_fold(self, cx, z, f, xs, e.span);
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
                    let permuted = application::resolve_constructor_arguments(
                        &ind, i, args, named, e.span,
                    )?;
                    let args = permuted.as_deref().unwrap_or(args);
                    return self.infer_ctor(cx, &ind, i, args, e.span);
                }
                if cx.selfref.as_ref().is_some_and(|s| s.name == *name) {
                    return recursion::elab_self_call(self, cx, args, *explicit, e.span);
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
                        let flat = vec![false; params.len()];
                        let r = application::resolve_named(
                            name, true, &params, 0, &flat, args, named, e.span,
                        )?;
                        let args: &[Expr] = r.as_ref().map_or(&args[..], |(a, _)| &a[..]);
                        return application::apply_explicit(
                            self,
                            cx,
                            Some(name),
                            params,
                            0,
                            head,
                            ty,
                            lvl,
                            args,
                        );
                    };
                    let mask: Vec<bool> = skel.params.iter().map(|b| b.implicit).collect();
                    let r = application::resolve_named(
                        name, true, &params, 0, &mask, args, named, e.span,
                    )?;
                    let (args, mask): (&[Expr], &[bool]) = match &r {
                        Some((a, m)) => (&a[..], &m[..]),
                        None => (&args[..], &mask[..]),
                    };
                    return application::apply_implicit(
                        self,
                        cx, name, params, true, 0, false, head, ty, lvl, args, mask,
                        expected, *goal_oriented, e.span,
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
                let params = self.params_of(name);
                // The named arguments are permuted into declaration order and
                // the mask is adjusted here, once, so both walkers below see
                // the positional call they have always seen (§8.3).
                let r = application::resolve_named(
                    name, false, &params, 0, &mask, args, named, e.span,
                )?;
                let (args, mask): (&[Expr], &[bool]) = match &r {
                    Some((a, m)) => (&a[..], &m[..]),
                    None => (&args[..], &mask[..]),
                };
                if !mask.iter().any(|&b| b) {
                    application::apply_explicit(
                        self,
                        cx,
                        Some(name),
                        params,
                        0,
                        head,
                        ty,
                        lvl,
                        args,
                    )
                } else {
                    application::apply_implicit(
                        self,
                        cx, name, params, false, 0, false, head, ty, lvl, args, mask, expected,
                        *goal_oriented, e.span,
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
                    let (binders, body) = matching::motive_lam(
                        m,
                        2,
                        "write `as \u{3bb} n z => T` (index, then value)",
                    )?;
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
                        cx, *form, *generated, arms, &scrut_t, &scrut_ty, &scrut_lvl, &result,
                        indep, &mlvl, e.span,
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
                    let (binders, body) = matching::motive_lam(
                        m,
                        2,
                        "write `as \u{3bb} n z => T` (index, then value)",
                    )?;
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
                        cx, *form, *generated, arms, &scrut_t, &scrut_ty, &scrut_lvl, &result,
                        indep, &mlvl, e.span,
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
                let (binders, body) =
                    matching::motive_lam(m, 1, "write `as \u{3bb} z => T`")?;
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
                if *form == MatchForm::If {
                    match matching::infer_if_constant_motive(
                        self, cx, scrut, arms, *generated, e.span,
                    ) {
                        matching::MotiveInference::Accepted(result) => return Ok(result),
                        matching::MotiveInference::Failed(error) => return Err(error),
                        matching::MotiveInference::Declined => {}
                    }
                }
                match matching::infer_match_constant_motive(
                    self, cx, *form, scrut, arms, *generated, e.span,
                ) {
                    matching::MotiveInference::Accepted(result) => return Ok(result),
                    matching::MotiveInference::Failed(error) => return Err(error),
                    matching::MotiveInference::Declined => {}
                }
                err(
                    format!(
                        "`{}` in inference position needs a motive: `{}`",
                        form.keyword(),
                        match form {
                            MatchForm::Match => "match e as \u{3bb} z => T { … }",
                            MatchForm::Split => "split e as \u{3bb} z => T;",
                            MatchForm::If => "give the `if` an expected result type, for \
                                              example with an annotated `let`",
                            MatchForm::IfLet => "give the `if let` an expected result type, for \
                                                 example with an annotated `let`",
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
                        MatchForm::If => "give the `if` an expected result type, for \
                                          example with an annotated `let`",
                        MatchForm::IfLet => "give the `if let` an expected result type, for \
                                             example with an annotated `let`",
                    }
                ),
                e.span,
            ),
            ExprKind::J { proof, motive, case } => {
                let (mbinders, mbody) = matching::motive_lam(
                    motive,
                    2,
                    "write `j(p, \u{3bb} y q => T, case)`",
                )?;
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
            ExprKind::OpSymbol { symbol: s, .. } => {
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
        let plan = matching::plan_convoy(
            h,
            arms,
            &scrut_t,
            scrut_ty,
            scrut_lvl,
            &motive,
            mlvl,
        );
        let elim = self.elab_match(
            cx,
            form,
            generated,
            &plan.arms,
            scrut_t.clone(),
            scrut_ty,
            scrut_lvl,
            plan.motive,
            plan.level,
            span,
        )?;
        Ok(matching::finish_convoy(
            elim,
            scrut_t,
            scrut_ty,
            scrut_lvl,
            mlvl,
            result,
        ))
    }

    /// A numeral at a user-defined carrier. Core `Nat` and `Fin` readings are
    /// already settled by `ExprElab`; this is declaration/class policy only.
    fn elab_overloaded_num_check(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
        expected_level: &Level,
        span: Span,
    ) -> R<Term> {
        // At another expected carrier, use the ordinary class resolver. The
        // class is optional at the language level: a program that has not
        // imported the standard algebra module keeps the historical Nat-only
        // mismatch below. Once `Numeral` is visible, however, a missing
        // instance is the useful diagnosis and not a later Nat-vs-carrier
        // conversion error.
        if let Some(class) = self.lookup_class("Numeral")
            && class.params.len() == 1
            && class.valparams.is_empty()
            && let Some(ind) = self.lookup_inductive(&class.name).cloned()
            && let Some(field) = ind.field_index("ofNat")
        {
            let targs = [(expected.clone(), expected_level.clone())];
            let (goal, goal_level) = self.lower_instance(cx, &ind, &targs, &[], span)?;
            let carrier = self
                .type_namespace(cx, expected, span)
                .unwrap_or_else(|| "the expected type".to_string());
            let display = format!("Numeral<{carrier}>");
            let mut trace = Vec::new();
            let Some(dict) = self.resolve_goal(
                cx,
                &goal,
                &goal_level,
                &display,
                span,
                &mut trace,
            ) else {
                return Err(ElabError::Resolution { goal: display, span, trace });
            };
            let (embed, embed_ty, embed_level) =
                self.project_field(cx, &ind, &goal, Rc::new(dict), field, span)?;
            let (out, _, _) = application::apply_explicit(
                self,
                cx,
                Some("ofNat"),
                Rc::new(Vec::new()),
                0,
                embed,
                embed_ty,
                embed_level,
                std::slice::from_ref(e),
            )?;
            return Ok(out);
        }
        // A numeral is the leaf case of
        // `issues/check-fallback-discards-expected-type.md`: its inferred type
        // is `Nat` without any work at all, so comparing costs one conversion
        // against a type the caller already had.
        let (num, num_ty, _) = self.elab_infer(cx, e)?;
        self.note_check_mismatch(cx, &num_ty, expected, &Level::Zero, span);
        Ok(num)
    }

    /// A local variable by absolute position (outermost first), as
    /// [`Self::resolve`] would return it.
    fn local(&self, cx: &Cx, pos: usize) -> (Term, Type, Level) {
        let idx = (cx.names.len() - 1 - pos) as u32;
        let entry = &cx.gamma.entries[pos];
        (Term::Var(LocalVar(idx)), entry.ty.shift_local(idx + 1), entry.level.clone())
    }


    fn operator_fallback_note(&self) -> Option<String> {
        let notes = self.attempt.op_fallback_notes.borrow();
        (!notes.is_empty()).then(|| notes.join("; "))
    }

    /// The gate's rejection, said as well as it can be said
    /// (`issues/check-fallback-discards-expected-type.md`). A bare
    /// `NotConvertible` at the declaration is what this exists to avoid: when
    /// checking noticed *which* expression disagreed and could state both
    /// types, that report replaces the kernel one — same rejection, at a span,
    /// with the types. Any other `TypeError` keeps the kernel's own report,
    /// because this slot has no claim about it.
    ///
    /// The operator note travels either way: it explains a designation that was
    /// resolved by fallback, which is as relevant to the precise message as to
    /// the bare one.
    fn kernel_error(&self, decl: &str, span: Span, e: TypeError) -> ElabError {
        if e == TypeError::NotConvertible
            && let Some((msg, at)) = self.attempt.pending_mismatch.borrow().clone()
        {
            let msg = match self.operator_fallback_note() {
                Some(note) => format!("{msg} (note: {note})"),
                None => msg,
            };
            return ElabError::Elab { msg, span: at };
        }
        ElabError::Kernel {
            decl: decl.to_string(),
            span,
            err: e,
            note: self.operator_fallback_note(),
        }
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
        named: &[NamedArg],
        expected: Option<&Type>,
        span: Span,
    ) -> R<(Term, Type, Level)> {
        match fskel {
            Some(skel) if skel.params.iter().any(|b| b.implicit) => {
                let mask: Vec<bool> = skel.params.iter().map(|b| b.implicit).collect();
                let params = skel_params(&skel);
                let r = application::resolve_named(
                    name, true, &params, 0, &mask, args, named, span,
                )?;
                let (args, mask): (&[Expr], &[bool]) = match &r {
                    Some((a, m)) => (&a[..], &m[..]),
                    None => (args, &mask[..]),
                };
                application::apply_implicit(
                    self,
                    cx, name, params, true, 0, false, t, ty, lvl, args, mask, expected, false,
                    span,
                )
            }
            Some(skel) => {
                let params = skel_params(&skel);
                let flat = vec![false; params.len()];
                let r = application::resolve_named(
                    name, true, &params, 0, &flat, args, named, span,
                )?;
                let args = r.as_ref().map_or(args, |(a, _)| &a[..]);
                application::apply_explicit(
                    self,
                    cx,
                    Some(name),
                    params,
                    0,
                    t,
                    ty,
                    lvl,
                    args,
                )
            }
            None => {
                application::refuse_named(
                    &format!("`{name}`"),
                    "its type binds no parameter names, so its arguments are positional                      (docs/named-arguments-design.md §7)",
                    named,
                )?;
                application::apply_explicit(
                    self,
                    cx,
                    None,
                    Rc::new(Vec::new()),
                    0,
                    t,
                    ty,
                    lvl,
                    args,
                )
            }
        }
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
            ExprKind::OpSymbol { symbol: sym, fixity } => {
                self.symbol_needs_a_carrier(cx, sym, *fixity)
            }
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
                // A call with a **result-only implicit**
                // ([`Self::call_defers_for_result_only`]): the semantic member
                // of this set, and the only one that can still elaborate if
                // deferral does not pay off — which is why it, alone, carries
                // the inference fallback in [`application::apply_implicit`].
                Some((n, args, false)) => {
                    self.call_defers_for_result_only(cx, n, args.len())
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Was this argument deferred by the **result-only implicit** rule — the
    /// one member of [`Self::is_checking_only`] that can still be elaborated
    /// in inference mode? See [`DeferredArg::fallback_infer`].
    fn deferral_can_fall_back(&self, cx: &Cx, e: &Expr) -> bool {
        match e.as_named() {
            Some(("absurd", _, _)) | Some(("FS", _, false)) => false,
            Some((n, args, false)) => self.call_defers_for_result_only(cx, n, args.len()),
            _ => false,
        }
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
    /// Read implicit solutions off an argument's type
    /// (docs/argument-type-reduction-design.md): the syntactic read first,
    /// and — only when it learned *nothing* — the same read against the
    /// type's weak head normal form.
    ///
    /// The retry is for an argument whose type is a **motive applied**. An
    /// induction principle with a value-parameter motive (`int_ind`'s `P: Int
    /// -> Type`) binds its hypothesis at `P(OfNat(k))`, which after `P` is
    /// given is a β-redex `(λ (z: Int) => add(a, z) = add(z, a))(OfNat(k))` —
    /// an `Id` that does not say so yet, so `cong_int(isucc, ih)` and
    /// `sym(ih)` both refused (issues/motive-application-hides-hypothesis-
    /// type.md). Reducing makes the evidence readable, and it is the same
    /// sentence [`Self::solve_from_expected`] already applies to the *expected*
    /// type one screen below.
    ///
    /// Three properties keep it from being a widening:
    ///
    ///  - **learn-only, twice.** [`unify_ty`] records into `Unsolved` slots and
    ///    never fails, so the retry can add solutions and cannot retract or
    ///    contradict one. A wrong solution is still a kernel rejection.
    ///  - **no progress is the trigger**, not "something is still unsolved":
    ///    an argument whose type taught anything at all takes exactly the path
    ///    it took before this existed, so no call that already elaborated
    ///    reaches the reduction.
    ///  - **the reduction is opportunistic.** Out of fuel is not an error here:
    ///    the honest outcome is the caller's own per-slot message about the
    ///    implicit it could not infer, not a complaint about a type the writer
    ///    never asked to reduce.
    fn unify_arg_ty(
        &self,
        cx: &Cx,
        dom: &Type,
        arg_ty: &Type,
        n: u32,
        sols: &mut [Sol],
        span: Span,
    ) {
        let learned = |sols: &[Sol]| sols.iter().filter(|s| s.solved().is_some()).count();
        let before = learned(sols);
        unify_ty(&cx.gamma, dom, arg_ty, n, 0, sols);
        if learned(sols) != before || !sols.iter().any(|s| matches!(s, Sol::Unsolved)) {
            return;
        }
        if let Ok(head) = self.whnf(cx, arg_ty, span) {
            unify_ty(&cx.gamma, dom, &head, n, 0, sols);
        }
    }

    /// Expected-type-directed solving (docs/unifier-completeness-design.md
    /// §5): the expected type, consulted for the implicits an argument's type
    /// cannot reach. Called from [`application::apply_implicit`] with the call's
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
        // Two attempts, in this order, and no more
        // (docs/congruence-in-inference-position-design.md §3).
        //
        // 1. The endpoints **as written**. This is the whole of decision 2 as
        //    it landed, and it stays first so that no goal that generalized
        //    before now generalizes differently: reducing can only destroy a
        //    match (`f(a) = f(b)` at a transparent `f` unfolds into two
        //    unrelated-looking bodies), so a syntactic success is never
        //    thrown away for a reduced one.
        // 2. The endpoints in **weak head normal form**, once each. This is a
        //    deliberate, bounded loosening of "exactly `(s, t)` is `==`": the
        //    *witness* comparison is still syntactic, and still `==` — what
        //    reduces is the goal, and only its two outermost nodes.
        //
        // Why the second attempt exists at all: a library statement is
        // written in the reader's terms, not the elaborator's.
        // `mul(OfNat(m), OfNat(n)) = mul(OfNat(n), OfNat(m))` names no
        // congruence context anywhere in its syntax; one whnf apiece turns
        // both sides into `OfNat(…)` and the context is `OfNat(□)`. Without
        // this the rule fires only at goals that were *already* spelled
        // through the function being abstracted, which is the minority of
        // them (issues/congruence-by-anti-unification.md, 2026-08-18).
        //
        // Why *only* the goal and not `s`/`t`: the witnesses come from the
        // proof's type and the goal's payload comes from the statement, and
        // both are written in the same unreduced terms. Reducing one side of
        // that comparison and not the other is what would break the match.
        //
        // Why whnf and not conversion: an unbounded `conv` call per `cong`
        // is the memory-superlinear hazard this project keeps out of the
        // elaborator, and it would also make failure quiet. Two whnfs are
        // linear and terminating, which is the property §3 of the issue
        // claims for this solver.
        let body = match lgg::lgg_body(&x, &y, &s, &t) {
            Ok(body) => body,
            Err(m) => {
                let rx = self.whnf_tm(cx, &x, span)?;
                let ry = self.whnf_tm(cx, &y, span)?;
                if *rx == *x && *ry == *y {
                    let msg = self.cong_mismatch(cx, &m, expected, &s, &t);
                    return Err(ElabError::Elab { msg, span });
                }
                lgg::lgg_body(&rx, &ry, &s, &t).map_err(|m| ElabError::Elab {
                    msg: self.cong_mismatch(cx, &m, expected, &s, &t),
                    span,
                })?
            }
        };
        sols[m] = Sol::Solved(Rc::new(Term::Lam {
            dom_level,
            cod_level,
            dom,
            body: Rc::new(body),
        }));
        Ok(())
    }

    /// The `cannot generalize` message
    /// (issues/lgg-diagnostic-dumps-kernel-terms.md).
    ///
    /// The solver reports a *position* and this reads it out: the goal as
    /// surface, the proof's endpoints as surface, and the two sides at the
    /// stopping node where they can be read in the goal's own context. What it
    /// deliberately never does is print a kernel term — at a lowered inductive
    /// that was four multi-thousand-character walls, and the useful fact was
    /// not recoverable from any of them.
    ///
    /// Every spelling is optional and its absence costs a clause, not the
    /// message: `spell_*` declines rather than half-spelling
    /// (`docs/surface-type-display-design.md` §2), and the position — which is
    /// the part the reader could not get before — needs no context at all.
    fn cong_mismatch(
        &self,
        cx: &Cx,
        m: &lgg::Mismatch,
        expected: &Type,
        s: &Term,
        t: &Term,
    ) -> String {
        let mut msg = m.to_string();
        // The two sides at the stopping node, when the walk stopped somewhere
        // that mentions none of the binders it descended under. A subterm that
        // *does* mention them has no reading in `cx` at all, and inventing one
        // would name the reader's variables wrongly — so the formers, already
        // in `m`'s own sentence, are the whole of what is said about it.
        if let Some((a, b)) = &m.at
            && let (Some(a), Some(b)) = (
                strengthen_tm(&cx.gamma, a, m.depth),
                strengthen_tm(&cx.gamma, b, m.depth),
            )
            && let (Some(a), Some(b)) =
                (self.spell_term_clean(cx, &a), self.spell_term_clean(cx, &b))
        {
            msg.push_str(&format!(" (`{a}` against `{b}`)"));
        }
        // *Clean* spellings throughout: every clause here makes a claim about
        // a term, and a half-spelled one is the kernel wall wearing surface
        // syntax (`issues/check-fallback-discards-expected-type.md`). A clause
        // that cannot be said cleanly is not said.
        if let Some(goal) = self.spell_type_clean(cx, expected) {
            msg.push_str(&format!(". The goal is `{goal}`"));
        } else {
            msg.push('.');
        }
        match (self.spell_term_clean(cx, s), self.spell_term_clean(cx, t)) {
            (Some(s), Some(t)) => {
                msg.push_str(&format!(", and the proof's endpoints are `{s}` and `{t}`"));
            }
            _ => msg.push_str(", and the proof's endpoints do not spell as surface"),
        }
        msg.push_str(
            " — every differing position has to be exactly the proof's endpoints \
             (issues/congruence-by-anti-unification.md §3)",
        );
        msg
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
        let resolved_global = self
            .key_of(self.instance_alias(name))
            .and_then(|key| self.names.global(&key).map(|info| (key, info)));
        match resolved_global {
            Some((key, GlobalInfo { abs, .. })) => {
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
                let var = GlobalVar(
                    len - 1 - abs + self.attempt.goal_arena.base() + meta_off,
                );
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
                self.attempt.direct_dependencies.borrow_mut().insert(key);
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

    /// Semantic operations in the expression world's δ context, including
    /// any dynamic meta binders currently in scope.
    fn semantic_oracle(&self) -> oracle::SemanticOracle {
        oracle::SemanticOracle::with_dynamic(
            &self.delta_psi,
            &self.meta_pushed.borrow(),
            self.fuel,
        )
    }

    /// Semantic operations in the real goal-statement world.
    fn goal_oracle(&self) -> oracle::SemanticOracle {
        oracle::SemanticOracle::in_world(self.goal_psi(), self.fuel)
    }

    /// Semantic operations over committed Ψ, with no declaration padding.
    fn committed_oracle(&self) -> oracle::SemanticOracle {
        oracle::SemanticOracle::in_world(self.psi.clone(), self.fuel)
    }

    /// The capabilities currently admitted to expression elaboration.
    fn expr_elab(&self) -> expr::ExprElab<'_> {
        expr::ExprElab::new(
            self.semantic_oracle(),
            self.attempt.goal_arena.allocator(),
            &self.attempt.slot_probe_target,
        )
    }

    /// [`Self::whnf`] for a term: δ against Ψ included, so a definition
    /// unfolds. Used where a *shape* has to be read off a computed term.
    pub(crate) fn whnf_tm(&self, cx: &Cx, t: &Term, span: Span) -> R<Rc<Term>> {
        self.expr_elab()
            .whnf_term(cx, t)
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
        self.expr_elab()
            .whnf_type(cx, ty)
            .map_err(|_| ElabError::Elab { msg: "out of fuel reducing a type".into(), span })
    }

    /// Rebuild [`Self::delta_psi`]. Called wherever Ψ or `goal_base` moves.
    fn refresh_delta_psi(&mut self) {
        if self.attempt.goal_arena.base() == 0 {
            self.delta_psi = self.psi.clone();
            return;
        }
        let mut bindings = (*self.psi.bindings).clone();
        bindings.resize(
            bindings.len() + self.attempt.goal_arena.base() as usize,
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
