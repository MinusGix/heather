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
use std::ops::{Deref, DerefMut};
use std::sync::Arc as Rc;

use heather_kernel::conv::ConvError;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::subst::GlobalSubst;
use heather_kernel::term::{
    GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type,
};
use heather_kernel::typing::{self, DEFAULT_FUEL, TypeError};
use heather_kernel::value::{ValueMetrics, ValueMetricsSnapshot};
use heather_syntax::{
    Arm, Decl, DeclKind, Expr, ExprKind, InstanceDecl, Item, LamBinder, MatchForm, NamedArg,
    OnStmt, OnTarget, ParseError, Ty, TyKind, parse_file,
};

mod access;
mod application;
pub mod arithmetic;
mod attempt;
mod binding;
mod alpha;
mod loops;
mod partial;
pub mod cutsat;
mod cutsat_cert;
pub mod omega;
mod omega_cert;
mod bv_omega;
mod ring;
mod linarith;
mod rewrite;
mod subst_local;
pub use omega_cert::{CutSatReport, OmegaPhases, OmegaReport, OmegaResidualConstraint};
pub mod function_ir_cert;
pub mod function_ir_source;
mod code;
mod codata;
mod constructor;
mod context;
mod spine;
mod defaults;
mod datarepr;
mod diagnostics;
mod dispatch;
mod display;
mod expr;
pub mod gate;
pub mod heather_emit;
pub mod relational_context;
pub mod stats;
pub use datarepr::{Obligation, Provenance};
mod layered;
mod names;
mod oracle;
mod readback;
mod patterns;
mod pool;
mod provenance;
pub mod reprgen;
pub use provenance::{AssumptionKind, AxiomReport, AxiomUse};
mod emission_walk;
pub use emission_walk::EmissionFinding;
mod iwf_confusion;
mod iwf_family;
mod iwf_w;
mod gendefs;
mod generalize;
mod goal_combinators;
mod goals;
pub mod host;
mod indexed;
mod interfaces;
mod infinitary;
mod inductive;
mod spelling;
mod sum_layout;
mod lgg;
mod solution_check;
mod lint;
mod lifetimes;
mod literals;
pub use lint::{Lint, LintProfile};
mod matching;
mod measure;
mod meaning;
mod measure_context;
mod metaprograms;
mod mutual_family;
mod mutual_rec;
mod module_delta;
mod module_image;
mod module_relocate;
pub use module_relocate::{NameObservations, NameWorld, RegistryPart, RelocationRefusal, RelocationTarget, WorldHasher, source_identifiers};
pub use names::{record_name_lookups, take_name_lookups};
mod quote;
mod range_sum;
mod sealing;
// The projected-tuple-tower round's two instruments
// (`docs/projected-tuple-tower-design.md` §11, `probes/README.md`): the
// value-graph counter that priced the naming, and the readback itself. Both
// are inert unless `HEATHER_RB` is set.
mod recursion;
mod representations;
pub mod resolve;
mod session;
pub use module_delta::{ItemSlice, ModuleDelta, ModuleDependencyIdentity, ModuleReplayError, SliceReport};
pub use module_image::{ModuleImageDecodeError, ModuleImageLimits, image_format};
pub use session::SemanticImage;
mod slots;
mod statements;

pub use stats::{ItemTiming, ScopeKind};
mod surface;
mod traits;
mod types;
mod unification;
mod vec;
mod wf;

pub(crate) use application::{
    ParamMeta, Skel, has_implicit_mark, skel_of_lam_binders, skel_of_ty, skel_params,
};
use attempt::{CheckNote, DeclAttempt, ReflNote};
use lifetimes::{DynamicScope, Memos, ModulePass, Policy};
pub(crate) use context::{Alias, Cx, DictBinder, TyVar};
use inductive::Inductive;
use metaprograms::{MetaDef, MetaPrograms};
use names::{
    DEFAULT_MODULE, GlobalInfo, GlobalRegistration, ImportSpec, NameKind, NameRes, Names, Scope,
    miss_msg, qkey, split_qual,
};
use recursion::SelfRef;
use representations::Representations;
use slots::{Ingredient, Slot};
pub(crate) use surface::{count_holes, count_holes_expr, count_tactic_slots, strengthen_global};
use surface::{
    Condition, condition_connective, condition_expression, decide_call, expression_as_type, is_true_of,
    lowered_condition, rebuild_connective, for_each_free_slot, has_free_slots,
    lower_argument_slots, slot_profile,
};
use traits::Traits;
use types::Types;
use solution_check::SolutionCheck;
use oracle::Unfold;
use unification::{Guesses, ResolveOb, Sol, unify_ty_root, zonked, zonked_tm};
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
pub const COMMON_MODULE: &str = names::COMMON_MODULE;

pub use diagnostics::{ElabError, GoalReport, GoalSource, IndexedRoute, KernelSite, LintFix, Warning};
pub use heather_syntax::Span;

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
            ElabError::ArgSlotEscape { .. } => {
                "an argument slot needs an enclosing checking position with a function type".into()
            }
            other => other.to_string(),
        }
    }

    /// Where the error points, when it points anywhere: an unsolved-goal
    /// listing points at its first goal. A declaration's errors point
    /// inside it, which is how `heather check --expectations` attributes
    /// them to the declarations that expect them; one that points elsewhere
    /// is reported as it stands, never taken as an expected refusal.
    pub fn span(&self) -> Option<Span> {
        match self {
            ElabError::Parse(e) => Some(e.span),
            ElabError::Elab { span, .. }
            | ElabError::Kernel { span, .. }
            | ElabError::Resolution { span, .. }
            | ElabError::ArgSlotEscape { span } => Some(*span),
            ElabError::UnsolvedGoals { goals, .. } => goals.first().map(|g| g.span),
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
    format!(
        "{severity}: {msg}\n  --> {file}:{line}:{col}\n{}",
        snippet(src, span)
    )
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
    // A span a lexer error measured in bytes can end inside a multi-byte
    // character (an unexpected `δ`); widen it to the character's end.
    let mut end = span.end.clamp(offset, src.len());
    while !src.is_char_boundary(end) {
        end += 1;
    }
    let span_chars = src[offset..end].chars().count();
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
        let name = self.name.strip_prefix("#decreasing:")
            .map(|n| format!("decreasing {n}")).unwrap_or_else(|| format!("?{}", self.name));
        let mut s = match at {
            Some(at) => format!("  {name} : {}   ({at})\n", self.statement),
            None => format!("  {name} : {}\n", self.statement),
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
        if self.name.starts_with("#decreasing:") {
            s.push_str(&format!("      discharge with `on {name} := proof;`\n"));
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
            ElabError::Kernel {
                decl, err, note, ..
            } => {
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
    let col = upto
        .rfind('\n')
        .map_or(upto.len(), |nl| upto.len() - nl - 1)
        + 1;
    (line, col)
}

type R<T> = Result<T, ElabError>;

fn err<T>(msg: impl Into<String>, span: Span) -> R<T> {
    Err(ElabError::Elab {
        msg: msg.into(),
        span,
    })
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
    l.as_constant().map_or_else(|| format!("{l:?}"), |n| n.to_string())
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
pub(crate) const IMPLICIT_MARK_REFUSED: &str = "implicit binders take effect in parameter types, `let` annotations, field \
     types, and lambdas; this position cannot use one — see \
     issues/implicit-binders-in-function-types.md";

/// The receiver-shaped builtins: names that a `.` call reaches without any
/// declaration behind them, so [`Elaborator::shadowed`] cannot see them. Read
/// only by receiver dispatch (docs/traits-receiver-dispatch-design.md §3),
/// which needs to know whether a call *had* another reading before it claims
/// one — a class field named `map` must make `xs.map(f)` ambiguous, never
/// silently the class's.
const BUILTIN_METHODS: [&str; 8] = [
    "map", "fold", "head", "tail", "cons", "cong", "inj", "absurd",
];

/// Where a resolved dictionary came from, when it came by **upcast**: the
/// *child* dictionary and its class type ([`Elaborator::resolve_goal_from`],
/// `docs/traits-named-upcast-design.md` §2.1). `None` for every other answer,
/// which is every answer already at the goal's own class.
type Upcast = Option<(Term, Type)>;

/// What an `if` condition's expression is, for its `Bool` reading
/// (`Elaborator::condition_type`).
enum ConditionType {
    Bool(Term, Type),
    Other(String),
    Unread,
}

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
    /// Lifted tactic proofs the binding refers to, pushed just before it
    /// (`docs/bv-omega-design.md` §7).
    aux: Vec<GlobalBinding>,
    binding: GlobalBinding,
    /// A theorem's proof, kept sealed beside its opaque binding when its
    /// statement carries data (`sealing.rs`).
    sealed: Option<Rc<Term>>,
    /// A theorem's proof for [`Elaborator::keep_proofs_for_export`], whether
    /// or not it is also sealed.
    export_proof: Option<Rc<Term>>,
    registration: GlobalRegistration,
    is_axiom: bool,
    direct_dependencies: Vec<String>,
}

/// Restores the temporary name-resolution environment after re-lowering
/// stored surface syntax.
struct ResolutionScope<'a> {
    stack: &'a RefCell<Vec<Rc<names::Scope>>>,
}

impl Drop for ResolutionScope<'_> {
    fn drop(&mut self) {
        self.stack
            .borrow_mut()
            .pop()
            .expect("a resolution scope was installed");
    }
}

/// The durable semantic world. It is immutable while shared; the first commit
/// in a fork obtains a private copy through [`Rc::make_mut`]. Keeping this
/// boundary explicit makes image capture and image restoration O(1), and is
/// the ownership seam at which per-registry overlays can replace whole-world
/// copy-on-write.
#[derive(Clone)]
struct Shared<T>(Rc<T>);

impl<T> Shared<T> {
    fn new(value: T) -> Self {
        Self(Rc::new(value))
    }
}

impl<T> Deref for Shared<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Clone> DerefMut for Shared<T> {
    #[track_caller]
    fn deref_mut(&mut self) -> &mut Self::Target {
        stats::make_mut(&mut self.0)
    }
}

#[derive(Clone)]
#[doc(hidden)]
pub struct CommittedWorld {
    psi: Shared<GlobalCtx>,
    delta_psi: Shared<GlobalCtx>,
    names: Shared<Names>,
    types: Shared<Types>,
    traits: Shared<Traits>,
    representations: Shared<Representations>,
    provenance: Shared<provenance::Provenance>,
    meta_programs: Shared<MetaPrograms>,
    /// Interface definitions by global key (`interfaces.rs`).
    interfaces: Shared<interfaces::Interfaces>,
}

impl CommittedWorld {
    fn empty() -> Self {
        Self {
            psi: Shared::new(GlobalCtx::default()),
            delta_psi: Shared::new(GlobalCtx::default()),
            names: Shared::new(Names::new(DEFAULT_MODULE)),
            types: Shared::new(Types::default()),
            traits: Shared::new(Traits::default()),
            representations: Shared::new(Representations::default()),
            provenance: Shared::new(provenance::Provenance::default()),
            meta_programs: Shared::new(MetaPrograms::default()),
            interfaces: Shared::new(interfaces::Interfaces::default()),
        }
    }
}

/// An elaboration session. Its fields are grouped by lifetime, and each group
/// has one clone rule and one rollback rule (`lifetimes.rs` has the table): a
/// clone shares the committed world and copies or freshens the rest group by
/// group; [`SemanticImage::elaborator`] instead supplies fresh transient state
/// around the shared world.
#[derive(Clone)]
pub struct Elaborator {
    /// Ψ, δΨ and the registries: what the session has accepted. Shared by
    /// clones and copied on write.
    committed: Rc<CommittedWorld>,
    /// What the module pass in progress owns: the kernel gate's pool and
    /// replay, the delta journal, the item loop, accumulated diagnostics.
    pass: ModulePass,
    /// Scratch state with exactly one ordinary declaration's lifetime.
    attempt: DeclAttempt,
    /// Fields set for a dynamic extent and put back when it ends.
    scope: DynamicScope,
    /// Configuration a driver sets: gate oracle, fuel, lints, collectors.
    policy: Policy,
    /// Caches, none of them semantic.
    memos: Memos,
}

impl Deref for Elaborator {
    type Target = CommittedWorld;

    fn deref(&self) -> &Self::Target {
        &self.committed
    }
}

impl DerefMut for Elaborator {
    #[track_caller]
    fn deref_mut(&mut self) -> &mut Self::Target {
        stats::make_mut(&mut self.committed)
    }
}

/// A recorded site that a kernel-located refusal turned out to be
/// ([`Elaborator::kernel_refusal`]): reported as its own probe would have
/// reported it, had the probe's budget reached the verdict.
enum RecordedSite {
    /// A written `refl`, with its two sides when both spell.
    Refl { span: Span, sides: Option<(String, String)> },
    /// A checking site, with its two types when both spell and differ.
    Check { span: Span, types: Option<(String, String)> },
}

impl RecordedSite {
    fn into_error(self, decl: &str, err: TypeError, with_op: impl Fn(String) -> String) -> ElabError {
        match self {
            RecordedSite::Check { span, types: Some((g, w)) } => ElabError::Elab {
                msg: with_op(format!("this has type `{g}`, but `{w}` is expected here")),
                span,
            },
            RecordedSite::Check { span, types: None } => ElabError::Kernel {
                decl: decl.to_string(),
                span,
                err,
                note: Some(with_op(
                    "the type of this expression does not convert to the type expected here".to_string(),
                )),
                site: KernelSite::Recorded,
            },
            RecordedSite::Refl { span, sides } => ElabError::Kernel {
                decl: decl.to_string(),
                span,
                err,
                note: Some(with_op(match sides {
                    Some((l, r)) => format!(
                        "`refl` needs both sides to be definitionally equal, but `{l}` and `{r}` are not"
                    ),
                    None => "`refl` needs both sides to be definitionally equal, and these are not".to_string(),
                })),
                site: KernelSite::Recorded,
            },
        }
    }
}

/// What a probed checking mismatch can say
/// ([`Elaborator::probed_check_note`]).
enum MismatchNote {
    /// Both types, in surface: the message replaces the kernel's report.
    Spelled(String),
    /// The site, and what can be shown of the types: the kernel's verdict
    /// stays and the span moves here, as a `refl` note's does.
    Located(String),
}

/// What a `p.f` turned out to be (docs/surface-records.md §4.2).
enum DotResolution {
    /// An already inferred intrinsic selected by its receiver.
    Inferred(Term, Type, Level),
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

    fn type_endpoint_can_anchor(&self, cx: &Cx, expression: &Expr) -> bool {
        !self.is_checking_only(cx, expression)
            && self.probe(|| self.elab_infer(cx, expression).is_ok())
    }

    fn type_endpoint_infers_by_fallback(&self, cx: &Cx, expression: &Expr) -> bool {
        self.deferral_can_fall_back(cx, expression) && self.probe(|| self.elab_infer(cx, expression).is_ok())
    }

    fn type_endpoint_may_need_checking(&self, cx: &Cx, expression: &Expr) -> bool {
        // An application's head is not a bare reference: `toNat(w)` fills
        // the implicit a bare `toNat` would leave to checking, and the
        // application is judged as a whole. A `match` with no motive infers
        // only when a constant motive does, so it is left to the probe.
        let mut heads = std::collections::HashSet::new();
        let mut found = false;
        surface::walk_expr(expression, &mut |part| {
            if let ExprKind::App { head, .. } = &part.kind {
                heads.insert(&**head as *const Expr);
            }
            if !found
                && (matches!(part.kind, ExprKind::Match { motive: None, .. })
                    || !heads.contains(&(part as *const Expr)) && self.is_checking_only(cx, part))
            {
                found = true;
            }
        });
        found
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
        if let Some(lowered) = self.try_codata_indexed_ty(cx, expression, span)? {
            return Ok(Some(lowered));
        }
        if let Some(lowered) = self.try_indexed_ty(cx, expression, span)? {
            return Ok(Some(lowered));
        }
        if let Some(lowered) = self.try_type_value_app(cx, expression, span)? {
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
        if let Some((fam, k)) = self.lookup_member(name) {
            return Some(expr::TypeFormerShape {
                indexed: fam.members[k].index.is_some(),
                value_parameters: 0,
            });
        }
        let ind = self.lookup_inductive(name)?;
        Some(expr::TypeFormerShape {
            indexed: ind.index.is_some() || !ind.co_index.is_empty(),
            value_parameters: ind.valparams.len(),
        })
    }
}

impl expr::EmissionElab for Elaborator {
    fn emit_ty(&self, cx: &Cx, ty: &Type, depth: u32) -> Option<Type> {
        Elaborator::emit_ty(self, cx, ty, depth)
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

    fn note_refl_mismatch(
        &self,
        cx: &Cx,
        lhs: &Term,
        rhs: &Term,
        ty: &Type,
        level: &Level,
        span: Span,
    ) {
        Elaborator::note_refl_mismatch(self, cx, lhs, rhs, ty, level, span);
    }
}

impl expr::ExpectedTypeDiagnosticsElab for Elaborator {
    fn display_expected_type(&self, cx: &Cx, expected: &Type) -> String {
        self.display_type(cx, expected)
    }
}

impl expr::UnitCheckingElab for Elaborator {
    fn read_expected_type_within(&self, cx: &Cx, expected: &Type, span: Span) -> R<Option<Type>> {
        // Budget first: a head the value machine reaches within it is read
        // as before, through the registry-aware read, at no more than the
        // budget again. Only a spent budget is "a verdict still to compute".
        match self
            .semantic_oracle()
            .bounded(diagnostics::VERDICT_READ_STEPS)
            .whnf_type(&cx.gamma, expected)
        {
            Ok(_) => self.whnf(cx, expected, span).map(Some),
            Err(_) => Ok(None),
        }
    }

    fn defer_unit_verdict(&self, cx: &Cx, expected: &Type, span: Span) {
        self.attempt.trivial_uses.borrow_mut().push(attempt::TrivialUse {
            span,
            cx: Rc::new(cx.clone()),
            expected: expected.clone(),
        });
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

    fn infer_statement_expression(&self, cx: &Cx, expression: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, expression)
    }

    fn infer_mut_call(&self, cx: &Cx, call: &Expr) -> R<(Term, Type, Level)> {
        self.scoped_cell(|s| &s.mut_call_site, Some(call.span), || self.elab_infer(cx, call))
    }

    fn read_local(&self, cx: &Cx, name: &str, span: Span) -> R<(Term, Type, Level)> {
        self.resolve_reading(cx, name, span)
    }

    fn annotation(&self, cx: &Cx, ty: &Type) -> Type {
        self.annotation_type(cx, ty, 0)
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
        if reference.args.is_empty() {
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
        self.elab_check_skel_slots(cx, result, expected, level, hint, skeleton, capture_slots)
    }
}

impl matching::MotiveSynthesisElab for Elaborator {
    fn generalizes_an_index(&self, cx: &Cx, scrutinee_type: &Type) -> bool {
        let var = |idx: &Term| matches!(idx, Term::Var(_));
        self.iwf_of_at(cx, scrutinee_type).is_some_and(|(_, fam)| var(&fam.idx))
            || self.indexed_of_at(cx, scrutinee_type).is_some_and(|(_, fam)| var(&fam.idx))
    }

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
        // A candidate is any stuck subterm of the goal, of whatever type, and
        // conversion at the scrutinee's type presumes both sides have it. Where
        // that type is irrelevant (Unit, Empty, sEmpty, …) the presumption is
        // the whole answer — a `Nat` candidate "converts" to a scrutinee at
        // `Empty`, and abstracting it breaks the motive
        // (docs/metatheory-ch07-extensions.md §28). So a hit stands only once
        // the candidate's own type converts too; misses, the common case, pay
        // nothing extra.
        let oracle = self.goal_oracle();
        oracle
            .convert_term(
                &cx.gamma,
                Layer::Prog,
                candidate,
                scrutinee,
                scrutinee_type,
                scrutinee_level,
            )
            .is_ok()
            && typing::infer_term(oracle.world(), 0, Layer::Prog, &cx.gamma, candidate, self.policy.fuel)
                .is_ok_and(|(ty, _)| {
                    oracle
                        .convert_type(&cx.gamma, Layer::Prog, &ty, scrutinee_type, scrutinee_level)
                        .is_ok()
                })
    }
}

impl matching::MatchSpeculationState for Elaborator {
    type Mark = (usize, usize);

    fn mark_match_state(&self) -> Self::Mark {
        (self.pass.warnings.borrow().len(), self.attempt.goal_arena.mark())
    }

    fn rollback_match_state(&self, mark: Self::Mark) {
        self.pass.warnings.borrow_mut().truncate(mark.0);
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

    fn lower_constant_convoy(
        &self,
        cx: &Cx,
        form: MatchForm,
        generated: bool,
        h: &str,
        arms: &[Arm],
        scrutinee: Term,
        scrutinee_type: &Type,
        scrutinee_level: &Level,
        motive: Type,
        motive_level: Level,
        result: &Type,
        span: Span,
    ) -> R<Term> {
        self.elab_convoy(
            cx, form, generated, h, arms, scrutinee, scrutinee_type, scrutinee_level, motive,
            &motive_level, result, span,
        )
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

    fn emits_checked_applications(&self, _cx: &Cx) -> bool {
        self.emits_at_forms()
    }

    fn respell_application_annotations(
        &self,
        cx: &Cx,
        dom: &Type,
        cod: &Type,
        scratch: u32,
    ) -> Option<(Option<Type>, Option<Type>)> {
        // The one chokepoint, in the application's scratch world
        // (`docs/annotation-component-respell-design.md` §2.5); `cod` binds
        // the argument, hence depth 1.
        let nd = self.emit_ty_in(cx, dom, 0, scratch);
        let nc = self.emit_ty_in(cx, cod, 1, scratch);
        (nd.is_some() || nc.is_some()).then_some((nd, nc))
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

    fn check_param_default(
        &self,
        cx: &Cx,
        arg: &Expr,
        expected: &Type,
        level: &Level,
        earlier: &[unification::EarlierArg],
    ) -> R<Term> {
        let ExprKind::App { args, .. } = &arg.kind else {
            return err("internal parameter default has the wrong form", arg.span);
        };
        self.elab_param_default(cx, args, expected, level, arg.span, earlier)
    }
}

impl recursion::SelfCallElab for Elaborator {
    fn note_recursion_on(&self, dec: &str) {
        let mut decs = self.attempt.recursion_decs.borrow_mut();
        if !decs.iter().any(|d| d == dec) {
            decs.push(dec.to_string());
        }
    }

    fn infer_self_call_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, argument)
    }

    fn self_call_application_params(&self, name: &str) -> Rc<Vec<ParamMeta>> {
        self.params_of(name)
    }

    fn misplaced_recursion(&self, name: &str) -> Option<(usize, String)> {
        match &*self.scope.misplaced_recursion.borrow() {
            Some((owner, dec, msg)) if owner == name => Some((*dec, msg.clone())),
            _ => None,
        }
    }

    fn apply_self_call_implicit(
        &self,
        cx: &Cx,
        name: &str,
        params: Rc<Vec<ParamMeta>>,
        head: Term,
        ty: Type,
        level: Level,
        args: &[Expr],
        mask: &[bool],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        application::apply_implicit(
            self, cx, name, params, true, 0, false, head, ty, level, args, mask, None, false, span,
        )
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
    fn deferred_argument_note(
        &self, cx: &Cx, head: &Term, params: &[ParamMeta],
        domains: &[(usize, Type)], slot_param: &[usize], sols: &[Sol],
    ) -> String {
        self.display_deferred_argument(cx, head, params, domains, slot_param, sols)
    }

    fn respell_solution(&self, cx: &Cx, dom: &Type, solution: &Term) -> Option<Term> {
        // Only a *type* argument is a code: the metavariable's declared
        // domain is `Ty l` exactly there.
        let Type::Ty(level) = dom else { return None };
        let coded = Type::El {
            level: level.clone(),
            tm: Rc::new(solution.clone()),
        };
        // The committed world, per the trait note — the payloads of the
        // discharge's `apply_global` are scoped there and not in the scratch
        // world the annotations live in.
        let emitted = self.emit_ty(cx, &coded, 0)?;
        let code = code::code_of(&emitted)?;
        (code != *solution).then_some(code)
    }

    fn classify_application_argument(
        &self,
        cx: &Cx,
        argument: &Expr,
    ) -> application::ArgumentClass {
        // An annotated domain does not make a lambda's body inferable:
        // `λ (a: A) => Some([a])` still needs the expected codomain. Prefer
        // per-call checking once the parameter type is solved, retaining
        // inference when the callback itself must teach that type. Keep this
        // scheduling rule local to applications: standalone annotated
        // lambdas (including equality endpoints) still infer normally.
        let annotated_lambda = matches!(&argument.kind, ExprKind::Lam { binders, .. }
            if binders.iter().all(|b| b.ty.is_some()));
        // A numeral or character literal waits for a later argument to fix
        // its carrier, and falls back to its own type (`Nat`, `Char`) when
        // nothing does: in `unsigned_le(9, b)` the width comes from `b`, so
        // `9` is a byte (docs/native-programs-read-like-programs-design.md S3).
        let literal = matches!(&argument.kind, ExprKind::Num(_) | ExprKind::Scaled(_) | ExprKind::Char(_));
        // A binding statement's continuation (`Bind::seq(e, λ #bindN => rest)`,
        // docs/sequencing-surface-design.md §2.2) waits for the expected type:
        // the rest of the block is checked at the carrier's `M(B)`, never
        // inferred from its first token, so that `Pure(match … { … })` at the
        // end of a block checks as it would without the bind.
        let continuation = matches!(&argument.kind, ExprKind::Lam { binders, .. }
            if binders.len() == 1 && binders[0].name.starts_with("#bind"));
        application::ArgumentClass {
            checking_only: annotated_lambda || literal || continuation || self.is_checking_only(cx, argument),
            fallback_infer: annotated_lambda || literal || continuation || self.deferral_can_fall_back(cx, argument),
        }
    }

    fn infer_application_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, argument)
    }

    fn infer_polymorphic_argument(
        &self, cx: &Cx, argument: &Expr, parameter: &Type, n: u32, sols: &[Sol],
    ) -> Option<R<(Term, Type, Level)>> {
        self.infer_bare_polymorphic_argument(cx, argument, parameter, n, sols)
    }

    fn infer_lambda_at_known_domains(
        &self, cx: &Cx, argument: &Expr, parameter: &Type, n: u32, sols: &[Sol],
    ) -> Option<R<(Term, Type, Level)>> {
        // A λ with an unannotated binder whose domain the call already knows
        // is as inferable as an annotated one: `antidiag(+, n, λ i k => …)`
        // inside a `∑` has `f: Nat → Nat → A`, so `i` and `k` are `Nat` before
        // anything fixes `A`, and the body's type is what fixes it. Only the
        // binders' domains have to be meta-free, read one Π at a time off the
        // written parameter type; the codomain is the body's to teach. A
        // domain that still waits on a meta, a binder past the written Π
        // chain, or an implicit binder keeps the argument blocked.
        let ExprKind::Lam { binders,body } = &argument.kind else { return None; };
        if binders.iter().all(|b| b.ty.is_some()) || binders.iter().any(|b| b.implicit) { return None; }
        let mut domains = Vec::with_capacity(binders.len());
        let mut ty = parameter;
        for binder in binders {
            let Type::Pi { dom,dom_level,cod,.. } = ty else { return None; };
            domains.push(match binder.ty {
                Some(_) => None,
                None => Some((zonked(dom,n,sols)?,dom_level.clone())),
            });
            ty = cod;
        }
        Some(self.expr_elab().infer_callback_from_domains(self,cx,binders,body,&domains))
    }

    #[allow(clippy::too_many_arguments)]
    fn unify_application_argument_type(
        &self,
        cx: &Cx,
        parameter: &Type,
        argument: &Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        guesses: Guesses<'_>,
        span: Span,
    ) -> Vec<(usize, Rc<Term>)> {
        self.unify_arg_ty(cx, parameter, argument, n, sols, meta_doms, guesses, span)
    }

    fn note_argument_mismatch(&self, cx: &Cx, got: &Type, expected: &Type, level: &Level, span: Span, clash: Option<application::SlotClash>) {
        if self.policy.owed_checks_forgotten {
            return;
        }
        self.note_check_clash(cx, got, expected, level, span, clash)
    }

    fn solve_application_from_expected(
        &self,
        cx: &Cx,
        result: &Type,
        expected: &Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        guesses: Guesses<'_>,
        span: Span,
    ) -> R<()> {
        self.solve_from_expected(cx, result, expected, n, sols, meta_doms, guesses, span)
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
            let written = params
                .get(obligation.param)
                .and_then(|p| p.solver.as_deref());
            let changed = self.fill_index_from_scope(cx, written, params, slot_param, sols)
                || self.fill_index_from_designation(
                    cx, written, params, slot_param, sols, meta_doms, n,
                    obligation.applied.as_ref(), span,
                );
            return Ok(if changed {
                application::ObligationProgress::Unblocked
            } else {
                application::ObligationProgress::Blocked
            });
        };
        let written = params.get(obligation.param).and_then(|p| p.solver.as_deref());
        // A class goal is displayed as written (`Monoid<A>`, layer 2 §7). A
        // proposition is displayed as this call instantiated it: `0 < 5`, not
        // the callee's `0 < n` (docs/positivity-evidence-design.md §3). Spelled,
        // not decoded: decoding reduces `0 < 0` to `False`, which hides the
        // goal the caller asked for. Operator notation in it is
        // issues/diagnostic-operator-resugaring.md's.
        let display = written
            .map(traits::render_ty)
            .unwrap_or_else(|| "a solver parameter".to_string());
        let applied = obligation
            .applied
            .as_ref()
            .map(|t| zonked_tm(t, n, sols).unwrap_or_else(|| t.clone()));
        let prefer = written
            .zip(applied.as_ref())
            .and_then(|(w, applied)| self.solver_carrier_head(w, params, applied));
        // A class over a type constructor shows the constructor the call
        // solved, `Bind<List>`, not the parameter it was written with.
        let display = written
            .zip(prefer.as_deref())
            .and_then(|(w, key)| {
                // Spelled only once committed: a scratch-world spine's globals
                // sit `n` places over.
                let committed = obligation.applied.as_ref().and_then(|t| zonked_tm(t, n, sols));
                self.kinded_goal_display(cx, w, params, key, committed.as_ref())
            })
            .unwrap_or(display);
        let mut trace = Vec::new();
        match self.resolve_goal(
            cx,
            &goal,
            &obligation.dom_level,
            &display,
            prefer.as_deref(),
            span,
            &mut trace,
        ) {
            Some(term) => {
                sols[obligation.slot] = Sol::Solved(Rc::new(term));
                Ok(application::ObligationProgress::Solved)
            }
            // A class goal is displayed as written (`Monoid<A>`, layer 2 §7).
            // A proposition is displayed as this call instantiated it: `0 <
            // 5`, not the callee's `0 < n` (docs/positivity-evidence-design.md
            // §3). Spelled, not decoded: decoding reduces `0 < 0` to `False`,
            // which hides the goal the caller asked for. Operator notation in
            // it is issues/diagnostic-operator-resugaring.md's. Spelled only
            // here, on failure: a resolved goal never needs it. Which kind
            // the goal was is the search's own verdict, its outermost
            // `no-class` record (a class goal arrives in spellings the
            // display path cannot classify).
            None => Err(ElabError::Resolution {
                goal: if trace.first().is_some_and(|top| {
                    trace.iter().any(|l| l.key == "no-class" && l.depth == top.depth)
                }) && let Some(spelled) = self.spell_type_clean(cx, &goal)
                {
                    spelled
                } else {
                    display
                },
                span,
                trace,
            }),
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
        match self
            .attempt
            .goal_arena
            .reserve_promoted(promoted.len() as u32)
        {
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
            let Some(dom) = zonked(&meta_doms[slot], n, sols) else {
                continue;
            };
            let parameter = slot_param[slot];
            let param = params
                .get(parameter)
                .map(|p| p.name.as_str())
                .unwrap_or("?");
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
        let mut goal = params
            .get(obligation.param)
            .and_then(|parameter| parameter.solver.as_deref())
            .map(traits::render_ty)
            .unwrap_or_else(|| "a solver parameter".to_string());
        let mut symbolic = false;
        for p in params {
            if let Some(symbol) = traits::op_index_symbol(&p.name)
                && goal.contains(&p.name)
            {
                goal = goal.replace(&p.name, symbol);
                symbolic = true;
            }
        }
        if symbolic {
            return ElabError::Elab {
                msg: format!(
                    "cannot infer the implicit arguments needed for `{goal}` in `{name}` \
                     from this call: the expected type or a scoped constraint must pin \
                     the indices before instance search can run. Supply the indices \
                     explicitly with `@{name}(…)` or give an expected type that names them"
                ),
                span,
            };
        }
        if let Some(solver) = params
            .get(obligation.param)
            .and_then(|parameter| parameter.solver.as_deref())
            && let Some(reference) = self.class_ref_of_ty(solver)
            && let Some(class) = self.lookup_class(&reference.name)
            && !class.valparams.is_empty()
        {
            return self.value_slot_refusal(&class, name, None, span);
        }
        // A class over a type constructor (issues/higher-kinded-classes.md):
        // its carrier is a value implicit, so `<…>` cannot give it. Name it,
        // and say what would have pinned it.
        if let Some(solver) = params
            .get(obligation.param)
            .and_then(|parameter| parameter.solver.as_deref())
            && let Some(reference) = self.class_ref_of_ty(solver)
            && let Some(class) = self.lookup_class(&reference.name)
            && class.is_kinded()
            && let Some(carrier) = reference
                .args
                .iter()
                .zip(&class.kinds)
                .filter(|(_, k)| k.is_some())
                .find_map(|(a, _)| match &a.kind {
                    TyKind::Named { name, args } if args.is_empty() => params
                        .iter()
                        .find(|p| !p.is_type && p.name == *name)
                        .map(|p| p.name.clone()),
                    _ => None,
                })
        {
            return ElabError::Elab {
                msg: format!(
                    "the goal of `{parameter}` (`{goal}`) needs the type constructor \
                     `{carrier}`, which this call does not determine: an argument at \
                     `{carrier}` applied (`{carrier}(Nat)`) pins it only when its type is a \
                     declared generic type applied to arguments (`Option<Nat>`), so a \
                     type with no such head leaves it open. Write it \
                     (`{name}({carrier} := Option, …)`) or pass `{parameter}` explicitly \
                     (`@{name}(…)`)"
                ),
                span,
            };
        }
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

/// The text a slice is keyed by: the item's exact source span, or, at the
/// first member of a mutual measure group, every member's span joined —
/// the group is elaborated as one there, so its slice answers for all of
/// them and must be keyed by all of them.
/// The names an item answers to for `--only`: its own, or every member's
/// for the head of a mutual measure group (the group is one slice).
fn slice_names(file: &heather_syntax::File, idx: usize, plan: &ItemPlan) -> Vec<String> {
    match plan.in_group.get(&idx) {
        Some(&g) if plan.groups[g][0] == idx => {
            plan.groups[g].iter().map(|&i| item_timing_name(&file.items[i])).collect()
        }
        _ => vec![item_timing_name(&file.items[idx])],
    }
}

fn slice_source(file: &heather_syntax::File, src: &str, idx: usize, plan: &ItemPlan) -> String {
    let span_of = |i: usize| lint::item_span(&file.items[i]);
    match plan.in_group.get(&idx) {
        Some(&g) if plan.groups[g][0] == idx => plan.groups[g]
            .iter()
            .map(|&i| {
                let sp = span_of(i);
                &src[sp.start..sp.end]
            })
            .collect::<Vec<_>>()
            .join("\n"),
        _ => {
            let sp = span_of(idx);
            src[sp.start..sp.end].to_string()
        }
    }
}

/// The refusal of a declaration's own name used as a value. A declaration
/// with no value parameters (a `def`, or a parameterless `fn`) has no
/// recursive call to make at all (docs/value-definitions-design.md §2.1).
fn self_name_refusal(selfref: &SelfRef, name: &str) -> String {
    if selfref.params.len() == selfref.n_tyvars {
        format!("`{name}` refers to itself, and a value (a `def`, or a `fn` without parameters) is not recursive")
    } else {
        format!("`{name}` can only be used here as a saturated recursive call")
    }
}

/// Append to a refusal of a member's self-reference, written by its bare
/// base name, the global that name would otherwise have meant
/// (issues/self-reference-hides-same-named-global.md). `note` is
/// [`Elaborator::self_shadow_note`]'s; errors other than a surface refusal
/// pass through unchanged.
fn with_self_shadow_note(e: ElabError, note: Option<&str>) -> ElabError {
    match (e, note) {
        (ElabError::Elab { msg, span }, Some(note)) => ElabError::Elab { msg: format!("{msg}\n{note}"), span },
        (e, _) => e,
    }
}

fn item_timing_name(item: &Item) -> String {
    match item {
        Item::Decl(decl) => decl.name.clone(),
        Item::Inductive(ind) => ind.name.clone(),
        Item::Class(class) => format!("class {}", class.name),
        Item::Instance(instance) => format!("instance {}", instance.class.name),
        Item::Designation(designation) => format!("designation {}", designation.symbol),
        Item::Datarepr(repr) => format!("datarepr {}", repr.name),
        Item::Impl(implementation) => {
            format!("impl {} for {}", implementation.op, implementation.repr)
        }
        Item::Import(import) => format!("import {}", import.module),
        Item::Generate(g) => format!("generate {}", host::tactic_name(&g.generator)),
        Item::Prefixed(p) => p.decl.name.clone(),
    }
}

impl Default for Elaborator {
    fn default() -> Self {
        Self::new()
    }
}

/// What a lifted obligation quantifies its arm binders at
/// (`docs/decreases-unfolding-design.md` §4): the constructor's stored field
/// types, instantiated at the scrutinee's type arguments.
impl measure::BinderTys for Elaborator {
    fn local_evidence(&self, decl: &Decl, scope: &[measure::Binder], goal: &Ty, arithmetic: bool) -> Option<Expr> {
        self.measure_local_evidence(decl, scope, goal, arithmetic)
    }
    fn ctor_fields(&self, scrut: &Ty, ctor: &str) -> Option<Vec<Ty>> {
        self.ctor_fields_of(scrut, ctor)
    }
    fn infer_local(&self, decl: &Decl, signatures: &[(String, Ty)], scope: &[measure::Binder], expr: &Expr) -> Option<Ty> {
        self.infer_measure_local(decl, signatures, scope, expr)
    }
}

/// Kernel workers a fresh elaborator uses when `HEATHER_KERNEL_WORKERS` is
/// unset. Eight: on the reused_callee certificate total CPU was flat from one
/// to eight workers and the wall was bounded by the serial elaborator past
/// four, so a wider default costs nothing but memory (peak RSS roughly tripled
/// at eight; the suite's per-process rail is sized for that). The width is
/// never a semantic decision — `docs/parallel-kernel-gate-design.md` §5.1 is
/// what makes a default above 1 safe to ship.
pub const DEFAULT_KERNEL_WORKERS: usize = 8;

/// The kernel worker count `HEATHER_KERNEL_WORKERS` asks for, if it names a
/// usable one (`docs/parallel-kernel-gate-design.md` §4).
///
/// A `--kernel-workers` flag wins over this; an unparseable or zero value is
/// ignored rather than refused, because instrumentation must never be the
/// reason a check fails.
pub fn kernel_workers_from_env() -> Option<usize> {
    kernel_workers_from_spec(&std::env::var("HEATHER_KERNEL_WORKERS").ok()?)
}

/// [`kernel_workers_from_env`]'s rule, without the environment: a positive
/// decimal is a width and everything else is nothing.
pub fn kernel_workers_from_spec(spec: &str) -> Option<usize> {
    spec.trim().parse::<usize>().ok().filter(|n| *n > 0)
}


/// The one shape an invisible difference almost always has, named so the
/// reader does not have to know how a type is represented to act on it
/// (issues/lgg-error-hides-the-implicit.md).
///
/// `El(c)` and the raw code `c` are the same type spelled two ways. They are
/// convertible and they are not equal as terms, and which one an elaboration
/// produces depends on where the type came from — a written annotation, an
/// inductive's lowering, a pattern's scrutinee — so two spellings of the same
/// goal routinely disagree here while printing identically.
const EL_AGAINST_CODE: &str = ". `El` against a type code is one type spelled \
     two ways — a raw code, and the `El` of that code — convertible but not equal \
     as terms, which is the usual source of a difference the spelling does not show";

impl Elaborator {
    /// An empty elaborator (no prelude).
    pub fn new() -> Self {
        Elaborator {
            committed: Rc::new(CommittedWorld::empty()),
            pass: ModulePass::new(),
            attempt: DeclAttempt::default(),
            scope: DynamicScope::default(),
            policy: Policy::new(),
            memos: Memos::default(),
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
        self.policy.gate = Some(gate);
    }

    /// How many kernel worker threads a module's proof obligations are checked
    /// on (`docs/parallel-kernel-gate-design.md`).
    ///
    /// 1 means the kernel runs inline at the gate, on this thread, in
    /// declaration order, exactly as it always has. Above 1 — which is the
    /// default ([`DEFAULT_KERNEL_WORKERS`]) — the *statement* is still checked
    /// synchronously and the binding still commits to Ψ immediately; the proof
    /// is queued and joined before the module is accepted, and a module whose
    /// join fails is discarded and re-run at width 1, so the width changes
    /// only how fast the answer arrives (§5.1).
    pub fn set_kernel_workers(&mut self, workers: usize) {
        self.pass.kernel_pool.set_workers(workers);
    }

    /// The configured worker count.
    pub fn kernel_workers(&self) -> usize {
        self.pass.kernel_pool.workers()
    }

    /// A clone that checks at this elaborator's width.
    ///
    /// `clone()` is deliberately inline (`pool.rs`, the `Clone` note): a
    /// clone is usually speculative or nested work, and a pool per candidate
    /// would cost more than it saves. A driver that forks off a *whole
    /// module* per probe — the certificate unit tests do — wants the width
    /// it configured, and says so here. Nothing else is shared with the
    /// original: the fork's pool starts empty and joins on its own.
    pub fn fork(&self) -> Self {
        let mut forked = self.clone();
        forked.set_kernel_workers(self.kernel_workers());
        forked
    }

    /// Roll this elaborator back to a clone of itself taken earlier —
    /// `*self = snapshot`, the whole-elaborator undo a speculative declaration
    /// form uses — **keeping the live kernel gate**.
    ///
    /// The pool is the one field a declaration may not restore (with the
    /// replay cursor and the journal, [`ModulePass::roll_back_to`]). Its queue
    /// holds the *module's* outstanding proof obligations, not this
    /// declaration's, and a clone's pool is inline and empty by construction
    /// (`ModulePass`'s `Clone`): assigning one over a live pool drops
    /// every queued verdict on the floor — the join that follows sees no
    /// outcomes, so a rejection already recorded by a worker is never
    /// reported and the serial fallback never runs — and silently leaves the
    /// gate inline for the rest of the module. That is a worker-count-visible
    /// answer, which is exactly what §5.1 forbids.
    ///
    /// The obligations the rolled-back declaration itself queued stay queued.
    /// They are checked against the frozen Ψ prefixes they were submitted
    /// with, so checking them is sound; if one fails, the module takes the
    /// ordinary discard-and-replay path and the caller sees the serial
    /// answer, which is the contract.
    pub(crate) fn restore_from_clone(&mut self, snapshot: Self) {
        // Every group but the module pass is the snapshot's; the module pass
        // decides field by field (`ModulePass::roll_back_to`). Destructured,
        // so that a new group has to say which it is.
        let Elaborator { committed, pass, attempt, scope, policy, memos } = snapshot;
        self.committed = committed;
        self.pass.roll_back_to(pass);
        self.attempt = attempt;
        self.scope = scope;
        self.policy = policy;
        self.memos = memos;
    }

    /// Wait for every queued proof obligation and report the first failure in
    /// declaration order.
    ///
    /// Called at the end of both module paths, before either returns, so that
    /// nothing downstream — an accepted verdict, a published image, a written
    /// executable — can observe a module whose proofs are still in flight
    /// (`docs/parallel-kernel-gate-design.md` §5). Idempotent: with nothing
    /// outstanding it is a branch.
    ///
    /// **A failing join vouches for nothing.** The pass that queued these
    /// items is about to be discarded and re-run serially (§5.1), so recording
    /// a verdict for its prefix would record a verdict the serial run is going
    /// to record again — against a different Ψ, and without the caller ever
    /// having seen the parallel pass's registrations. Verdicts are replayed
    /// only when every queued check passed, which is exactly when the parallel
    /// pass is the one the caller keeps.
    pub fn join_kernel_gate(&mut self) -> Option<ElabError> {
        let waited = std::time::Instant::now();
        let outcomes = self.pass.kernel_pool.join();
        if outcomes.is_empty() {
            return None;
        }
        // The wall this thread really spent blocked is what the *enclosing*
        // scopes are charged; the workers' own clocks go to their declaration
        // rows below (`docs/parallel-kernel-gate-design.md` §7).
        stats::add(stats::Timer::KernelGate, waited.elapsed().as_nanos() as u64);
        let mut failure = None;
        for outcome in &outcomes {
            // Attribution first, and for every item: a failing module's table
            // is the one worth having (`--timings` is written before the
            // failure is reported).
            stats::fold_deferred_kernel(
                outcome.item.row.as_ref(),
                outcome.ns,
                &outcome.kernel,
            );
            if failure.is_some() {
                continue;
            }
            if let Err(err) = &outcome.verdict {
                let item = outcome.item.as_ref();
                failure = Some(match err {
                    Some(err) => ElabError::Kernel {
                        decl: item.name.clone(),
                        span: item.span,
                        err: *err,
                        note: None,
                        site: KernelSite::Other,
                    },
                    None => ElabError::Elab {
                        msg: format!("the kernel worker checking `{}` panicked", item.name),
                        span: item.span,
                    },
                });
            }
        }
        if failure.is_some() {
            // The pass that queued these is about to be discarded and replayed
            // serially (§5.1). Its verdicts are not (§5.2): every one of
            // them is the kernel's answer for a (Ψ prefix, binding) pair, and
            // the replay reproduces those pairs exactly until the
            // declaration this failure names. Keeping them is what makes a
            // rejected module cost one kernel pass rather than two — which is
            // the dev loop's most common module.
            self.pass.kernel_replay.record(pool::Replay::record(&outcomes));
            return failure;
        }
        if let Some(g) = self.policy.gate.as_ref() {
            for outcome in &outcomes {
                let item = outcome.item.as_ref();
                g.accepted(
                    &item.psi,
                    &gate::GateItem {
                        name: &item.name,
                        ctx: &item.ctx,
                        ty: &item.ty,
                        level: &item.level,
                        body: &item.body,
                        opaque: item.opaque,
                        layer: item.layer,
                        lands_in_psi: item.lands_in_psi,
                    },
                    &outcome.unsealed,
                );
            }
        }
        self.charge_deferred_unseals(&outcomes);
        None
    }

    /// Charge the sealed proofs the pool's checks opened to the items that
    /// queued them, once the module's slices are built
    /// (`ModuleJournal::deferred_unseals`).
    fn charge_deferred_unseals(&self, outcomes: &[pool::Outcome]) {
        if let Some(journal) = self.pass.module_journal.borrow_mut().as_mut() {
            for outcome in outcomes.iter().filter(|o| !o.unsealed.is_empty()) {
                journal.deferred_unseals.push((outcome.item.psi.bindings.len(), outcome.unsealed.clone()));
            }
        }
    }

    /// Queue one proof obligation, or run it here when the pool is inline.
    /// The statement has already been checked and the binding is about to be
    /// (or has just been) committed.
    pub(crate) fn defer_kernel_term(
        &mut self,
        name: &str,
        span: Span,
        ctx: &LocalCtx,
        ty: &Type,
        level: &Level,
        body: &Term,
        opaque: bool,
        layer: Layer,
        lands_in_psi: bool,
        unsealed: Vec<usize>,
    ) {
        stats::count(stats::Counter::DeclsGated);
        self.pass.kernel_pool.submit(pool::Deferred {
            name: name.to_string(),
            span,
            psi: Rc::clone(&self.psi.0),
            ctx: ctx.clone(),
            ty: ty.clone(),
            level: level.clone(),
            body: body.clone(),
            opaque,
            layer,
            lands_in_psi,
            fuel: self.policy.fuel,
            unsealed,
            row: stats::current_item(),
        });
    }

    /// Whether the kernel gate runs inline on this thread. False only when a
    /// worker pool is configured *and* nothing else forces the serial path:
    /// the `value-metrics` collector is an `Rc` this elaborator owns and the
    /// profiled checker entry points want, so enabling it pins the gate here.
    pub(crate) fn gate_is_inline(&self) -> bool {
        self.pass.kernel_pool.is_inline() || self.policy.value_metrics.is_some()
    }

    /// Select project-local source conventions without changing what syntax
    /// the language accepts. Intended for drivers before they check a module.
    pub fn set_lint_profile(&mut self, profile: LintProfile) {
        self.policy.lint_profile = profile;
    }

    /// Turn on the review-mode lints — today `redundant-match-motive`, whose
    /// recognizer re-elaborates and kernel-checks every written motive, and
    /// `recursion-meaning`, which states and gates one unfolding equation per
    /// structurally recursive `fn` (`meaning.rs`). Off by default; `heather
    /// check --review` sets it.
    pub fn set_review_lints(&mut self, on: bool) {
        self.policy.review_lints = on;
    }

    /// Keep every theorem's proof from here on, for an exporter
    /// (`docs/export-fragment-design.md` §1). Off by default: an ordinary
    /// check drops a proof whose statement carries no data.
    pub fn keep_proofs_for_export(&mut self) {
        self.pass.export_proofs.get_or_insert_with(Default::default);
    }

    /// The proof of the theorem at absolute Ψ index `abs`, if
    /// [`Self::keep_proofs_for_export`] was on when it committed.
    pub fn export_proof(&self, abs: usize) -> Option<&Rc<Term>> {
        let (stmt, proof) = self.pass.export_proofs.as_ref()?.get(&abs)?;
        match self.psi.bindings.get(abs)? {
            GlobalBinding::Tm { ty, body: None, .. } if ty == stmt => Some(proof),
            _ => None,
        }
    }

    /// The module-qualified name of the declaration at absolute Ψ index
    /// `abs` (`std::nat::Nat::add`), or `None` for a binding no name
    /// resolves to: a lifted tactic proof, a generated intermediate.
    pub fn global_key_at(&self, abs: usize) -> Option<&str> {
        self.names.global_name_at(abs as u32)
    }

    /// The machine name of the generated definition at `abs`
    /// (`logic::And#tycode_fn`), qualified by its owner's module: what an
    /// exporter names a binding no declaration committed.
    pub fn generated_key_at(&self, abs: usize) -> Option<String> {
        let key = self.types.gdefs().key_for_abs(&(abs as u32))?;
        let owner = self.types.by_tag(key.tag())?;
        Some(names::qkey(&owner.scope.module, &key.name(&owner.name)))
    }

    /// The constructor names of the nominal type with tag `tag`, in
    /// declaration order: what an exporter calls a native inductive's
    /// constructors.
    pub fn constructor_names(&self, tag: u32) -> Option<Vec<String>> {
        Some(self.types.by_tag(tag)?.ctors.iter().map(|c| c.name.clone()).collect())
    }

    /// Begin aggregating value-machine allocation and cache activity across
    /// kernel gates and in-language analyzer evaluation.
    pub fn enable_value_metrics(&mut self) {
        let metrics = Rc::new(ValueMetrics::default());
        // Scope rows carry the value-machine columns too, so the registry
        // needs to be able to read the collector this elaborator installed
        // (`docs/instrumentation-design.md` §3).
        stats::set_value_metrics_source(Some((*metrics).clone()));
        self.policy.value_metrics = Some(metrics);
    }

    /// Reset the active collector without changing whether instrumentation is
    /// enabled. Useful for measuring one source fragment after its imports;
    /// call only between checks, when no profiled arena is still active.
    /// The typing seam's conversion-miss table, heaviest bucket first
    /// (`ValueMetrics::conv_miss_report`). Empty unless the `value-metrics`
    /// feature is on and metrics were enabled.
    pub fn value_conv_miss_report(&self) -> Option<String> {
        self.policy.value_metrics.as_deref().map(ValueMetrics::conv_miss_report)
    }

    pub fn reset_value_metrics(&self) {
        if let Some(metrics) = &self.policy.value_metrics {
            metrics.reset();
        }
    }

    pub fn value_metrics(&self) -> Option<ValueMetricsSnapshot> {
        self.policy.value_metrics
            .as_ref()
            .map(|metrics| metrics.snapshot())
    }

    /// Begin collecting scope rows — per surface item here, plus whatever
    /// module and run scopes the driver opens
    /// (`docs/instrumentation-design.md` §3). Collection is per *thread*, not
    /// per elaborator: a caller measures the elaborator it drives on its own
    /// thread and nothing else.
    pub fn enable_item_timings(&mut self) {
        stats::enable();
    }

    /// Drain the collected rows without disabling collection.
    pub fn take_item_timings(&self) -> Vec<ItemTiming> {
        stats::take_rows()
    }

    /// Begin auditing every emitted annotation slot against the chokepoint
    /// (`emission_walk`; docs/annotation-component-respell-design.md §2.5).
    /// Each checked declaration is walked once more, so this is a debugging
    /// and test-time switch, not a default.
    pub fn enable_emission_walk(&mut self) {
        self.policy.emission_findings = Some(Rc::new(RefCell::new(Vec::new())));
    }

    /// Re-open the gap `OwedChecks` closed (#168): an inferred argument's
    /// comparison with its parameter is recorded by nobody, as before that
    /// round. A **test-time switch** and nothing else — it exists so the
    /// safety net under every such gap, the kernel's locator
    /// ([`KernelSite::Unrecorded`], issues/elab-accepts-conjunction-for-equation.md),
    /// can be tested against a real one rather than a constructed refusal.
    #[doc(hidden)]
    pub fn forget_owed_argument_checks(&mut self) {
        self.policy.owed_checks_forgotten = true;
    }

    /// Lower every recursive `fn` structurally, without asking the planner
    /// whether that means its source. Test-time only: it reproduces the
    /// planner's past misses (issues/recursion-let-reads-changing-parameter.md,
    /// the varied branch of #389) so the meaning check
    /// (issues/recursion-meaning-check.md) can be tested against real
    /// miscompiles rather than constructed ones.
    #[doc(hidden)]
    pub fn skip_recursion_plan(&mut self) {
        self.policy.recursion_plan_skipped = true;
    }

    /// Drain emission-slot findings without disabling the walk.
    pub fn take_emission_findings(&self) -> Vec<EmissionFinding> {
        self.policy.emission_findings
            .as_ref()
            .map_or_else(Vec::new, |f| f.borrow_mut().drain(..).collect())
    }

    pub(crate) fn record_omega_failure_report(&self, report: OmegaReport) {
        self.pass.omega_failure_reports.borrow_mut().push(report);
    }

    /// Drain audit reports for successfully reconstructed `omega` uses.
    pub fn take_omega_reports(&self) -> Vec<OmegaReport> {
        self.pass.omega_reports.borrow_mut().drain(..).collect()
    }

    /// Drain structured reports for exhausted `omega` attempts. These survive
    /// the failed declaration's ordinary transactional rollback.
    pub fn take_omega_failure_reports(&self) -> Vec<OmegaReport> {
        self.pass.omega_failure_reports.borrow_mut().drain(..).collect()
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
        match self.policy.value_metrics.as_deref() {
            Some(metrics) => {
                typing::check_type_profiled(psi, 0, layer, gamma, ty, level, self.policy.fuel, metrics)
            }
            None => typing::check_type(psi, 0, layer, gamma, ty, level, self.policy.fuel),
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
        match self.policy.value_metrics.as_deref() {
            Some(metrics) => typing::check_term_profiled(
                psi, 0, layer, gamma, term, ty, level, self.policy.fuel, metrics,
            ),
            None => typing::check_term(psi, 0, layer, gamma, term, ty, level, self.policy.fuel),
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
        // The prelude is elaborated on every fresh elaborator, in tests and in
        // shipping code alike, and nothing said how much that cost
        // (`issues/prelude-clone-cost-grew.md`).
        let _prelude = stats::guard(stats::Timer::Prelude);
        e.elab_module_source(PRELUDE_MODULE, PRELUDE)?;
        Ok(e)
    }

    /// [`Self::with_prelude`] with [`Self::keep_proofs_for_export`] on from
    /// the start, so the prelude's own theorems keep their proofs too.
    pub fn with_prelude_for_export() -> R<Self> {
        let mut e = Self::new();
        e.keep_proofs_for_export();
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
    /// What one container's item loop needs before it starts: the mutual
    /// groups of `docs/mutual-recursion-design.md` §1, and the declaration
    /// names §8's forward-reference message reads.
    fn begin_container(&mut self, file: &heather_syntax::File) -> ItemPlan {
        let mut groups = measure_groups(&file.items);
        let mut kinds = vec![GroupKind::Measure; groups.len()];
        // Mutual `inductive` groups (docs/mutual-inductive-design.md §1).
        for g in mutual_family::inductive_groups(&file.items) {
            groups.push(g);
            kinds.push(GroupKind::Inductive);
        }
        // Mutual structural recursion over a mutual family (§6 there): a
        // member is one of this container's groups', or an imported one.
        let local_members: Vec<&str> = groups
            .iter()
            .zip(&kinds)
            .filter(|(_, k)| **k == GroupKind::Inductive)
            .flat_map(|(g, _)| g.iter())
            .filter_map(|&i| match &file.items[i] {
                Item::Inductive(d) => Some(d.name.as_str()),
                _ => None,
            })
            .collect();
        let is_member = |n: &str| local_members.contains(&n) || self.lookup_member(n).is_some();
        let structural = mutual_rec::structural_groups(&file.items, &is_member);
        for g in structural {
            groups.push(g);
            kinds.push(GroupKind::Structural);
        }
        let mut in_group: HashMap<usize, usize> = HashMap::new();
        for (g, members) in groups.iter().enumerate() {
            for &idx in members {
                in_group.insert(idx, g);
            }
        }
        *self.pass.container_decls.borrow_mut() = file
            .items
            .iter()
            .enumerate()
            .filter_map(|(i, it)| match it {
                Item::Decl(d) => {
                    Some((d.name.clone(), d.decreases.is_some(), i))
                }
                Item::Prefixed(p) => Some((p.decl.name.clone(), false, i)),
                _ => None,
            })
            .collect();
        self.pass.container_at.set(0);
        ItemPlan { groups, kinds, in_group }
    }

    /// One item, with a mutual group elaborated at its *first* member and the
    /// rest of the group a no-op (§1).
    fn elab_item_at(
        &mut self,
        file: &heather_syntax::File,
        idx: usize,
        item: &Item,
        plan: &ItemPlan,
    ) -> R<()> {
        self.pass.container_at.set(idx);
        match item {
            Item::Decl(d) => match plan.in_group.get(&idx) {
                Some(&g) if plan.groups[g][0] == idx => {
                    let members: Vec<&Decl> = plan.groups[g]
                        .iter()
                        .map(|&k| match &file.items[k] {
                            Item::Decl(d) => d,
                            _ => unreachable!("a group holds declarations"),
                        })
                        .collect();
                    match plan.kinds[g] {
                        GroupKind::Structural => {
                            self.session_transaction(|me| me.elab_structural_group(&members))
                        }
                        _ => self.session_transaction(|me| me.elab_measure_group(&members)),
                    }
                }
                Some(_) => Ok(()),
                None => self.elab_decl(d),
            },
            // The declaration forms that are not a `fn`: each lowers to a
            // family of generated definitions. `gendefs` already times
            // *pushing* one; this brackets the lowering that builds them, so
            // an `inductive`'s or an `instance`'s own work has a column
            // instead of landing in `other`
            // (`docs/instrumentation-design.md` §5).
            Item::Inductive(i) => match plan.in_group.get(&idx) {
                Some(&g) if plan.groups[g][0] == idx => {
                    let members: Vec<&heather_syntax::InductiveDecl> = plan.groups[g]
                        .iter()
                        .map(|&k| match &file.items[k] {
                            Item::Inductive(d) => d,
                            _ => unreachable!("an inductive group holds inductives"),
                        })
                        .collect();
                    stats::timed(stats::Timer::Lower, || {
                        self.session_transaction(|me| me.elab_mutual_inductives(&members))
                    })
                }
                Some(_) => Ok(()),
                None => stats::timed(stats::Timer::Lower, || self.elab_inductive(i)),
            },
            Item::Class(c) => stats::timed(stats::Timer::Lower, || self.elab_class(c)),
            Item::Instance(i) => stats::timed(stats::Timer::Lower, || self.elab_instance(i)),
            Item::Designation(d) => stats::timed(stats::Timer::Lower, || self.elab_designation(d)),
            Item::Datarepr(d) => stats::timed(stats::Timer::Lower, || self.elab_datarepr(d)),
            Item::Impl(i) => stats::timed(stats::Timer::Lower, || self.elab_impl(i)),
            Item::Generate(g) => self.elab_generate(g),
            Item::Prefixed(p) => self.elab_prefixed(p),
            Item::Import(_) => Ok(()),
        }
    }

    /// Elaborate a module, kernel-checking every declaration.
    ///
    /// A module's answer never depends on the worker count
    /// (`docs/parallel-kernel-gate-design.md` §5.1): the parallel pass is an
    /// accelerator for modules that are *accepted*, and any deferred failure
    /// discards it whole and re-runs the module serially, so what the caller
    /// receives is what the serial gate would have said — the same error, at
    /// the same declaration, with the same notes, over the same Ψ.
    pub fn elab_module_source(&mut self, module: &str, src: &str) -> R<()> {
        let mut deferred_failed = false;
        if self.gate_is_inline() {
            return self.elab_module_pass(module, src, &mut deferred_failed);
        }
        self.pass.kernel_replay.clear();
        let mark = self.module_pass_checkpoint();
        let parallel = self.elab_module_pass(module, src, &mut deferred_failed);
        if !deferred_failed {
            return parallel;
        }
        self.restore_module_pass(mark);
        self.serially(|me| me.elab_module_pass(module, src, &mut false))
    }

    /// Run `f` with the kernel gate inline, restoring the configured width
    /// afterwards. The pool is quiescent at both ends: the fallback is entered
    /// only after a join, and the inline pass queues nothing.
    fn serially<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let width = self.pass.kernel_pool.workers();
        self.pass.kernel_pool.set_workers(1);
        // The discarded pass's verdicts become answerable exactly here, for
        // exactly this pass (§5.2).
        self.pass.kernel_replay.arm();
        let out = f(self);
        self.pass.kernel_replay.finish();
        self.pass.kernel_pool.set_workers(width);
        out
    }

    /// One pass over a module's items at whatever width the pool is set to.
    /// `deferred_failed` is set when a *queued* proof was rejected or its
    /// worker panicked — the one outcome a parallel pass can reach that the
    /// serial gate could not, and therefore the one that costs a replay.
    fn elab_module_pass(
        &mut self,
        module: &str,
        src: &str,
        deferred_failed: &mut bool,
    ) -> R<()> {
        // Parse time is its own column: it is not elaboration, and a frontend
        // regression in one is not a regression in the other
        // (`docs/instrumentation-design.md` §5).
        let file = stats::timed(stats::Timer::Parse, || parse_file(src))?;
        let lint_source = lint::Source::new(src, self.policy.lint_profile);
        self.enter_module(module, &file)?;
        self.slice_enter(module);
        let plan = self.begin_container(&file);
        for (idx, item) in file.items.iter().enumerate() {
            let name = item_timing_name(item);
            let _item = stats::scope(stats::ScopeKind::Item, module, &name);
            // The miss sampler's item column
            // (issues/conv-miss-sampler-item-attribution.md): every
            // conversion miss the kernel records until the item ends is
            // charged to this declaration. A no-op without `value-metrics`.
            #[cfg(feature = "value-metrics")]
            if let Some(metrics) = &self.value_metrics {
                metrics.set_current_item(Some(Rc::from(name.as_str())));
            }
            let slice_source = slice_source(&file, src, idx, &plan);
            let slice_start = lint::item_span(item).start;
            let slice_mark = self.slice_begin();
            // Every sealed proof the item opens, here or in its kernel
            // checks, is charged to its slice (`issues/theorem-witness-unfolding.md`).
            let unsealing = heather_kernel::unseal::Recording::start();
            // `--only` names items that elaborate from source however exact
            // the prefix is (`docs/check-only-design.md`); a group is named
            // through any member.
            let forced = self.slice_forced(&slice_names(&file, idx, &plan));
            // A replayed slice carries the item's warnings, source lints
            // included: nothing is re-run over it.
            if !forced && self.try_replay_slice(idx, &slice_source, slice_start) {
                if let Some(mark) = slice_mark {
                    self.slice_end(mark, slice_source, slice_start, true, unsealing.finish());
                }
                continue;
            }
            let warn_mark = self.pass.warnings.borrow().len();
            let omega_mark = self.pass.omega_reports.borrow().len();
            let r = self.elab_item_at(&file, idx, item, &plan);
            // Canonical derived instances are minted **between** items, where
            // Ψ may grow (docs/traits-layer2-design.md §8). A failed item
            // mints nothing: its derivations are as speculative as the rest of
            // it.
            if r.is_err() {
                self.pass.pending_derived.borrow_mut().clear();
                self.pass.warnings.borrow_mut().truncate(warn_mark);
                self.pass.omega_reports.borrow_mut().truncate(omega_mark);
            } else {
                self.mint_pending();
                stats::timed(stats::Timer::Lint, || self.run_source_lints(item, &lint_source));
                if let Some(mark) = slice_mark {
                    self.slice_elaborated();
                    self.slice_end(mark, slice_source, slice_start, false, unsealing.finish());
                }
            }
            #[cfg(feature = "value-metrics")]
            if let Some(metrics) = &self.value_metrics {
                metrics.set_current_item(None);
            }
            if r.is_err() {
                self.pass.container_decls.borrow_mut().clear();
                if let Some(g) = self.policy.gate.as_ref() {
                    g.abandon(&self.psi);
                }
                // Nothing may outlive the module with proofs in flight, the
                // failure path included (`docs/parallel-kernel-gate-design.md`
                // §5). The item's own error is the one reported — unless a
                // queued proof also failed, in which case this whole pass is
                // discarded and replayed serially, and the error the caller
                // sees is the replay's.
                if self.join_kernel_gate().is_some() {
                    *deferred_failed = true;
                }
            }
            r?;
            // The early abort (§5.1): a queued proof has already failed, so
            // the rest of this pass is work the replay will do again. Stop
            // here and let the join report it.
            if self.pass.kernel_pool.poll_failed() {
                break;
            }
        }
        self.pass.container_decls.borrow_mut().clear();
        // The join, before this returns and therefore before any caller can
        // publish an image, record a verdict, or write an executable.
        match self.join_kernel_gate() {
            Some(e) => {
                *deferred_failed = true;
                Err(e)
            }
            None => Ok(()),
        }
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
        let mut scope = self
            .names
            .module_scope(module)
            .cloned()
            .unwrap_or_else(|| Scope::new(module));
        let mut written: Vec<(&str, bool)> = Vec::new();
        for item in &file.items {
            let Item::Import(imp) = item else { continue };
            if imp.module == module {
                return err(
                    format!("a module cannot import itself (`{module}`)"),
                    imp.span,
                );
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
            if written.contains(&(imp.module.as_str(), imp.reexport)) {
                return err(format!("`{}` is imported twice", imp.module), imp.span);
            }
            written.push((&imp.module, imp.reexport));
            let mut exported = Vec::new();
            for (n, nspan) in &imp.listed {
                if imp.reexport && let Some(why) = self.access_refusal(n) {
                    return err(why, *nspan);
                }
                if !self.names.declares(&imp.module, n) {
                    return err(format!("`{}` declares no `{n}`", imp.module), *nspan);
                }
                if let Some(other) = scope
                    .imports
                    .iter()
                    .find(|i| i.module != imp.module && i.listed.iter().any(|l| l == n)
                        && self.names.origin(&i.module, n) != self.names.origin(&imp.module, n))
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
                if imp.reexport {
                    exported.push(n.clone());
                    // Selecting a type also exposes its constructors. Methods and
                    // instances remain explicit selections (including qualified names).
                    if let Some(origin) = self.names.origin(&imp.module, n)
                        && let Some(ind) = self.types.inductive(&qkey(origin, n))
                    {
                        for ctor in &ind.ctors {
                            if self.names.declares(&imp.module, &ctor.name)
                                && !exported.contains(&ctor.name) {
                                exported.push(ctor.name.clone());
                            }
                        }
                    }
                }
            }
            for name in &exported {
                let origin = self.names.origin(&imp.module, name);
                if self.names.declares(module, name) && self.names.origin(module, name) != origin {
                    return err(format!("reexport `{name}` conflicts with a declaration in `{module}`"), imp.span);
                }
                for previous in &scope.imports {
                    if previous.exported.contains(name) && self.names.origin(&previous.module, name) != origin {
                        return err(format!("reexport `{name}` conflicts between `{}` and `{}`", previous.module, imp.module), imp.span);
                    }
                }
            }
            let listed: Vec<String> = imp.listed.iter().map(|(n, _)| n.clone()).collect();
            match scope.imports.iter_mut().find(|i| i.module == imp.module) {
                Some(existing) => { existing.listed.extend(listed); existing.exported.extend(exported); },
                None => scope.imports.push(ImportSpec {
                    module: imp.module.clone(),
                    listed,
                    exported,
                }),
            }
        }
        // The common prelude, implicitly, when it is already in this world:
        // the modules it exports from are elaborated before it and so never
        // import it, and every later module's closure holds it, as the
        // loader and the image keys add it (issues/std-prelude-facade.md).
        if module != COMMON_MODULE
            && self.names.has_module(COMMON_MODULE)
            && scope.imports.iter().all(|i| i.module != COMMON_MODULE)
        {
            scope.imports.push(ImportSpec {
                module: COMMON_MODULE.to_string(),
                listed: Vec::new(),
                exported: Vec::new(),
            });
        }
        self.names.enter_scope(scope);
        // The interface boundary is per module: the definitions this module
        // declares are transparent in it, every other module's are withheld.
        if !self.interfaces.is_empty() {
            self.refresh_delta_psi();
        }
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
        // An unfolding equation the walk declined to generate: say which body
        // shape stopped it (docs/decreases-unfolding-design.md §3), since
        // "unknown name" is the wrong thing to say about an equation the
        // reader is right to expect.
        if let Some(why) = self.pass.unfold_refusals.borrow().get(name) {
            // A reason that already names the document that explains it — a
            // group's, `docs/mutual-recursion-design.md` §6 — points there
            // instead.
            let see = if why.contains("docs/") {
                ""
            } else {
                ", see docs/decreases-unfolding-design.md §3"
            };
            return NameRes::Restricted(format!(
                "no unfolding equation for `{}`: {why}{see}",
                name.strip_suffix("_unfold").unwrap_or(name)
            ));
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
        let scopes = self.scope.resolution_scopes.borrow();
        // Omega's generated certificate may explicitly name its library
        // dependencies. This overlay applies to this qualified lookup only:
        // it neither opens bare names nor changes the caller's saved imports.
        if (self.scope.omega_depth.get() > 0 || self.scope.ring_depth.get() > 0)
            && let Some((module, base)) = split_qual(name)
            && matches!(module, "omega" | "nat" | "int" | "logic" | "list" | "ring" | "linarith")
            && self.names.declares(module, base)
        {
            return NameRes::Found(module.to_string());
        }
        if self.scope.rule_citation.borrow().as_deref() == Some(name)
            && let Some((module, base)) = split_qual(name)
            && self.names.declares(module, base)
            && (self.names.module() == module || self.names.scope().imports_module(module))
        {
            return NameRes::Found(module.to_string());
        }
        self.names
            .resolve_kinds(scopes.last().map(Rc::as_ref), name, kinds, |m, ty, ctor| {
                self.types
                    .inductive(&qkey(m, ty))
                    .is_some_and(|i| i.ctors.iter().any(|c| c.name == ctor))
            })
    }

    /// Run reflection or generation with names resolved as if read in a
    /// checked module. Bare names follow that module's imports and ambiguity
    /// rules; qualification still requires visibility there. The scope is
    /// restored on return (including an error or panic), and calls may nest.
    /// This read-only context does not change the checked global environment.
    pub fn with_module_scope<T>(
        &self, module: &str, read: impl FnOnce(&Self) -> T,
    ) -> Result<T, String> {
        let scope = self.names.module_scope(module)
            .ok_or_else(|| format!("unknown checked module `{module}`"))?;
        self.scope.resolution_scopes.borrow_mut().push(Rc::new(scope.clone()));
        let _guard = ResolutionScope { stack: &self.scope.resolution_scopes };
        Ok(read(self))
    }

    /// Install the declaration scope for one read of stored inductive syntax.
    /// The guard restores the caller's scope on every return path.
    fn use_inductive_scope<'a>(&'a self, ind: &inductive::Inductive) -> ResolutionScope<'a> {
        self.scope.resolution_scopes
            .borrow_mut()
            .push(Rc::clone(&ind.scope));
        ResolutionScope {
            stack: &self.scope.resolution_scopes,
        }
    }

    /// The base half of a written name — `nat::Nat::sub` and `sub` both name `sub`.
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

    /// [`recursion::elab_self_call`], with a refusal *of the call* — one at
    /// the call itself or one naming the callee, not an error inside an
    /// argument that happens to surface here — noted with the global the
    /// written name hides ([`Self::self_shadow_note`]).
    fn self_call_noted(&self, cx: &Cx, written: &str, args: &[Expr], explicit: bool, span: Span) -> R<(Term, Type, Level)> {
        recursion::elab_self_call(self, cx, args, explicit, span).map_err(|e| {
            let ElabError::Elab { msg, span: at } = &e else { return e };
            let selfref = cx.selfref.as_ref().expect("a self-call has a self-reference");
            if *at != span && !msg.contains(&format!("`{}`", selfref.name)) {
                return e;
            }
            let note = self.self_shadow_note(selfref, written);
            with_self_shadow_note(e, note.as_deref())
        })
    }

    /// Inside a member `T::name`, the bare `name` is the member's own
    /// self-reference, checked before any global, so a top-level `name` is
    /// hidden there. When `written` is that bare spelling and a declaration
    /// of the name does resolve outside the member, the note naming it and
    /// the qualified spelling that reaches it
    /// (issues/self-reference-hides-same-named-global.md). `None` for a
    /// non-member, the qualified spelling, or a name nothing else declares.
    fn self_shadow_note(&self, selfref: &SelfRef, written: &str) -> Option<String> {
        if selfref.name == selfref.written_name || written != selfref.name {
            return None;
        }
        let key = self.key_of(self.instance_alias(written))?;
        if key == selfref.written_name || key.ends_with(&format!("::{}", selfref.written_name)) {
            return None;
        }
        // The module-qualified spelling, offered only when it reaches the
        // same declaration from here.
        let reach = split_qual(&key)
            .map(|(module, _)| qkey(module, written))
            .filter(|spelling| self.key_of(spelling).as_deref() == Some(key.as_str()));
        let member = &selfref.written_name;
        let hides = format!(
            "note: inside the member `{member}`, the bare name `{written}` is `{member}` itself \
             (its self-reference), which hides the declaration `{key}`"
        );
        Some(match reach {
            Some(spelling) => format!("{hides}; write `{spelling}` to reach it"),
            None => hides,
        })
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
        if let Some(target) = self.access_alias(name) {
            return self.key_of_declared_kinds(target, kinds);
        }
        // A designed path under its module's name, `m::f::rec`: `m`'s own
        // `f::rec`, as `m::f` is `m`'s `f`.
        let (module, path) = name.split_once("::")?;
        let target = self.access_alias(path)?;
        self.key_of_declared_kinds(&format!("{module}::{target}"), kinds)
    }

    fn key_of_declared_kinds(&self, name: &str, kinds: &[NameKind]) -> Option<String> {
        match self.resolve_declared_kinds(name, kinds) {
            NameRes::Found(m) => {
                // A *member* declares the qualified string itself
                // (issues/type-owned-members-receiver-slice.md), so its key
                // keeps both halves: `List::nth` in module `list` is
                // `list::List::nth`. The two other qualified readings —
                // `nat::Nat::sub` (module path) and `Option::None` (constructor by
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

    /// Inside a member of `T` (`fn T::f`), a bare name may name `T`'s other
    /// members: `cong_cons` for `List::cong_cons` inside `List::append_assoc`
    /// (docs/sections-design.md §6). The member joins the candidate set with
    /// the same rank as every other reading, so when the bare name also
    /// resolves on its own the two are ambiguous (`Err`, the message): a
    /// precedence either way would let a library's growth reinterpret checked
    /// text (docs/modules-design.md §8). Only a declared member counts, never
    /// the constructor reading of `T::C`. It is consulted only where a written
    /// expression enters elaboration ([`Self::owner_rewrite`]), so the
    /// elaborator's own lookups of library names, and receiver dispatch's
    /// ambient readings, are untouched.
    fn owner_member(&self, name: &str) -> Result<Option<String>, String> {
        let Some(owner) = self.scope.member_owner.as_deref() else { return Ok(None) };
        if name.contains("::") || self.scope.instance_scope.iter().any(|(base, _)| base == name) {
            return Ok(None);
        }
        let full = format!("{owner}::{name}");
        let NameRes::Found(m) = self.resolve_declared(&full) else { return Ok(None) };
        if !self.names.declares(&m, &full) {
            return Ok(None);
        }
        match self.resolve_declared(name) {
            NameRes::NotFound | NameRes::NoSuchQualifier(_) | NameRes::Restricted(_) => Ok(Some(full)),
            NameRes::Found(other) => Err(format!(
                "`{name}` is ambiguous here: inside a member of `{owner}` it can name \
                 `{owner}::{name}` (`{m}`) or `{name}` (`{other}`). Write `{owner}::{name}` \
                 for the member, or qualify the other (`{other}::{name}`) \
                 (docs/sections-design.md §6)"
            )),
            NameRes::Ambiguous(origins) => Err(format!(
                "`{name}` is ambiguous here: inside a member of `{owner}` it can name \
                 `{owner}::{name}` (`{m}`), and it is also declared in {}. Qualify it \
                 (docs/sections-design.md §6)",
                origins.iter().map(|o| format!("`{o}`")).collect::<Vec<_>>().join(" and ")
            )),
        }
    }

    /// A bare written name, or the bare head of a written call, that names a
    /// sibling member ([`Self::owner_member`]) is rewritten to its qualified
    /// spelling before the expression is elaborated, so every route after it
    /// (implicit masks, receivers, deferral) sees the declaration's own name.
    /// Locals, aliases and the declaration's own name shadow it, as they
    /// shadow every global.
    fn owner_rewrite(&self, cx: &Cx, e: &Expr) -> R<Option<Expr>> {
        if self.scope.member_owner.is_none() {
            return Ok(None);
        }
        let (name, span) = match &e.kind {
            ExprKind::Var(n) => (n, e.span),
            ExprKind::App { head, .. } => match &head.kind {
                ExprKind::Var(n) => (n, head.span),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        if cx.names.iter_inner().any(|n| n == name)
            || cx.aliases.iter_inner().any(|a| a.name == *name)
            || cx.selfref.as_ref().is_some_and(|s| s.matches(name))
        {
            return Ok(None);
        }
        let full = match self.owner_member(name) {
            Ok(Some(full)) => full,
            Ok(None) => return Ok(None),
            Err(msg) => return err(msg, span),
        };
        let mut out = e.clone();
        match &mut out.kind {
            ExprKind::Var(n) => *n = full,
            ExprKind::App { head, .. } => head.kind = ExprKind::Var(full),
            _ => unreachable!(),
        }
        Ok(Some(out))
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
        if self.scope.instance_scope.is_empty() {
            return name;
        }
        match self
            .scope.instance_scope
            .iter()
            .rev()
            .find(|(base, _)| base == name)
        {
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
        self.types
            .inductive(&self.key_of_kinds(name, &[NameKind::Inductive])?)
    }

    /// The mutual group member a name denotes in type position
    /// (docs/mutual-inductive-design.md §2): its family and its position
    /// among the family's members. A member is declared as an `Inductive`
    /// name, so it resolves, shadows and is imported exactly as a type does;
    /// it is found here and not by [`Self::lookup_inductive`] because it has
    /// no declaration of its own.
    pub(crate) fn lookup_member(&self, name: &str) -> Option<(Rc<Inductive>, usize)> {
        self.types
            .member(&self.key_of_kinds(name, &[NameKind::Inductive])?)
            .map(|(i, k)| (Rc::clone(i), *k))
    }

    pub(crate) fn lookup_ctor(&self, name: &str) -> Option<(Rc<Inductive>, usize)> {
        // `Option::None` resolves through the *type*, so the key is the
        // constructor's own name in the type's module.
        let key = self.key_of(name)?;
        self.types
            .constructor(&key)
            .map(|(i, k)| (Rc::clone(i), *k))
    }

    /// The error for a name that did not resolve. An ambiguous name must
    /// never be reported as an unknown one — that is the whole point of the
    /// regime — so every "unknown X" site routes its message through here and
    /// gets overridden when ambiguity is the real reason.
    fn name_miss(&self, name: &str, fallback: impl Into<String>, span: Span) -> ElabError {
        let res = self.resolve_name(name);
        let mut msg = miss_msg(&res, name, fallback.into())
            .unwrap_or_else(|| format!("`{name}` cannot be used here"));
        // §8 of `docs/mutual-recursion-design.md`: a member whose run was
        // broken forward-references a name that *is* declared, further down.
        // "unknown" is true and unhelpful; say what would have grouped them.
        let later = self
            .pass.container_decls
            .borrow()
            .iter()
            .find(|(n, _, i)| n == name && *i > self.pass.container_at.get())
            .map(|(_, d, _)| *d);
        if matches!(res, NameRes::NotFound)
            && let Some(measured) = later
        {
            msg.push_str(&format!(". `{name}` is declared below"));
            if measured {
                msg.push_str(
                    "; adjacent `decreases` declarations share one recursion only when \
                     each of them carries `decreases`, nothing else stands between them, \
                     and they call *each other* (docs/mutual-recursion-design.md §1). \
                     A call that is not answered needs the callee declared first",
                );
            }
        }
        ElabError::Elab { msg, span }
    }

    /// Is `name` declared in the module being elaborated, as one of `kinds`?
    /// The duplicate-declaration test: a *module* never declares one name
    /// twice, while two modules may.
    fn own_declares(&self, name: &str, kinds: &[NameKind]) -> bool {
        self.names.declares_own(self.names.module(), name, kinds)
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
        self.semantic_commit_name(name, kind);
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
        std::mem::take(&mut self.pass.warnings.borrow_mut())
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
        let mut warnings = self.pass.warnings.borrow_mut();
        if warnings.iter().any(|w| w.lint == lint && w.span == span) {
            return;
        }
        warnings.push(Warning {
            lint,
            msg: msg.into(),
            span,
            fix,
        });
    }

    fn run_source_lints(&self, item: &Item, source: &lint::Source<'_>) {
        for warning in self
            .pass.warnings
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
                && self.pass.warnings.borrow().iter().any(|w| {
                    w.lint == Lint::UnreachableMatchArm
                        && w.span.start <= finding.span.start
                        && finding.span.end <= w.span.end
                })
            {
                continue;
            }
            if !self.in_generated() {
                self.pass.warnings.borrow_mut().push(Warning {
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
        self.check_module_source_inner(module, src)
    }

    pub(crate) fn check_module_source_inner(&mut self, module: &str, src: &str) -> Vec<ElabError> {
        let mut deferred_failed = false;
        if self.gate_is_inline() {
            return self.check_module_pass(module, src, &mut deferred_failed);
        }
        self.pass.kernel_replay.clear();
        let mark = self.module_pass_checkpoint();
        let parallel = self.check_module_pass(module, src, &mut deferred_failed);
        if !deferred_failed {
            return parallel;
        }
        // §5.1: the recovery contract — report every bad declaration, keep
        // checking the good ones — is a *serial* statement about declaration
        // order, and a deferred rejection arrives out of that order and after
        // its declaration has already been committed to Ψ. So the pass is
        // discarded whole, down to the last registration and warning, and the
        // module is re-checked serially. The caller sees the serial answer.
        self.restore_module_pass(mark);
        self.serially(|me| me.check_module_pass(module, src, &mut false))
    }

    fn check_module_pass(
        &mut self,
        module: &str,
        src: &str,
        deferred_failed: &mut bool,
    ) -> Vec<ElabError> {
        let file = match stats::timed(stats::Timer::Parse, || parse_file(src)) {
            Ok(f) => f,
            Err(e) => return vec![e.into()],
        };
        let lint_source = lint::Source::new(src, self.policy.lint_profile);
        if let Err(e) = self.enter_module(module, &file) {
            return vec![e];
        }
        self.slice_enter(module);
        let plan = self.begin_container(&file);
        let mut errs = Vec::new();
        for (idx, item) in file.items.iter().enumerate() {
            let warn_mark = self.pass.warnings.borrow().len();
            let name = item_timing_name(item);
            // The declaration scope, the same bracket as `elab_module_source`
            // — `heather check` is the primary command and had none
            // (`docs/instrumentation-design.md` §5) — carrying the miss
            // sampler's item column with it
            // (issues/conv-miss-sampler-item-attribution.md). A no-op without
            // `value-metrics`, and free without `--timings`.
            let item_scope = stats::scope(stats::ScopeKind::Item, module, &name);
            #[cfg(feature = "value-metrics")]
            if let Some(metrics) = &self.value_metrics {
                metrics.set_current_item(Some(Rc::from(name.as_str())));
            }
            // A slice of the previous delta stands in for the item when its
            // text and the prefix so far match
            // (`docs/declaration-slice-replay-design.md` §4).
            let slice_source = slice_source(&file, src, idx, &plan);
            let slice_start = lint::item_span(item).start;
            let slice_mark = self.slice_begin();
            // Every sealed proof the item opens, here or in its kernel
            // checks, is charged to its slice (`issues/theorem-witness-unfolding.md`).
            let unsealing = heather_kernel::unseal::Recording::start();
            // `--only` names items that elaborate from source however exact
            // the prefix is (`docs/check-only-design.md`); a group is named
            // through any member.
            let forced = self.slice_forced(&slice_names(&file, idx, &plan));
            // A replayed slice carries the item's warnings, source lints
            // included: nothing is re-run over it.
            if !forced && self.try_replay_slice(idx, &slice_source, slice_start) {
                if let Some(mark) = slice_mark {
                    self.slice_end(mark, slice_source, slice_start, true, unsealing.finish());
                }
                #[cfg(feature = "value-metrics")]
                if let Some(metrics) = &self.value_metrics {
                    metrics.set_current_item(None);
                }
                continue;
            }
            let r = self.elab_item_at(&file, idx, item, &plan);
            #[cfg(feature = "value-metrics")]
            if let Some(metrics) = &self.value_metrics {
                metrics.set_current_item(None);
            }
            drop(item_scope);
            if r.is_err() {
                self.pass.pending_derived.borrow_mut().clear();
                // §4: a failed item's warnings are as speculative as the rest
                // of it — it registers nothing, and it says nothing.
                self.pass.warnings.borrow_mut().truncate(warn_mark);
            } else {
                self.mint_pending();
                stats::timed(stats::Timer::Lint, || self.run_source_lints(item, &lint_source));
                if let Some(mark) = slice_mark {
                    self.slice_elaborated();
                    self.slice_end(mark, slice_source, slice_start, false, unsealing.finish());
                }
            }
            if let Err(e) = r {
                errs.push(e);
                // The refused declaration's gate question is dead, and the
                // next declaration lands at the same Ψ length.
                if let Some(g) = self.policy.gate.as_ref() {
                    g.abandon(&self.psi);
                }
            }
            // The early abort (§5.1): this pass is already doomed to be
            // replayed serially, so stop elaborating declarations for it.
            if self.pass.kernel_pool.poll_failed() {
                break;
            }
        }
        self.pass.container_decls.borrow_mut().clear();
        // The join (`docs/parallel-kernel-gate-design.md` §5). This is the
        // path `check_module_delta` runs inside, so the semantic image, the
        // declaration cache and `heather check`'s verdict all sit behind it.
        if let Some(e) = self.join_kernel_gate() {
            *deferred_failed = true;
            errs.push(e);
        }
        errs
    }

    /// The canonical derived instances minted so far, in mint order
    /// (docs/traits-layer2-design.md §8) — one per *derivation*, not per use
    /// site, which is the coherence invariant this table is.
    pub fn derived_instances(&self) -> Vec<&str> {
        self.traits
            .derived()
            .iter()
            .map(|d| d.name.as_str())
            .collect()
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

    /// Whether the global at Ψ position `abs` is a declared assumption: the
    /// kernel binding has a theorem's shape, so only the elaborator knows.
    pub fn is_assumption_at(&self, abs: usize) -> bool {
        u32::try_from(abs)
            .ok()
            .and_then(|abs| self.names.global_name_at(abs))
            .is_some_and(|key| self.provenance.is_axiom(key))
    }

    /// Every non-axiom declaration whose proof or body reaches an axiom.
    /// Sorted by resolved declaration identity.
    pub fn axiom_violations(&self) -> Vec<AxiomReport> {
        self.provenance.tainted()
    }

    /// A declared global's elaborated statement and body, by written name —
    /// what an analyzer's input is read out of (the fn to transcribe is an
    /// ordinary declaration, already checked and in Ψ).
    /// The binding at `abs`'s own world: the Ψ prefix its prefix-scoped
    /// statement and body resolve against.
    fn prefix_world(&self, abs: usize) -> GlobalCtx {
        self.psi.prefix(abs)
    }

    /// `ty`, a statement scoped at binding `abs`, with its checked spellings
    /// in component form, for a `box` (`typing::spell_checked_in_code_ty`).
    fn code_form_ty(&self, abs: usize, ctx: &LocalCtx, ty: Rc<Type>, level: &Level) -> Option<Rc<Type>> {
        if heather_kernel::subst::holds_checked_spelling_ty(&ty) {
            let world = self.prefix_world(abs);
            typing::spell_checked_in_code_ty(&world, 0, Layer::Code, ctx, ty, level, self.policy.fuel).ok()
        } else {
            Some(ty)
        }
    }

    pub(crate) fn global_body(&self, name: &str) -> Option<(Rc<Type>, Rc<Term>)> {
        self.global_body_at(self.lookup_global(name)?.abs as usize)
    }

    /// [`Self::global_body`] by Ψ coordinate.
    pub(crate) fn global_body_at(&self, abs: usize) -> Option<(Rc<Type>, Rc<Term>)> {
        match self.psi.bindings.get(abs)? {
            GlobalBinding::Tm {
                ty,
                body: Some(body),
                ..
            } => Some((Rc::clone(ty), Rc::clone(body))),
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
    ///
    /// By name, this entry is the tests' (`wf.rs`); certgen resolves the name
    /// once and calls [`Self::fn_type_code_at`].
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn fn_type_code(&self, name: &str) -> Option<Term> {
        self.fn_type_code_at(self.lookup_global(name)?.abs as usize)
    }

    /// [`Self::fn_type_code`] by Ψ coordinate, which is how certgen reaches it
    /// once it has resolved the declaration's name.
    pub(crate) fn fn_type_code_at(&self, abs: usize) -> Option<Term> {
        let GlobalBinding::Tm { ctx, ty, level, .. } = self.psi.bindings.get(abs)? else {
            return None;
        };
        // A box payload holds no checked spelling (`docs/intro-by-type-design.md`
        // §2.3), and a statement elaborated outside a quote may: translate it
        // in the binding's own world before rescoping.
        let ty = self.code_form_ty(abs, ctx, Rc::clone(ty), level)?;
        let ty = &ty;
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

    /// A global's binding index by written name — the Ψ coordinate
    /// [`Self::global_name_at`] inverts. Reflection-internal.
    pub(crate) fn global_abs(&self, name: &str) -> Option<usize> {
        Some(self.lookup_global(name)?.abs as usize)
    }

    /// The layer a term binding was bound at, by the name the current module
    /// resolves: `c` for every declaration, codata included
    /// (docs/kernel-m-codes-design.md §0).
    pub fn global_layer(&self, name: &str) -> Option<Layer> {
        match self.psi.bindings.get(self.global_abs(name)?)? {
            GlobalBinding::Tm { layer, .. } => Some(*layer),
            _ => None,
        }
    }

    /// The written (base) name of the binding at absolute Ψ index `abs` —
    /// the reverse of [`Self::global_abs`], for resolving a stored body's
    /// `GlobalVar`s to callee names. The name registry maintains this reverse
    /// index when the declaration commits.
    pub(crate) fn global_name_at(&self, abs: usize) -> Option<String> {
        let key = self.names.global_name_at(abs as u32)?;
        Some(key.rsplit("::").next().unwrap_or(key).to_string())
    }

    /// Does `name`, read where the current context is, resolve back to the
    /// binding at absolute Ψ index `abs`? What a renderer whose output is
    /// re-parsed has to ask before it uses a base name
    /// (issues/omega-renders-member-by-base-name.md).
    pub(crate) fn base_name_resolves_to(&self, name: &str, abs: usize) -> bool {
        self.lookup_global(name).is_some_and(|i| i.abs as usize == abs)
    }

    /// A name as the current module resolves it, qualified: what a producer
    /// asks of a name an author wrote.
    pub fn qualified_global(&self, name: &str) -> Option<String> {
        self.global_qualified_name_at(self.global_abs(name)?)
    }

    /// The canonical qualified spelling of a global. Generated modules use
    /// this rather than [`Self::global_name_at`]'s deliberately presentation-
    /// oriented base name when they refer across a module boundary.
    pub(crate) fn global_qualified_name_at(&self, abs: usize) -> Option<String> {
        Some(self.names.global_name_at(abs as u32)?.to_string())
    }

    /// The **declared** name of the global at `abs`: its qualified key minus
    /// the module, so `nat::Nat::add` gives `Nat::add` and `ir_v1::dbl` gives
    /// `dbl`. The split is [`names::split_qual`]'s, at the first `::`, since
    /// module names are single-segment. What certgen derives its generated
    /// items' stems from (docs/certgen-global-identity-design.md §2).
    pub(crate) fn global_declared_name_at(&self, abs: usize) -> Option<String> {
        let key = self.names.global_name_at(abs as u32)?;
        Some(names::split_qual(key).map_or(key, |(_, d)| d).to_string())
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
            .checked_add(self.global_padding())?
            .checked_add(self.scope.meta_pushed.borrow().len() as u32)?
            .checked_sub(var.0.checked_add(1)?)?;
        Some(abs as usize)
    }

    /// The parameter table of the binding at absolute Ψ index `abs`, empty for
    /// a binding that has none. The by-index companion of [`Self::params_of`].
    pub(crate) fn params_at(&self, abs: usize) -> Rc<Vec<ParamMeta>> {
        self.names
            .params_at(abs as u32)
            .unwrap_or_else(|| Rc::new(Vec::new()))
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
        Some(if ind.iwf_infinitary() {
            IndexedRoute::IwfW
        } else if ind.skel.is_some() {
            IndexedRoute::Iwf
        } else {
            IndexedRoute::One
        })
    }

    // -- declarations -------------------------------------------------------

    /// Elaborate one declaration, always leaving the goal state clean — the
    /// `Elaborator` outlives a declaration (and an `elab_source` call), so a
    /// stale `goal_base` would silently corrupt the next one.
    fn elab_decl(&mut self, decl: &Decl) -> R<()> {
        let owner = decl.name.rsplit_once("::").map(|(owner, _)| owner.to_string());
        self.elab_decl_as(decl, owner)
    }

    /// A declaration an `instance` synthesizes: its qualified name is the
    /// instance's, not a member of a type or function, so its body names no
    /// siblings (docs/sections-design.md §6).
    pub(crate) fn elab_decl_unowned(&mut self, decl: &Decl) -> R<()> {
        self.elab_decl_as(decl, None)
    }

    fn elab_decl_as(&mut self, decl: &Decl, owner: Option<String>) -> R<()> {
        self.scoped(|s| &mut s.member_owner, owner, |me| me.elab_decl_owned(decl))
    }

    fn elab_decl_owned(&mut self, decl: &Decl) -> R<()> {
        // `unfolding f, g`: the declaration sees through these interface
        // definitions, its gate included (docs/interface-definitions-design.md §4).
        if !decl.unfolding.is_empty() {
            let keys = self.unfolding_keys(decl)?;
            let mut inner = decl.clone();
            inner.unfolding.clear();
            self.scope.unfolded.extend(keys.iter().cloned());
            self.refresh_delta_psi();
            let out = self.elab_decl_owned(&inner);
            let keep = self.scope.unfolded.len() - keys.len();
            self.scope.unfolded.truncate(keep);
            self.refresh_delta_psi();
            return out;
        }
        // A `meta fn` is a different declaration form: modal signature,
        // quotation body, `Layer::Meta` check, elaborator-side registration
        // (docs/in-language-map-design.md §3–4).
        if decl.is_meta {
            return self.elab_meta_decl(decl);
        }
        // An `evidence theorem` is an ordinary theorem, registered for
        // `:= infer` once it has passed its gate
        // (docs/positivity-evidence-design.md §6 A).
        if decl.is_evidence {
            self.evidence_shape(decl)?;
            self.elab_decl_one(decl, None)?;
            return self.register_evidence(decl);
        }
        // An `interface fn` is elaborated as the `fn` it is, then registered,
        // with its unfolding equations beside it
        // (docs/interface-definitions-design.md).
        if decl.is_interface {
            self.interface_shape(decl)?;
            let mut plain = decl.clone();
            plain.is_interface = false;
            return self.session_transaction(|me| {
                me.elab_decl_owned(&plain)?;
                let equations = me.interface_equations(decl)?;
                me.register_interface(decl, equations)
            });
        }
        // `decreases e` is not one declaration but a family of them
        // (docs/decreases-unfolding-design.md §2): the arm, the eliminator,
        // the declaration itself, and — for a `fn` whose body the walk of §3
        // handles — the unfolding companions.
        // `for` loops lift into a named step over a fold, and the
        // declaration is the family that results (crates/elab/src/loops.rs).
        // `partial fn` is the family of crates/elab/src/partial.rs: its body
        // over the carrier of its own calls, and `f` as `CoTree::rec` of it.
        if decl.partial.is_some() {
            return self.session_transaction(|me| me.elab_partial_decl(decl));
        }
        if loops::has_loop(decl) {
            return self.session_transaction(|me| me.elab_loop_decl(decl));
        }
        if decl.decreases.is_some() {
            return self.session_transaction(|me| me.elab_measure_decl(decl));
        }
        // A `fn` whose structural lowering would not mean its source is
        // lowered by measure, or refused where that has no unfolding equation
        // either (issues/fn-recursion-means-the-function.md).
        // A `fn` returning codata recurses *guardedly*, not structurally: its
        // self-calls become one `corec` (docs/codata-elaborator-design.md §5),
        // so a `match` reading a parameter is the step's own observation.
        let corecursive = matches!(&decl.result.kind,
            heather_syntax::ast::TyKind::Named { name, .. }
                if self.lookup_inductive(name).is_some_and(|i| i.codata));
        if decl.kind == DeclKind::Fn && !corecursive {
            if self.policy.recursion_plan_skipped {
                return self.elab_structural_fn(decl);
            }
            let self_ref = recursion::SelfRef::of_decl(decl);
            let types: Vec<Option<&Ty>> = decl
                .tyvars
                .iter()
                .map(|_| None)
                .chain(decl.params.iter().map(|p| Some(&p.ty)))
                .collect();
            match recursion::plan(&self_ref, &types, &decl.body) {
                recursion::RecursionPlan::Structural => {}
                recursion::RecursionPlan::ByMeasure { dec, read, name, from } => {
                    return self.elab_recursion_by_measure(decl, &self_ref, dec, read, &name, from);
                }
                recursion::RecursionPlan::Misplaced { dec, msg } => {
                    let misplaced = Some((self_ref.name.clone(), dec, msg));
                    return self.scoped(|s| s.misplaced_recursion.get_mut(), misplaced, |me| me.elab_decl_one(decl, None));
                }
            }
            return self.elab_structural_fn(decl);
        }
        self.elab_decl_one(decl, None)
    }

    /// A `fn` the planner lowers structurally. In review mode, also check
    /// that the lowering means the source (issues/recursion-meaning-check.md);
    /// only a `fn` whose self-calls were lowered under a guard has a
    /// recursion to check.
    fn elab_structural_fn(&mut self, decl: &Decl) -> R<()> {
        self.elab_decl_one(decl, None)?;
        let decs = self.attempt.recursion_decs.borrow().clone();
        if self.policy.review_lints && !decs.is_empty() {
            self.review_recursion_meaning(decl, &decs);
        }
        Ok(())
    }

    /// A `fn` whose recursive `match` reads its own parameter, lowered as if
    /// it had been written `decreases p` (`p.len()` for a list), which gives
    /// the source's meaning (issues/fn-recursion-means-the-function.md). The
    /// measure's obligations are left to `omega`, the route's own default, so
    /// the route needs `nat` and `omega` in scope; without them, or at a type
    /// with no measure, the reading is refused with what to write instead.
    fn elab_recursion_by_measure(
        &mut self,
        decl: &Decl,
        self_ref: &recursion::SelfRef,
        dec: usize,
        read: Span,
        name: &str,
        from: usize,
    ) -> R<()> {
        let fname = &self_ref.name;
        let param = &self_ref.params[dec].0;
        let source = &self_ref.params[from].0;
        let what = if from != dec {
            format!(
                "`{name}`, bound from `{source}` above the recursive `match`, is read inside \
                 it, and the recursive call passes `{source}` a different value \
                 (issues/recursion-let-reads-changing-parameter.md)"
            )
        } else if name == param {
            format!("`{param}` is read inside its own recursive `match`")
        } else {
            format!("`{name}`, bound from `{param}` above the recursive `match`, is read inside it")
        };
        let keep = if from != dec {
            format!("bind `{name}` inside each arm that reads it")
        } else {
            "name this level's value by its pattern (`Succ(k)`, `Cons(h, t)`)".to_string()
        };
        let refuse = |why: &str| {
            err(
                format!(
                    "{what}: the structural lowering compiles the recursion at the `match`, \
                     so there it would be the value `{fname}` was first called with, not this \
                     level's. {why} Or {keep} (issues/fn-recursion-means-the-function.md)"
                ),
                read,
            )
        };
        let measure = decl
            .params
            .get(dec - decl.tyvars.len())
            .and_then(|p| match &p.ty.kind {
                TyKind::Nat => Some(Expr { kind: ExprKind::Var(param.clone()), span: p.span }),
                TyKind::Named { name, .. } if name.rsplit("::").next() == Some("List") => {
                    Some(Expr {
                        kind: ExprKind::Dot {
                            recv: Box::new(Expr { kind: ExprKind::Var(param.clone()), span: p.span }),
                            name: "len".into(),
                            tyargs: Vec::new(),
                            args: Some(Vec::new()),
                            named: Vec::new(),
                        },
                        span: p.span,
                    })
                }
                _ => None,
            });
        let Some(measure) = measure else {
            return refuse(&format!(
                "It would be lowered by a measure instead, but `{param}` is neither a `Nat` nor \
                 a `List`: declare `decreases` with a measure on it yourself."
            ));
        };
        let available = [
            "nat::Nat::le_trans",
            "omega::nat_le_of_not_not_le",
            "int::Int::negsucc_lt_ofnat",
        ]
        .iter()
        .all(|n| matches!(self.resolve_declared(n), NameRes::Found(_)));
        if !available {
            return refuse(
                "It would be lowered by a measure on it instead, whose obligations `omega` \
                 discharges: `import nat; import int; import omega;` for that.",
            );
        }
        self.emit_lint(
            Lint::RecursionByMeasure,
            format!(
                "{what}, so `{fname}` is compiled as if it had been declared `decreases`: it \
                 computes what it says, but at a symbolic argument it no longer unfolds by \
                 conversion; cite `{fname}_unfold` for that, or {keep} to keep the \
                 structural lowering (issues/fn-recursion-means-the-function.md)"
            ),
            read,
        );
        let mut by_measure = decl.clone();
        by_measure.decreases = Some(measure);
        // The source wrote no `decreases`: a refusal that names it says why
        // the declaration is under one, and what keeps it structural.
        self.session_transaction(|me| me.elab_measure_decl(&by_measure)).map_err(|e| match e {
            ElabError::Elab { msg, span } if msg.contains("under `decreases`") => ElabError::Elab {
                msg: format!(
                    "{msg}\n(`{fname}` is compiled as if declared `decreases` because {what}; \
                     or {keep} to keep the structural lowering, \
                     issues/fn-recursion-means-the-function.md)"
                ),
                span,
            },
            other => other,
        })
    }

    /// One ordinary declaration, with `obligations` the measure-obligation
    /// table to reword errors through where this declaration was generated by
    /// [`measure`] (`None` for source declarations).
    fn elab_decl_one(&mut self, decl: &Decl, obligations: Option<&measure::Obligations>) -> R<()> {
        // Constraints sharing a symbol at one carrier become one dictionary
        // of a synthesized class, made here — between items, where Ψ may
        // grow — before the declaration's own attempts begin
        // (issues/constraints-sharing-indices.md).
        let merged = self.merge_linked_constraints(decl)?;
        let decl = merged.as_ref().unwrap_or(decl);
        let warn_mark = self.pass.warnings.borrow().len();
        let mut reserved = 0;
        self.attempt.goal_arena.enable_restarts();
        let r = loop {
            self.attempt.prepare();
            self.pass.pending_derived.borrow_mut().clear();
            let r = self.check_decl(decl, reserved);
            let requested = self.attempt.goal_arena.take_requested_base();
            if requested <= reserved {
                break r;
            }
            // Nothing in an ordinary declaration is registered before its
            // kernel gate. Goal-capacity discovery is therefore speculative:
            // discard its diagnostics and goal arena, enlarge the stable Ψ
            // prefix, and elaborate the declaration again from its source.
            self.pass.warnings.borrow_mut().truncate(warn_mark);
            self.attempt.clear_goals();
            reserved = reserved.max(requested);
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
                Err(match obligations {
                    Some(o) => o.explain(error),
                    None => error,
                })
            }
        }
    }

    /// A declaration whose body holds `for` loops: each loop's step and
    /// state, then the declaration over folds (crates/elab/src/loops.rs).
    /// Each part goes through [`Self::elab_decl`], so a step with loops of
    /// its own is lowered the same way.
    fn elab_loop_decl(&mut self, decl: &Decl) -> R<()> {
        let family = loops::lower(decl, self)?;
        for part in &family.parts {
            match part {
                loops::Part::State(d) => self.elab_inductive(d)?,
                loops::Part::Decl(d) => self.elab_decl(d)?,
            }
        }
        // §7.1: always attempted, and never a reason to refuse `f` — the
        // generated statement is untrusted, so a refusal is recorded for a
        // later `f_unfold` reference to report.
        if let Err(e) = self.elab_decl_one(&family.unfold, None) {
            self.pass.unfold_refusals.borrow_mut().insert(family.unfold.name.clone(), format!("the generated `{}` was refused ({e})", family.unfold.name));
        }
        // Designated last: the generated parts above are spelled with the
        // minted names, which a designation takes out of the surface.
        for (designed, minted) in &family.designations {
            self.designate_access(designed, minted);
        }
        Ok(())
    }

    /// A `partial fn`: `f#body`, then `f` over `CoTree::rec`, then
    /// `f_unfold` (crates/elab/src/partial.rs). Each part goes through
    /// [`Self::elab_decl`], so a body with loops is lowered as any is.
    fn elab_partial_decl(&mut self, decl: &Decl) -> R<()> {
        let family = partial::lower(decl)?;
        for part in &family.parts {
            self.elab_decl(part)?;
        }
        if let Err(e) = self.elab_decl_one(&family.unfold, None) {
            self.pass.unfold_refusals.borrow_mut().insert(family.unfold.name.clone(), format!("the generated `{}` was refused ({e})", family.unfold.name));
        }
        for (designed, minted) in &family.designations {
            self.designate_access(designed, minted);
        }
        Ok(())
    }

    /// `fn f(x̄) -> T decreases e { body }` is not one declaration but the
    /// family of `docs/decreases-unfolding-design.md` §2 — `f#body`, `f#rec`,
    /// `f` — elaborated in order. Each member is an ordinary declaration
    /// checked the ordinary way, so nothing the generator writes is trusted.
    fn elab_measure_decl(&mut self, decl: &Decl) -> R<()> {
        // The lowering reads names by their last binding, so a `let m = m - 1`
        // would shadow the measure's `m` (issues/decreases-shadowed-let.md).
        let decl = &measure::deshadowed(decl);
        let measure = decl.decreases.clone().expect("a measure declaration");
        measure::check_shape(decl, &measure)?;
        // The wrapper spells `nat::Nat::Lt`, `nat::Nat::le_trans` and `nat::Nat::lt_succ_self`;
        // the default closer spells `omega`'s certificates, which name the
        // `omega` module. Neither is the prelude's, so the module has to import
        // them — checked here so the message says so.
        if !matches!(self.resolve_declared("nat::Nat::le_trans"), NameRes::Found(_)) {
            return err(
                "`decreases` states its obligations with `nat::Nat::Lt` and discharges them \
                 through `nat::Nat::le_trans`: `import nat;` first",
                measure.span,
            );
        }
        // `omega`'s certificates name `omega::` and `int::` lemmas, so the
        // default closer is available only where both modules are imported;
        // otherwise every obligation is an ordinary unsolved goal, reported
        // with its statement.
        let omega_available = ["omega::nat_le_of_not_not_le", "int::Int::negsucc_lt_ofnat"]
            .iter()
            .all(|n| matches!(self.resolve_declared(n), NameRes::Found(_)));
        self.check_measure_is_nat(decl, &measure)?;
        // A member recurses under its **base** name, as `SelfRef` does.
        let self_name = decl.name.rsplit("::").next().unwrap_or(&decl.name).to_string();
        // §4: each self-call site's obligation is a declaration of its own,
        // elaborated first because the body and both companions reference it.
        // A lifted obligation the *checker* refuses is not an error on `f` —
        // the generated statement may be one this syntactic pass got wrong —
        // so the declaration is re-lowered with its obligations back at the
        // calls, exactly as it was before this round, and the companions are
        // declined with the reason. An obligation that is genuinely unprovable
        // fails again there, with the message §2 of the measures doc pins.
        // A computed scrutinee's equation enters the lowering only where a
        // lifted obligation reads it (design §13): lowered with every
        // candidate bound, then again with just the ones the obligations
        // quantify, so a body whose obligations never read one keeps the
        // plain match it was written with.
        let mut auto = measure::AutoEqs::All;
        let mut family = measure::lower(decl, &self_name, &measure, omega_available, self, true, &auto)?;
        if family.auto_candidates > 0 {
            let mut used: Vec<usize> = family
                .obligations
                .iter()
                .flat_map(|o| o.decl.params.iter().filter_map(|p| measure::auto_eq_index(&p.name)))
                .collect();
            used.sort_unstable();
            used.dedup();
            let all = used.len() == family.auto_candidates;
            auto = measure::AutoEqs::Only(used);
            if !all {
                family = measure::lower(decl, &self_name, &measure, omega_available, self, true, &auto)?;
            }
        }
        let mut lifted = true;
        for part in &family.obligations {
            if let Err(why) = self.elab_decl_one(&part.decl, Some(&part.obligations)) {
                self.pass.unfold_refusals.borrow_mut().insert(
                    measure::unfold_name(&decl.name),
                    format!("the lifted `{}` was refused ({why})", part.decl.name),
                );
                lifted = false;
                break;
            }
        }
        if !lifted {
            family = measure::lower(decl, &self_name, &measure, omega_available, self, false, &measure::AutoEqs::Off)?;
        }
        for part in &family.decls {
            self.elab_decl_one(&part.decl, Some(&part.obligations))?;
        }
        // §7: the unfolding companions are **always attempted** and silently
        // skipped where §3's walk refuses the body — a hard error would
        // regress programs that are accepted today for the sake of a theorem
        // they never cite. The refusal is recorded so a later reference to
        // `f_unfold` reports the shape rather than an unknown name.
        //
        // A companion that the walk builds but the *checker* refuses is
        // treated the same way (amends §3): the generator is untrusted, so a
        // term it got wrong must not take `f` down with it. The recorded
        // reason quotes the checker, so the case stays diagnosable.
        let unfold = measure::unfold_name(&decl.name);
        if lifted {
            match measure::companions(decl, &self_name, &measure, omega_available, self, &auto) {
                Err(why) => {
                    self.pass.unfold_refusals.borrow_mut().insert(unfold, why);
                }
                Ok(parts) => {
                    for part in parts {
                        if let Err(e) = self.elab_decl_one(&part.decl, Some(&part.obligations)) {
                            self.pass.unfold_refusals
                                .borrow_mut()
                                .insert(unfold, format!("the generated `{}` was refused ({e})", part.decl.name));
                            break;
                        }
                    }
                }
            }
        }
        // The recursor and its step have designed spellings, `f::rec` and
        // `f::body`: `f` at a bound on its measure, and one step of it with
        // its recursion any function, which a proof by induction on the
        // bound states its claims about where no `f_unfold` exists
        // (docs/decreases-unfolding-design.md §11). Designated last: the
        // companions above are spelled with the minted names, which a
        // designation takes out of the surface.
        self.designate_access(&format!("{}::rec", decl.name), &measure::rec_name(&decl.name));
        self.designate_access(&format!("{}::body", decl.name), &measure::body_name(&decl.name));
        Ok(())
    }

    /// N > 1 adjacent `decreases` declarations that call one another
    /// (`docs/mutual-recursion-design.md` §1) are one recursion: the product
    /// motive `f#grp`, one `g#body` per member, the shared `f#grp_rec`, and
    /// each member as a projection (§3). Every generated declaration is
    /// checked the ordinary way, so nothing the generator writes is trusted.
    fn elab_measure_group(&mut self, members: &[&Decl]) -> R<()> {
        let span = members[0].span;
        // As `elab_measure_decl`: every name in a member's body means one binder.
        let owned: Vec<Decl> = members.iter().map(|d| measure::deshadowed(d)).collect();
        let members: Vec<&Decl> = owned.iter().collect();
        let members = &members[..];
        let mut gm: Vec<measure::GroupMember<'_>> = Vec::new();
        for d in members {
            let measure = d.decreases.clone().expect("a measure declaration");
            measure::check_shape(d, &measure)?;
            gm.push(measure::GroupMember {
                decl: d,
                self_name: base_name(&d.name).to_string(),
                measure,
            });
        }
        // §2's circularity check runs before the measures are elaborated: a
        // measure calling a member is an unbound name at this point, and
        // "unbound" is the wrong thing to say about it.
        measure::check_group_shape(&gm)?;
        for m in &gm {
            self.check_measure_is_nat(m.decl, &m.measure)?;
        }
        if !matches!(self.resolve_declared("nat::Nat::le_trans"), NameRes::Found(_)) {
            return err(
                "`decreases` states its obligations with `nat::Nat::Lt` and discharges them \
                 through `nat::Nat::le_trans`: `import nat;` first",
                span,
            );
        }
        // §3: the group's motive is a nested `Pair`, and its members are
        // reached by `.fst`/`.snd`.
        if self.lookup_inductive("Pair").is_none() {
            return err(
                "a mutual `decreases` group shares one recursion whose motive is the \
                 product of its members' (docs/mutual-recursion-design.md §3): \
                 `import pair;` first",
                span,
            );
        }
        let omega_available = ["omega::nat_le_of_not_not_le", "int::Int::negsucc_lt_ofnat"]
            .iter()
            .all(|n| matches!(self.resolve_declared(n), NameRes::Found(_)));
        let family = measure::lower_group(&gm, omega_available, self)?;
        for part in &family.obligations {
            self.elab_decl_one(&part.decl, Some(&part.obligations))?;
        }
        for part in &family.decls {
            self.elab_decl_one(&part.decl, Some(&part.obligations))?;
        }
        // §6: the unfolding companions do not extend to a group this round.
        // Each member records the refusal on its own `f_unfold`, so a citation
        // reports the reason rather than an unknown name.
        for d in members {
            self.pass.unfold_refusals.borrow_mut().insert(
                measure::unfold_name(&d.name),
                format!(
                    "`{}` is a member of a mutual `decreases` group, whose unfolding \
                     equations are deferred (docs/mutual-recursion-design.md §6)",
                    base_name(&d.name)
                ),
            );
        }
        Ok(())
    }

    /// A written type as the declaration it names, where it names one.
    fn ctor_fields_of(&self, scrut: &Ty, ctor: &str) -> Option<Vec<Ty>> {
        match &scrut.kind {
            TyKind::Nat => match ctor {
                "Zero" => Some(Vec::new()),
                "Succ" => Some(vec![scrut.clone()]),
                _ => None,
            },
            TyKind::Named { name, args } => {
                let ind = self.lookup_inductive(name)?;
                // Only the plain parameterized shape: an index or a value
                // parameter puts the field types under binders this
                // substitution does not carry.
                if ind.index.is_some() || !ind.valparams.is_empty() || ind.params.len() != args.len()
                {
                    return None;
                }
                let c = ind.ctors.iter().find(|c| c.name == ctor)?;
                let m: Vec<(String, Ty)> = ind
                    .params
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .collect();
                Some(
                    c.fields
                        .iter()
                        .map(|(_, t)| measure::instantiate_ty(t, &m))
                        .collect(),
                )
            }
            _ => None,
        }
    }

    /// The measure is a `Nat`, checked in the declaration's own parameter
    /// context and *before* anything is generated, so the message says so
    /// rather than surfacing as a mismatch inside a generated `nat::Nat::Lt`.
    fn check_measure_is_nat(&mut self, decl: &Decl, measure: &Expr) -> R<()> {
        self.attempt.prepare();
        self.attempt.goal_arena.configure(count_holes(decl), 0);
        self.refresh_delta_psi();
        let r = self.decl_head_cx(decl).map(|cx| {
            self.elab_check(&cx, measure, &Type::Nat, &Level::Zero)
                .map(|_| ())
                .map_err(|error| match error {
                    ElabError::Elab { msg, span } => ElabError::Elab {
                        msg: format!("a `decreases` measure is a `Nat`: {msg}"),
                        span,
                    },
                    other => other,
                })
        });
        self.attempt.finish();
        self.refresh_delta_psi();
        r?
    }

    /// The binders a declaration's *measure* is written against: its type
    /// parameters, then its value parameters. This is the prefix of
    /// [`Self::check_decl`]'s telescope builder, as `instance_head_cx` is —
    /// used only for the `decreases` preflight, where the constraint slots and
    /// notation installations a body needs are not yet in play.
    fn decl_head_cx(&self, decl: &Decl) -> R<Cx> {
        let mut cx = Cx::empty();
        for tv in &decl.tyvars {
            let level = Level::constant(tv.level);
            cx.push(
                tv.name.clone(),
                Type::Ty(level.clone()),
                Level::constant(tv.level + 1),
            );
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
        for p in &decl.params {
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

    /// The sole commit point for a checked ordinary declaration.
    ///
    /// Every operation here is infallible. In particular, no declaration can
    /// become visible to later source unless `check_decl` returned a complete
    /// value after the kernel gate.
    fn commit_decl(&mut self, pending: PendingDecl) {
        // Registration bookkeeping as its own column: the Ψ push, the name
        // and provenance tables, the module journal's event, and the δ-world
        // rebuild that follows them (`docs/instrumentation-design.md` §5).
        let _commit = stats::guard(stats::Timer::DeclCommit);
        let PendingDecl {
            aux,
            binding,
            sealed,
            export_proof,
            registration,
            is_axiom,
            direct_dependencies,
        } = pending;
        // A lifted proof has no name to register: like a key-less generated
        // definition, it travels in the module's Ψ suffix.
        for lemma in aux {
            self.psi.push(lemma);
        }
        let abs = self.psi.bindings.len() as u32;
        if let (Some(kept), Some(proof), GlobalBinding::Tm { ty, .. }) = (&mut self.pass.export_proofs, export_proof, &binding) {
            kept.insert(abs as usize, (Rc::clone(ty), proof));
        }
        match sealed {
            Some(proof) => self.psi.push_sealed(binding, proof),
            None => self.psi.push(binding),
        }
        self.semantic_commit_global(abs, registration, is_axiom, direct_dependencies);
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
            cx.push(
                tv.name.clone(),
                Type::Ty(level.clone()),
                Level::constant(tv.level + 1),
            );
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

    /// A `def`'s value with no written type, inferred: its term, which is
    /// the body, and its type, which is the statement
    /// (docs/value-definitions-design.md §2.2). A value whose type inference
    /// cannot find is refused with the spelling that fixes it.
    fn infer_value(&self, cx: &Cx, decl: &Decl, e: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, e).map_err(|error| match error {
            ElabError::Elab { msg, span } if msg.contains("infer") => ElabError::Elab {
                msg: format!(
                    "{msg} (`{}` has no written type, so its value must infer one: write it \
                     as `def {}: T = …;`)",
                    decl.name, decl.name
                ),
                span,
            },
            other => other,
        })
    }

    fn check_decl(
        &mut self,
        decl: &Decl,
        reserved_goals: u32,
    ) -> R<PendingDecl> {
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
                expanded = Decl {
                    params: x.params,
                    ..decl.clone()
                };
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
        // A name with two qualifiers (an instance's member,
        // `Le::Judge::verdict`, or a member function's `Pos` fact,
        // `T::f::pos`) splits at its first `::` like any other: the type owns
        // it, and the declared string is the whole name.
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
            //
            // A **function** owns one as well (issues/function-owned-members.md):
            // `theorem ten_pow::pos(i): 0 < ten_pow(i)` is a fact about
            // `ten_pow` named under it, not about its result type. The receiver
            // never reaches it — `f.pos` dispatches on the type of `f`, a
            // function type with no namespace — so qualification is its one
            // route, and the declared string is the same `f::pos` a type's
            // member would be.
            if !self.names_a_carrier(owner) {
                if self.names_a_function(owner) {
                    // `f::pos` is read as module `f`'s `pos` first
                    // (`names::resolve_kinds`), and functions share modules'
                    // lower-case spelling, so a function named like a visible
                    // module could declare a member its own module could never
                    // reach.
                    let scope = self.names.scope();
                    if owner == scope.module
                        || scope.imports_module(owner)
                        || owner == names::PRELUDE_MODULE
                    {
                        return err(
                            format!(
                                "`{}` would read as `{base}` in the module `{owner}`, not \
                                 as a member of the function `{owner}` — rename the \
                                 function or the module",
                                decl.name
                            ),
                            decl.span,
                        );
                    }
                } else if self.lookup_global(owner).is_some() {
                    return err(
                        format!(
                            "`{owner}` is a theorem, so `{}` attaches to nothing — \
                             members belong to types and functions; name a lemma \
                             about it on its own",
                            decl.name
                        ),
                        decl.span,
                    );
                } else {
                    return err(
                        format!(
                            "`{owner}` is not a type, a type former or a function in \
                             scope, so `{}` attaches to nothing — a member declaration \
                             is `fn <Type>::{base}(…)` or `theorem <function>::{base}(…)`, \
                             and the owner must be declared (or be a kernel type) \
                             before it",
                            decl.name
                        ),
                        decl.span,
                    );
                }
            }
            if base.is_empty() {
                return err("a member needs a name after `::`", decl.span);
            }
        }
        // Reserve the goal prefix *before* anything is elaborated: the
        // telescope and result type are elaborated first and their types end
        // up embedded in the emitted term, so they must live in the same
        // (shifted) world as the body.
        self.attempt
            .goal_arena
            .configure(count_holes(decl) + count_tactic_slots(decl), reserved_goals);
        self.refresh_delta_psi();
        // Elaborate the parameter telescope. Type parameters come first and
        // are ordinary kernel binders at `Ty 0` — level-0 parametric
        // polymorphism, Tarski-style, so a *use* of one in type position is
        // `El A` (docs/surface-polymorphism.md §2). They are registered in
        // `cx.tyvars`, the same table an `inductive`'s parameters use while
        // its fields are lowered; the difference is only that these survive
        // into the kernel term.
        //
        // The telescope and the result type are one attributed phase
        // (`docs/instrumentation-design.md` §5): everything a declaration's
        // *statement* costs, as against what its proof costs. The bracket is
        // exclusive, so the resolution, unification and generated-definition
        // work it contains stays in those columns and this one is the walk's
        // own share.
        // A default runs at the call, where an earlier parameter's name is
        // bound to the call's argument for it (`defaults::elab_param_default`).
        // So a default may mention the value parameters before it, and is
        // refused here, rather than at every call, when it mentions its own
        // parameter or a later one (the telescope is ordered, §9.4) or a type
        // parameter, which no alias can bind
        // (issues/parameter-defaults-mention-type-parameters.md).
        for (i, p) in decl.params.iter().enumerate() {
            let Some(default) = p.default.as_deref() else { continue };
            let mentions = |n: &String| datarepr::mentions_free(default, std::slice::from_ref(n), &mut Vec::new());
            if let Some(t) = decl.tyvars.iter().map(|t| &t.name).find(|n| measure::mentions_context(default, n)) {
                return err(
                    format!(
                        "`{}`'s default mentions the type parameter `{t}`, and a default cannot \
                         mention a type parameter yet (issues/parameter-defaults-mention-type-parameters.md): \
                         its expected type already says what `{t}` is at each call",
                        p.name
                    ),
                    default.span,
                );
            }
            if let Some(later) = decl.params[i..].iter().map(|q| &q.name).find(|n| mentions(n)) {
                let whose = if *later == p.name { "its own parameter".to_string() } else { format!("the later parameter `{later}`") };
                return err(
                    format!(
                        "`{}`'s default mentions {whose}: a default reads only the parameters \
                         before it, whose arguments the call has already given",
                        p.name
                    ),
                    default.span,
                );
            }
        }
        let decl_type = stats::guard(stats::Timer::DeclType);
        let mut cx = Cx::empty();
        cx.index_ambiguity = ambiguous.into();
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
                    format!(
                        "`{name}` is both a type parameter and a parameter of `{}`",
                        decl.name
                    ),
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
                ty: Type::El {
                    level: level.clone(),
                    tm: Rc::new(Term::Var(LocalVar(0))),
                },
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
            // A default is checked here, in the telescope of the parameters
            // before it, as well as at each call that leaves it out, so one no
            // call uses is still checked (docs/named-arguments-design.md §9.7).
            if let Some(default) = p.default.as_deref() {
                self.check_default_at_declaration(&cx, &decl.name, &p.name, default, &ty, &lvl)?;
            }
            // A binder of a class type at a written index is what fills a value
            // slot that unification left open (§5's ladder step 2), for the dot
            // sugars here and for a call's goal in `apply_implicit`.
            if let Some(r) = self.class_ref_of_ty(&p.ty)
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
                    ty: Type::El {
                        level: level.clone(),
                        tm: Rc::new(Term::Var(LocalVar(0))),
                    },
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
        // `def x = e;` (docs/value-definitions-design.md §2.2): the type is
        // `e`'s, so `e` is inferred once and is the body as well.
        let inferred = match &decl.result.kind {
            TyKind::TypeOf(e)
                if decl.value
                    && decl.body.stmts.is_empty()
                    && decl.body.ons.is_empty()
                    && decl.body.result.span == e.span =>
            {
                Some(self.infer_value(&cx, decl, e)?)
            }
            _ => None,
        };
        let (res_ty, res_lvl) = match &inferred {
            Some((_, ty, level)) => (ty.clone(), level.clone()),
            None => self.elab_ty(&cx, &decl.result)?,
        };
        drop(decl_type);
        *self.attempt.telescope.borrow_mut() = cx.names.clone();
        // The graph records what the checked proof/body references, not names
        // appearing only in its public statement (issues/axiom-provenance.md).
        self.attempt.direct_dependencies.borrow_mut().clear();
        if decl.kind != DeclKind::Axiom {
            cx.selfref = Some(Rc::new(SelfRef::of_decl(decl)));
        }
        // An axiom has no term to check. Ordinary definitions and theorems
        // elaborate their block exactly as before.
        //
        // The proof/body walk, the other half of the declaration's own work
        // and on every workload measured so far the larger one. Exclusive, so
        // the diagnostic probes, the whnf probes, resolution and the
        // generated definitions minted while walking keep their own columns.
        let decl_body = stats::guard(stats::Timer::DeclBody);
        let body = if decl.kind == DeclKind::Axiom {
            self.solve_goals(&[], &decl.name)?;
            None
        } else if let Some((term, _, _)) = inferred {
            self.solve_goals(&decl.body.ons, &decl.name)?;
            Some(term)
        } else {
            // A `decreases` declaration never reaches here: `elab_measure_decl`
            // has already replaced it by the family of `measure.rs`.
            debug_assert!(decl.decreases.is_none());
            // A corecursive definition (docs/codata-elaborator-design.md §5):
            // the result is codata and the body calls itself, so the body is
            // one `corec`'s step, checked at the step type with the
            // self-reference turned into seeds rather than induction
            // hypotheses.
            let corec = match cx.selfref.as_ref() {
                Some(selfref) => self.corec_plan(&cx, decl, selfref, &res_ty, decl.span)?,
                None => None,
            };
            let body = if let Some(site) = &corec {
                let mut bcx = cx.clone();
                bcx.selfref = None;
                bcx.corec = Some(Rc::clone(site));
                let (step_ty, step_lvl) = Self::corec_body_ty(site);
                let step = statements::check_block(
                    self,
                    &bcx,
                    &decl.body,
                    &step_ty,
                    &step_lvl,
                    None,
                    None,
                    true,
                )?;
                self.corec_close(&cx, decl.tyvars.len(), site, step, decl.span)?
            } else {
                statements::check_block(
                    self,
                    &cx,
                    &decl.body,
                    &res_ty,
                    &res_lvl,
                    None,
                    None,
                    true,
                )?
            };
            self.solve_goals(&decl.body.ons, &decl.name)?;
            Some(body)
        };
        // A capacity restart discards this attempt: none of it is gated.
        if self.attempt.goal_arena.restart_requested() {
            return err("internal: restarting declaration for goal capacity", decl.span);
        }
        let (sigma, aux, lifted_world) = self.lift_proved(&decl.name, decl.span)?;
        let lifted = aux.len() as u32;
        let goal_base = self.attempt.goal_arena.base();
        drop(decl_body);

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
        // statement's own) at each binder's depth. Through the one emission
        // chokepoint (§2.5), so a statement component that arrived as a code
        // literal is spelled the way every slot copied off it is; the
        // reflection boundary reads a statement back through
        // `unspell_ty_deep`, which is the inverse of the reference half and
        // sees a decoded literal exactly as it would have seen an inline one.
        //
        // Respelling, closing the telescope and the one global substitution
        // are one phase — what the elaborator spends turning a checked pair
        // into the pair the kernel is handed
        // (`docs/instrumentation-design.md` §5).
        let decl_emit = stats::guard(stats::Timer::DeclEmit);
        let empty_cx = Cx::empty();
        let n_params = param_info.len() as u32;
        let mut stmt = match self.emit_ty(&empty_cx, &res_ty, n_params) {
            Some(r) => r,
            None => res_ty,
        };
        let mut stmt_lvl = res_lvl;
        let mut term = body;
        for (i, (dom, dom_lvl)) in param_info.into_iter().enumerate().rev() {
            let dom = match self.emit_ty(&empty_cx, &dom, i as u32) {
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
        // With lifted proofs, their globals sit between Ψ and the goal
        // prefix: shift the committed globals up past them first.
        let term = term.map(|term| term.shift_global_above(lifted, goal_base).apply_global(&sigma));
        let stmt = stmt.shift_global_above(lifted, goal_base).apply_global(&sigma);
        // The declaration is checked in the world its lifted proofs extend.
        // The spike checks it inline and asks no cache.
        let lifted_psi = lifted_world.unwrap_or_else(|| Rc::clone(&self.psi.0));
        drop(decl_emit);

        // The emission audit, on exactly the pair the kernel is about to be
        // handed (`emission_walk`; design §2.5). Off unless asked for.
        if let Some(found) = self.policy.emission_findings.as_ref() {
            let findings =
                emission_walk::walk_decl(self, &decl.name, &stmt, term.as_ref());
            found.borrow_mut().extend(findings);
        }
        self.attribute_image(&decl.name, &stmt, term.as_ref());

        // The kernel is the gate: check the statement, then the term.
        // `stats::time_kernel` attributes exactly this to the kernel half of
        // the frontend suite's phase split (crates/elab/src/stats.rs).
        //
        // An installed gate oracle (`gate.rs`) may vouch for the declaration
        // instead, in which case neither call runs. Nothing installs one by
        // default; `heather check --cache` is the only caller today.
        let empty = LocalCtx::nil();
        if let Some(term) = term.as_ref() {
            let opaque = matches!(decl.kind, DeclKind::Theorem);
            self.gate_bodied(&lifted_psi, &decl.name, decl.span, &empty, &stmt, &stmt_lvl, term, opaque)?;
        } else {
            // Axioms extend the trusted assumptions, but their statements are
            // still required to be well-formed kernel types.
            stats::time_kernel(|| {
                self.kernel_check_type(&self.psi, Layer::Prog, &empty, &stmt, &stmt_lvl)
            })
            .map_err(|e| {
                self.kernel_refusal(&decl.name, decl.span, e, &self.psi, Layer::Prog, &empty, None, &stmt, &stmt_lvl)
            })?;
        }

        // A default's names resolve where the declaration was written, at
        // every call (docs/named-arguments-design.md §9.4).
        let default_scope = Rc::new(self.names.scope().clone());
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
                    default: None,
                })
                .chain(decl.params.iter().enumerate().map(|(i, p)| ParamMeta {
                    name: p.name.clone(),
                    implicit: p.implicit,
                    is_type: false,
                    is_self: p.is_self,
                    // The parameter's own domain skeleton — what argument
                    // lambdas are checked against and what suppresses
                    // bare-reference insertion at this argument (§5.3/§6.1).
                    skel: skel_of_ty(&p.ty),
                    solver: p.solver.map(|_| Rc::new(p.ty.clone())),
                    default: p.default.as_ref().map(|e| Rc::new(application::ParamDefault {
                        expr: (**e).clone(),
                        scope: Rc::clone(&default_scope),
                        owner: qkey(self.names.module(), &decl.name),
                        index: decl.tyvars.len() + i,
                    })),
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
        //
        // Its proof is kept *sealed* beside the binding when the statement
        // carries data (`sealing.rs`): still invisible to δ, to every
        // comparison and to the binding's interface, but opened where an
        // elimination is stuck on the theorem — a witness projected, a
        // branch matched on (`issues/theorem-witness-unfolding.md`, D).
        let sealed = match (decl.kind, &term) {
            (DeclKind::Theorem, Some(proof)) if sealing::carries_data(&lifted_psi, &stmt) => {
                Some(Rc::new(proof.clone()))
            }
            _ => None,
        };
        let export_proof = match (decl.kind, &term) {
            (DeclKind::Theorem, Some(proof)) if self.pass.export_proofs.is_some() => Some(Rc::new(proof.clone())),
            _ => None,
        };
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
            && let Some(gate) = self.policy.gate.as_ref()
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
            aux,
            binding,
            sealed,
            export_proof,
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

    /// The kernel gate for one bodied global in `psi`: the cache oracle, then
    /// the statement here, then the body here or on the pool. Shared by a
    /// declaration and the tactic proofs it lifts, which extend Ψ before it
    /// (`docs/bv-omega-design.md` §7).
    #[allow(clippy::too_many_arguments)]
    fn gate_bodied(
        &mut self,
        psi: &Rc<GlobalCtx>,
        name: &str,
        span: Span,
        ctx: &LocalCtx,
        ty: &Type,
        level: &Level,
        body: &Term,
        opaque: bool,
    ) -> R<()> {
        // A declaration of a module that imports interface definitions is
        // checked with their bodies withheld, as the elaborator's worlds are
        // (docs/interface-definitions-design.md §3): the gate's conversion is
        // where a proof's unfolding actually happens. Withholding only takes
        // δ-steps away, so the gate never accepts more than it would without.
        let gated;
        let psi = match self.delta_psi.withheld.clone() {
            Some(withheld) => {
                gated = Rc::new(psi.withholding(Some(withheld)));
                &gated
            }
            None => psi,
        };
        let item = gate::GateItem { name, ctx, ty, level, body, opaque, layer: Layer::Code, lands_in_psi: true };
        if self.policy.gate.as_ref().is_some_and(|g| g.admits(psi, &item)) {
            return Ok(());
        }
        // Whatever sealed proofs the statement or the body open are part of
        // what the verdict is about (`KernelGate::accepted`).
        let recording = heather_kernel::unseal::Recording::start();
        // The statement is checked here, synchronously, whatever the pool is
        // doing: every dependent needs it, and it is the cheap half
        // (`docs/parallel-kernel-gate-design.md` §2).
        stats::time_kernel(|| self.kernel_check_type(psi, Layer::Prog, ctx, ty, level))
            .map_err(|e| self.kernel_refusal(name, span, e, psi, Layer::Prog, ctx, None, ty, level))?;
        if self.gate_is_inline() {
            // A serial replay may already hold this exact obligation's
            // verdict, earned by a worker of the pass it replaces
            // (`docs/parallel-kernel-gate-design.md` §5.2). `None` — which is
            // every ordinary run — asks the kernel.
            let verdict = match self.pass.kernel_replay.reuse(psi.bindings.len(), self.policy.fuel, &item) {
                Some(verdict) => verdict,
                None => stats::time_kernel(|| self.kernel_check_term(psi, Layer::Code, ctx, body, ty, level)),
            };
            verdict.map_err(|e| {
                let refusal = self.kernel_refusal(name, span, e, psi, Layer::Code, ctx, Some(body), ty, level);
                self.withheld_note(refusal, psi, ty, Some(body))
            })?;
            let unsealed = recording.finish();
            if let Some(g) = self.policy.gate.as_ref() {
                g.accepted(psi, &item, &unsealed);
            }
        } else {
            // Queued against the Ψ the binding is about to extend;
            // `accepted` travels with it and is replayed at the join.
            drop(item);
            stats::count(stats::Counter::DeclsGated);
            self.pass.kernel_pool.submit(pool::Deferred {
                name: name.to_string(),
                span,
                psi: Rc::clone(psi),
                ctx: ctx.clone(),
                ty: ty.clone(),
                level: level.clone(),
                body: body.clone(),
                opaque,
                layer: Layer::Code,
                lands_in_psi: true,
                fuel: self.policy.fuel,
                unsealed: recording.finish(),
                row: stats::current_item(),
            });
        }
        Ok(())
    }

    /// The declaration's goal substitution, with every lifted tactic proof
    /// (`docs/bv-omega-design.md` §7) kernel-checked as a global of its own,
    /// in its own context, and substituted as a reference to it. Returns the
    /// substitution, the lifted globals in order, and the world they extend
    /// Ψ to (`None` when nothing was lifted). The substitution's payloads are
    /// scoped in that world: a caller shifts its term's committed globals up
    /// past the lifted ones before applying it.
    fn lift_proved(&mut self, name: &str, span: Span) -> R<(GlobalSubst, Vec<GlobalBinding>, Option<Rc<GlobalCtx>>)> {
        let mut sigma = self.goal_subst();
        let lifted = self.attempt.goal_arena.lifted();
        if lifted.is_empty() {
            return Ok((sigma, Vec::new(), None));
        }
        let base = self.attempt.goal_arena.base();
        let m = lifted.len() as u32;
        for entry in sigma.entries.iter_mut() {
            if let heather_kernel::subst::GlobalEntry::Tm(t) = entry {
                *t = Rc::new(t.shift_global(m));
            }
        }
        // Out of the goal world, into Ψ and the lifted slots before this
        // one: an earlier lifted proof or value is referred to (a `let`
        // bound to one is inlined into what follows it, and `omega` names
        // its atom list), and any other goal is refused, which the two
        // dummies would disagree about.
        let mut world: GlobalCtx = (*self.psi).clone();
        let mut aux = Vec::new();
        let mut earlier: HashMap<usize, (usize, LocalCtx)> = HashMap::new();
        for (j, slot) in lifted.into_iter().enumerate() {
            let out = |dummy: Term| GlobalSubst {
                entries: (0..base as usize)
                    .map(|k| {
                        heather_kernel::subst::GlobalEntry::Tm(Rc::new(match earlier.get(&k) {
                            Some((i, delta)) => Term::GlobalTm { var: GlobalVar((j - 1 - i) as u32), subst: LocalSubst::id(delta) },
                            None => dummy.clone(),
                        }))
                    })
                    .collect(),
            };
            let (zero, one) = (out(Term::Zero), out(Term::Succ(Rc::new(Term::Zero))));
            let into = |sigma: &GlobalSubst| (
                slot.gamma.shift_global_above(j as u32, base).apply_global(sigma),
                slot.ty.shift_global_above(j as u32, base).apply_global(sigma),
                slot.body.shift_global_above(j as u32, base).apply_global(sigma),
            );
            let (gamma, ty, body) = into(&zero);
            if (gamma.clone(), ty.clone(), body.clone()) != into(&one) {
                return err("internal: a lifted proof mentions a goal", span);
            }
            // Its context is checked here too: a declaration's own gate never
            // sees a nonempty one.
            let at = Rc::new(world.clone());
            stats::time_kernel(|| typing::check_local_ctx(&at, 0, Layer::Prog, &gamma, self.policy.fuel))
                .map_err(|e| self.kernel_error(&format!("{name}#aux{j}"), span, e))?;
            self.gate_bodied(&at, &format!("{name}#aux{j}"), span, &gamma, &ty, &slot.level, &body, !slot.transparent)?;
            let binding = GlobalBinding::Tm {
                ctx: gamma.clone(),
                layer: Layer::Code,
                ty: Rc::new(ty),
                level: slot.level,
                body: slot.transparent.then(|| Rc::new(body)),
            };
            world.push(binding.clone());
            aux.push(binding);
            earlier.insert(slot.slot, (j, gamma.clone()));
            sigma.entries[slot.slot] = heather_kernel::subst::GlobalEntry::Tm(Rc::new(Term::GlobalTm {
                var: GlobalVar(m - 1 - j as u32),
                subst: LocalSubst::id(&gamma),
            }));
        }
        Ok((sigma, aux, Some(Rc::new(world))))
    }

    /// `cx` with every binder's type in the emission spelling
    /// ([`Self::annotation_type`]), the context a lifted proof or a named
    /// value is committed in. The kernel types the body's binders by the
    /// spellings the declaration emitted (its statement's `Π` domains, its
    /// `λ` annotations), and a slot reference `u^{id}` checks each of those
    /// binders against the slot's own context: stored as the elaborator
    /// keeps it, with a coded declaration inline, every reference converted
    /// an inline copy of `X86Profile` or `Stack<M>` against its `El` name,
    /// once per binder per tactic call (`omega`'s atom list is one such
    /// reference per call). Respelled, the two are one syntax and the
    /// conversion is the reflexivity shortcut.
    pub(crate) fn emitted_cx(&self, cx: &Cx) -> Cx {
        let n = cx.gamma.len();
        let scope = self.psi.bindings.len();
        let mut entries = Vec::with_capacity(n);
        let mut changed = false;
        for i in 0..n {
            let entry = cx.gamma.entries.get(i).expect("a binder in range");
            let key = (Rc::as_ptr(&entry.ty) as usize, i, scope);
            let known = self.attempt.emitted_entries.borrow().get(&key).map(|(_, ty)| Rc::clone(ty));
            let ty = match known {
                Some(ty) => ty,
                None => {
                    let ty = self.emit_ty(&cx.prefix(i), &entry.ty, 0).map_or_else(|| Rc::clone(&entry.ty), Rc::new);
                    self.attempt.emitted_entries.borrow_mut().insert(key, (Rc::clone(&entry.ty), Rc::clone(&ty)));
                    ty
                }
            };
            changed |= !Rc::ptr_eq(&ty, &entry.ty);
            entries.push(heather_kernel::term::CtxEntry { ty, level: entry.level.clone() });
        }
        if !changed {
            return cx.clone();
        }
        let mut out = cx.clone();
        out.gamma = LocalCtx::from_vec(cx.gamma.base, entries);
        out
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
        self.attempt
            .goal_arena
            .allocate(cx, name, hint, ty, level, span, key, promoted_parameter)
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
                    );
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
            Err(ElabError::UnsolvedGoals {
                decl: decl.to_string(),
                goals: unsolved,
            })
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
    pub(crate) fn goal_psi(&self) -> GlobalCtx {
        self.attempt.goal_arena.world(&self.psi, &self.scope.meta_pushed.borrow())
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
        // A class over a type constructor, `Bind<Option>`, is its record
        // applied to the constructor (issues/higher-kinded-classes.md).
        if let Some(t) = self.kinded_class_ty(ty) {
            return self.elab_ty(cx, &t);
        }
        match &ty.kind {
            // A generated declaration's type (`host::Leaves::Member`).
            TyKind::Named { name, .. } if let Some(k) = host::leaf_index(name) => self.host_ty_leaf(cx, k, ty.span),
            // An expression in type position: infer it, require its type to be
            // a universe, and decode (docs/surface-universe.md §4). `El` is the
            // kernel's own decoding, so nothing here is a coercion — the term
            // *is* a code, and `El ⌜T⌝ ⇝ T` makes a written type and a decoded
            // one convertible rather than merely equal-looking.
            TyKind::OfExpr(e) => self.expr_elab().lower_expression_type(self, cx, e, ty.span),
            // A `def`'s type, inferred from its value
            // (docs/value-definitions-design.md §2.2). `check_decl` reads the
            // value once for both; this is every other reading of the stored
            // declaration.
            TyKind::TypeOf(e) => {
                let (_, ty, level) = self.elab_infer(cx, e)?;
                Ok((ty, level))
            }
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
        if let Some((input, discards)) = binding::generated(e) {
            return self
                .elab_check_skel_slots_written(cx, e, expected, lvl, hint, skel, capture_slots)
                .map_err(|error| self.restate_bind_error(cx, input, discards, error));
        }
        if binding::generated_loop(e) {
            return self
                .elab_check_skel_slots_written(cx, e, expected, lvl, hint, skel, capture_slots)
                .map_err(|error| self.restate_loop_error(cx, e, Some(expected), error));
        }
        self.elab_check_skel_slots_written(cx, e, expected, lvl, hint, skel, capture_slots)
    }

    /// [`Self::elab_check_skel_slots`], below the binding-statement restatement.
    #[allow(clippy::too_many_arguments)]
    fn elab_check_skel_slots_written(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
        lvl: &Level,
        hint: Option<(&str, &str)>,
        skel: Option<&Skel>,
        capture_slots: bool,
    ) -> R<Term> {
        let _depth = expr::ExprDepthGuard::enter(&self.scope.expr_depth, e.span)?;
        // An arm body under a constant-motive probe (`matching::probe_arm_type`):
        // inferred, and its type recorded when it lives outside the arm. An
        // arm that names nothing lets the probe go on to the next one.
        if let Some(probe) = cx.arm_type_probe.as_ref()
            && *expected == matching::arm_probe_marker()
        {
            let probe = Rc::clone(probe);
            let mut icx = cx.clone();
            icx.arm_type_probe = None;
            let found = self.elab_infer(&icx, e).ok().and_then(|(_, ty, level)| {
                let extra = cx.gamma.len().checked_sub(probe.base)?;
                let ty = matching::strengthen_past(&ty, &cx.gamma, extra)?;
                let marked = matching::mentions_marker(&ty)
                    || matching::mentions_marker(&Type::Unit { level: level.clone() });
                (!marked).then_some((ty, level))
            });
            return match found {
                Some(found) => {
                    if let Ok(mut slot) = probe.found.lock() {
                        *slot = Some(found);
                    }
                    err("a constant motive was found; the probe stops here", e.span)
                }
                None => Ok(Term::Zero),
            };
        }
        self.refuse_value_call(cx, e)?;
        // A corecursive body's two positions, a node and a child
        // (docs/codata-elaborator-design.md §5.2).
        if let Some(site) = cx.corec.as_ref()
            && let Some(t) = self.corec_check(cx, site, e, expected, lvl)?
        {
            return Ok(t);
        }
        // A friend's body over a corecursive definition's free carrier
        // (docs/codata-elaborator-design.md §5.5).
        if let Some(mode) = cx.friend.as_ref()
            && let Some(t) = self.friend_check(cx, mode, e, expected, lvl)?
        {
            return Ok(t);
        }
        if let Some(quoted) = self.quote_for_by(cx, e, expected, lvl)? {
            return Ok(quoted);
        }
        // A branch of a tactic's split (`host::Leaves`).
        if let ExprKind::Var(name) = &e.kind
            && let Some(k) = host::leaf_index(name)
        {
            return self.host_leaf(cx, k, expected, lvl, e.span);
        }
        if let Some(receiver) = cx.dot_receiver.as_ref().and_then(|r| r.inference(cx, e))
            && let Some(Ok((t, got, _))) = receiver.get()
        {
            stats::count(stats::Counter::DotReceiverReuses);
            self.note_check_mismatch(cx, got, expected, lvl, e.span);
            return Ok(t.clone());
        }
        if capture_slots && has_free_slots(e) {
            match self.probe(|| self.elab_check_skel_slots(cx, e, expected, lvl, hint, skel, false)) {
                Ok(_) => {
                    // Every slot found a smaller function-typed checking
                    // position. Repeat on the real elaborator; the probe's
                    // state is deliberately discarded.
                    return self.elab_check_skel_slots(cx, e, expected, lvl, hint, skel, false);
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
                        match self.probe(|| {
                            self.attempt.slot_probe_target.set(Some(target));
                            self.elab_check_skel_slots(cx, e, expected, lvl, hint, skel, false)
                        }) {
                            Ok(_) => nested.push(target),
                            Err(ElabError::ArgSlotEscape { span }) if span == target => {}
                            Err(other) => return Err(other),
                        }
                    }
                    let profile = slot_profile(e, &nested)?
                        .expect("an escaping slot remains after nested captures");
                    let lowered = lower_argument_slots(e, profile, &nested);
                    return self
                        .elab_check_skel_slots(cx, &lowered, expected, lvl, hint, skel, false);
                }
                Err(other) => return Err(other),
            }
        }
        // A written motive in checking position has a mechanically testable
        // redundancy criterion: in a probe ([`Self::probe`]), remove just the motive,
        // and ask the ordinary goal-derived route to check the same match
        // against the same expected type. The probe makes goals, warnings,
        // fallback provenance, derived instances, and fuel bookkeeping
        // transactional; no declaration is duplicated — but the match is
        // elaborated twice and kernel-checked once more, paid in full when
        // the motive turns out to be required, which is every motive left
        // in a library that adopted the lint's findings. So it is a
        // review-mode lint (`set_review_lints`), not part of a check.
        if self.policy.review_lints
            && let ExprKind::Match {
            generated: false,
            scrut,
            motive: Some(motive),
            eqbind: None,
            ..
        } = &e.kind
            && !self.attempt.motive_redundancy_probe.get()
        {
            let mut omitted = e.clone();
            let ExprKind::Match {
                motive: omitted_motive,
                ..
            } = &mut omitted.kind
            else {
                unreachable!()
            };
            *omitted_motive = None;
            // One probe per written motive: the matches nested under this
            // one are elaborated here with their motives kept and are probed
            // by the real pass below, once each, not once per enclosing
            // probe (`attempt.rs`).
            let redundant = self.probe(|| {
                self.attempt.motive_redundancy_probe.set(true);
                self.elab_check_skel_slots(cx, &omitted, expected, lvl, hint, skel, capture_slots)
                    .is_ok_and(|term| {
                        self.kernel_check_term(&self.goal_psi(), Layer::Prog, &cx.gamma, &term, expected, lvl)
                            .is_ok()
                    })
            });
            if redundant {
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
        if let Some(rewritten) = self.owner_rewrite(cx, e)? {
            return self.elab_check_skel_slots(cx, &rewritten, expected, lvl, hint, skel, capture_slots);
        }
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
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "squash")
            && args.len() == 1
            && named.is_empty()
            && !self.shadowed(cx, "squash")
        {
            let head_ty = self.whnf(cx, expected, e.span)?;
            if let Type::Squash { level, ty } = head_ty {
                let payload = self.elab_check(cx, &args[0], &ty, &level)?;
                return Ok(Term::Squash {
                    level,
                    ty,
                    tm: Rc::new(payload),
                });
            }
        }
        match &e.kind {
            // `split_all; all_goals { body }`: the parser packages the two
            // statement combinators behind an unspellable head. Elaborated
            // local types decide which domains are finite; the resulting
            // nested matches are ordinary proof terms whose leaves check the
            // same body independently in each branch.
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if name == heather_syntax::SPLIT_ALL_GOALS)
                && named.is_empty() =>
            {
                let [body] = args.as_slice() else {
                    return err("internal `all_goals` form has the wrong arity", e.span);
                };
                let split = goal_combinators::split_all(self, cx, body, e.span);
                self.elab_check_skel_slots(cx, &split, expected, lvl, hint, skel, capture_slots)
            }
            ExprKind::App { head, args, named, explicit: false, goal_oriented: false }
                if matches!(&head.kind, ExprKind::Var(name) if name == constructor::FIELD_DEFAULT)
                    && named.is_empty() =>
            {
                self.elab_field_default(cx, args, expected, lvl, e.span)
            }
            ExprKind::App { args, .. } if defaults::is_param_default(e) => {
                // Reached only off a spine walker's path, which hands the
                // call's earlier arguments to `check_param_default` instead.
                self.elab_param_default(cx, args, expected, lvl, e.span, &[])
            }
            ExprKind::App { head, args, named, explicit: false, goal_oriented: false }
                if matches!(&head.kind, ExprKind::Var(name) if name == goal_combinators::SPLIT_STUCK)
                    && named.is_empty() =>
            {
                let [body] = args.as_slice() else {
                    return err("internal case splitter has the wrong arity", e.span);
                };
                // Every goal the splitter hands on is checked to restate the
                // one it stands for before anything is built at it: a motive
                // instance or a simplified goal that is not the goal would
                // otherwise surface only as the kernel's verdict on the whole
                // declaration, with `split_all` having reported success.
                match goal_combinators::next_step(self, cx, expected, body, e.span) {
                    goal_combinators::Step::Refuted(expr)
                    | goal_combinators::Step::Closed(expr)
                    | goal_combinators::Step::Intro(expr)
                    | goal_combinators::Step::Conjoin(expr) => {
                        self.elab_check_skel_slots(cx, &expr, expected, lvl, hint, skel, capture_slots)
                    }
                    goal_combinators::Step::Split(split) => {
                        let goal = goal_combinators::simplify_goal(self, cx, &inductive::decoded(expected));
                        goal_combinators::restates(self, cx, &goal, expected, lvl, "simplified goal", e.span)?;
                        let (scrut, ty, level) = self.elab_infer(cx, &split.scrut)?;
                        goal_combinators::restates(self, cx, &split.motive.inst_top(0, &scrut), &goal, lvl, "case split's motive, at its scrutinee,", e.span)?;
                        match split.dependent {
                            None => self.elab_convoy(
                                cx, heather_syntax::MatchForm::Match, true, &split.equation, &split.arms,
                                scrut, &ty, &level, split.motive, lvl, &goal, e.span,
                            ),
                            Some(dependent) => {
                                let refl = Term::Refl { level: level.clone(), ty: Rc::new(ty.clone()), tm: Rc::new(scrut.clone()) };
                                let at = dependent.inst_top_above(0, 1, &scrut).inst_top(0, &refl);
                                goal_combinators::restates(self, cx, &at, &goal, lvl, "case split's motive, at its scrutinee and `refl`,", e.span)?;
                                self.elab_convoy_dependent(
                                    cx, &split.equation, &split.arms, scrut, &ty, &level, split.motive, dependent, lvl, &goal, e.span,
                                )
                            }
                        }
                    }
                    goal_combinators::Step::Leaf(goal) => {
                        goal_combinators::restates(self, cx, &goal, expected, lvl, "simplified goal", e.span)?;
                        goal_combinators::check_refl_leaf(self, cx, body, &goal, e.span)?;
                        self.elab_check_skel_slots(cx, body, &goal, lvl, hint, skel, capture_slots)
                    }
                }
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
            ExprKind::Refl if self.shadowed(cx, "refl") => self.elab_check_skel_slots(
                cx,
                &Expr {
                    kind: ExprKind::Var("refl".to_string()),
                    span: e.span,
                },
                expected,
                lvl,
                hint,
                skel,
                capture_slots,
            ),
            ExprKind::ArgSlot(_) | ExprKind::Hole(_) | ExprKind::Refl | ExprKind::AutoRefl => self
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
            ExprKind::Block(block) => {
                statements::check_block(self, cx, block, expected, lvl, hint, skel, capture_slots)
            }
            // A quote against its `Code(g |- T)` type — checking-only, like
            // the kernel's `BoxTm` (docs/in-language-map-design.md §5).
            ExprKind::Quote(payload) => self.elab_quote(cx, payload, expected, e.span),
            ExprKind::Match {
                form,
                motive: None,
                scrut,
                arms,
                eqbind,
                generated,
            } => {
                // Stage-2 motive synthesis (issues/elab-stage2-metas.md,
                // docs/goal-motive-synthesis-design.md): abstract the
                // scrutinee out of the expected type so the motive is
                // genuinely dependent; the non-dependent motive (expected
                // under `z`) is what "no occurrence anywhere" falls back to.
                let (scrut_t, scrut_ty, scrut_lvl) = self
                    .elab_infer(cx, scrut)
                    .map_err(|error| matching::if_resolution_error(*form, scrut, error))?;
                // A recursion whose self-calls vary a parameter generalizes it
                // into the motive (docs/ih-generalization-design.md): the goal
                // becomes a Π over the varied parameters, the arms are wrapped
                // in the matching lambdas, and the recursor is applied back to
                // the parameters. Only here, in checking position — the goal
                // is what there is to generalize.
                //
                // A local scrutinee refines the hypotheses that mention it the
                // same way (issues/elab-match-refines-hypothesis-kernel-
                // rejects.md): they join the generalized positions, so each
                // arm sees them at its constructor.
                // Only the `match` that is the recursion generalizes: a case
                // split on a parameter every self-call passes unchanged
                // leaves the enclosing guard standing (`guard_param`), and
                // its arms' calls vary nothing of its own.
                let dec = recursion::descends_on_param(cx, &scrut_t);
                let guard = recursion::guard_param(cx, &scrut_t, arms);
                let mut positions = match guard {
                    Some(dec) => self.varying_params(cx, arms, dec),
                    None => Vec::new(),
                };
                // With `match h:` the convoy's equation is stated about the
                // computed scrutinee itself, and an arm that passes `h` to a
                // hypothesis needs that hypothesis about the same term, so
                // neither is refined (design §5.1).
                let refines = eqbind.is_none() || matches!(scrut_t, Term::Var(_));
                for p in refines.then(|| self.refined_hypotheses(cx, arms, &scrut_t, dec, expected)).unwrap_or_default() {
                    if !positions.contains(&p) {
                        positions.push(p);
                    }
                }
                positions.sort_unstable();
                if !positions.is_empty() {
                    let (gen_ty, gen_lvl) =
                        self.generalize_expected(cx, &positions, expected, lvl);
                    let motive = matching::synthesize_motive(
                        self, cx, &scrut_t, &scrut_ty, &scrut_lvl, &gen_ty, e.span,
                    );
                    let arms = self.wrap_arms(cx, arms, &positions);
                    let positions = Rc::new(positions);
                    let mut gcx = cx.clone();
                    if let Some(dec) = guard {
                        gcx.generalized = Some(Rc::new(generalize::Generalization {
                            dec,
                            positions: Rc::clone(&positions),
                            span: e.span,
                        }));
                    }
                    let run = |mcx: &Cx, eq: Option<&str>| match eq {
                        None => self.elab_match(
                            mcx,
                            *form,
                            *generated,
                            &arms,
                            scrut_t.clone(),
                            &scrut_ty,
                            &scrut_lvl,
                            motive.clone(),
                            gen_lvl.clone(),
                            e.span,
                        ),
                        Some(h) => self.elab_convoy(
                            mcx, *form, *generated, h, &arms, scrut_t.clone(), &scrut_ty,
                            &scrut_lvl, motive.clone(), &gen_lvl, &gen_ty, e.span,
                        ),
                    };
                    let elim = match eqbind {
                        None => self.elab_match_pending(&gcx, &scrut_ty, &run)?,
                        Some(h) => run(&gcx, Some(h))?,
                    };
                    return Ok(self.instantiate_generalized(cx, elim, gen_ty, &positions));
                }
                // An alias whose type is about the scrutinee rides along as a
                // convoy, so each arm sees it at its constructor (design §7.2).
                let dependents = if eqbind.is_none() {
                    self.dependent_aliases(cx, arms, &scrut_t)
                } else {
                    Vec::new()
                };
                if !dependents.is_empty() {
                    let (gen_ty, gen_lvl) = self.alias_generalized(&dependents, expected, lvl);
                    let motive = matching::synthesize_motive(
                        self, cx, &scrut_t, &scrut_ty, &scrut_lvl, &gen_ty, e.span,
                    );
                    let arms = self.wrap_alias_arms(arms, &dependents);
                    let run = |mcx: &Cx, eq: Option<&str>| match eq {
                        None => self.elab_match(
                            mcx, *form, *generated, &arms, scrut_t.clone(), &scrut_ty, &scrut_lvl,
                            motive.clone(), gen_lvl.clone(), e.span,
                        ),
                        Some(h) => self.elab_convoy(
                            mcx, *form, *generated, h, &arms, scrut_t.clone(), &scrut_ty,
                            &scrut_lvl, motive.clone(), &gen_lvl, &gen_ty, e.span,
                        ),
                    };
                    let elim = match eqbind {
                        None => self.elab_match_pending(cx, &scrut_ty, &run)?,
                        Some(h) => run(cx, Some(h))?,
                    };
                    return Ok(self.instantiate_aliases(cx, elim, gen_ty, &dependents));
                }
                let motive = matching::synthesize_motive(
                    self, cx, &scrut_t, &scrut_ty, &scrut_lvl, expected, e.span,
                );
                let run = |mcx: &Cx, eq: Option<&str>| match eq {
                    None => self.elab_match(
                        mcx,
                        *form,
                        *generated,
                        arms,
                        scrut_t.clone(),
                        &scrut_ty,
                        &scrut_lvl,
                        motive.clone(),
                        lvl.clone(),
                        e.span,
                    ),
                    Some(h) => self.elab_convoy(
                        mcx, *form, *generated, h, arms, scrut_t.clone(), &scrut_ty, &scrut_lvl,
                        motive.clone(), lvl, expected, e.span,
                    ),
                };
                match eqbind {
                    None => self.elab_match_pending(cx, &scrut_ty, &run),
                    Some(h) => run(cx, Some(h)),
                }
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
            // A bracket literal is selected by its expected container type.
            // Primitive vectors are the bootstrap representation and retain
            // their intrinsic reading, just as `Nat` does for numerals. Every
            // other container opts in through the canonical prelude protocol.
            ExprKind::CollectionLit(elems) => {
                let expr = self.expr_elab();
                if let Some(vector) = expr.vector_literal_type(cx, expected, e.span)? {
                    expr.check_indexed_form(self, cx, e, &vector)
                        .expect("classified as an ExprElab indexed checking form")
                } else {
                    self.check_collection_literal(cx, e, elems, expected, lvl, e.span)
                }
            }
            // `FZ` / `FS(j)` against an expected `Fin`. Checking-only, like
            // `refl` and a collection literal: `FZ` inhabits `Fin(Succ k)` for
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
                self.expr_elab().check_unit_form(self, cx, expected, lvl, e.span)
            }
            // `decide` — proof by reflection at a decided goal
            // (docs/reflection-through-decide-instances-design.md §4). Sugar
            // for `bool::decide_yes(refl)`: resolution picks the `Decide`
            // instance, the kernel runs its decision and judges the `refl`.
            // The name is also `bool::decide`'s, so the shadowing guard is
            // narrower than `trivial`'s: a local, an alias, the declaration
            // itself, or a user global of that name wins; the library's own
            // `decide` does not, since a bare `decide` at a goal that is not
            // a function was never that value.
            ExprKind::Var(name)
                if name == "decide"
                    && !self.decide_shadowed(cx)
                    && self.ctor_here_expected(cx, name, expected).is_none() =>
            {
                self.elab_decide(cx, expected, lvl, e.span)
            }
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if name == "rel_cong" || name == "rel_derive")
                && !self.shadowed(cx, e.as_named().unwrap().0)
                && self.ctor_here_expected(cx, e.as_named().unwrap().0, expected).is_none() =>
            {
                let tactic = e.as_named().unwrap().0;
                let [proof] = args.as_slice() else {
                    return err(format!("`{tactic}` takes exactly one proof expression"), e.span);
                };
                if !named.is_empty() {
                    return err(format!("`{tactic}` takes a positional proof expression"), e.span);
                }
                relational_context::proof::check(
                    self, cx, proof, expected, lvl, e.span, tactic == "rel_derive",
                )
            }
            ExprKind::Var(name) if name == "rel_derive"
                && !self.shadowed(cx, name)
                && self.ctor_here_expected(cx, name, expected).is_none() => {
                relational_context::proof::derive(self, cx, expected, lvl, e.span)
            }
            // `by t` runs the tactic `t` against the expected type
            // (docs/host-elaboration-interface-design.md, `host.rs`).
            ExprKind::App { head, args, .. }
                if matches!(&head.kind, ExprKind::Var(name) if name == heather_syntax::BY_TACTIC) =>
            {
                let [tactic] = args.as_slice() else {
                    return err("`by` runs one tactic", e.span);
                };
                self.run_by(cx, tactic, expected, lvl, e.span)
            }
            // `rewrite(h, …, e)` rewrites the goal along equations, writing
            // `j`'s motive by abstracting each left side
            // (docs/equation-rewrite-design.md).
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if name == "rewrite")
                && !named.iter().any(|a| a.name == "in")
                && !self.shadowed(cx, "rewrite")
                && self.ctor_here_expected(cx, "rewrite", expected).is_none() =>
            {
                self.elab_rewrite(cx, args, named, expected, lvl, e.span)
            }
            // `subst(h, e)` eliminates a local variable along `h`, reverting
            // the locals that depend on it (docs/equation-rewrite-design.md §8).
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if name == "subst")
                && !self.shadowed(cx, "subst")
                && self.ctor_here_expected(cx, "subst", expected).is_none() =>
            {
                self.elab_subst(cx, args, named, expected, lvl, e.span)
            }
            // `ring` normalizes both sides of an equation at `Int` or `Nat`
            // by reflection; `ring(h, …)` also combines equations
            // (docs/ring-normalization-design.md).
            ExprKind::Var(name)
                if name == "ring"
                    && !self.shadowed(cx, name)
                    && self.ctor_here_expected(cx, name, expected).is_none() =>
            {
                self.elab_ring(cx, &[], expected, lvl, e.span)
            }
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if name == "ring")
                && !self.shadowed(cx, "ring")
                && self.ctor_here_expected(cx, "ring", expected).is_none() =>
            {
                if !named.is_empty() {
                    return err("`ring` takes its equations positionally", e.span);
                }
                self.elab_ring(cx, args, expected, lvl, e.span)
            }
            // `linarith` proves a linear order goal at an ordered field from
            // the facts, up to its `≈` (docs/linarith-design.md); `nlinarith`
            // multiplies the facts too (docs/nonlinear-arithmetic-design.md).
            ExprKind::Var(name)
                if matches!(name.as_str(), "linarith" | "nlinarith")
                    && !self.shadowed(cx, name)
                    && self.ctor_here_expected(cx, name, expected).is_none() =>
            {
                self.elab_linarith(cx, &[], expected, lvl, e.span, name == "nlinarith")
            }
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if let ExprKind::Var(name) = &head.kind
                && matches!(name.as_str(), "linarith" | "nlinarith")
                && !self.shadowed(cx, name)
                && self.ctor_here_expected(cx, name, expected).is_none() =>
            {
                if !named.is_empty() {
                    return err(format!("`{name}` takes its facts positionally"), e.span);
                }
                self.elab_linarith(cx, args, expected, lvl, e.span, name == "nlinarith")
            }
            // `positivity` is `:= infer`'s proposition search run as a tactic,
            // with `omega` as the fallback at every subgoal the evidence rules
            // cannot close (docs/positivity-evidence-design.md §10).
            ExprKind::Var(name)
                if name == "positivity"
                    && !self.shadowed(cx, name)
                    && self.ctor_here_expected(cx, name, expected).is_none() =>
            {
                self.positivity(cx, expected, lvl, e.span)
            }
            // The obligation a `fn f(…) → Pos<A>` result states, restated at
            // its body by the parser (`result_fact`): the same search, with a
            // failure that names the way to prove it by hand.
            // A `Pos<A>` record field's fact, left out of a construction.
            ExprKind::Var(name) if name == heather_syntax::POS_SEARCH => {
                self.infer_proposition(cx, expected, lvl, e.span)
            }
            ExprKind::Var(name) if name == heather_syntax::POS_RESULT => {
                self.positivity(cx, expected, lvl, e.span).map_err(|e| match e {
                    ElabError::Elab { msg, span } => ElabError::Elab {
                        msg: format!(
                            "{msg}\n  hint: a function whose result is `Pos<A>` must return a \
                             positive value, and its fact `f::pos` is proved by searching its \
                             body. A body the search cannot read (a recursion, a case split) \
                             proves it by hand: `on ?pos := …;` in the body, at `0 < f(…)`"
                        ),
                        span,
                    },
                    e => e,
                })
            }
            // `omega` is the kernel-certified vertical slice of the linear
            // solver. It is only an untrusted elaborator shortcut:
            // reconstruction returns an ordinary Heather
            // expression and this recursive call checks it at the original
            // goal before the enclosing declaration reaches the kernel gate.
            ExprKind::Var(name)
                if (name == "omega"
                    || name == "__omega_diseq_branch"
                    || name == "__omega_connective_branch")
                    && !self.shadowed(cx, name)
                    && self.ctor_here_expected(cx, name, expected).is_none() =>
            {
                self.elab_omega(cx, name, expected, lvl, e.span)
            }
            // `omega(h, …)`: the listed proofs join the context for this call
            // only, read as facts exactly as a `let` of each would be
            // (`issues/omega-fact-arguments.md`).
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if name == "omega")
                && !self.shadowed(cx, "omega")
                && self.ctor_here_expected(cx, "omega", expected).is_none() =>
            {
                if !named.is_empty() {
                    return err("`omega` takes its facts positionally", e.span);
                }
                let (cx, facts) = self.omega_fact_context(cx, args)?;
                let proof = self.elab_omega(&cx, "omega", expected, lvl, e.span)?;
                Ok(statements::LetValue::discard_around(self, &cx, facts, proof, expected, lvl))
            }
            // `bv_omega` lifts word arithmetic to Nat (docs/bv-omega-design.md):
            // it writes a proof from the bridge lemmas and `omega`, and this
            // arm checks it at the goal like any other source.
            ExprKind::Var(name)
                if name == "bv_omega"
                    && !self.shadowed(cx, name)
                    && self.ctor_here_expected(cx, name, expected).is_none() =>
            {
                if self.key_of("bitvec_omega::add_form").is_none() {
                    return err("`bv_omega` requires its lemmas; add `import bitvec_omega;`", e.span);
                }
                let _certificate_scope = omega_cert::CertificateScope::enter(&self.scope.omega_depth);
                let generate = |careful| {
                    bv_omega::generate(self, cx, expected, careful).map_err(|detail| ElabError::Elab {
                        msg: format!("`bv_omega` got stuck: {detail}"),
                        span: e.span,
                    })
                };
                let mut generated = generate(false)?;
                let parse = |source: &str| {
                    omega_cert::parse_generated_expr(source).map_err(|detail| ElabError::Elab {
                        msg: format!("`bv_omega` wrote a proof that does not parse: {detail}\n  generated: {source}"),
                        span: e.span,
                    })
                };
                let mark = (self.pass.warnings.borrow().len(), self.attempt.goal_arena.mark());
                let mut checked = self.generated_scope(|me| me.elab_check(cx, &parse(&generated.source)?, expected, lvl));
                // The first proof is optimistic (a goal read off a word's
                // fact, facts restated untried); where it is refused, the
                // careful one is the answer, and its failure the diagnosis.
                // The refused attempt's named atom lists go with it.
                if checked.is_err() && generated.retry {
                    self.pass.warnings.borrow_mut().truncate(mark.0);
                    self.attempt.goal_arena.rollback(mark.1);
                    generated = generate(true)?;
                    checked = self.generated_scope(|me| me.elab_check(cx, &parse(&generated.source)?, expected, lvl));
                }
                match checked {
                    // Lifted into a lemma of its own where the declaration
                    // reserved a slot (docs/bv-omega-design.md §7): the
                    // kernel checks it once, in its context, and the body
                    // carries only a reference.
                    Ok(term) => Ok(self
                        .attempt
                        .goal_arena
                        .allocate_proved(&self.emitted_cx(cx), expected.clone(), lvl.clone(), term.clone(), e.span)
                        .unwrap_or(term)),
                    Err(error) => {
                        // Name the side condition that failed, not only the goal
                        // (§5): each one alone, in the context the bundle had.
                        for obligation in &generated.obligations {
                            let probe = parse(&format!(
                                "{{\n{}\nhave __bv_side: ({}) = omega;\n__bv_side\n}}",
                                generated.prelude, obligation.statement
                            ))?;
                            if let Err(side) = self.generated_scope(|me| me.elab_infer(cx, &probe)) {
                                return err(
                                    format!("`bv_omega`: {}; `omega` could not prove `{}`:\n{side}", obligation.why, obligation.shown),
                                    e.span,
                                );
                            }
                        }
                        Err(ElabError::Elab {
                            msg: format!("{error}\n  generated `bv_omega` proof: {}", generated.source),
                            span: e.span,
                        })
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
                .check_builtin_numeral(cx, t, expected, e.span)
            {
                Some(result) => result,
                None => self.elab_overloaded_num_check(cx, e, expected, lvl, e.span),
            },
            // The two literals of docs/string-char-design.md §3, on the
            // numeral's ladder: the spec type's introduction form at `Char` /
            // `String`, and `CharLiteral` / `StringLiteral` at every other
            // carrier.
            ExprKind::Char(c) => self.elab_char_check(cx, *c, e, expected, lvl),
            ExprKind::Scaled(lit) => self.elab_scaled_check(cx, lit, e, expected, lvl),
            ExprKind::Str(text) => self.elab_string_check(cx, text, e, expected, lvl),
            // A lambda against an expected Π: the *expected* domain is what
            // the binder is pushed with, so the emitted annotation always
            // matches the type it is checked against. A written annotation is
            // a readability aid and must be convertible with it
            // (docs/surface-function-types.md §5.2).
            // A type constructor written as a λ abstracting a declaration's
            // declared slot takes the canonical spelling the unifier learns
            // (docs/lambda-carrier-instances-design.md §7.3).
            ExprKind::Lam { binders, body }
                if let Some(term) = self.check_slot_lambda(cx, binders, body, expected, e.span)? =>
            {
                Ok(term)
            }
            ExprKind::Lam { binders, body } => self
                .expr_elab()
                .check_lambda(self, cx, binders, body, expected, lvl, skel, e.span),
            // A universe as the expected type: a *type* has been written where
            // a term is expected, so read it as one and quote it
            // (docs/surface-universe.md §4).
            _ if matches!(expected, Type::Ty(_)) => {
                let Type::Ty(want) = expected else {
                    unreachable!()
                };
                self.expr_elab()
                    .check_at_universe(self, cx, e, want, e.span)
            }
            // A declared type former, partially applied, against an expected
            // function type that ends in a universe: η-expand into the
            // type-valued function the remaining value parameters describe
            // (docs/record-type-partial-application.md §2). Sits here for the
            // same reason the universe arm above does — the reading has to be
            // chosen before the constructor arms see the same name — and
            // declines quietly for every other shape.
            _ if matches!(
                &e.kind,
                ExprKind::Var(_) | ExprKind::TyApp { .. } | ExprKind::App { .. }
            ) && let Some(term) = self.check_type_former_value(cx, e, expected, e.span)? =>
            {
                Ok(term)
            }
            // A constructor in checking position: the expected type *is* the
            // encoding, so every annotation of the injection and the field
            // tuple is read off it (docs/inductive-tier0-lowering.md §4).
            // Unsaturated against an expected `Π`, it η-expands into a function
            // value (docs/constructor-function-values.md §2).
            // The name is read with the expected type as evidence
            // ([`Self::ctor_here_expected`]), so a bare constructor the name
            // layer left ambiguous is settled by the type that is checking it.
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if named.is_empty()
                && matches!(
                    &head.kind,
                    ExprKind::Var(name)
                        if matches!(
                            name.as_str(),
                            heather_syntax::ANON_CTOR_ONLY
                                | heather_syntax::ANON_CTOR_LEFT
                                | heather_syntax::ANON_CTOR_RIGHT
                        )
                ) =>
            {
                let ExprKind::Var(name) = &head.kind else { unreachable!() };
                let (ind, i) = self.anonymous_ctor_expected(cx, name, expected, e.span)?;
                self.build_ctor_value(cx, &ind, i, args, expected, lvl, e.span)
            }
            ExprKind::Var(name) if self.ctor_here_expected(cx, name, expected).is_some() => {
                let (ind, i) = self
                    .ctor_here_expected(cx, name, expected)
                    .expect("just checked");
                self.build_ctor_value(cx, &ind, i, &[] as &[Expr], expected, lvl, e.span)
            }
            ExprKind::App { .. } if self.ctor_spine_expected(cx, e, expected).is_some() => {
                let (ind, i, args, named) = self
                    .ctor_spine_expected(cx, e, expected)
                    .expect("just checked");
                self.lint_manual_list_construction(cx, e, &ind, i);
                let written: Vec<(&str, &Expr, Span)> = named.iter().map(|na| (na.name.as_str(), &na.expr, na.name_span)).collect();
                if let Some(filled) = self.with_field_defaults(&ind, i, &args, &written, e.span)? {
                    return self.build_ctor_value(cx, &ind, i, &filled, expected, lvl, e.span);
                }
                let permuted =
                    application::resolve_constructor_arguments(&ind, i, &args, &named, e.span)?;
                let args = permuted.unwrap_or(args);
                self.build_ctor_value(cx, &ind, i, &args, expected, lvl, e.span)
            }
            // A record update is the record literal that keeps the other
            // fields (`record_update_expr`), checked as one.
            ExprKind::RecordUpdate { base, fields } => {
                let literal = self.record_update_expr(cx, base, fields, e.span)?;
                self.elab_check_skel_slots(cx, &literal, expected, lvl, hint, skel, capture_slots)
            }
            // A record literal *is* a constructor application once its fields
            // are put in declaration order, so checking mode is the tier-0
            // constructor path — which is what lets the expected type supply
            // the instantiation and no annotation be written
            // (docs/surface-records.md §6).
            ExprKind::RecordLit {
                name,
                tyargs,
                fields,
            } if tyargs.is_empty() => {
                if let Some(ind) = self.lookup_inductive(name).cloned().filter(|ind| ind.is_record) {
                    let written: Vec<(&str, &Expr, Span)> = fields.iter().map(|f| (f.name.as_str(), &f.expr, f.span)).collect();
                    if let Some(filled) = self.with_field_defaults(&ind, 0, &[], &written, e.span)? {
                        return self.build_ctor_value(cx, &ind, 0, &filled, expected, lvl, e.span);
                    }
                }
                let args = self.record_lit_args(name, fields, e.span)?;
                let Some(ind) = self.lookup_inductive(name).cloned() else {
                    return Err(self.name_miss(name, format!("unknown type `{name}`"), e.span));
                };
                self.build_ctor_value(cx, &ind, 0, &args, expected, lvl, e.span)
            }
            // `.f` resolution has to exist in *both* modes: a projection
            // synthesizes, but the method fallback may be checking-only
            // (`p.absurd()`), and routing it through inference would break it.
            ExprKind::Dot {
                recv,
                name,
                tyargs,
                args,
                named,
            } => {
                let receiver_cx = cx.with_dot_receiver(recv);
                let cx = &receiver_cx;
                let resolution =
                    self.resolve_dot(cx, recv, name, tyargs, args, named, e.span)?;
                if !tyargs.is_empty() && !matches!(&resolution, DotResolution::Method(_)) {
                    return err(
                        format!("type arguments after `.{name}` require a method call"),
                        e.span,
                    );
                }
                match resolution {
                    DotResolution::Inferred(t, got, _) => {
                        self.note_check_mismatch(cx, &got, expected, lvl, e.span);
                        Ok(t)
                    }
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
                                    let (t, got, _) = application::apply_implicit(
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
                                    self.note_check_mismatch(cx, &got, expected, lvl, e.span);
                                    return Ok(t);
                                }
                            }
                            // A projection synthesizes; its field type is
                            // compared at the gate like any inferred type's.
                            self.note_check_mismatch(cx, &ty, expected, lvl, e.span);
                            Ok(t)
                        }
                        Some(args) => {
                            let (t, got, _) = self.apply_projection(
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
                            self.note_check_mismatch(cx, &got, expected, lvl, e.span);
                            Ok(t)
                        }
                    },
                    // Dispatch is a projection with its own arguments, so it
                    // takes the applied route unconditionally — there is no
                    // bare form (§4 rule 7).
                    DotResolution::Dispatch(t, ty, l, fskel, dargs) => {
                        let (t, got, _) = self.apply_projection(
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
                        self.note_check_mismatch(cx, &got, expected, lvl, e.span);
                        Ok(t)
                    }
                    DotResolution::Method(m) => self
                        .elab_check_skel_slots(cx, &m, expected, lvl, hint, skel, capture_slots)
                        .map_err(|e| self.method_call_failure(cx, recv, &m, e)),
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
                //
                // A universe hides only under `El`, and only one level up:
                // `El^{1+l} (Ty l) ⇝ Ty l` is the sole rule that produces a
                // `Ty`, so an `El^0` — every proposition, every `Le(a, b)` at
                // `Int` — cannot reduce to one and is not reduced here. The
                // reduction is a probe, not a need: every consumer below
                // reduces the hint itself where it wants a head form, and the
                // conversion in `note_check_mismatch` is semantic. Measured on
                // issues/omega-per-goal-elaboration-cost.md: this probe ran
                // the small-step reducer on `Le(x, dot(row, atoms))` for
                // seconds per argument, computing the dot product by
                // substitution to learn that it was not a universe.
                let head = match expected {
                    Type::El { level, .. } if level.equiv(&Level::Zero) => expected.clone(),
                    _ => self.whnf(cx, expected, e.span)?,
                };
                if let Type::Ty(want) = &head {
                    return self
                        .expr_elab()
                        .check_at_universe(self, cx, e, want, e.span);
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
                // Keep the named relation/application structure for inference;
                // the expected-type solver performs its own reduction retry.
                let (t, got, _) =
                    self.elab_infer_at(cx, e, if suppress { None } else { Some(expected) })?;
                // A *type* where a value is expected — the proposition `n = 0`
                // where a `Bool` is — is refused here rather than noted: the
                // kernel's verdict on it is `LevelMismatch`, which the notes
                // below are never read for
                // (issues/prop-in-bool-position-reaches-kernel.md).
                if matches!(got, Type::Ty(_)) {
                    if let Some(refusal) = self.type_where_value_expected(cx, e, &got, &head, lvl) {
                        return Err(refusal);
                    }
                }
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

    /// `cx` with each of `omega(h, …)`'s arguments bound as a fact. Each is
    /// elaborated where it was written and named by an alias the user cannot
    /// spell, so the certificate can cite it; a bare local is in scope
    /// already. The certificate cites only the facts it needs, so the bound
    /// values are returned too, for the caller to discard around the proof:
    /// a fact no certificate cites still faces the kernel, as a `let` does
    /// (`statements.rs`).
    fn omega_fact_context(&self, cx: &Cx, facts: &[Expr]) -> R<(Cx, Vec<statements::LetValue>)> {
        let mut inner = cx.clone();
        let mut values = Vec::new();
        let mut next = 0;
        for fact in facts {
            if let ExprKind::Var(name) = &fact.kind {
                if cx.names.contains(name) || cx.aliases.iter_inner().any(|alias| alias.name == *name) {
                    continue;
                }
            }
            let (term, ty, level) = self.elab_infer(cx, fact)?;
            let name = loop {
                let name = format!("__omega_fact_{next}");
                next += 1;
                if !inner.names.contains(&name) && !inner.aliases.iter_inner().any(|alias| alias.name == name) {
                    break name;
                }
            };
            let value = statements::LetValue::new(Rc::new(term), ty, level);
            inner.aliases.push(Rc::new(value.alias(name, cx.names.len(), None)));
            values.push(value);
        }
        Ok((inner, values))
    }

    /// `omega` at `expected`, reading its facts from `cx`: reconstruction
    /// writes a certificate and this checks it like any other source.
    /// `name` is `omega` or one of the certificate's own branch markers.
    fn elab_omega(&self, cx: &Cx, name: &str, expected: &Type, lvl: &Level, span: Span) -> R<Term> {
        if self.scope.omega_depth.get() == 0 && self.key_of("omega::nat_le_of_not_not_le").is_none() {
            return err(
                "`omega` requires its certificate library; add `import omega;`",
                span,
            );
        }
        let outer_depth = self.scope.omega_depth.get();
        let written_cx = cx;
        let source_cx = omega_cert::source_context(cx);
        let cx = source_cx.as_ref();
        let _certificate_scope = omega_cert::CertificateScope::enter(&self.scope.omega_depth);
        omega_cert::reset_phases();
        let reconstruct_guard = stats::guard(stats::Timer::OmegaReconstruct);
        let mut cert = omega_cert::reconstruct(
            self,
            cx,
            expected,
            name != "__omega_diseq_branch",
            name != "__omega_connective_branch",
            true,
        )
        .map_err(|detail| {
            // Stuck: an arm equation not yet in scope might be the missing
            // fact (docs/dependent-match-compiler-design.md §4.3.1).
            self.want_match_equations(written_cx);
            ElabError::Elab {
                msg: format!("`omega` got stuck: {detail}"),
                span: span,
            }
        })?;
        let reconstruct_ns = reconstruct_guard.finish();
        let mut phases = omega_cert::phases();
        phases.reconstruct_ns = reconstruct_ns;
        phases.depth = outer_depth;
        phases.source_len = cert.source.len();
        // The certificate is parsed from generated text: its spans index
        // that text, not the user's file, and a lint about how the
        // generator spells a list is the generator's problem, not the
        // reader's. Same rule as datarepr emissions (`emit_lint`).
        let check_guard = stats::guard(stats::Timer::OmegaCheck);
        // The certificate names its atom list rather than spelling it
        // at every row: elaborated once here, and a transparent slot
        // of the declaration's where there is one, so the kernel
        // checks one list per certificate, not one per use.
        let named;
        let cx = match &cert.atoms {
            Some(literal) => {
                let (list_ty, parsed) = omega_cert::parse_atom_list(literal).map_err(|detail| ElabError::Elab {
                    msg: format!("`omega` wrote an atom list that does not parse: {detail}\n  generated: {literal}"),
                    span: span,
                })?;
                let checked = self.generated_scope(|me| {
                    let (ty, level) = me.elab_ty(cx, &list_ty)?;
                    let atoms = me.elab_check(cx, &parsed, &ty, &level)?;
                    Ok((atoms, ty, level))
                });
                let (atoms, ty, level) = checked.map_err(|error: ElabError| ElabError::Elab {
                    msg: format!("{error}\n  generated Omega atom list: {literal}"),
                    span: span,
                })?;
                let term = self
                    .attempt
                    .goal_arena
                    .allocate_transparent(&self.emitted_cx(cx), ty.clone(), level.clone(), atoms.clone());
                let term = match term {
                    goals::Named::Slot(reference) => reference,
                    goals::Named::Inline => atoms,
                    goals::Named::Restart => {
                        return err("internal: restarting declaration to reserve a slot for `omega`'s atoms", span);
                    }
                };
                let mut inner = cx.clone();
                inner.aliases.push(Rc::new(Alias {
                    name: omega_cert::ATOMS.to_string(),
                    depth: cx.names.len(),
                    term: Rc::new(term),
                    ty,
                    level,
                    skel: None,
                    spliced: None,
                    shifted: Default::default(),
                }));
                named = inner;
                &named
            }
            None => cx,
        };
        // A guard round binds the guards it reads at their unfolding, and
        // settles the facts it reads for the omegas inside it.
        let guarded;
        let guard_round = cert.guards.take();
        let cx = match &guard_round {
            Some(round) => {
                let mut inner = cx.clone();
                for alias in &round.aliases {
                    inner.aliases.push(Rc::new(Alias {
                        name: alias.name.clone(),
                        depth: cx.names.len(),
                        term: Rc::clone(&alias.term),
                        ty: alias.ty.clone(),
                        level: alias.level.clone(),
                        skel: None,
                        spliced: None,
                        shifted: Default::default(),
                    }));
                }
                self.scope.omega_settled_guards.borrow_mut().push(round.settles.clone());
                guarded = inner;
                &guarded
            }
            None => cx,
        };
        let checked = self
            .generated_scope(|me| me.elab_check(cx, &cert.expr, expected, lvl));
        if guard_round.is_some() {
            self.scope.omega_settled_guards.borrow_mut().pop();
        }
        phases.check_ns = check_guard.finish();
        let term = checked.map_err(|error| ElabError::Elab {
            msg: match &cert.atoms {
                Some(atoms) => format!("{error}\n  generated Omega certificate: {}\n  where {} = {atoms}", cert.source, omega_cert::ATOMS),
                None => format!("{error}\n  generated Omega certificate: {}", cert.source),
            },
            span: span,
        })?;
        cert.report.phases = phases;
        self.pass.omega_reports.borrow_mut().push(cert.report);
        Ok(term)
    }

    /// The refusal of an expression whose type is a universe — a type, most
    /// often a proposition — checked where a value of a non-universe type is
    /// expected (`issues/prop-in-bool-position-reaches-kernel.md`).
    ///
    /// The kernel refuses these as a bare `LevelMismatch` (the inferred type
    /// lives a level above the expected one), and [`Self::kernel_error`] reads
    /// the deferred checking notes only for `NotConvertible`, so the author
    /// of `fn z(n: Nat) → Bool { n = 0 }` was told neither type. The refusal
    /// is made here, at the expression, and only on a *decided* answer: the
    /// expected type was reduced by the caller, but a universe can still hide
    /// behind a δ-step that reduction does not take, so the semantic
    /// conversion has the last word and anything short of `NotConvertible`
    /// falls back to the ordinary note. It runs only when the inferred type
    /// is a universe and differs from the expected one, which no well-typed
    /// checking site produces.
    ///
    /// A proposition met where `bool::Bool` is expected also says how to get
    /// its decision, when there is one: a trial `decide_bit<P>()` resolves
    /// `Decide<P>` exactly as the written call would, and its state is rolled
    /// back like any declined speculation. Whether that position should
    /// *become* `decide_bit<P>()` is `issues/bool-from-decidable-prop.md`'s
    /// question; until it is answered, this is an error.
    fn type_where_value_expected(
        &self,
        cx: &Cx,
        e: &Expr,
        got: &Type,
        expected: &Type,
        lvl: &Level,
    ) -> Option<ElabError> {
        if self
            .goal_oracle()
            .convert_type(&cx.gamma, Layer::Prog, got, expected, lvl)
            != Err(ConvError::NotConvertible)
        {
            return None;
        }
        let want = self.display_type_clean(cx, expected);
        let bool_ty = Ty {
            kind: TyKind::Named {
                name: "bool::Bool".to_string(),
                args: Vec::new(),
            },
            span: e.span,
        };
        let is_bool = self.elab_ty(cx, &bool_ty).is_ok_and(|(b, _)| {
            self.goal_oracle()
                .convert_type(&cx.gamma, Layer::Prog, expected, &b, &Level::Zero)
                .is_ok()
        });
        let msg = if is_bool {
            if self.decide_bit_resolves(cx, e) {
                "this is a proposition, but a `Bool` is expected here; \
                 `decide_bit<…>()` around it reads its decision as a `Bool`"
                    .to_string()
            } else {
                "this is a proposition, but a `Bool` is expected here, and it has no \
                 `Decide` instance to read its decision as one"
                    .to_string()
            }
        } else {
            let got = self.display_type_clean(cx, got).unwrap_or_else(|| "a universe".into());
            match want {
                Some(w) => format!(
                    "this is a type (it has type `{got}`), but a value of `{w}` is expected here"
                ),
                None => format!(
                    "this is a type (it has type `{got}`), but a value is expected here"
                ),
            }
        };
        Some(ElabError::Elab { msg, span: e.span })
    }

    /// Does `bool::decide_bit<P>()` elaborate, for the proposition `P` written
    /// as `e`? A trial for [`Self::type_where_value_expected`]'s hint: its
    /// warnings and goals are rolled back whatever the answer.
    fn decide_bit_resolves(&self, cx: &Cx, e: &Expr) -> bool {
        let prop = expression_as_type(e).unwrap_or_else(|| Ty {
            kind: TyKind::OfExpr(Box::new(e.clone())),
            span: e.span,
        });
        let call = Expr {
            kind: ExprKind::App {
                head: Box::new(Expr {
                    kind: ExprKind::TyApp {
                        head: Box::new(Expr {
                            kind: ExprKind::Var("bool::decide_bit".to_string()),
                            span: e.span,
                        }),
                        args: vec![prop],
                    },
                    span: e.span,
                }),
                args: Vec::new(),
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span: e.span,
        };
        let _rollback = matching::MatchRollback::new(self);
        self.elab_infer(cx, &call).is_ok()
    }

    /// Notice what the kernel is going to reject, and where
    /// (`issues/check-fallback-discards-expected-type.md`). Checking that ends
    /// in inference holds an inferred type and used to drop it, so the simplest
    /// type error in the language — a literal at the wrong type — was
    /// discovered by the decl-final gate: at the declaration, with no span and
    /// no types, as a bare `NotConvertible`.
    ///
    /// The kernel stays the judge, and this method does not even raise an error:
    /// it records a candidate in [`DeclAttempt::check_notes`], which only the
    /// gate reads and only when the gate itself rejects. `Layer::Prog` against
    /// [`Self::goal_psi`] is [[auto-refl-empty-block]]'s gate, for its reason
    /// (a type mentioning an outstanding goal must still be well-scoped).
    ///
    /// **One outcome is silence rather than an error**, and it is the
    /// difference between reporting and judging: out of fuel is *inconclusive*
    /// — the gate has a fresh budget and may well succeed, and a message about
    /// two types that might yet convert is worse than no message. Only
    /// `NotConvertible`, which is the decided answer, is reported.
    fn note_check_mismatch(&self, cx: &Cx, got: &Type, expected: &Type, lvl: &Level, span: Span) {
        self.note_check_clash(cx, got, expected, lvl, span, None)
    }

    /// [`Self::note_check_mismatch`] for an argument whose type disagreed
    /// with an implicit already solved: the clash is said beside the
    /// mismatch if the gate refuses (issues/unifier-checked-assignment.md).
    fn note_check_clash(&self, cx: &Cx, got: &Type, expected: &Type, lvl: &Level, span: Span, clash: Option<application::SlotClash>) {
        // **Recording is not probing** (`issues/elab-diagnostic-probe-cost.md`).
        // The conversion below used to run here, on every checking site of
        // every declaration, to find out whether there was anything to say —
        // and on a run where nothing fails, every one of those answers was
        // discarded. What is kept here is the *candidate*: the two types, the
        // context they were compared in, and the span. The probe runs in
        // [`Self::probed_check_note`], only when the gate has actually
        // rejected the declaration.
        //
        // The one filter cheap enough to apply at record time is syntactic
        // equality, which is a decision — identical types convert — and not a
        // probe, so it costs nothing and shortens the list.
        if got == expected {
            return;
        }
        stats::count(stats::Counter::DiagCandidates);
        self.attempt.check_notes.borrow_mut().push(CheckNote {
            span,
            cx: Rc::new(cx.clone()),
            got: got.clone(),
            expected: expected.clone(),
            level: lvl.clone(),
            clash,
        });
    }

    /// The deferred half of [`Self::note_check_mismatch`]: run one recorded
    /// candidate's conversion and spelling, and return the message if it has
    /// one.
    ///
    /// A diagnostic probe is elaborator-side conversion run for the *message*,
    /// not for the judgement. That is what makes it its own column
    /// (`docs/instrumentation-design.md` §5) rather than a share of the body
    /// walk that contains the site — and now that the probe runs only on
    /// rejection, the column reads as what it always meant: on a successful
    /// module it is zero.
    fn probed_check_note(&self, note: &CheckNote) -> Option<(MismatchNote, Span)> {
        stats::count(stats::Counter::DiagNotes);
        let _phase = stats::guard(stats::Timer::DiagNote);
        let CheckNote {
            span,
            cx,
            got,
            expected,
            level,
            clash,
        } = note;
        if self
            .goal_oracle()
            .convert_type(&cx.gamma, Layer::Prog, got, expected, level)
            != Err(ConvError::NotConvertible)
        {
            return None;
        }
        // **Readable, or located.** This message makes a claim about two
        // types, and a claim the reader cannot check is worse than no claim:
        // so the claim is made only when both types spell *entirely* in
        // surface — no raw node anywhere — and do not spell **alike**. The
        // look-alike case is real and is where the display's own limit shows:
        // `And<…>` against `And<…>`, whose type arguments are the whole
        // difference ([[display-inductive-type-arguments]]).
        //
        // Below that bar the conversion was still *decided* here, so the site
        // is known, and it used to be dropped with the claim: a stuck `match`
        // in an inferred type (a commuting conversion the kernel does not
        // have) came back as a bare `NotConvertible` at the declaration and
        // was found by bisecting a generated proof by hand
        // (issues/elab-accepts-projection-through-opaque-theorem.md). So the
        // gate's verdict stays, as [`Self::note_refl_mismatch`]'s does, the
        // span moves to the site, and the note says only what it can show.
        //
        // A receiver placed into a type-owned member's unmarked first
        // parameter says more than the two types do: the declaration forgot
        // `self` (issues/type-member-missing-self-diagnostic.md).
        if let Some(msg) = self.unmarked_receiver_note(cx, *span, got) {
            return Some((MismatchNote::Spelled(msg), *span));
        }
        // Likewise a receiver at another instance of the member's type: the
        // member is what the reader wrote the call to, so it is named
        // (issues/width-specific-method-on-other-width.md).
        if let Some(msg) = self.member_receiver_note(cx, *span, got, expected) {
            return Some((MismatchNote::Spelled(msg), *span));
        }
        let got_s = self.display_type_clean(cx, got);
        let want_s = self.display_type_clean(cx, expected);
        let note = match (got_s, want_s) {
            (Some(g), Some(w)) if g != w => MismatchNote::Spelled(format!(
                "this has type `{g}`, but `{w}` is expected here{}{}{}",
                clash.as_ref().map(|c| self.slot_clash_note(cx, c)).unwrap_or_default(),
                self.opaque_equation_note(cx, got, expected),
                self.cast_help(cx, got, expected, *span),
            )),
            (Some(g), Some(_)) => MismatchNote::Located(format!(
                "this has type `{g}` where a type that displays the same is expected; \
                 they differ in something the display does not show"
            )),
            (None, Some(w)) => MismatchNote::Located(format!(
                "the type of this expression does not convert to `{w}` \
                 (its own type has no surface spelling)"
            )),
            (Some(g), None) => MismatchNote::Located(format!(
                "this has type `{g}`, which does not convert to the type expected here \
                 (that type has no surface spelling)"
            )),
            (None, None) => MismatchNote::Located(
                "the type of this expression does not convert to the type expected here \
                 (neither has a surface spelling)"
                    .to_string(),
            ),
        };
        Some((note, *span))
    }

    /// What an argument's [`application::SlotClash`] adds to its mismatch:
    /// the implicit, what an earlier argument solved it to, and what this
    /// one's type says. Each value is spelled as the type it decodes to when
    /// the slot is a type, as a term otherwise; one that does not spell
    /// leaves the clause out rather than show a raw node.
    fn slot_clash_note(&self, cx: &Cx, clash: &application::SlotClash) -> String {
        let show = |t: &Rc<Term>| match &clash.dom {
            Some(Type::Ty(level)) => {
                self.display_type_clean(cx, &Type::El { level: level.clone(), tm: Rc::clone(t) })
            }
            _ => self.spell_term_clean(cx, t),
        };
        let name = &clash.name;
        let first = show(&clash.first);
        if clash.guessed {
            // A guess is the head with its leading arguments, the last one
            // abstracted ([`unification::Guesses`]); the reader who meant
            // another argument writes the λ.
            let guess = first.or_else(|| self.spell_type_constructor(cx, clash)).map(|f| format!(" as `{f}`")).unwrap_or_default();
            let later = match clash.later.as_ref().and_then(show) {
                Some(later) => format!(", and this argument's type would make it `{later}`"),
                None => String::new(),
            };
            return format!(
                "; `{name}` was guessed{guess}{later}: no argument fixes it, so it took the type's \
                 constructor with every argument but the last, and abstracted the last. If \
                 another argument is the one that varies, give `{name}` as a λ \
                 (`{name} := λ A => …`)"
            );
        }
        match (first, clash.later.as_ref().and_then(show)) {
            (Some(first), Some(later)) if first != later => format!(
                "; `{name}` was inferred as `{first}` from an earlier argument, \
                 and this argument's type would make it `{later}`"
            ),
            _ => format!("; `{name}` was inferred from an earlier argument, and this argument's type disagrees"),
        }
    }

    /// A solution at a type-constructor slot (`M: Type → Type`), spelled
    /// applied to a hole: `Pair2<Nat>` as `Pair2<Nat, ·>`, the argument it
    /// abstracted shown where it goes. `None` for any other slot type, or a
    /// solution that does not spell.
    fn spell_type_constructor(&self, cx: &Cx, clash: &application::SlotClash) -> Option<String> {
        let Some(Type::Pi { dom_level, cod_level, dom, cod }) = &clash.dom else { return None };
        let (Type::Ty(_), Type::Ty(level)) = (&**dom, &**cod) else { return None };
        let mut hole = cx.clone();
        hole.push("·".to_string(), (**dom).clone(), dom_level.clone());
        let tm = Term::App {
            fun: Rc::new(clash.first.shift_local(1)),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(dom.shift_local(1)),
            cod: Rc::new(cod.shift_local_above(1, 1)),
            arg: Rc::new(Term::Var(LocalVar(0))),
        };
        self.display_type_clean(&hole, &Type::El { level: level.clone(), tm: Rc::new(tm) })
    }

    /// The first recorded checking mismatch that has something to say, probed
    /// in the order the sites were met: the first *spelled* one, else the
    /// first one that is only located.
    ///
    /// Recording order plus "stop at the first" is exactly the eager version's
    /// "the first note to fill the slot wins": the same candidates are tried in
    /// the same order and the same one answers. What changed is that the ones
    /// after it are never run — and that on a declaration the gate accepts,
    /// none of them is. A located note does not stop the search: it used to be
    /// silence, and a later site that names both types (or a `refl` note,
    /// which [`Self::kernel_error`] tries before it) says more.
    fn pending_mismatch(&self) -> Option<(MismatchNote, Span)> {
        let notes = self.attempt.check_notes.borrow();
        let mut located = None;
        for note in notes.iter() {
            match self.probed_check_note(note) {
                Some((MismatchNote::Spelled(msg), at)) => {
                    return Some((MismatchNote::Spelled(msg), at));
                }
                Some(found) => {
                    located.get_or_insert(found);
                }
                None => {}
            }
        }
        located
    }

    /// The first checking mismatch recorded since note `from` that the probe
    /// decides, as an error: for a construction the declaration gate never
    /// sees, such as an `IWf`-route family's signature built at its
    /// declaration (`inductive.rs`), where nothing else would refuse it.
    pub(crate) fn mismatch_since(&self, from: usize) -> Option<ElabError> {
        let notes = self.attempt.check_notes.borrow();
        notes.iter().skip(from).find_map(|note| {
            self.probed_check_note(note).map(|(m, span)| {
                let (MismatchNote::Spelled(msg) | MismatchNote::Located(msg)) = m;
                ElabError::Elab { msg, span }
            })
        })
    }

    /// [`Self::note_check_mismatch`] at the one checking form that compares
    /// nothing (`issues/elab-refl-accepts-match-eta-kernel-rejects.md`).
    ///
    /// A written `refl` emits `Refl(lhs)` against the goal's `lhs = rhs` and
    /// leaves the equation to the kernel — deliberately, and still. The cost
    /// was the message: a false equation came back as `NotConvertible` at the
    /// whole declaration, naming neither side, which is how three library
    /// proofs about `int::Int::add` were debugged the hard way. The note is filled
    /// here and read only by the gate, only when the gate rejects, so nothing
    /// is reported that the kernel did not refuse.
    ///
    /// **It adds to the gate's report; it does not replace it**, which is
    /// where this parts company with [`Self::note_check_mismatch`]. A refusal
    /// spelled `NotConvertible` at a named declaration is what the certifying
    /// pipeline's mutation controls read — a corrupted ELF header must be
    /// refused *by conversion*, not by a parse slip — and those refusals are
    /// `refl` pins whose sides are far too large to spell. So the verdict and
    /// its class stay, the span moves to the `refl`, and the two sides are
    /// appended when they can be shown.
    ///
    /// **Budgeted, and silent when the budget runs out.** Unlike the checking
    /// note, this conversion is work the kernel is about to do again, and the
    /// sides of an expensive `refl` — a certificate pinned against its
    /// transcription — are exactly where repeating it would be felt. A small
    /// budget keeps the cost of the note proportional to what it can say: a
    /// disagreement between a stuck `match` and its scrutinee is decided in a
    /// handful of steps, and anything that outruns the budget is inconclusive
    /// (`OutOfFuel`, never a wrong `NotConvertible`) and says nothing. Two
    /// syntactically identical sides skip even the world the oracle needs.
    fn note_refl_mismatch(
        &self,
        cx: &Cx,
        lhs: &Term,
        rhs: &Term,
        ty: &Type,
        level: &Level,
        span: Span,
    ) {
        if lhs == rhs {
            return;
        }
        // Recorded, not probed — [`Self::note_check_mismatch`]'s reason, and
        // the expensive half of it: the certificate is thousands of `refl`
        // pins whose two sides are large, and a budgeted conversion on every
        // one of them was 18% of a successful build
        // (`issues/elab-diagnostic-probe-cost.md`).
        stats::count(stats::Counter::DiagCandidates);
        self.attempt.refl_notes.borrow_mut().push(ReflNote {
            span,
            cx: Rc::new(cx.clone()),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            ty: ty.clone(),
            level: level.clone(),
        });
    }

    /// The deferred half of [`Self::note_refl_mismatch`]
    /// ([`Self::probed_check_note`]'s counterpart at the `refl` form).
    fn probed_refl_note(&self, note: &ReflNote) -> Option<(String, Span)> {
        // [`Self::probed_check_note`]'s column, for the same reason: the
        // conversion below is the note's, not the gate's.
        stats::count(stats::Counter::DiagNotes);
        let _phase = stats::guard(stats::Timer::DiagNote);
        let ReflNote {
            span,
            cx,
            lhs,
            rhs,
            ty,
            level,
        } = note;
        let oracle = oracle::SemanticOracle::in_world(
            self.goal_psi(),
            self.policy.fuel.min(diagnostics::REFL_NOTE_FUEL),
        );
        if oracle.convert_term(&cx.gamma, Layer::Prog, lhs, rhs, ty, level)
            != Err(ConvError::NotConvertible)
        {
            return None;
        }
        // Readable or silent, for [`Self::note_check_mismatch`]'s reason: two
        // sides the reader cannot check, or that spell alike, are worse than
        // the gate's honest `NotConvertible`.
        let (Some(lhs_s), Some(rhs_s)) = (
            self.spell_term_clean(cx, lhs),
            self.spell_term_clean(cx, rhs),
        ) else {
            return None;
        };
        if lhs_s == rhs_s {
            return None;
        }
        let opaque = self
            .opaque_stuck_note(&oracle, cx, &[lhs, rhs])
            .map_or_else(String::new, |why| format!("; {why}"));
        Some((
            format!(
                "`refl` needs both sides to be definitionally equal, \
                 but `{lhs_s}` and `{rhs_s}` are not{opaque}"
            ),
            *span,
        ))
    }

    /// [`Self::opaque_stuck_note`] for a checking note between two
    /// equations, read at their endpoints, as a suffix for the message. Only
    /// for two types that both spell — the probe has shown they are small
    /// enough to read — and only for an equation as written: a type is not
    /// reduced to find one, since a certificate's pinned equations are where
    /// reducing again costs what the gate's own check does.
    fn opaque_equation_note(&self, cx: &Cx, got: &Type, expected: &Type) -> String {
        let oracle = oracle::SemanticOracle::in_world(
            self.goal_psi(),
            self.policy.fuel.min(diagnostics::REFL_NOTE_FUEL),
        );
        let ends: Vec<&Term> = [got, expected]
            .into_iter()
            .filter_map(|ty| match ty {
                Type::Id { lhs, rhs, .. } => Some([&**lhs, &**rhs]),
                _ => None,
            })
            .flatten()
            .collect();
        self.opaque_stuck_note(&oracle, cx, &ends)
            .map_or_else(String::new, |why| format!("; {why}"))
    }

    /// Why a side of a refused conversion will never compute, when the
    /// reason is a global that does not unfold
    /// (`issues/stuck-on-opaque-theorem-diagnostic.md`). "`ex().witness` and
    /// `3` are not" reads as "the number is wrong" to a writer used to `fn`s;
    /// what is wrong is that nothing ever computes `ex().witness`.
    ///
    /// A side qualifies when its whnf is stuck eliminating
    /// ([`oracle::SemanticOracle::eliminated_global`]) a named, body-less
    /// global with no sealed proof: an `axiom`, or a `theorem` whose
    /// statement [`sealing::carries_data`] did not accept. A theorem whose
    /// statement carries data is opened by the elimination, so meeting one
    /// here means the budget ran out first, and nothing is claimed. Only on a
    /// refusal the probe already decided, so it costs an evaluation of each
    /// side under the same small budget, on the error path.
    fn opaque_stuck_note(
        &self,
        oracle: &oracle::SemanticOracle,
        cx: &Cx,
        sides: &[&Term],
    ) -> Option<String> {
        sides.iter().find_map(|side| {
            let abs = self.global_abs_of(oracle.eliminated_global(&cx.gamma, side)?)?;
            let Some(GlobalBinding::Tm { body: None, .. }) = self.psi.bindings.get(abs) else {
                return None;
            };
            if self.psi.sealed.get(abs).is_some() {
                return None;
            }
            let report = self.provenance.report(&self.global_qualified_name_at(abs)?)?;
            let name = self.global_declared_name_at(abs)?;
            Some(if report.is_axiom {
                format!(
                    "`{name}` is an axiom, so it has no proof to unfold \
                     and what is stuck on it never computes"
                )
            } else {
                format!(
                    "`{name}` is a theorem whose statement was not judged to carry data, \
                     so its proof is not kept and never unfolds; \
                     to compute with what it builds, declare it as a `fn`"
                )
            })
        })
    }

    /// The first recorded `refl` that has something to say, in the order the
    /// `refl`s were met — [`Self::pending_mismatch`]'s counterpart, preserving
    /// the same first-wins order for the same reason.
    fn pending_refl_note(&self) -> Option<(String, Span)> {
        let notes = self.attempt.refl_notes.borrow();
        notes.iter().find_map(|n| self.probed_refl_note(n))
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
        let (mbinders, mbody) =
            matching::motive_lam(motive, 1, "write `squash_ind(q, λ z => B, λ x => b)`")?;
        let (scrut_t, scrut_ty, _) = self.elab_infer(cx, scrut)?;
        let head = self.whnf(cx, &scrut_ty, scrut.span)?;
        let squash_ty = head.clone();
        let Type::Squash {
            level: src_level,
            ty: src_ty,
        } = head
        else {
            return err("`squash_ind` needs a scrutinee of type `∥A∥`", scrut.span);
        };
        let mut mcx = cx.clone();
        mcx.push(mbinders[0].clone(), squash_ty, src_level.clone());
        let (motive_t, dst_level) = self.elab_ty(&mcx, &mbody)?;

        let ExprKind::Lam { binders, body } = &case.kind else {
            return err(
                "the `squash_ind` case is a lambda: write `λ x => b`",
                case.span,
            );
        };
        if binders.len() != 1 || binders[0].ty.is_some() {
            return err(
                "the `squash_ind` case binds one unannotated witness: `λ x => b`",
                case.span,
            );
        }
        let mut bcx = cx.clone();
        bcx.push(
            binders[0].name.clone(),
            (*src_ty).clone(),
            src_level.clone(),
        );
        let packed = Rc::new(Term::Squash {
            level: src_level.clone(),
            ty: Rc::new(src_ty.shift_local(1)),
            tm: Rc::new(Term::Var(LocalVar(0))),
        });
        let inner =
            motive_t.apply_local(&LocalSubst::id(&cx.gamma).shift_local(1).extended(packed));
        let branch_ty = Type::Squash {
            level: dst_level.clone(),
            ty: Rc::new(inner),
        };
        let case_t = self.elab_check(&bcx, body, &branch_ty, &dst_level)?;
        let scrut_t = Rc::new(scrut_t);
        let result_inner =
            motive_t.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&scrut_t)));
        let result = Type::Squash {
            level: dst_level.clone(),
            ty: Rc::new(result_inner),
        };
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
    fn elab_infer_at(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<(Term, Type, Level)> {
        if let Some((input, discards)) = binding::generated(e) {
            return self
                .elab_infer_at_written(cx, e, expected)
                .map_err(|error| self.restate_bind_error(cx, input, discards, error));
        }
        if binding::generated_loop(e) {
            return self
                .elab_infer_at_written(cx, e, expected)
                .map_err(|error| self.restate_loop_error(cx, e, expected, error));
        }
        self.elab_infer_at_written(cx, e, expected)
    }

    /// [`Self::elab_infer_at`], below the binding-statement restatement.
    fn elab_infer_at_written(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<(Term, Type, Level)> {
        if let Some(receiver) = cx.dot_receiver.as_ref().and_then(|r| r.inference(cx, e)) {
            if let Some(result) = receiver.get() {
                // A failed inference must still be allowed to check against
                // a domain supplied by the enclosing call.
                if result.is_ok() || expected.is_none() {
                    stats::count(stats::Counter::DotReceiverReuses);
                    return result.clone();
                }
            } else if expected.is_none() {
                stats::count(stats::Counter::DotReceiverInferences);
                let result = self.elab_infer_uncached(cx, e, None);
                let _ = receiver.set(result.clone());
                return result;
            }
        }
        self.elab_infer_uncached(cx, e, expected)
    }

    /// `x()` where `x` is a `def`: a value is used as `x`, so the empty call
    /// is refused rather than read as the value
    /// (docs/value-definitions-design.md §2.3). A call with arguments applies
    /// a function-typed value and is not this.
    fn refuse_value_call(&self, cx: &Cx, e: &Expr) -> R<()> {
        let ExprKind::App { head, args, named, .. } = &e.kind else { return Ok(()) };
        if !args.is_empty() || !named.is_empty() {
            return Ok(());
        }
        let ExprKind::Var(name) = &head.kind else { return Ok(()) };
        if cx.names.iter_inner().any(|n| n == name)
            || cx.aliases.iter_inner().any(|a| a.name == *name)
            || cx.selfref.as_ref().is_some_and(|s| s.matches(name))
        {
            return Ok(());
        }
        let NameRes::Found(module) = self.resolve_name(name) else { return Ok(()) };
        let base = name.strip_prefix(&format!("{module}::")).unwrap_or(name);
        if self.names.is_value(&module, base) {
            return err(
                format!("`{name}` is a value (a `def`), not a function: write `{name}`, without `()`"),
                e.span,
            );
        }
        Ok(())
    }

    fn elab_infer_uncached(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<(Term, Type, Level)> {
        self.refuse_value_call(cx, e)?;
        if let ExprKind::App { head, .. } = &e.kind {
            if matches!(&head.kind, ExprKind::Var(name) if name == heather_syntax::BY_TACTIC) {
                return err(
                    "`by` runs a tactic against the statement it must prove, and there is none here; \
                     use it where the expected type is known, or annotate: `let p: P = by t;`",
                    e.span,
                );
            }
        }
        if let Some(site) = cx.corec.as_ref()
            && recursion::surface_self_call(&site.selfref, e).is_some()
        {
            let name = &site.selfref.written_name;
            return err(
                format!(
                    "this call to `{name}` is not guarded: a corecursive call must be a child of the \
                     constructor the definition returns — `C(…, {name}(…), …)` or \
                     `C(…, λ y => {name}(…), …)` (docs/codata-elaborator-design.md §5)"
                ),
                e.span,
            );
        }
        if let Some(condition) = lowered_condition(e) {
            return self.elab_condition(cx, e, &condition, expected);
        }
        let (term, ty, level) = self.elab_infer_written(cx, e, expected)?;
        Ok((self.reduced_decision(cx, e, term), ty, level))
    }

    /// An `if`'s (or a `while`'s) condition, which the parser lowered to
    /// `decide_bit<c>()` (`decide<c>()` with an evidence binder) before any
    /// type was known (issues/bool-conditions-and-literals.md). The
    /// condition's type picks the reading:
    ///
    /// - a **proposition**: its `Decide` instance's bit, as always — this
    ///   reading is tried first and is the whole cost when it succeeds;
    /// - a **`Bool`**: the Bool itself. `decide_bit<b.IsTrue()>()` is `b` by
    ///   the `IsTrue` instance's own `bit := b`, so `if b` is the match on `b`
    ///   that the frontends and `rt` read, with nothing to unfold; with
    ///   evidence (`if h: b`) it is `decide<b.IsTrue()>()`, so `h: b.IsTrue()`;
    /// - a **connective mixing the two** (`b ∧ n = 0`, `(n = 0) && b`): the
    ///   proposition with each `Bool` operand read as `b.IsTrue()`
    ///   ([`Self::mixed_condition`]).
    ///
    /// A condition that is none of these is refused naming the readings; one
    /// that does not elaborate as a term, or is a type, keeps the proposition
    /// reading's own error.
    fn elab_condition(&self, cx: &Cx, e: &Expr, c: &Condition, expected: Option<&Type>) -> R<(Term, Type, Level)> {
        let as_proposition = matching::MatchRollback::new(self);
        let proposition_error = match self.elab_infer_written(cx, e, expected) {
            Ok((term, ty, level)) => {
                as_proposition.commit();
                return Ok((self.reduced_decision(cx, e, term), ty, level));
            }
            Err(error) => error,
        };
        drop(as_proposition);
        let mut not_bool = None;
        if let Some(condition) = &c.expr {
            match self.condition_type(cx, condition, !c.evidence) {
                ConditionType::Bool(term, bool_ty) => {
                    if !c.evidence {
                        return Ok((term, bool_ty, Level::Zero));
                    }
                    // The Bool read as the proposition its `IsTrue` instance decides.
                    let span = condition.span;
                    let is_true = Ty { kind: TyKind::OfExpr(Box::new(is_true_of(condition))), span };
                    return self.elab_infer_written(cx, &decide_call(is_true, true, span), expected).map_err(|_| proposition_error);
                }
                ConditionType::Other(got) => not_bool = Some((got, condition.span)),
                ConditionType::Unread => {}
            }
        }
        if let Some(mixed) = self.mixed_condition(cx, c, expected) {
            return mixed;
        }
        if let Some((got, span)) = not_bool {
            return err(
                format!(
                    "a condition is a proposition, decided by its `Decide` instance, or a `Bool`; \
                     this is a value of `{got}`"
                ),
                span,
            );
        }
        Err(proposition_error)
    }

    /// What a condition's expression elaborates to: a `Bool` (the term and
    /// the elaborated `Bool` type), a value of another type (spelled), or
    /// nothing the `Bool` reading can use (no elaboration, or a type). Every
    /// trace of the attempt is rolled back unless `keep` and it is a `Bool`.
    fn condition_type(&self, cx: &Cx, condition: &Expr, keep: bool) -> ConditionType {
        let attempt = matching::MatchRollback::new(self);
        let bool_ty = Ty { kind: TyKind::Named { name: "bool::Bool".to_string(), args: Vec::new() }, span: condition.span };
        let Ok((term, ty, _)) = self.elab_infer(cx, condition) else { return ConditionType::Unread };
        let Ok((bool_ty, _)) = self.elab_ty(cx, &bool_ty) else { return ConditionType::Unread };
        let Ok(head) = self.whnf(cx, &ty, condition.span) else { return ConditionType::Unread };
        if matches!(head, Type::Ty(_)) {
            return ConditionType::Unread;
        }
        if self.goal_oracle().convert_type(&cx.gamma, Layer::Prog, &head, &bool_ty, &Level::Zero).is_err() {
            return ConditionType::Other(self.display_type_clean(cx, &ty).unwrap_or_else(|| "this type".into()));
        }
        if keep {
            attempt.commit();
        }
        ConditionType::Bool(term, bool_ty)
    }

    /// A connective whose operands are not all of one kind
    /// (issues/mixed-bool-prop-condition.md): the condition read on the
    /// proposition side, each `Bool` operand as `b.IsTrue()`, so
    /// `if b ∧ n = 0` decides `b.IsTrue() ∧ n = 0`, whose bit is
    /// `b && n.same(0)` by the instances, and `if h: b ∧ n = 0` binds the
    /// evidence of both. The proposition side is the one that keeps evidence
    /// available. A `Bool` subtree is one operand (`(a && b).IsTrue()`), and
    /// `&&`, `||` and `!` between a proposition and a `Bool` are read as
    /// `∧`, `∨` and `¬`. `None` when the condition is no connective or no
    /// operand is a `Bool`: the readings already tried own the error.
    ///
    /// `&&` binds tighter than `=`, so `b && n = 0` is `(b && n) = 0`, never
    /// this reading; it is written `b ∧ n = 0` or `b && (n = 0)`.
    fn mixed_condition(&self, cx: &Cx, c: &Condition, expected: Option<&Type>) -> Option<R<(Term, Type, Level)>> {
        condition_connective(&c.ty)?;
        let mut bools = 0;
        let proposition = self.mixed_operand(cx, &c.ty, true, &mut bools);
        if bools == 0 {
            return None;
        }
        let call = decide_call(proposition, c.evidence, c.ty.span);
        let attempt = matching::MatchRollback::new(self);
        let read = self.elab_infer_written(cx, &call, expected);
        if read.is_ok() {
            attempt.commit();
        }
        Some(read.map(|(term, ty, level)| (self.reduced_decision(cx, &call, term), ty, level)))
    }

    /// One operand of [`Self::mixed_condition`], rebuilt: a `Bool` as its
    /// `IsTrue`, a connective over its rebuilt operands, anything else as
    /// written. `root` is the whole condition, already known not to be a
    /// `Bool`.
    fn mixed_operand(&self, cx: &Cx, ty: &Ty, root: bool, bools: &mut usize) -> Ty {
        if !root
            && let Some(operand) = condition_expression(ty)
            && let ConditionType::Bool(..) = self.condition_type(cx, &operand, false)
        {
            *bools += 1;
            return Ty { kind: TyKind::OfExpr(Box::new(is_true_of(&operand))), span: ty.span };
        }
        match condition_connective(ty) {
            Some((name, operands)) => {
                let operands = operands.iter().map(|o| self.mixed_operand(cx, o, false, bools)).collect();
                rebuild_connective(name, operands, ty.span)
            }
            None => ty.clone(),
        }
    }

    /// `decide_bit<P>()` at a resolved instance, read as the instance's own
    /// bit (issues/native-frontend-decided-matches.md): `b.eq_bit(10)` for
    /// `b = '\n'`, `x || y` for a disjunction with each operand read the same
    /// way. An evidence-free `if` matches on this term, so the frontend, the
    /// kernel and `split_all` see the comparisons a step branches on, never
    /// the dictionary record whose proofs mention them. The way a literal's
    /// embedding is read (`reduced_embedding`): the projection unfolds only
    /// as far as the field's body. A local dictionary does not unfold.
    fn reduced_decision(&self, cx: &Cx, e: &Expr, term: Term) -> Term {
        let ExprKind::App { head, args, named, .. } = &e.kind else { return term };
        let ExprKind::TyApp { head: callee, .. } = &head.kind else { return term };
        if !matches!(&callee.kind, ExprKind::Var(name) if name == "decide_bit") || !args.is_empty() || !named.is_empty() {
            return term;
        }
        let Term::GlobalTm { var, .. } = crate::spelling::app_spine(&term).0 else { return term };
        if self.global_abs_of(*var).and_then(|abs| self.global_qualified_name_at(abs)).as_deref() != Some("bool::decide_bit") {
            return term;
        }
        self.instance_bit(cx, &term).unwrap_or(term)
    }

    /// The first reduct of a bit that is a constructor or another
    /// definition's call, with each projected argument (a connective's
    /// operand, itself an instance's bit) read the same way.
    fn instance_bit(&self, cx: &Cx, term: &Term) -> Option<Term> {
        let oracle = self.goal_oracle();
        for reduct in oracle.unfold(&cx.gamma, term, Unfold::InstanceBit) {
            if crate::spelling::is_inj(&reduct) {
                return Some(reduct);
            }
            let (head, _) = crate::spelling::app_spine(&reduct);
            // A global the source cannot name (a class field's accessor) is a
            // step of the instance's own reduction.
            if !self.named_head(head) {
                continue;
            }
            fn operands(elab: &Elaborator, cx: &Cx, term: &Term) -> Term {
                let mut output = term.clone();
                if let Term::App { fun, arg, .. } | Term::AppAt { fun, arg } = &mut output {
                    *fun = Rc::new(operands(elab, cx, fun));
                    let (head, _) = crate::spelling::app_spine(arg);
                    let accessor = matches!(head, Term::GlobalTm { .. }) && !elab.named_head(head);
                    if (accessor || crate::spelling::proj_of(arg).is_some()) && let Some(bit) = elab.instance_bit(cx, arg) {
                        *arg = Rc::new(bit);
                    }
                }
                output
            }
            return Some(operands(self, cx, &reduct));
        }
        None
    }

    /// A global the source names: a declaration, not a minted accessor.
    fn named_head(&self, head: &Term) -> bool {
        let Term::GlobalTm { var, .. } = head else { return false };
        self.global_abs_of(*var).and_then(|abs| self.global_qualified_name_at(abs)).is_some()
    }

    fn elab_infer_written(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<(Term, Type, Level)> {
        let _depth = expr::ExprDepthGuard::enter(&self.scope.expr_depth, e.span)?;
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
        if let Some(rewritten) = self.owner_rewrite(cx, e)? {
            return self.elab_infer_at(cx, &rewritten, expected);
        }
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
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
                Type::Squash {
                    level: level.clone(),
                    ty: Rc::new(ty),
                },
                level,
            ));
        }
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "emit_code")
            && !self.shadowed(cx, "emit_code")
            && self.ctor_here(cx, "emit_code").is_none()
        {
            if args.len() != 1 || !named.is_empty() {
                return err("`emit_code` takes one positional meta function name", e.span);
            }
            return self.elab_emit_code(cx, &args[0], e.span);
        }
        if matches!(e.as_named(), Some(("rel_cong" | "rel_derive", _, false)))
            && !self.shadowed(cx, e.as_named().unwrap().0)
            && self.ctor_here(cx, e.as_named().unwrap().0).is_none()
        {
            return err(format!("`{}` needs an expected relation goal; annotate this proof position", e.as_named().unwrap().0), e.span);
        }
        // `rewrite(h, …, in := hyp)` transports a hypothesis: its type is
        // what it proves (docs/equation-rewrite-design.md §7). In checking
        // position it arrives here through the inference fallback.
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "rewrite")
            && named.iter().any(|a| a.name == "in")
            && !self.shadowed(cx, "rewrite")
            && self.ctor_here(cx, "rewrite").is_none()
        {
            return self.elab_rewrite_in(cx, args, named, e.span);
        }
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
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
            | ExprKind::CollectionLit(_) => self
                .expr_elab()
                .infer_form(self, cx, e)
                .expect("classified as an ExprElab inference form"),
            // `{ let x = e; … result }` — the block's statements extend a
            // clone of `cx`, and its result is inferred there
            // (docs/let-and-blocks-design.md §4.4). Inference-transparent:
            // the block contributes no term of its own, because a `let` is an
            // alias.
            ExprKind::Char(c) => self.elab_char_infer(cx, *c, e),
            ExprKind::Scaled(lit) => self.elab_scaled_infer(cx, lit, e),
            ExprKind::Str(text) => self.elab_string_infer(cx, text, e),
            ExprKind::Block(block) => statements::infer_block(self, cx, block),
            ExprKind::RecordUpdate { base, fields } => {
                let literal = self.record_update_expr(cx, base, fields, e.span)?;
                self.elab_infer(cx, &literal)
            }
            // Intensional analysis: the result type is written, so unlike a
            // quote this one *infers*
            // (docs/certgen-transcriber-in-language-design.md §3).
            ExprKind::MatchCode {
                scrut,
                motive,
                arms,
            } => self.elab_match_code(cx, scrut, motive, arms, e.span),
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
                    self.value_skel(cx, name)
                        .filter(|s| s.leading_implicit() > 0)
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
            ExprKind::Dot {
                recv,
                name,
                tyargs,
                args,
                named,
            } => {
                let receiver_cx = cx.with_dot_receiver(recv);
                let cx = &receiver_cx;
                let resolution =
                    self.resolve_dot(cx, recv, name, tyargs, args, named, e.span)?;
                if !tyargs.is_empty() && !matches!(&resolution, DotResolution::Method(_)) {
                    return err(
                        format!("type arguments after `.{name}` require a method call"),
                        e.span,
                    );
                }
                match resolution {
                DotResolution::Inferred(t, ty, l) => Ok((t, ty, l)),
                DotResolution::Project(t, ty, l, fskel) => match args {
                    None => Ok((t, ty, l)),
                    Some(args) => self
                        .apply_projection(cx, name, t, ty, l, fskel, args, named, expected, e.span),
                },
                DotResolution::Dispatch(t, ty, l, fskel, dargs) => self
                    .apply_projection(cx, name, t, ty, l, fskel, &dargs, named, expected, e.span),
                DotResolution::Method(m) => self
                    .elab_infer_at(cx, &m, expected)
                    .map_err(|e| self.method_call_failure(cx, recv, &m, e)),
                }
            }
            // A record literal in inference position: the fields are permuted
            // into declaration order and the instantiation is recovered from
            // them, exactly as for any constructor application
            // (docs/inductive-tier0-lowering.md §2).
            ExprKind::RecordLit {
                name,
                tyargs,
                fields,
            } => {
                let args = self.record_lit_args(name, fields, e.span)?;
                let Some(ind) = self.lookup_inductive(name).cloned() else {
                    return Err(self.name_miss(name, format!("unknown type `{name}`"), e.span));
                };
                if tyargs.is_empty() {
                    self.infer_ctor(cx, &ind, 0, &args, e.span)
                } else {
                    let head = Expr {
                        kind: ExprKind::Var(name.clone()),
                        span: e.span,
                    };
                    self.ctor_at(cx, &head, tyargs, &args, e.span)
                        .unwrap_or_else(|| err(format!("unknown type `{name}`"), e.span))
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
                // A fully instantiated type such as `And<P, Q>` also has a
                // code in inference position (`let result = P ∧ Q`). A
                // same-named constructor with fields cannot infer without
                // arguments; a nullary constructor can, and keeps its term
                // reading. Checking at a universe already chooses the type
                // reading, including that ambiguous nullary case.
                if let ExprKind::Var(name) = &head.kind
                    && let Some(shape) = expr::UniverseElab::visible_type_former(self, cx, name)
                    && !shape.indexed && shape.value_parameters == 0
                    && self.ctor_here(cx, name)
                        .is_none_or(|(ind, i)| !ind.ctors[i].fields.is_empty())
                {
                    let written = surface::expression_as_type(e).expect("named type application");
                    let (ty, level) = self.elab_ty(cx, &written)?;
                    let term = expr::ExprElab::quote_type_at(self, cx, &ty, &level, &level, e.span)?;
                    return Ok((term, Type::Ty(level.clone()), Level::succ(level)));
                }
                if let Some(r) = self.ctor_at(cx, head, args, &[] as &[Expr], e.span) {
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
                let solver_here = (0..prefix).any(|k| {
                    params
                        .get(args.len() + k)
                        .is_some_and(|p| p.solver.is_some())
                });
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
            ExprKind::App { head, .. }
                if matches!(
                    &head.kind,
                    ExprKind::Var(name)
                        if matches!(
                            name.as_str(),
                            heather_syntax::ANON_CTOR_ONLY
                                | heather_syntax::ANON_CTOR_LEFT
                                | heather_syntax::ANON_CTOR_RIGHT
                        )
                ) =>
            {
                err(
                    "anonymous constructor notation is checking-only: give it an expected type",
                    e.span,
                )
            }
            // `f<T, …>(a, b)` and `@f<T, …>(a, b)`. The type arguments are
            // applied first; what happens to the remaining `{}`-implicits is
            // `@`'s business and not `<…>`'s — the two are orthogonal knobs
            // (issues/at-and-type-arguments.md).
            ExprKind::App {
                head,
                args,
                named,
                explicit,
                goal_oriented,
            } if matches!(head.kind, ExprKind::TyApp { .. }) => {
                let ExprKind::TyApp {
                    head: callee,
                    args: tyargs,
                } = &head.kind
                else {
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
                    let borrowed: Vec<&Expr> = args.iter().collect();
                    let named: Vec<_> = named.iter().collect();
                    let permuted =
                        application::resolve_constructor_arguments(&ind, ci, &borrowed, &named, e.span)?;
                    let args = permuted.as_deref().unwrap_or(&borrowed);
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
                    && cx.selfref.as_ref().is_some_and(|s| s.matches(n))
                {
                    recursion::check_self_tyargs(cx, tyargs, head.span)?;
                    application::refuse_named(
                        &format!("a recursive call to `{n}`"),
                        "the termination guard reads *which position* decreases, so a                          self-call's arguments stay where the declaration put them",
                        named,
                    )?;
                    return self.self_call_noted(cx, n, args, *explicit, e.span);
                }
                let (name, t, ty, lvl, mask) = self.elab_ty_app(cx, callee, tyargs, head.span)?;
                let params = self.params_of(&name);
                let flat;
                let full = if !*explicit && mask.iter().any(|&b| b) {
                    &mask[..]
                } else {
                    flat = vec![false; mask.len()];
                    &flat[..]
                };
                let r = application::resolve_named(
                    &name,
                    false,
                    &params,
                    tyargs.len(),
                    full,
                    args,
                    named,
                    e.span,
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
                self.lint_manual_list_construction(cx, e, &ind, i);
                if let Some(r) = self.infer_defaulted_ctor(cx, &ind, i, args.len() + named.len(), e) {
                    return r;
                }
                let permuted =
                    application::resolve_constructor_arguments(&ind, i, &args, &named, e.span)?;
                let args = permuted.unwrap_or(args);
                self.infer_ctor(cx, &ind, i, &args, e.span)
            }
            // An application whose head is *not* a name: no parameter
            // metadata exists for it, so it is always explicit.
            ExprKind::App {
                head,
                args,
                named,
                explicit,
                ..
            } if e.as_named().is_none() => {
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
            ExprKind::App {
                args,
                named,
                explicit,
                goal_oriented,
                ..
            } => {
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
                    if cx.selfref.as_ref().is_some_and(|s| s.matches(name)) {
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
                // `FS(j)` is checking-only, like `refl` and a collection literal:
                // it inhabits `Fin(Succ k)` for every `k`, and nothing in the
                // term names one (§3.1). Said only where `FS` is not some
                // other declaration's constructor and is not shadowed, so a
                // user `FS` still resolves.
                if name == "FS" && !self.shadowed(cx, name) && self.ctor_here(cx, name).is_none() {
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
                    // Ambiguous declarations are not an absent builtin name.
                    // Dot calls may select by receiver; a bare call retains
                    // the ordinary module ambiguity rule.
                    if matches!(self.resolve_name(name), NameRes::Ambiguous(_)) {
                        return Err(self.name_miss(name, String::new(), e.span));
                    }
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
                            self,
                            cx,
                            args,
                            name,
                            "no arguments",
                            e.span,
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
                    && cx.selfref.as_ref().is_some_and(|s| s.matches(f_name))
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
                            self,
                            cx,
                            args,
                            name,
                            "`(init, f)`",
                            e.span,
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
                        [arg, k] => match &k.kind {
                            ExprKind::Num(n) => match n.as_u64() {
                                Some(n) => (n as usize, arg),
                                None => return err("`inj`'s field index must fit in 64 bits", k.span),
                            },
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
                    self.lint_manual_list_construction(cx, e, &ind, i);
                    if let Some(r) = self.infer_defaulted_ctor(cx, &ind, i, args.len() + named.len(), e) {
                        return r;
                    }
                    let borrowed: Vec<&Expr> = args.iter().collect();
                    let named: Vec<_> = named.iter().collect();
                    let permuted =
                        application::resolve_constructor_arguments(&ind, i, &borrowed, &named, e.span)?;
                    let args = permuted.as_deref().unwrap_or(&borrowed);
                    return self.infer_ctor(cx, &ind, i, args, e.span);
                }
                if cx.selfref.as_ref().is_some_and(|s| s.matches(name)) {
                    return self.self_call_noted(cx, name, args, *explicit, e.span);
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
                if cx.names.iter_inner().any(|n| n == name) || cx.aliases.iter_inner().any(|a| a.name == *name)
                {
                    let (head, ty, lvl) = self.resolve(cx, name, e.span)?;
                    let skel = self.value_skel(cx, name);
                    let params = skel
                        .as_deref()
                        .map_or_else(|| Rc::new(Vec::new()), skel_params);
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
                        cx,
                        name,
                        params,
                        true,
                        0,
                        false,
                        head,
                        ty,
                        lvl,
                        args,
                        mask,
                        expected,
                        *goal_oriented,
                        e.span,
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
                        cx,
                        name,
                        params,
                        false,
                        0,
                        false,
                        head,
                        ty,
                        lvl,
                        args,
                        mask,
                        expected,
                        *goal_oriented,
                        e.span,
                    )
                }
            }
            ExprKind::Match {
                form,
                motive: Some(m),
                scrut,
                arms,
                eqbind,
                generated,
            } => {
                let (scrut_t, scrut_ty, scrut_lvl) = self.elab_infer(cx, scrut)?;
                // An indexed scrutinee's motive binds the index too
                // (docs/inductive-indexed-lowering.md §6.1).
                // Route 2b's forded family (docs/inductive-fording-lowering.md
                // §12.1): the same two-binder motive rule as route 1's, over
                // the Σ+`sEq` form instead of the eliminator's.
                if let Some((ind, fam)) = self.iwf_of_at(cx, &scrut_ty) {
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
                    let t = self.elab_match_iwf(
                        acx,
                        *form,
                        &ind,
                        &fam,
                        arms,
                        scrut_t,
                        motive2,
                        mlvl.clone(),
                        crate::iwf_family::IndexMotive::Plain,
                        e.span,
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
                        acx,
                        *form,
                        &ind,
                        &fam,
                        arms,
                        scrut_t,
                        motive2,
                        mlvl.clone(),
                        e.span,
                    )?;
                    return Ok((t, result, mlvl));
                }
                let (binders, body) = matching::motive_lam(m, 1, "write `as \u{3bb} z => T`")?;
                let mut mcx = cx.clone();
                mcx.push(binders[0].clone(), scrut_ty.clone(), scrut_lvl.clone());
                let (motive, mlvl) = self.elab_ty(&mcx, &body)?;
                let result = motive
                    .apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(scrut_t.clone())));
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
                    cx,
                    *form,
                    *generated,
                    arms,
                    scrut_t,
                    &scrut_ty,
                    &scrut_lvl,
                    motive,
                    mlvl.clone(),
                    e.span,
                )?;
                Ok((t, result, mlvl))
            }
            // A motive-less `match` whose branches do not depend on the
            // scrutinee: one arm names the type, and the motive is that type,
            // constant (issues/match-arg-of-polymorphic-callee-needs-motive.md).
            // Tried before the message below, and only ever *replaced* by it —
            // a synthesis that does not go through leaves no trace.
            ExprKind::Match {
                form,
                motive: None,
                scrut,
                arms,
                eqbind,
                generated,
            } => {
                if *form == MatchForm::If && eqbind.is_none() {
                    match matching::infer_if_constant_motive(
                        self, cx, scrut, arms, *generated, e.span,
                    ) {
                        matching::MotiveInference::Accepted(result) => return Ok(result),
                        matching::MotiveInference::Failed(error) => return Err(error),
                        matching::MotiveInference::Declined => {}
                    }
                }
                match matching::infer_match_constant_motive_eq(
                    self, cx, *form, scrut, arms, eqbind.as_deref(), *generated, e.span,
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
                            MatchForm::If =>
                                "give the `if` an expected result type, for \
                                              example with an annotated `let`",
                            MatchForm::IfLet =>
                                "give the `if let` an expected result type, for \
                                                 example with an annotated `let`",
                        }
                    ),
                    e.span,
                )
            }
            // Both the form and the *suggested spelling* are the written
            // one: `match e as \u{3bb} z => T { … }` is not a thing a writer who
            // typed `split` can paste (issues/diagnostics-name-the-written-form.md).
            ExprKind::Match {
                form, motive: None, ..
            } => err(
                format!(
                    "`{}` in inference position needs a motive: `{}`",
                    form.keyword(),
                    match form {
                        MatchForm::Match => "match e as \u{3bb} z => T { … }",
                        MatchForm::Split => "split e as \u{3bb} z => T;",
                        MatchForm::If =>
                            "give the `if` an expected result type, for \
                                          example with an annotated `let`",
                        MatchForm::IfLet =>
                            "give the `if let` an expected result type, for \
                                             example with an annotated `let`",
                    }
                ),
                e.span,
            ),
            ExprKind::J {
                proof,
                motive,
                case,
            } => {
                let (mbinders, mbody) =
                    matching::motive_lam(motive, 2, "write `j(p, \u{3bb} y q => T, case)`")?;
                let (y, p) = (&mbinders[0], &mbinders[1]);
                let (proof_t, proof_ty, _) = self.elab_infer(cx, proof)?;
                let head = self.whnf(cx, &proof_ty, proof.span)?;
                let Type::Id {
                    level,
                    ty,
                    lhs,
                    rhs,
                } = head
                else {
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
                &Expr {
                    kind: ExprKind::Var("refl".to_string()),
                    span: e.span,
                },
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

    /// A motive-less `match` with no equation binding, whose arms see the
    /// equation `e = pattern` as **pending** (docs/dependent-match-compiler-
    /// design.md §4.3): the arms elaborate without it, and a reader of
    /// hypotheses that ran in them records that it wanted it. Only when the
    /// arms then fail is the match elaborated again as its convoy, with the
    /// equation bound under [`MATCH_EQ`]; a match that checks without the
    /// equation keeps its term, so function bodies and every conversion
    /// against a restated `match` are unchanged. If the convoy fails too, the
    /// first error is the one reported.
    ///
    /// An indexed family has no homogeneous equation yet (§9), so there the
    /// match is elaborated once, as before.
    fn elab_match_pending(
        &self,
        cx: &Cx,
        scrut_ty: &Type,
        run: &dyn Fn(&Cx, Option<&str>) -> R<Term>,
    ) -> R<Term> {
        if self.iwf_of_at(cx, scrut_ty).is_some() || self.indexed_of_at(cx, scrut_ty).is_some() {
            return run(cx, None);
        }
        let id = self.attempt.match_eq_next.get();
        self.attempt.match_eq_next.set(id.wrapping_add(1));
        let mark = matching::MatchSpeculationState::mark_match_state(self);
        let mut pcx = cx.clone();
        let mut pending = (*pcx.pending_eqs).clone();
        pending.push(id);
        pcx.pending_eqs = Rc::new(pending);
        let first = run(&pcx, None);
        let wanted = {
            let mut wanted = self.attempt.match_eq_wanted.borrow_mut();
            let had = wanted.contains(&id);
            wanted.retain(|w| *w != id);
            had
        };
        match first {
            Err(error) if wanted => {
                matching::MatchSpeculationState::rollback_match_state(self, mark);
                run(cx, Some(MATCH_EQ)).map_err(|_| {
                    matching::MatchSpeculationState::rollback_match_state(self, mark);
                    error
                })
            }
            other => other,
        }
    }

    /// A reader of hypotheses (`omega`, `linarith`) is about to list them:
    /// every pending match equation in scope is wanted (§4.3).
    pub(crate) fn want_match_equations(&self, cx: &Cx) {
        if cx.pending_eqs.is_empty() {
            return;
        }
        let mut wanted = self.attempt.match_eq_wanted.borrow_mut();
        for id in cx.pending_eqs.iter() {
            if !wanted.contains(id) {
                wanted.push(*id);
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
        // An indexed family's arms live at *different* indices, so `e = z`
        // would relate two values at two types. The index packed with the
        // value is one type, `Σ(j: I). F(j)`, and that equation is the one
        // bound (docs/dependent-match-compiler-design.md §9).
        if let Some((ind, fam)) = self.iwf_of_at(cx, scrut_ty) {
            let family = PackedFamily {
                ity: fam.ity.clone(),
                ilvl: fam.ilvl.clone(),
                flvl: fam.lvl(),
                idx: Rc::clone(&fam.idx),
                at: &|i, k| fam.ty_at(i, k),
                eliminate: &|acx: &Cx, arms: &[Arm], scrut: Term, motive: Type, level: Level| {
                    self.elab_match_iwf(
                        acx, form, &ind, &fam, arms, scrut, motive, level,
                        iwf_family::IndexMotive::Plain, span,
                    )
                },
            };
            return self.elab_convoy_packed(
                cx, form, generated, h, arms, scrut_t, scrut_ty, scrut_lvl, &family, motive, mlvl,
                result, span,
            );
        }
        if let Some((ind, fam)) = self.indexed_of_at(cx, scrut_ty) {
            let (ity, ilvl) = self.index_type_of(cx, &ind, span)?;
            let family = PackedFamily {
                ity,
                ilvl,
                flvl: fam.level.clone(),
                idx: Rc::clone(&fam.idx),
                at: &|i, k| fam.el_at(i, k),
                eliminate: &|acx: &Cx, arms: &[Arm], scrut: Term, motive: Type, level: Level| {
                    self.elab_match_indexed(acx, form, &ind, &fam, arms, scrut, motive, level, span)
                },
            };
            return self.elab_convoy_packed(
                cx, form, generated, h, arms, scrut_t, scrut_ty, scrut_lvl, &family, motive, mlvl,
                result, span,
            );
        }
        let plan = matching::plan_convoy(h, arms, &scrut_t, scrut_ty, scrut_lvl, &motive, mlvl);
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
            elim, scrut_t, scrut_ty, scrut_lvl, mlvl, result,
        ))
    }

    /// [`Self::elab_convoy`] on an indexed family (design §9): each arm takes
    /// `h : ⟨i, e⟩ = ⟨idx(C, x̄), C(x̄)⟩` at `Σ(j: I). F(j)`, through the
    /// two-binder motive `λ j z => Π(p: ⟨i, e⟩ = ⟨j, z⟩). M(j, z)`, applied to
    /// `refl`. `M(j, z)` is the index generalized as route 1 does it; the
    /// equation's left side is not, since it is the scrutinee's own.
    #[allow(clippy::too_many_arguments)]
    fn elab_convoy_packed(
        &self,
        cx: &Cx,
        form: MatchForm,
        generated: bool,
        h: &str,
        arms: &[Arm],
        scrut_t: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        fam: &PackedFamily<'_>,
        motive: Type,
        mlvl: &Level,
        result: &Type,
        span: Span,
    ) -> R<Term> {
        let m2 = self.generalize_index(cx, &motive, &fam.idx);
        let (ilvl, flvl) = (fam.ilvl.clone(), fam.flvl.clone());
        let slvl = Level::join(ilvl.clone(), flvl.clone());
        // `Σ(j: I). F(j)` and `⟨i, z⟩`, scoped `k` binders past Γ.
        let sigma = |k: u32| Type::Sigma {
            fst_level: ilvl.clone(),
            snd_level: flvl.clone(),
            fst: Rc::new(fam.ity.shift_local(k)),
            snd: Rc::new((fam.at)(Term::Var(LocalVar(0)), k + 1)),
        };
        let pack = |k: u32, i: Term, z: Term| Term::Pair {
            fst_level: ilvl.clone(),
            snd_level: flvl.clone(),
            fst_ty: Rc::new(fam.ity.shift_local(k)),
            snd_ty: Rc::new((fam.at)(Term::Var(LocalVar(0)), k + 1)),
            fst: Rc::new(i),
            snd: Rc::new(z),
        };
        let here = pack(0, (*fam.idx).clone(), scrut_t.clone());
        // Over `(Γ, j, z)`.
        let equation = Type::Id {
            level: slvl.clone(),
            ty: Rc::new(sigma(2)),
            lhs: Rc::new(here.shift_local(2)),
            rhs: Rc::new(pack(2, Term::Var(LocalVar(1)), Term::Var(LocalVar(0)))),
        };
        let convoyed = Type::Pi {
            dom_level: slvl.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(equation),
            cod: Rc::new(m2.shift_local(1)),
        };
        let clvl = Level::join(slvl.clone(), mlvl.clone());
        let at_scrut = Type::Id {
            level: slvl.clone(),
            ty: Rc::new(sigma(0)),
            lhs: Rc::new(here.clone()),
            rhs: Rc::new(here.clone()),
        };
        let convoyed_here = Type::Pi {
            dom_level: slvl.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(at_scrut.clone()),
            cod: Rc::new(result.shift_local(1)),
        };
        let plan = matching::plan_convoy(h, arms, &scrut_t, scrut_ty, scrut_lvl, &motive, mlvl);
        let prepared = self.prepare_arms(
            cx, form, generated, &plan.arms, &scrut_t, scrut_ty, scrut_lvl, &convoyed_here, false,
            &clvl, span,
        )?;
        let (acx, arms) = match &prepared {
            Some((c, a)) => (c, a.as_slice()),
            None => (cx, plan.arms.as_slice()),
        };
        let elim = (fam.eliminate)(acx, arms, scrut_t, convoyed, clvl)?;
        Ok(crate::spelling::checked_app(
            Rc::new(elim),
            slvl.clone(),
            mlvl.clone(),
            Rc::new(at_scrut),
            Rc::new(result.shift_local(1)),
            Rc::new(Term::Refl { level: slvl, ty: Rc::new(sigma(0)), tm: Rc::new(here) }),
        ))
    }

    /// [`Self::elab_convoy`] at a motive that reads the equation as well:
    /// `dependent` is scoped under the scrutinee's binder and then the
    /// equation's, and `motive` is it with the equation unused, as the other
    /// readers of a motive expect it. `split_all` builds one where a convoy
    /// in the goal takes the case's equation for its own `refl`
    /// (`goal_combinators::dependent_motive`).
    #[allow(clippy::too_many_arguments)]
    fn elab_convoy_dependent(
        &self,
        cx: &Cx,
        h: &str,
        arms: &[Arm],
        scrut_t: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        motive: Type,
        dependent: Type,
        mlvl: &Level,
        result: &Type,
        span: Span,
    ) -> R<Term> {
        let mut plan = matching::plan_convoy(h, arms, &scrut_t, scrut_ty, scrut_lvl, &motive, mlvl);
        if let Type::Pi { cod, .. } = &mut plan.motive {
            *cod = Rc::new(dependent);
        }
        let elim = self.elab_match(
            cx,
            heather_syntax::MatchForm::Match,
            true,
            &plan.arms,
            scrut_t.clone(),
            scrut_ty,
            scrut_lvl,
            plan.motive,
            plan.level,
            span,
        )?;
        Ok(matching::finish_convoy(
            elim, scrut_t, scrut_ty, scrut_lvl, mlvl, result,
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
        // class is optional at the language level: a program whose closure
        // does not hold the standard algebra module keeps the historical
        // Nat-only mismatch below. Once `algebra::Numeral` is in the closure,
        // however — read by identity, not by a name this module may not
        // import (issues/numerals-without-algebra-import.md) — a missing
        // instance is the useful diagnosis and not a later Nat-vs-carrier
        // conversion error.
        if let Some((ind, named)) = self.literal_class_record(literals::NUMERAL)
            && let Some(field) = ind.field_index("ofNat")
        {
            let targs = [(expected.clone(), expected_level.clone())];
            let (goal, goal_level) = self.lower_instance(cx, &ind, &targs, &[], span)?;
            let carrier = self
                .type_namespace(cx, expected, span)
                .unwrap_or_else(|| "the expected type".to_string());
            let display = format!("Numeral<{carrier}>");
            let mut trace = Vec::new();
            match self.resolve_goal(cx, &goal, &goal_level, &display, None, span, &mut trace) {
                Some(dict) => {
                    let (embed, embed_ty, embed_level) =
                        self.project_field(cx, &ind, &goal, Rc::new(dict), field, span)?;
                    let since = self.attempt.trivial_uses.borrow().len();
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
                    self.settle_deferred_units(since)?;
                    return Ok(self.reduced_embedding(cx, out));
                }
                None if named => {
                    return Err(ElabError::Resolution {
                        goal: display,
                        span,
                        trace,
                    });
                }
                // Reached by identity only, and no instance: the `Nat`
                // reading below, as before the class was reachable.
                None => {}
            }
        }
        // A numeral is the leaf case of
        // `issues/check-fallback-discards-expected-type.md`: its inferred type
        // is `Nat` without any work at all, so comparing costs one conversion
        // against a type the caller already had.
        let (num, num_ty, _) = self.elab_infer(cx, e)?;
        self.note_check_mismatch(cx, &num_ty, expected, &Level::Zero, span);
        Ok(num)
    }

    /// Interpret `[…]` through the one protocol owned by the implicit
    /// prelude. The syntax supplies both class inputs: the expected container
    /// and the literal's statically known length. The dictionary's dependent
    /// `element` field then supplies the checking type for every entry, and
    /// `fromLiteral` consumes the primitive vector lowering.
    fn check_collection_literal(
        &self,
        cx: &Cx,
        literal: &Expr,
        elems: &[Expr],
        expected: &Type,
        expected_level: &Level,
        span: Span,
    ) -> R<Term> {
        let class_key = names::qkey(PRELUDE_MODULE, "CollectionLiteral");
        let class = self
            .traits
            .class(&class_key)
            .cloned()
            .ok_or_else(|| ElabError::Elab {
                msg: "internal: the prelude collection-literal protocol is missing".into(),
                span,
            })?;
        let ind = self
            .types
            .inductive(&class_key)
            .cloned()
            .ok_or_else(|| ElabError::Elab {
                msg: "internal: the prelude collection-literal dictionary is missing".into(),
                span,
            })?;
        if class.params.len() != 1 || class.valparams.len() != 1 {
            return err("internal: malformed prelude collection-literal protocol", span);
        }
        let Some(element_field) = ind.field_index("element") else {
            return err("internal: collection-literal protocol has no `element` field", span);
        };
        let Some(from_field) = ind.field_index("fromLiteral") else {
            return err(
                "internal: collection-literal protocol has no `fromLiteral` field",
                span,
            );
        };

        // The carrier by its code, when it has one: a field's `List<Instr>`
        // arrives as its inline lowering, and the goal and the two
        // conversions below would otherwise compare that against the
        // instance's code-spelled type by unfolding every code inside it —
        // each element type's whole sum, and every sum its fields name, per
        // literal (`issues/native-tool-test-cold-certificate-rail.md`, log).
        let respelled = self.respell_ty(cx, expected);
        let expected = respelled.as_ref().unwrap_or(expected);
        let length = inductive::nat_lit(elems.len());
        let targs = [(expected.clone(), expected_level.clone())];
        let vargs = [(length.clone(), Type::Nat, Level::Zero)];
        let (goal, goal_level) = self.lower_instance(cx, &ind, &targs, &vargs, span)?;
        let carrier = self.display_type(cx, expected);
        let display = format!("CollectionLiteral<{carrier}>({})", elems.len());
        let mut trace = Vec::new();
        let Some(dict) = self.resolve_goal(cx, &goal, &goal_level, &display, None, span, &mut trace)
        else {
            return Err(ElabError::Resolution { goal: display, span, trace });
        };
        let dict = Rc::new(dict);

        let (element, element_universe, _) =
            self.project_field(cx, &ind, &goal, Rc::clone(&dict), element_field, span)?;
        // Projection from a resolved dictionary can retain the whole
        // dependent dictionary term. Normalize the field value before it is
        // embedded in every vector-element annotation below.
        let element = (*self.whnf_tm(cx, &element, span)?).clone();
        let Type::Ty(element_level) = self.whnf(cx, &element_universe, span)? else {
            return err(
                "internal: collection-literal `element` is not a type code",
                span,
            );
        };
        let element_ty = Type::El {
            level: element_level.clone(),
            tm: Rc::new(element),
        };
        // Build the compact domain before projecting `fromLiteral`: keeping
        // this independently rooted prevents the later dependent projection
        // from becoming part of the vector's annotations.
        let literal_dom = Type::Vec {
            level: element_level.clone(),
            elem: Rc::new(element_ty.clone()),
            len: Rc::new(length),
        };

        let (from, from_ty, _) =
            self.project_field(cx, &ind, &goal, dict, from_field, span)?;
        let from = (*self.whnf_tm(cx, &from, span)?).clone();
        let Type::Pi {
            dom_level: _,
            cod_level,
            dom,
            cod,
        } = self.whnf(cx, &from_ty, span)?
        else {
            return err(
                "internal: collection-literal `fromLiteral` is not a function",
                span,
            );
        };
        let Type::Vec { elem: vector_element, .. } = &*inductive::decoded(&dom) else {
            return err(
                "internal: collection-literal `fromLiteral` does not accept a vector",
                span,
            );
        };
        if !self.conv_types(cx, vector_element, &element_ty, &element_level) {
            return err(
                "internal: collection-literal element and conversion domain disagree",
                span,
            );
        }
        // Checking the same surface node directly through ExprElab is the
        // bootstrap boundary: it constructs the primitive vector and cannot
        // re-enter this protocol route.
        let vector = self
            .expr_elab()
            .check_indexed_form(self, cx, literal, &literal_dom)
            .expect("a collection literal is an indexed vector checking form")?;
        let vector = Rc::new(vector);
        let result_ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&vector)));
        if !self.conv_types(cx, &result_ty, expected, &cod_level) {
            return err(
                "internal: collection-literal conversion does not return its carrier",
                span,
            );
        }
        let converted = crate::spelling::checked_app(
            Rc::new(from),
            element_level,
            expected_level.clone(),
            Rc::new(literal_dom),
            Rc::new(expected.shift_local(1)),
            vector,
        );
        let value = (*self.whnf_tm(cx, &converted, span)?).clone();
        Ok(self.collection_literal_spine(cx, value, elems.len()))
    }

    /// A local variable by absolute position (outermost first), as
    /// [`Self::resolve`] would return it.
    pub(crate) fn local(&self, cx: &Cx, pos: usize) -> (Term, Type, Level) {
        let idx = (cx.names.len() - 1 - pos) as u32;
        let entry = &cx.gamma.entries[pos];
        (
            Term::Var(LocalVar(idx)),
            entry.ty.shift_local(idx + 1),
            entry.level.clone(),
        )
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
    ///
    /// Both notes are *probed* here rather than read: the conversion that
    /// decides whether either has anything to say runs at this verdict, not at
    /// the site it was recorded at (`issues/elab-diagnostic-probe-cost.md`).
    /// This is the only place a rejection is reported from — the parallel
    /// gate's join reports no note, discards its pass and replays it serially
    /// (`docs/parallel-kernel-gate-design.md` §5.1) — so the candidates are
    /// always in hand, at every width.
    ///
    /// A written `refl`'s note ([`Self::note_refl_mismatch`]) travels a third
    /// way: it neither replaces the report nor merely annotates the
    /// declaration. The verdict stays the kernel's, and the *span* becomes the
    /// `refl` that stands for it — the one expression in the body that claimed
    /// the conversion the gate refused. A checking mismatch whose types do not
    /// both spell travels the same way ([`MismatchNote::Located`]), when no
    /// `refl` note has more to say.
    fn kernel_error(&self, decl: &str, span: Span, e: TypeError) -> ElabError {
        // A head of the wrong former is the same disagreement met one step
        // later: a proof of `same(x, y)` filled into a goal whose statement
        // unfolds to a Π is refused where the goal is *applied*, as
        // `HeadMismatch`, and the site that explains it is the checking note
        // at the `on` (issues/elab-accepts-conjunction-for-equation.md).
        let conversion = matches!(e, TypeError::NotConvertible | TypeError::HeadMismatch);
        if conversion
            && let Some((note, at)) = self.refused_decide().or_else(|| self.refused_trivial())
        {
            return ElabError::Kernel {
                decl: decl.to_string(),
                span: at,
                err: e,
                note: Some(note),
                site: KernelSite::Recorded,
            };
        }
        let mismatch = conversion
            .then(|| self.pending_mismatch())
            .flatten();
        let located = match mismatch {
            Some((MismatchNote::Spelled(msg), at)) => {
                let msg = match self.operator_fallback_note() {
                    Some(note) => format!("{msg} (note: {note})"),
                    None => msg,
                };
                return ElabError::Elab { msg, span: at };
            }
            Some((MismatchNote::Located(msg), at)) => Some((msg, at)),
            None => None,
        };
        let refl = conversion
            .then(|| self.pending_refl_note())
            .flatten()
            .or(located);
        let (span, refl_note) = match refl {
            Some((msg, at)) => (at, Some(msg)),
            None => (span, None),
        };
        let site = if refl_note.is_some() {
            KernelSite::Recorded
        } else if conversion {
            KernelSite::Unrecorded
        } else {
            KernelSite::Other
        };
        let note = match (refl_note, self.operator_fallback_note()) {
            (Some(refl), Some(op)) => Some(format!("{refl} (note: {op})")),
            (Some(refl), None) => Some(refl),
            (None, op) => op,
        };
        ElabError::Kernel {
            decl: decl.to_string(),
            span,
            err: e,
            note,
            site,
        }
    }

    /// [`Self::kernel_error`] for a refusal of `body` at `ty` (or of `ty`
    /// itself, with no body) in `psi`; Γ: when no recorded site's probe
    /// decides it, ask the kernel where it failed
    /// (`issues/elab-accepts-conjunction-for-equation.md`).
    ///
    /// **Why the kernel, and why only here.** Every recorded site is a place
    /// the elaborator *knew* it was trusting the gate. An unrecorded refusal
    /// is one where it did not know — a route that placed a term without
    /// comparing or recording — and no list of routes kept by hand closes
    /// that class: the inferred-argument route (#168), the β-redex spelling
    /// (#184) and the check fallback were each found by a bisection after a
    /// bare `NotConvertible`. The kernel is the one place every placement
    /// passes through, so it is the one that can always say where. It costs
    /// one more check of the refused declaration, and runs on no other path.
    ///
    /// The located term is then looked for among the recorded sites, by
    /// syntax: a site whose probe was only *inconclusive* (a `refl` whose
    /// sides outran the note's small budget) is still the site, and the
    /// kernel has now decided it, so the report moves there as if the probe
    /// had. Only a refusal that matches no recorded site stays
    /// [`KernelSite::Unrecorded`], at the declaration, naming the refused
    /// term and its two types where they spell.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn kernel_refusal(
        &self,
        decl: &str,
        span: Span,
        e: TypeError,
        psi: &GlobalCtx,
        layer: Layer,
        gamma: &LocalCtx,
        body: Option<&Term>,
        ty: &Type,
        level: &Level,
    ) -> ElabError {
        let error = self.kernel_error(decl, span, e);
        let ElabError::Kernel { site: KernelSite::Unrecorded, note: op_note, .. } = &error else {
            return error;
        };
        let with_op = |said: String| match op_note {
            Some(op) => format!("{said} (note: {op})"),
            None => said,
        };
        let found = match body {
            Some(body) => typing::locate_refusal(psi, 0, layer, gamma, body, ty, level, self.policy.fuel),
            None => typing::locate_type_refusal(psi, 0, layer, gamma, ty, level, self.policy.fuel),
        };
        let said = match &found {
            Some(found) if found.psi_len == psi.bindings.len() => {
                if let Some(at) = self.recorded_site_of(psi, found) {
                    return at.into_error(decl, e, with_op);
                }
                self.refused_site_note(found)
            }
            Some(_) => "no checking site recorded this refusal; the kernel refused a term \
                        under a binder of the global context, which has no surface spelling"
                .to_string(),
            None => "no checking site recorded this refusal, and the kernel refused no \
                     term check in it"
                .to_string(),
        };
        ElabError::Kernel {
            decl: decl.to_string(),
            span,
            err: e,
            note: Some(with_op(said)),
            site: KernelSite::Unrecorded,
        }
    }

    /// The recorded site a located refusal is, if any: a written `refl` at
    /// the same depth whose side converts with the refused `Refl`'s, or a
    /// checking site at the same depth whose two types convert with the
    /// refused check's. **By conversion, not syntax**: the kernel holds the
    /// emitted spelling (the statement and every slot are respelled on their
    /// way through the emission chokepoint), the note the elaborator's, and
    /// the two differ in exactly the way conversion forgives. Budgeted like
    /// the `refl` note; out of budget is no match. Only in a world with no
    /// goal slots, where the two sides' global indices agree.
    fn recorded_site_of(&self, psi: &GlobalCtx, found: &typing::RefusedSite) -> Option<RecordedSite> {
        let world = self.goal_psi();
        if world.bindings.len() != psi.bindings.len() {
            return None;
        }
        let oracle = oracle::SemanticOracle::in_world(world, self.policy.fuel.min(diagnostics::REFL_NOTE_FUEL));
        let gamma = &found.gamma;
        let same_depth = |c: &Cx| c.gamma.base == gamma.base && c.gamma.entries.len() == gamma.entries.len();
        if let Term::Refl { tm, .. } = &found.term {
            let refls = self.attempt.refl_notes.borrow();
            let site = refls.iter().find(|n| {
                same_depth(&n.cx)
                    && (n.lhs == **tm || oracle.convert_term(gamma, Layer::Prog, &n.lhs, tm, &n.ty, &n.level).is_ok())
            });
            if let Some(n) = site {
                let sides = self.spell_term_clean(&n.cx, &n.lhs).zip(self.spell_term_clean(&n.cx, &n.rhs));
                return Some(RecordedSite::Refl { span: n.span, sides });
            }
        }
        let (Some(expected), Some(inferred)) = (&found.expected, &found.inferred) else {
            return None;
        };
        let converts = |a: &Type, b: &Type, level: &Level| {
            a == b || oracle.convert_type(gamma, Layer::Prog, a, b, level).is_ok()
        };
        let checks = self.attempt.check_notes.borrow();
        let n = checks.iter().find(|n| {
            same_depth(&n.cx) && converts(&n.expected, expected, &n.level) && converts(&n.got, inferred, &n.level)
        })?;
        let got = self.display_type_clean(&n.cx, &n.got);
        let want = self.display_type_clean(&n.cx, &n.expected);
        Some(RecordedSite::Check { span: n.span, types: got.zip(want).filter(|(g, w)| g != w) })
    }

    /// The located refusal, said: the term and the two types, each where it
    /// spells in full ([`Self::spell_term_clean`], [`Self::display_type_clean`]:
    /// a claim about a type the reader cannot check is worse than none).
    fn refused_site_note(&self, found: &typing::RefusedSite) -> String {
        let cx = self.refused_site_cx(found);
        let term = cx.as_ref().and_then(|cx| self.spell_term_clean(cx, &found.term));
        let spell = |ty: &Option<Type>| match (&cx, ty) {
            (Some(cx), Some(ty)) => self.display_type_clean(cx, ty),
            _ => None,
        };
        let (got, want) = (spell(&found.inferred), spell(&found.expected));
        let what = match term {
            Some(t) => format!("`{t}`"),
            None => "a term with no surface spelling".to_string(),
        };
        let types = match (got, want) {
            (Some(g), Some(w)) if g != w => format!(", which has type `{g}`, where `{w}` is expected"),
            (Some(g), Some(_)) => format!(
                ", which has type `{g}` where a type that displays the same is expected"
            ),
            (None, Some(w)) => format!(" where `{w}` is expected"),
            (Some(g), None) => format!(", which has type `{g}`"),
            (None, None) => String::new(),
        };
        format!(
            "no checking site recorded this refusal: the kernel refused {what}{types} \
             (an elaborator gap: issues/elab-accepts-conjunction-for-equation.md)"
        )
    }

    /// Names for a located refusal's Γ, binder by binder: the name a
    /// recorded site's context gave it, where that context shares Γ up to
    /// it (those are the binders the source wrote, under the names it
    /// wrote); else the declaration's parameter name at that position (the
    /// kernel's outermost binders are the telescope, whose types the
    /// statement respells, so they are matched by position); else a fresh
    /// name, as the display names a binder the kernel does not name.
    fn refused_site_cx(&self, found: &typing::RefusedSite) -> Option<Cx> {
        let gamma = &found.gamma;
        if !matches!(gamma.base, heather_kernel::term::CtxBase::Nil) {
            return None;
        }
        let shared = |c: &Cx| -> usize {
            if c.gamma.base != gamma.base {
                return 0;
            }
            (0..c.gamma.entries.len().min(gamma.entries.len()))
                .take_while(|&i| c.gamma.entries.get(i) == gamma.entries.get(i))
                .count()
        };
        let checks = self.attempt.check_notes.borrow();
        let refls = self.attempt.refl_notes.borrow();
        let none = crate::spine::Binders::default();
        let (k, written) = checks.iter().map(|n| &n.cx).chain(refls.iter().map(|n| &n.cx))
            .map(|c| (shared(c), &c.names))
            .max_by_key(|(k, _)| *k)
            .unwrap_or((0, &none));
        let telescope = self.attempt.telescope.borrow();
        let mut cx = Cx::empty();
        for i in 0..gamma.entries.len() {
            let entry = gamma.entries.get(i)?;
            let name = match (i < k).then(|| written.get(i)).flatten().or_else(|| telescope.get(i)) {
                Some(name) => name.to_string(),
                None => ["x", "y", "z", "a", "b", "c"]
                    .iter()
                    .map(|n| n.to_string())
                    .chain((i..).map(|n| format!("x{n}")))
                    .find(|n| !cx.names.contains(n))?,
            };
            cx.push(name, (*entry.ty).clone(), entry.level.clone());
        }
        Some(cx)
    }

    /// Is a bare `decide` something the writer bound, rather than the goal
    /// combinator? The library's own `bool::decide` is the one global that
    /// does not count (see the checking arm).
    fn decide_shadowed(&self, cx: &Cx) -> bool {
        cx.names.iter_inner().any(|n| n == "decide")
            || cx.aliases.iter_inner().any(|a| a.name == "decide")
            || cx.selfref.as_ref().is_some_and(|s| s.matches("decide"))
            || self
                .key_of("decide")
                .is_some_and(|key| key != names::qkey("bool", "decide"))
    }

    /// The `decide` goal combinator: elaborate `bool::decide_yes(refl)` at
    /// the goal and remember what it resolved to, so a gate refusal can be
    /// reported at this `decide` with the instance named.
    fn elab_decide(&self, cx: &Cx, expected: &Type, lvl: &Level, span: Span) -> R<Term> {
        let Some(yes) = self.key_of("bool::decide_yes") else {
            return err(
                "`decide` proves a closed goal by running its `Decide` instance, and needs \
                 the class in scope: add `import bool;`",
                span,
            );
        };
        let e = Expr {
            kind: ExprKind::App {
                head: Box::new(Expr {
                    kind: ExprKind::Var(yes),
                    span,
                }),
                args: vec![Expr {
                    kind: ExprKind::Refl,
                    span,
                }],
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        let t = self.elab_check(cx, &e, expected, lvl)?;
        // `decide_yes(P, inst, refl)`, outermost argument first: the `refl`,
        // whose left side is `or_index(inst.dec)`, then the dictionary.
        let mut args = Vec::new();
        let mut head = &t;
        while let Some((fun, arg)) = crate::spelling::app_of(head) {
            args.push(&**arg);
            head = fun;
        }
        if let [Term::Refl { tm, .. }, inst, ..] = args.as_slice() {
            // The instance as the registry names it — module-qualified, the
            // way a resolution trace names a candidate — when the dictionary
            // is a declared instance's global; a minted derivation is spelled.
            let mut head = *inst;
            while let Some((fun, _)) = crate::spelling::app_of(head) {
                head = fun;
            }
            let instance = match head {
                Term::GlobalTm { var, .. } => self
                    .global_abs_of(*var)
                    .and_then(|abs| self.names.global_name_at(abs as u32))
                    .map(str::to_string),
                _ => None,
            }
            .or_else(|| self.spell_term_clean(cx, inst))
            .unwrap_or_else(|| "its `Decide` instance".to_string());
            self.attempt.decide_uses.borrow_mut().push(attempt::DecideUse {
                span,
                gamma: cx.gamma.clone(),
                index: (**tm).clone(),
                goal: self.display_type(cx, expected),
                instance,
            });
        }
        Ok(t)
    }

    /// After a `NotConvertible` at the gate: the first written `decide` whose
    /// decision reduces to the wrong side, with the note that names it. The
    /// re-reduction runs only on the failure path and under the gate's own
    /// budget; an inconclusive one stays silent, like a `refl`'s note.
    fn refused_decide(&self) -> Option<(String, Span)> {
        let uses = self.attempt.decide_uses.borrow();
        if uses.is_empty() {
            return None;
        }
        let oracle = oracle::SemanticOracle::in_world(self.goal_psi(), self.policy.fuel);
        let zero = inductive::nat_lit(0);
        uses.iter().find_map(|u| {
            (oracle.convert_term(&u.gamma, Layer::Prog, &u.index, &zero, &Type::Nat, &Level::Zero)
                == Err(ConvError::NotConvertible))
            .then(|| {
                (
                    format!(
                        "`decide` resolved `Decide<{}>` to `{}`, whose decision here is not \
                         `Inl`: the goal is false, or not closed enough to decide",
                        u.goal, u.instance
                    ),
                    u.span,
                )
            })
        })
    }

    /// After a `NotConvertible` at the gate: the first `trivial` left unread
    /// ([`expr::UnitCheckingElab`]) whose expected type, reduced now under
    /// the gate's own budget, is not `True`. [`Self::refused_decide`]'s
    /// counterpart: the reduction runs only on the failure path, and an
    /// inconclusive one stays silent.
    fn refused_trivial(&self) -> Option<(String, Span)> {
        let uses = self.attempt.trivial_uses.borrow();
        if uses.is_empty() {
            return None;
        }
        let oracle = oracle::SemanticOracle::in_world(self.goal_psi(), self.policy.fuel);
        uses.iter().find_map(|u| {
            let head = oracle.whnf_type(&u.cx.gamma, &u.expected).ok()?;
            if matches!(head, Type::Unit { .. }) {
                return None;
            }
            let goal = self.display_type(&u.cx, &u.expected);
            let reduct = match self.display_type_clean(&u.cx, &head) {
                Some(r) if r != goal => format!(", which reduces to `{r}`"),
                _ => String::new(),
            };
            Some((
                format!(
                    "`trivial` proves `True`, but `{goal}` is expected here{reduct}: \
                     the verdict is false, or not closed enough to compute"
                ),
                u.span,
            ))
        })
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
        let TyKind::Named { name, args } = &t.kind else {
            return e;
        };
        if !args.is_empty() || !self.shadowed(cx, name) {
            return e;
        }
        let ElabError::Elab { msg, span } = e else {
            return e;
        };
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
    /// (Which of these readings races a type-owned member is finer than
    /// this: `member_head` asks `ambient_reading_survives`,
    /// docs/receiver-member-resolution-design.md §2.)
    fn shadowed(&self, cx: &Cx, name: &str) -> bool {
        cx.names.iter_inner().any(|n| n == name)
            || cx.aliases.iter_inner().any(|a| a.name == *name)
            || self.lookup_global(name).is_some()
            // The declaration's own name. It is not in `globals` until it is
            // checked, so without this a `fn map` could not recurse: its
            // self-call took the built-in vector-`map` path instead
            // (found writing docs/surface-polymorphism.md §9's headline test).
            || cx.selfref.as_ref().is_some_and(|s| s.matches(name))
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
                let r =
                    application::resolve_named(name, true, &params, 0, &mask, args, named, span)?;
                let (args, mask): (&[Expr], &[bool]) = match &r {
                    Some((a, m)) => (&a[..], &m[..]),
                    None => (args, &mask[..]),
                };
                application::apply_implicit(
                    self, cx, name, params, true, 0, false, t, ty, lvl, args, mask, expected,
                    false, span,
                )
            }
            Some(skel) => {
                let params = skel_params(&skel);
                let flat = vec![false; params.len()];
                let r =
                    application::resolve_named(name, true, &params, 0, &flat, args, named, span)?;
                let args = r.as_ref().map_or(args, |(a, _)| &a[..]);
                application::apply_explicit(self, cx, Some(name), params, 0, t, ty, lvl, args)
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
        if let Some(selfref) = cx.selfref.as_ref().filter(|s| s.matches(name)) {
            let note = self.self_shadow_note(selfref, name);
            return err(self_name_refusal(selfref, name), span).map_err(|e| with_self_shadow_note(e, note.as_deref()));
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
            // Quoted from the type the emission sites would write
            // (`docs/per-instantiation-type-codes-design.md` §5): a written
            // `f<List<Nat>>` carries `El (List#tycode_fn^δ ⌜Nat⌝)` rather than
            // the boxed literal every emission walk still finds here.
            let emitted = self.emit_ty(cx, &a_ty, 0);
            let Some(c) = code::code_of(emitted.as_ref().unwrap_or(&a_ty)) else {
                return err("this type cannot be a type argument", a.span);
            };
            let head = self.whnf(cx, &ty, span)?;
            let Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } = head
            else {
                return err(
                    format!("internal: `{name}`'s type parameter is not a `Π`"),
                    span,
                );
            };
            let arg = Rc::new(c);
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg)));
            lvl = cod_level.clone();
            t = crate::spelling::checked_app(Rc::new(t), dom_level, cod_level, dom, cod, arg);
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
    /// - `CollectionLit` — "a collection literal needs an expected container type".
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
    ///   where its instantiation is decidable (the §5.3 route). At a
    ///   meta-bearing domain it waits, then the obligation retry may infer
    ///   its instance from the domain's already solved parts.
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
        if defaults::is_param_default(e) {
            return true;
        }
        match &e.kind {
            ExprKind::Hole(_) | ExprKind::AutoRefl | ExprKind::CollectionLit(_) => true,
            // A bare operator symbol that needs a carrier
            // (docs/bare-symbol-checking-carrier-design.md §3.2, §4.3). Same
            // sentence as the bare implicit prefix two arms down: it *can*
            // infer — `+` infers to `add` — but only at a shape that
            // mis-teaches, since `add`'s type would pin the call's carrier to
            // `Nat` at a call whose carrier is `Bool`. Checking position is
            // where its resolution is decidable, so at a meta-bearing domain it
            // waits for one, and the per-argument deferral is what hands it the
            // carrier a later argument produced.
            ExprKind::OpSymbol {
                symbol: sym,
                fixity,
            } => self.symbol_needs_a_carrier(cx, sym, *fixity),
            ExprKind::Refl => !self.shadowed(cx, "refl"),
            ExprKind::Lam { binders, .. } => binders.iter().any(|b| b.ty.is_none()),
            ExprKind::Var(name) => {
                (name == "rel_derive" && !self.shadowed(cx, name) && self.ctor_here(cx, name).is_none())
                    || (name == "FZ"
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
            // A cast takes its target from the checking position, as a
            // numeral does (docs/casting-design.md §5.2).
            ExprKind::App { .. } if surface::is_cast(e) => true,
            ExprKind::App { .. } => match e.as_named() {
                Some(("absurd", _, _)) => !self.shadowed(cx, "absurd"),
                Some((name @ ("rel_cong" | "rel_derive"), _, false)) => !self.shadowed(cx, name) && self.ctor_here(cx, name).is_none(),
                Some(("FS", _, false)) => {
                    !self.shadowed(cx, "FS") && self.ctor_here(cx, "FS").is_none()
                }
                // A call with a **result-only implicit**
                // ([`Self::call_defers_for_result_only`]): the semantic member
                // of this set, and the only one that can still elaborate if
                // deferral does not pay off — which is why it, alone, carries
                // the inference fallback in [`application::apply_implicit`].
                Some((n, args, false)) => self.call_defers_for_result_only(cx, n, args.len()),
                _ => false,
            },
            _ => false,
        }
    }

    /// Was this argument deferred by the **result-only implicit** rule — the
    /// one member of [`Self::is_checking_only`] that can still be elaborated
    /// in inference mode? See [`DeferredArg::fallback_infer`].
    fn deferral_can_fall_back(&self, cx: &Cx, e: &Expr) -> bool {
        if defaults::is_param_default(e) {
            return false;
        }
        match e.as_named() {
            Some(("absurd", _, _)) | Some(("FS", _, false)) => false,
            Some((n, args, false)) => self.call_defers_for_result_only(cx, n, args.len()),
            _ => false,
        }
    }

    /// [`unification::U::type_args`]: which arguments of the rigid spine `t`
    /// — in the committed world, `d` binders past `cx.gamma` — sit at a `Ty`
    /// domain, read off the **head's** type. An `app(…)` node states its
    /// domain; an `app@` node's is its head's (`docs/app-by-head-type-design.md`
    /// §6.2), so the unifier's type-argument prefix asks here. The domain is
    /// read as the `app` emitter would have written it: the Π of the running
    /// type's weak head, instantiated at the earlier arguments. `None` under
    /// binders (their types are not in `cx.gamma`) and for a head whose type
    /// does not expose a Π per argument — the refusal the rule already gives
    /// a head it cannot read.
    fn spine_type_args(&self, cx: &Cx, t: &Term, d: u32, span: Span) -> Option<Vec<bool>> {
        if d != 0 {
            return None;
        }
        let doms = self.app_domains(cx, t, span)?;
        Some(doms.iter().map(|(dom, _)| matches!(&**dom, Type::Ty(_))).collect())
    }

    /// The domain, and its level, of every argument of the application spine
    /// `t` in `cx`, outermost last — what an `app(…)` node would state, read
    /// off the head's type instead (`docs/app-by-head-type-design.md` §6.2's
    /// `app_domains`): the head is inferred, and each argument peels one Π
    /// off the weak head of the running type, which is then instantiated at
    /// it — the walk `application.rs` makes when it writes the node. `None`
    /// when the head does not infer in `cx` or its type runs out of Π's.
    pub(crate) fn app_domains(
        &self,
        cx: &Cx,
        t: &Term,
        span: Span,
    ) -> Option<Vec<(Rc<Type>, Level)>> {
        self.app_walk(cx, t, span).map(|(domains, _)| domains)
    }

    /// The type of the application spine `t` in `cx`, read the way
    /// [`Self::app_domains`] reads its domains: the head inferred, then one Π
    /// instantiated per argument. For a caller that only needs to know what
    /// `t` is — the speller naming a field read off it — this costs the
    /// head's inference and the substitutions, never a check of the
    /// arguments.
    pub(crate) fn spine_type(&self, cx: &Cx, t: &Term, span: Span) -> Option<Type> {
        self.app_walk(cx, t, span).map(|(_, ty)| ty)
    }

    fn app_walk(&self, cx: &Cx, t: &Term, span: Span) -> Option<(Vec<(Rc<Type>, Level)>, Type)> {
        let (head, args) = spelling::app_spine(t);
        let oracle = self.semantic_oracle();
        let (mut ty, _) =
            typing::infer_term(oracle.world(), 0, Layer::Prog, &cx.gamma, head, self.policy.fuel).ok()?;
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            // A syntactic Π is read as it stands, as the kernel's fast path
            // reads it; only a type that has to reduce is whnf'd.
            let w = if matches!(ty, Type::Pi { .. }) { ty } else { self.whnf(cx, &ty, span).ok()? };
            let Type::Pi { dom, cod, dom_level, .. } = w else {
                return None;
            };
            out.push((dom, dom_level));
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(a)));
        }
        Some((out, ty))
    }

    /// [`unification::U::canonical_head`]: the weak head of a rigid term,
    /// when reduction exposes a canonical form. Under the stuck-spelling
    /// budget, since the answer is discarded whenever it is not one, and
    /// `None` under binders, whose types are not in `cx.gamma` — the same
    /// scope [`Self::spine_type_args`] reads.
    fn canonical_head(&self, cx: &Cx, t: &Term, d: u32) -> Option<Term> {
        if d != 0 {
            return None;
        }
        let w = self.semantic_oracle().whnf_term_bounded(&cx.gamma, t).ok()?;
        unification::canonical(&w).then_some(w)
    }

    /// [`unification::U::next_head`]: `t`, in `cx`, unfolded to the first
    /// reduct whose spine is headed by another global or local, or by a
    /// former or constructor. A β-redex or an eliminator on the way is
    /// stepped through, as a whnf would: a definition whose body is a
    /// `match` on a constructor argument reaches the arm it selects. One
    /// stuck on a neutral is no next head (`None`), and nor is a walk past
    /// [`Unfold::NextHead`] head reducts or the oracle's fuel.
    fn next_head(&self, cx: &Cx, t: &Term) -> Option<Term> {
        let head = spelling::app_spine(t).0.clone();
        self.semantic_oracle().unfold_to(&cx.gamma, t, Unfold::NextHead, |r| {
            let exposed = match spelling::app_spine(&r).0 {
                h @ (Term::GlobalTm { .. } | Term::Var(_)) => *h != head,
                h => !unification::steps_through(h),
            };
            exposed.then_some(r)
        })
    }

    /// The unifier's context for a root attempt in `cx`: the scope, and
    /// [`Self::spine_type_args`] for the `app@` nodes of a subject. Every
    /// solution is held to its slot's declared type in `doms` (the call's
    /// scratch world; a slot past its end is not judged), and `true` means a
    /// write was refused for not inhabiting it ([`SolutionCheck`]).
    #[allow(clippy::too_many_arguments)]
    fn unify_root(&self, cx: &Cx, pat: &Type, subj: &Type, n: u32, sols: &mut [Sol], doms: &[Type], span: Span) -> bool {
        self.unify_checked(cx, pat, subj, n, 0, sols, doms, None, Guesses::Take, None, span)
    }

    /// Does the registered instance `global`'s **conclusion** — its type
    /// past every parameter, each parameter a fresh slot — decidedly differ
    /// from `goal` ([`unification::Clash`])? Instance search asks before it
    /// builds the candidate (issues/instance-conclusion-matched-first.md):
    /// building elaborates a reference at the goal, premises and all, and
    /// then the kernel refuses it, which is the whole cost of a candidate
    /// that could never have matched. A closed instance is its own
    /// conclusion. `false` is "may match", always the answer when the
    /// conclusion cannot be read (a universe-polymorphic instance's `UΠ`, a
    /// binding out of reach) or the unifier could not decide.
    pub(crate) fn conclusion_clashes(&self, cx: &Cx, global: &str, goal: &Type, span: Span) -> bool {
        let Some(GlobalInfo { abs, .. }) = self.names.global(global) else { return false };
        let Some(GlobalBinding::Tm { ty, .. }) = self.psi.bindings.get(*abs as usize) else { return false };
        // The use-site type, as a reference to the global would carry it
        // (`elab_var`): rescoped to the full Ψ, then out of the empty context
        // it was declared in into this Γ.
        let len = self.psi.bindings.len() as u32;
        let meta_off = self.scope.meta_pushed.borrow().len() as u32;
        let var = len - 1 - abs + self.global_padding() + meta_off;
        let empty = LocalSubst {
            tail: SubstTail::Empty { len: cx.gamma.entries.len() as u32, base: cx.gamma.base },
            terms: vec![],
        };
        let ty = ty.shift_global(var + 1).apply_local(&empty);
        // One slot per leading binder, instantiated as an application's
        // implicits are: the slots sit innermost, under the identity.
        let mut n = 0u32;
        let mut t = &ty;
        while let Type::Pi { cod, .. } = t {
            n += 1;
            t = cod;
        }
        let mut doms = Vec::with_capacity(n as usize);
        let mut conclusion = ty.shift_global(n);
        for slot in 0..n {
            let Type::Pi { dom, cod, .. } = conclusion else { return false };
            doms.push((*dom).clone());
            let meta = Term::GlobalTm { var: GlobalVar(slot), subst: LocalSubst::id(&cx.gamma) };
            conclusion = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(meta)));
        }
        let pat = self.unspell_deep_now(&conclusion, n).unwrap_or(conclusion);
        let subj = self.unspell_deep_now(goal, 0);
        let subj = subj.as_ref().unwrap_or(goal);
        let mut sols = vec![Sol::Unsolved; n as usize];
        let clash = unification::Clash::default();
        self.unify_checked(cx, &pat, subj, n, 0, &mut sols, &doms, None, Guesses::Take, Some(&clash), span);
        clash.seen()
    }

    /// [`Self::unify_root`] for a subject `d` binders past `cx`: the
    /// metavariables are scoped in `cx`, and a solution that mentions one of
    /// the `d` is not learned. The tactic host's holes, made in a scope
    /// enclosing the one a comparison happens in, are unified this way.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn unify_under(&self, cx: &Cx, pat: &Type, subj: &Type, n: u32, d: u32, sols: &mut [Sol], doms: &[Type], span: Span) -> bool {
        self.unify_checked(cx, pat, subj, n, d, sols, doms, None, Guesses::Take, None, span)
    }

    /// The one root of the unifier: its context in `cx`, its writes held to
    /// `doms` by a [`SolutionCheck`], `disagree` told of a later subject a
    /// solved slot meets ([`unification::U::disagree`]), and its guesses
    /// taken, postponed or recorded as `guesses` says.
    #[allow(clippy::too_many_arguments)]
    fn unify_checked(
        &self,
        cx: &Cx,
        pat: &Type,
        subj: &Type,
        n: u32,
        d: u32,
        sols: &mut [Sol],
        doms: &[Type],
        disagree: Option<&dyn Fn(usize, &Term)>,
        guesses: Guesses<'_>,
        clash: Option<&unification::Clash>,
        span: Span,
    ) -> bool {
        let type_args = |t: &Term, e: u32| self.spine_type_args(cx, t, e, span);
        let canonical_head = |t: &Term, e: u32| self.canonical_head(cx, t, e);
        let respell = |t: &Type| self.respell_ty(cx, t);
        let constructor = |t: &Type| self.constructor_spelling(cx, t, span);
        let slot_view = |t: &Term| self.slot_view(t);
        let check = SolutionCheck::new(self, cx, doms, n);
        let admit = |i: usize, s: &Term, sols: &[Sol]| check.admit(i, s, sols);
        let next_head = |t: &Term| self.next_head(cx, t);
        let u = unification::U {
            gamma: &cx.gamma,
            subject_metas: None,
            type_args: &type_args,
            canonical_head: &canonical_head,
            respell: &respell,
            constructor: &constructor,
            slot_view: &slot_view,
            admit: &admit,
            disagree,
            next_head: &next_head,
            guesses,
            clash,
        };
        unify_ty_root(&u, pat, subj, n, d, sols);
        check.settle(sols)
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
    /// (docs/argument-type-reduction-design.md): one read, in which the
    /// unifier itself unfolds the argument's type wherever it does not meet
    /// the parameter's as it stands (the δ-lazy order,
    /// issues/unifier-lazy-delta.md).
    ///
    /// There used to be a second read against the type's weak head normal
    /// form, taken when the first learned *nothing*: for an argument whose
    /// type is a **motive applied** (`P(OfNat(k))`, a β-redex
    /// `(λ (z: Int) => add(a, z) = add(z, a))(OfNat(k))`,
    /// issues/motive-application-hides-hypothesis-type.md), a field type read
    /// through a projection, or a definition's body. The unifier's own step
    /// reaches each of those, at the place the read stops meeting and only
    /// while it has a slot to learn, so the retry is gone. The *expected*
    /// type's whnf in [`Self::solve_from_expected`] stays: a higher-kinded
    /// carrier (`?M(?B)` against `Tac<Nat>`) is matched by its spelling, not
    /// by unfolding.
    ///
    /// Every read is **held to the slots' declared types** (`meta_doms`):
    /// a slot whose type is already known takes only a solution that
    /// inhabits it ([`SolutionCheck`], at the unifier's one write), so a
    /// read never records what the call could not keep.
    /// When it refused something, the argument was written in other symbols —
    /// `x ≈ y` at `Rat` against `a * d ≈ c * b` at `Int` — and the read
    /// walks the type's first [`Unfold::IndexRead`] reducts,
    /// stopping at the first declaration application that teaches something
    /// that fits: `Dyadic::Le(a, b)` is `Rat::Le(a.rat(), b.rat())` one δ
    /// step on (issues/index-inference-through-unfolding.md).
    #[allow(clippy::too_many_arguments)]
    ///
    /// Returns the slots already solved that the argument's own type met
    /// with another subject ([`application::SlotClash`]): read off the
    /// first read only, since the reduct walk runs only when it learned
    /// nothing.
    fn unify_arg_ty(
        &self,
        cx: &Cx,
        dom_orig: &Type,
        arg_ty: &Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        guesses: Guesses<'_>,
        span: Span,
    ) -> Vec<(usize, Rc<Term>)> {
        let clashes = RefCell::new(Vec::new());
        self.unify_arg_reads(cx, dom_orig, arg_ty, n, sols, meta_doms, &clashes, guesses, span);
        clashes.into_inner()
    }

    #[allow(clippy::too_many_arguments)]
    fn unify_arg_reads(
        &self,
        cx: &Cx,
        dom_orig: &Type,
        arg_ty: &Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        clashes: &RefCell<Vec<(usize, Rc<Term>)>>,
        guesses: Guesses<'_>,
        span: Span,
    ) {
        let learned = |sols: &[Sol]| sols.iter().filter(|s| s.solved().is_some()).count();
        let before = learned(sols);
        // Both sides in the **inline** spelling first
        // (`docs/per-instantiation-type-codes-design.md` §4.2, amended
        // 2026-09-10): the congruence below is syntactic, and a callee's
        // domain arrives off its respelled statement, where a parameterized
        // instantiation is `El (app(D#tycode_fn^δ; ā))` and the argument's own
        // type is the former. Unspelled, `Iff<P, ?Q>` meets `Σ…` and solves;
        // spelled, it solves nothing and the writer is told to give the type
        // argument. The pattern is in the call's scratch world and the subject
        // in the committed one, which is the whole of the bookkeeping.
        let dom_inline = self.unspell_deep_now(dom_orig, n);
        let dom = dom_inline.as_ref().unwrap_or(dom_orig);
        let arg_inline = self.unspell_deep_now(arg_ty, 0);
        let arg_ty = arg_inline.as_ref().unwrap_or(arg_ty);
        let unify_checked =
            |sols: &mut [Sol], subject: &Type| -> bool { self.unify_checked(cx, dom, subject, n, 0, sols, meta_doms, None, guesses, None, span) };
        let record = |slot: usize, later: &Term| clashes.borrow_mut().push((slot, Rc::new(later.clone())));
        let rejected = self.unify_checked(cx, dom, arg_ty, n, 0, sols, meta_doms, Some(&record), guesses, None, span);
        if learned(sols) != before || !sols.iter().any(|s| matches!(s, Sol::Unsolved)) {
            return;
        }
        // An operation slot the syntactic read filled with a declaration of
        // another type: `Rat::Same(x, y)` read as `?≈(?*(a, d), ?*(c, b))` at
        // `Int` pairs `?≈` with `Rat::Same` (issues/index-inference-through-
        // unfolding.md). The argument's type was written in its own symbols,
        // and the parameter's are a step or two of unfolding away; read those
        // reducts, nearest first, while they are still applications of a
        // declaration, and stop at the first that teaches something that
        // fits. Bounded, and only on this path, so no call that read cleanly
        // ever steps.
        if rejected
            && let Type::El { level, tm } = arg_ty
        {
            let oracle = self.goal_oracle();
            for reduct in oracle.unfold(&cx.gamma, tm, Unfold::IndexRead) {
                if !unification::global_spine(&reduct) {
                    continue;
                }
                let unfolded = Type::El { level: level.clone(), tm: Rc::new(reduct) };
                unify_checked(sols, &unfolded);
                if learned(sols) != before {
                    return;
                }
            }
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
    ///   scratch-world result type against the written expected type, then
    ///   its weak head normal form, learn-only. This is the same call the LGG path makes as its step 1,
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
        guesses: Guesses<'_>,
        span: Span,
    ) -> R<()> {
        // The LGG trigger, read off the scratch-world result type.
        let flex = (|| {
            let Type::Id { lhs, rhs, .. } = result_ty else {
                return None;
            };
            let (Some((f_lhs, s_raw)), Some((f_rhs, t_raw))) =
                (spelling::app_of(lhs), spelling::app_of(rhs))
            else {
                return None;
            };
            let Term::GlobalTm { var, subst } = &**f_lhs else {
                return None;
            };
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
        // The same inline-spelling pre-pass `unify_arg_ty` takes, for the same
        // reason (§4.2, amended 2026-09-10).
        let inline_result = self.unspell_deep_now(result_ty, n);
        let result_ty = inline_result.as_ref().unwrap_or(result_ty);
        let inline_expected = self.unspell_deep_now(expected, 0);
        let expected = inline_expected.as_ref().unwrap_or(expected);
        let Some((m, s_raw, t_raw)) = flex else {
            // Preserve named relations and operation applications before
            // unfolding a transparent relation into its definition. Held to
            // the slots' types as an argument's read is: `x ≈ z` at `Rat`
            // against `?≈(?*(a, f), ?*(e, b))` at `Int` pairs `?≈` with
            // `Rat::Same` (issues/index-inference-through-unfolding.md).
            self.unify_checked(cx, result_ty, expected, n, 0, sols, meta_doms, None, guesses, None, span);
            // The expected type's weak head can teach only the metas the
            // result type still mentions: unification records into the
            // pattern's metas and nowhere else. Once it mentions none, the
            // read would learn nothing, and at a closed verdict it is the
            // verdict's whole evaluation, which the kernel is about to run
            // again — `decide_yes(refl)` at `heavy(300).IsTrue()`, whose
            // result `P` the line above has just solved
            // (issues/closed-verdict-evaluated-twice.md).
            if zonked(result_ty, n, sols).is_some() {
                return Ok(());
            }
            let head = self.whnf(cx, expected, span)?;
            let head = self.unspell_deep_now(&head, 0).unwrap_or(head);
            self.unify_checked(cx, result_ty, &head, n, 0, sols, meta_doms, None, guesses, None, span);
            return Ok(());
        };
        // Step 1, with `?f` withheld (unsolved-but-untouchable — `unify_tm`
        // records only into `Unsolved`, and the flex-head guard skips the
        // spines it heads). The pattern is in the scratch world and the
        // subject in the committed one, exactly as at an argument's domain.
        sols[m] = Sol::Withheld;
        self.unify_root(cx, result_ty, expected, n, sols, meta_doms, span);
        let expected_head = self.whnf(cx, expected, span)?;
        let expected_head = self.unspell_deep_now(&expected_head, 0).unwrap_or(expected_head);
        self.unify_root(cx, result_ty, &expected_head, n, sols, meta_doms, span);
        sols[m] = Sol::Unsolved;
        // `s` and `t` must be meta-*free* once the solved metas are
        // substituted away: the witnesses are compared with `==`, and an
        // unsolved meta is not a term (decision 2).
        let (Some(s), Some(t)) = (zonked_tm(&s_raw, n, sols), zonked_tm(&t_raw, n, sols)) else {
            return Ok(());
        };
        let Type::Id { lhs: x, rhs: y, .. } = expected_head else {
            return Ok(());
        };
        // The abstraction's domain is `?f`'s *declared* parameter type — the
        // only place it can come from, since no argument has it. It is a `Π`
        // by construction of the trigger (a meta that is applied), and its
        // own metas are solved by now or the call could not have got here.
        let dom_ty = &meta_doms[m];
        let Some(dom_ty) = zonked(dom_ty, n, sols) else {
            return Ok(());
        };
        let Type::Pi {
            dom_level,
            cod_level,
            dom,
            ..
        } = self.whnf(cx, &dom_ty, span)?
        else {
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
        //
        // 3. The reduced goal again with the **witness up to conversion**
        //    (`lgg::lgg_body_up_to_conversion`), only after both of the above
        //    failed: at a differing node that mentions none of the walk's
        //    binders, the sides convert to `(s, t)`. Conversion runs only
        //    there, top-down, so typically once per side, and the abstraction
        //    is kept only if it kernel-checks at `?f`'s type. A failure
        //    reports attempt 2's mismatch, so the message is the one it always
        //    was. A goal on a family reaches this: its reduct carries the
        //    constructor's pieces as each function spelled them
        //    (issues/cong-inference-through-iwf-w-children.md).
        let body = match lgg::lgg_body(&x, &y, &s, &t) {
            Ok(body) => body,
            Err(first) => {
                let rx = self.whnf_tm(cx, &x, span)?;
                let ry = self.whnf_tm(cx, &y, span)?;
                let reduced = *rx != *x || *ry != *y;
                let second = if reduced { lgg::lgg_body(&rx, &ry, &s, &t) } else { Err(first) };
                match second {
                    Ok(body) => body,
                    Err(mismatch) => {
                        let fits = |body: &Term| {
                            let f = Term::Lam {
                                dom_level: dom_level.clone(),
                                cod_level: cod_level.clone(),
                                dom: Rc::clone(&dom),
                                body: Rc::new(body.clone()),
                            };
                            let fl = Level::join(dom_level.clone(), cod_level.clone());
                            typing::check_term(&self.goal_psi(), 0, Layer::Prog, &cx.gamma, &f, &dom_ty, &fl, self.policy.fuel)
                                .is_ok()
                        };
                        // `(a, b)`, scoped in `Γ`: `(s, t)` up to conversion
                        // there, at `?f`'s domain.
                        let oracle = self.goal_oracle();
                        let witness = |a: &Term, b: &Term| {
                            let conv = |l: &Term, r: &Term| {
                                oracle.convert_term(&cx.gamma, Layer::Prog, l, r, &dom, &dom_level).is_ok()
                            };
                            conv(a, &s) && conv(b, &t)
                        };
                        let witness_fst = |a: &Term, b: &Term, s1: &Term, t1: &Term, ty: &Type, level: &Level| {
                            let conv = |l: &Term, r: &Term| {
                                oracle.convert_term(&cx.gamma, Layer::Prog, l, r, ty, level).is_ok()
                            };
                            conv(a, s1) && conv(b, t1)
                        };
                        match lgg::lgg_body_up_to_conversion(&rx, &ry, &s, &t, &witness, &witness_fst).ok().filter(|body| fits(body)) {
                            Some(body) => body,
                            None => {
                                let msg = self.cong_mismatch(cx, &mismatch, expected, &s, &t);
                                return Err(ElabError::Elab { msg, span });
                            }
                        }
                    }
                }
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
            // `#scrut` and its kin are elaborator-internal binder names. A
            // reader cannot look one up, and a clause built on one reads as
            // the kernel wall wearing surface syntax — which is what the
            // *clean* spellings below are there to refuse. The formers in
            // `m`'s own sentence still say what the node is.
            && !a.contains('#')
            && !b.contains('#')
        {
            msg.push_str(&format!(" (`{a}` against `{b}`)"));
        }
        // *Clean* spellings throughout: every clause here makes a claim about
        // a term, and a half-spelled one is the kernel wall wearing surface
        // syntax (`issues/check-fallback-discards-expected-type.md`). A clause
        // that cannot be said cleanly is not said.
        // No bare `.` in the `else`: the next clause opens with `, and the
        // proof's endpoints`, so a period here punctuates the sentence into
        // `against \`Nil\`., and the proof's …`. A clause that cannot be said
        // is not said, and it leaves no mark either.
        if let Some(goal) = self.spell_type_clean(cx, expected) {
            msg.push_str(&format!(". The goal is `{goal}`"));
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
        if let Some(why) = self.cong_invisible_difference(cx, m, s, t) {
            msg.push_str(&why);
        } else if let Some(why) = self.cong_goal_sides_look_equal(cx, expected) {
            msg.push_str(&why);
        } else if m.sides.0 == "El" || m.sides.1 == "El" {
            msg.push_str(EL_AGAINST_CODE);
        }
        msg
    }

    /// The other half of the same complaint: the *goal* prints as `X = X`.
    ///
    /// `. The goal is \`wrap(c, Red) = wrap(c, Red)\`` above a sentence that
    /// says those two sides differ reads as a lie, and the reader has no way
    /// to see what parts them — for the same reason as in
    /// [`Self::cong_invisible_difference`]: the walk compares terms and the
    /// message renders surface (issues/lgg-error-hides-the-implicit.md).
    fn cong_goal_sides_look_equal(&self, cx: &Cx, expected: &Type) -> Option<String> {
        let Type::Id { lhs, rhs, .. } = expected else {
            return None;
        };
        if lhs == rhs {
            return None;
        }
        let (l, r) = (
            self.spell_term_clean(cx, lhs)?,
            self.spell_term_clean(cx, rhs)?,
        );
        if l != r {
            return None;
        }
        let d = lgg::first_difference(lhs, rhs);
        let mut why =
            format!(". The goal's own two sides both spell `{l}` and are not the same term");
        if let Some(d) = &d {
            why.push_str(&format!(" — they part {d:#}"));
        }
        why.push_str(", so the difference the walk stopped at is one the spelling does not show");
        if matches!(&d, Some(d) if d.sides.0 == "El" || d.sides.1 == "El") {
            why.push_str(EL_AGAINST_CODE);
        }
        Some(why)
    }

    /// The clause that keeps the message above from contradicting itself.
    ///
    /// When the walk stops at the very position the proof witnesses — the two
    /// sides there *spell* exactly like the two endpoints — the sentence names
    /// the same two strings as both the difference and the match, and a reader
    /// following it concludes the condition is already met
    /// (issues/lgg-error-hides-the-implicit.md). The difference is real and
    /// invisible: the witness test is structural `==` with no conversion
    /// (decision 2), so a type argument spelled two convertible ways is a
    /// difference the surface speller drops.
    ///
    /// So: find the side whose spelling matches its endpoint but whose term
    /// does not, and say where the two actually part. [`lgg::first_difference`]
    /// answers that in the same vocabulary the rest of the message uses, which
    /// is why this stays a *position* and never prints a kernel term — the
    /// wall `issues/lgg-diagnostic-dumps-kernel-terms.md` exists to stop.
    fn cong_invisible_difference(
        &self,
        cx: &Cx,
        m: &lgg::Mismatch,
        s: &Term,
        t: &Term,
    ) -> Option<String> {
        let (a, b) = m.at.as_ref()?;
        // Read both sides in `cx` — the same strengthening the `(a against b)`
        // clause above uses, and for the same reason: a subterm that mentions
        // a binder the walk descended under has no reading here at all.
        let a = strengthen_tm(&cx.gamma, a, m.depth)?;
        let b = strengthen_tm(&cx.gamma, b, m.depth)?;
        for (side, goal, endpoint) in [("left", &a, s), ("right", &b, t)] {
            if goal == endpoint {
                continue;
            }
            let (Some(g), Some(e)) = (
                self.spell_term_clean(cx, goal),
                self.spell_term_clean(cx, endpoint),
            ) else {
                continue;
            };
            if g != e {
                continue;
            }
            let mut why = format!(
                ". That position is the one the proof witnesses, and it looks like it: \
                 the {side} side there and the proof's {side} endpoint both spell `{g}`, \
                 but they are not the same term"
            );
            if let Some(d) = lgg::first_difference(goal, endpoint) {
                why.push_str(&format!(" — they part {d:#}"));
            }
            why.push_str(
                ". The witness test is structural, never up to conversion \
                 (issues/congruence-by-anti-unification.md §3 decision 2), so a difference \
                 the surface spelling drops still declines. Spell the endpoint the way the \
                 goal does, or use an explicit congruence lemma",
            );
            if m.sides.0 == "El" || m.sides.1 == "El" {
                why.push_str(EL_AGAINST_CODE);
            }
            return Some(why);
        }
        None
    }

    // -- names --------------------------------------------------------------

    /// `name` as the expression being elaborated: its term goes into the
    /// result, so a `let` alias it names is spliced ([`Alias::splice`]).
    fn resolve(&self, cx: &Cx, name: &str, span: Span) -> R<(Term, Type, Level)> {
        self.resolve_at(cx, name, span, true)
    }

    /// [`Self::resolve`] for a caller that reads the type, or builds a
    /// candidate it may drop: a `let` alias it names is not recorded as
    /// spliced, so its value still reaches the kernel if no use puts it there.
    pub(crate) fn resolve_reading(&self, cx: &Cx, name: &str, span: Span) -> R<(Term, Type, Level)> {
        self.resolve_at(cx, name, span, false)
    }

    fn resolve_at(&self, cx: &Cx, name: &str, span: Span, splice: bool) -> R<(Term, Type, Level)> {
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
        let local_pos = cx.names.lookup(name);
        let alias = cx.aliases.iter_inner().find(|a| a.name == *name);
        match (local_pos, alias) {
            (Some(pos), Some(a)) if a.depth <= pos => return Ok(self.local(cx, pos)),
            (_, Some(a)) => {
                // Inlined at the use site, shifted across the binders pushed
                // since it was bound (same as a `fn` definition's globals).
                let by = (cx.names.len() - a.depth) as u32;
                let (term, ty) = if splice { a.splice(by) } else { a.at(by) };
                return Ok((term, ty, a.level.clone()));
            }
            (Some(pos), None) => return Ok(self.local(cx, pos)),
            (None, None) => {}
        }
        if let Some((ind, i)) = self.ctor_of(name).or_else(|| self.ctor_over_types(name)) {
            return self.infer_ctor(cx, &ind, i, &[] as &[Expr], span);
        }
        // The enclosing declaration's own name: only a saturated, guarded
        // *call* means anything (it is the induction hypothesis, not a value).
        if let Some(selfref) = cx.selfref.as_ref().filter(|s| s.matches(name)) {
            let note = self.self_shadow_note(selfref, name);
            return err(self_name_refusal(selfref, name), span).map_err(|e| with_self_shadow_note(e, note.as_deref()));
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
                let meta_off = self.scope.meta_pushed.borrow().len() as u32;
                let var = GlobalVar(len - 1 - abs + self.global_padding() + meta_off);
                let GlobalBinding::Tm { ty, level, .. } = &self.psi.bindings[*abs as usize] else {
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
                // A checking-only form used where nothing is expected.
                if name == "rewrite" {
                    return err(
                        "`rewrite(h, …, e)` needs an expected type: it rewrites a goal, so it \
                         only means anything where one is known (a `theorem` body, an \
                         annotated `let`, an argument)\n  hint: to rewrite a hypothesis's \
                         type instead, write `rewrite(h, …, in := hyp)`",
                        span,
                    );
                }
                if name == "subst" {
                    return err(
                        "`subst(h, e)` needs an expected type: it eliminates a variable from a \
                         goal, so it only means anything where one is known (a `theorem` body, \
                         an annotated `let`, an argument)",
                        span,
                    );
                }
                // The proof-search tactics are checking forms too: met where
                // nothing is expected, the name is not a missing import
                // (`issues/checking-tactic-in-inference-position-diagnostic.md`).
                if matches!(name, "omega" | "ring" | "linarith" | "nlinarith" | "bv_omega" | "positivity") {
                    let call = if matches!(name, "bv_omega" | "positivity") {
                        name.to_string()
                    } else {
                        format!("{name}(…)")
                    };
                    return err(
                        format!(
                            "`{name}` needs an expected type (it is checking-only, like `refl`): it \
                             proves a goal, so it only means anything where one is known (a \
                             `theorem` body, an annotated `let`, an argument)\n  hint: state what \
                             it proves: `let k: (T) = {call};`"
                        ),
                        span,
                    );
                }
                Err(self.name_miss(name, format!("unbound name `{name}`"), span))
            }
        }
    }

    // -- kernel oracle ------------------------------------------------------

    /// Semantic operations in the expression world's δ context, including
    /// any dynamic meta binders currently in scope.
    fn semantic_oracle(&self) -> oracle::SemanticOracle {
        if let Some(world) = self.attempt.goal_arena.delta_world(&self.delta_psi) {
            return oracle::SemanticOracle::with_dynamic(&world, &self.scope.meta_pushed.borrow(), self.policy.fuel);
        }
        oracle::SemanticOracle::with_dynamic(&self.delta_psi, &self.scope.meta_pushed.borrow(), self.policy.fuel)
    }

    /// Semantic operations in the real goal-statement world.
    fn goal_oracle(&self) -> oracle::SemanticOracle {
        oracle::SemanticOracle::in_world(self.goal_psi(), self.policy.fuel)
    }

    /// Semantic operations over committed Ψ, with no declaration padding.
    fn committed_oracle(&self) -> oracle::SemanticOracle {
        oracle::SemanticOracle::in_world((*self.psi).clone(), self.policy.fuel)
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
            .map_err(|_| ElabError::Elab {
                msg: "out of fuel reducing a term".into(),
                span,
            })
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
        let head = self
            .expr_elab()
            .whnf_type(cx, ty)
            .map_err(|_| ElabError::Elab {
                msg: "out of fuel reducing a type".into(),
                span,
            })?;
        // …and one level down a sum, for the same reason: a flat
        // declaration's whole-type code is spelled over its spine's names,
        // so the kernel's reduct of a code that *computes* to it stops at
        // `Sum(El (D#payload₀^δ), El (D#suffix₀^δ))`, which no structural
        // reader can see the tag through (`unspell_sum_components`).
        // A recursive declaration's code is spelled over its `Wf` slot pair
        // the same way (`unspell_wf_slots`).
        Ok(self
            .unspell_sum_components(&head)
            .or_else(|| self.unspell_wf_slots(&head))
            .unwrap_or(head))
    }

    /// `HEATHER_IMAGE_ATTRIBUTION=<file>` (a measurement instrument): append
    /// one `decl<TAB>slot<TAB>nodes` row per emitted slot kind of this
    /// declaration, charged the syntax nodes a module image spends on it
    /// (`emission_walk::tally_decl`). Rows only; the file is never truncated.
    pub(crate) fn attribute_image(&self, decl: &str, stmt: &Type, term: Option<&Term>) {
        static PATH: std::sync::OnceLock<Option<std::ffi::OsString>> = std::sync::OnceLock::new();
        let Some(path) = PATH.get_or_init(|| std::env::var_os("HEATHER_IMAGE_ATTRIBUTION")) else {
            return;
        };
        use std::io::Write;
        let rows = emission_walk::tally_decl(self, decl, stmt, term);
        let mut out = String::new();
        for (slot, nodes) in rows {
            out.push_str(&format!("{decl}\t{slot}\t{nodes}\n"));
        }
        if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
            let _ = f.write_all(out.as_bytes());
        }
    }

    /// How far the committed bindings are pushed out by the declaration-local
    /// goal block. Every site that renumbers a `GlobalVar` against the
    /// padding takes this; only `GoalArena::allocate`'s own
    /// `goal_base − 1 − k` does not.
    /// Does elaboration here emit the checked spellings
    /// (`docs/intro-by-type-design.md` §4.1)? Everywhere but inside a
    /// quotation payload: the kernel refuses them there (§2.3).
    pub(crate) fn emits_at_forms(&self) -> bool {
        !self.under_quotation()
    }

    /// Is a quotation payload elaborating above this point? Asked of the
    /// elaborator's dynamic scope, never of a `Cx`: a helper inside a payload
    /// that starts from a fresh `Cx` is still inside it.
    pub(crate) fn under_quotation(&self) -> bool {
        self.scope.quote_depth.get() > 0
    }

    pub(crate) fn global_padding(&self) -> u32 {
        self.attempt.goal_arena.base()
    }

    /// Rebuild [`Self::delta_psi`]. Called wherever Ψ or `goal_base` moves.
    fn refresh_delta_psi(&mut self) {
        self.attempt.goal_arena.invalidate_delta_world();
        // The interface boundary (`interfaces.rs`): the elaborator's worlds
        // withhold other modules' interface definitions; `psi`, the gate's,
        // never does.
        let withheld = self.withheld_policy();
        if self.global_padding() == 0 {
            self.delta_psi = match withheld {
                Some(w) => Shared::new(self.psi.withholding(Some(w))),
                None => self.psi.clone(),
            };
            return;
        }
        let placeholder = GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(Type::Nat),
            level: Level::Zero,
            body: None,
        };
        let padded = self.psi.extended(std::iter::repeat_n(placeholder, self.attempt.goal_arena.base() as usize));
        *self.delta_psi = match withheld {
            Some(w) => padded.withholding(Some(w)),
            None => padded,
        };
    }
}

/// The base name a declaration recurses under, as `Cx.selfref` uses it.
fn base_name(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// Does `block` call one of `names` at a position the measure walk rewrites —
/// the head of a saturated application (`docs/mutual-recursion-design.md` §1)?
/// Shadowing is not tracked here: an over-approximated edge only groups two
/// declarations that did not need grouping, which §1 says costs nothing, while
/// the rewrite itself does track it and leaves a shadowed call alone.
fn calls_in(block: &heather_syntax::Block, names: &[String], out: &mut Vec<usize>) {
    let mut scan = |e: &Expr| {
        surface::walk_expr(e, &mut |x| {
            let ExprKind::App { head, .. } = &x.kind else {
                return;
            };
            let callee = match &head.kind {
                ExprKind::TyApp { head, .. } => &head.kind,
                other => other,
            };
            if let ExprKind::Var(n) = callee
                && let Some(j) = names.iter().position(|m| m == n)
                && !out.contains(&j)
            {
                out.push(j);
            }
        });
    };
    for s in &block.stmts {
        match s {
            heather_syntax::Stmt::Let { expr, .. }
            | heather_syntax::Stmt::LetRecord { expr, .. }
            | heather_syntax::Stmt::LetCode { expr, .. } => {
                scan(expr)
            }
        }
    }
    scan(&block.result);
}

/// The mutual groups of `docs/mutual-recursion-design.md` §1: within each
/// maximal run of *consecutive* `decreases` declarations, the strongly
/// connected components of size > 1, as item indices in declaration order.
///
/// Nothing here is trusted — a wrong grouping costs an uglier obligation or a
/// refused generated term, never a wrong proof (§1).
fn measure_groups(items: &[Item]) -> Vec<Vec<usize>> {
    let mut groups = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let start = i;
        while i < items.len()
            && matches!(&items[i], Item::Decl(d) if d.decreases.is_some() && !d.is_meta)
        {
            i += 1;
        }
        if i == start {
            i += 1;
            continue;
        }
        let run: Vec<&Decl> = items[start..i]
            .iter()
            .map(|it| match it {
                Item::Decl(d) => d,
                _ => unreachable!("the run holds declarations only"),
            })
            .collect();
        let n = run.len();
        let names: Vec<String> = run.iter().map(|d| base_name(&d.name).to_string()).collect();
        // `reach[a][b]`: `a` calls `b`, transitively. The runs are a handful
        // of declarations, so the closure is cheaper than a Tarjan.
        let mut reach = vec![vec![false; n]; n];
        for (a, d) in run.iter().enumerate() {
            let mut hits = Vec::new();
            calls_in(&d.body, &names, &mut hits);
            for b in hits {
                reach[a][b] = true;
            }
        }
        for k in 0..n {
            for a in 0..n {
                for b in 0..n {
                    if reach[a][k] && reach[k][b] {
                        reach[a][b] = true;
                    }
                }
            }
        }
        let mut taken = vec![false; n];
        for a in 0..n {
            if taken[a] {
                continue;
            }
            let comp: Vec<usize> = (a..n)
                .filter(|&b| b == a || (reach[a][b] && reach[b][a]))
                .collect();
            for &b in &comp {
                taken[b] = true;
            }
            if comp.len() > 1 {
                groups.push(comp.into_iter().map(|b| start + b).collect());
            }
        }
    }
    groups
}

/// The per-container facts the item loops share (`begin_container`).
struct ItemPlan {
    groups: Vec<Vec<usize>>,
    /// Parallel to `groups`: what each group is a group of.
    kinds: Vec<GroupKind>,
    in_group: HashMap<usize, usize>,
}

/// What a group of items is (`ItemPlan::groups`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum GroupKind {
    /// `decreases` declarations under one measure
    /// (docs/mutual-recursion-design.md §1).
    Measure,
    /// Mutual `inductive` declarations (docs/mutual-inductive-design.md §1).
    Inductive,
    /// Declarations without a measure that call one another, one of them
    /// recursing over a mutual family (docs/mutual-inductive-design.md §6).
    Structural,
}

/// The reserved name of a match's anonymous equation once it is bound
/// (docs/dependent-match-compiler-design.md §4.1). `__` names are the
/// machinery's; a certificate may spell it, a user does not write it.
pub(crate) const MATCH_EQ: &str = "__match_eq";

/// An indexed family as [`Elaborator::elab_convoy_packed`] reads it: its index
/// type, its levels, the family at an index, and its own eliminator at a
/// two-binder motive.
struct PackedFamily<'a> {
    ity: Type,
    ilvl: Level,
    flvl: Level,
    idx: Rc<Term>,
    /// `F(i)`, scoped `k` binders past Γ, `i` scoped there too.
    at: &'a dyn Fn(Term, u32) -> Type,
    eliminate: &'a dyn Fn(&Cx, &[Arm], Term, Type, Level) -> R<Term>,
}

