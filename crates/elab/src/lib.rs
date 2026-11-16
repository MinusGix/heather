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
//!
//! # Methods live on their area's view, not on `Elaborator`
//!
//! [`Elaborator`] holds the session's state, the entry points a driver
//! calls and the few helpers every area shares. What elaborates is written
//! on *views*: each area's module defines a type that borrows the
//! elaborator and dereferences to it, one for its `&self` methods and, where
//! it has them, one for its `&mut self` methods:
//!
//! ```ignore
//! pub(crate) struct Classes<'e>(pub(crate) &'e Elaborator);
//! pub(crate) struct ClassesMut<'e>(pub(crate) &'e mut Elaborator);
//! ```
//!
//! Another area calls `Classes(self).class_ref_of_ty(goal)`. Inside a view,
//! `self.field` and `self.method()` reach the elaborator through the
//! dereference, so a body reads as it would on `Elaborator`.
//!
//! The split is by area for the reader, and it is also what keeps an edit
//! cheap to compile. rustc compiles all the methods of one `Self` type as one
//! codegen unit, placed with the module that defines the type, whatever
//! files the `impl` blocks are written in. While every method was an
//! `impl Elaborator`, one unit held the whole elaborator and every edit
//! recompiled it (issues/elaborator-crate-compile-per-edit.md;
//! `scripts/codegen-units` lists a build's units by size). So a new method
//! goes on the view of the area it belongs to, and a new area gets a view in
//! its own module.
//!
//! What differs from writing on `Elaborator` directly:
//! - `self.clone()` clones the view. A copy of the elaborator is
//!   `self.0.clone()`. Views derive neither `Clone` nor `Copy`, so the
//!   mistake does not compile where the copy is used as an elaborator.
//! - A `Mut` view reaches the elaborator through `DerefMut`, which borrows
//!   all of it: two fields borrowed at once are written `self.0.a` and
//!   `self.0.b`.
//! - A view is a temporary, so nothing a method returns may borrow from it:
//!   a method that hands back a guard or a reference into the elaborator
//!   stays on `Elaborator`.
//! - A method call on a view falls through the dereference when the view's
//!   own method is private and out of sight. A view method that shares its
//!   name with a trait method of `Elaborator` is called by path
//!   (`MismatchNotes::note_refl_mismatch(&MismatchNotes(self), ..)`).

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};
use heather_kernel::rc::Rc;
use std::sync::Arc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::subst::GlobalSubst;
use heather_kernel::term::{
    GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type,
};
use heather_kernel::typing::{self, DEFAULT_FUEL, TypeError};
use heather_kernel::value::{ValueMetrics, ValueMetricsSnapshot};
use heather_syntax::{
    Arm, Decl, DeclKind, Expr, ExprKind, Item, LamBinder, MatchForm,
    OnStmt, OnTarget, ParseError, Ty, TyKind,
};

/// The process allocator for every binary that links the elaborator: the
/// `heather` CLI and the test and bench binaries that drive it in process.
///
/// Checking is allocation-bound. Kernel terms are `Arc` trees built node by
/// node, substitution rebuilds the spine above every change, and the
/// elaborator's own tables are maps of small boxed values, so the allocator's
/// fast path is on every hot loop there is. glibc's `malloc` takes a lock-free
/// but branchy path per call and returns freed chunks through per-size bins;
/// a size-segregated thread-local allocator does the same work in a handful
/// of instructions. Which one matters less than not being glibc's: measured
/// by preload, mimalloc, jemalloc and tcmalloc land within noise of each
/// other (issues/global-allocator.md has the table).
///
/// It is declared here and not in the kernel: the kernel's dependency list
/// is an audited minimum (issues/dependency-policy.md), an allocator
/// implements no judgment, and a kernel linked alone (its own tests and
/// benches) keeps the system allocator. No `unsafe` is written for it; the
/// attribute and the crate's safe unit type are the whole integration.
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

mod access;
mod module_pass;
mod app_unify;
mod refusals;
mod inference;
mod mismatch_notes;
mod checking;
mod declarations;
mod name_lookup;
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
pub use display::global_type_source;
mod shown;
pub use shown::show_global;
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
mod refold;
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
mod tested;
mod lgg;
mod solution_check;
mod lint;
mod lifetimes;
mod literals;
pub use lint::{Lint, LintProfile};
mod matching;
mod measure;
mod branch_equations;
mod function_induction;
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
// (`docs/elaborator/projected-tuple-tower-design.md` §11, `probes/README.md@ef3961a`): the
// value-graph counter that priced the naming, and the readback itself. Both
// are inert unless `HEATHER_RB` is set.
mod recursion;
mod registered;
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
    ParamMeta, Skel, has_implicit_mark, skel_of_lam_binders, skel_of_ty,
};
use attempt::DeclAttempt;
use lifetimes::{DynamicScope, Memos, ModulePass, Policy};
pub(crate) use context::{Alias, Cx, DictBinder, TyVar};
use inductive::Inductive;
use metaprograms::{MetaDef, MetaPrograms};
use names::{
    DEFAULT_MODULE, GlobalInfo, GlobalRegistration, NameKind, NameRes, Names,
    miss_msg,
};
use recursion::SelfRef;
use representations::Representations;
use slots::{Ingredient, Slot};
pub(crate) use surface::{count_holes, count_holes_expr, strengthen_global};
use surface::{
    expression_as_type, has_free_slots,
};
use traits::Traits;
use types::Types;
use solution_check::SolutionCheck;
use unification::{Guesses, ResolveOb, Sol, zonked, zonked_tm};
pub(crate) use unification::{embed, mentions_binder, strengthen_tm, strengthen_ty};

/// The stage-1 prelude: `sym`/`trans`/`cong`/`cong_succ`, monomorphic at
/// `Nat` where the equation's type is not a parameter.
/// (The universe-polymorphic versions are layer-m `Λ ℓ⃗` territory — later
/// stage; the Nat suite only ever congs by `Succ`.)
pub const PRELUDE: &str = include_str!("prelude.hthr");

/// The prelude's module name: an implicit import of every module
/// (docs/language/modules-design.md §3.2). Public so a loader can skip resolving it to
/// a file — there is no `prelude.hthr` on disk to find.
pub const PRELUDE_MODULE: &str = names::PRELUDE_MODULE;
pub const COMMON_MODULE: &str = names::COMMON_MODULE;

pub use diagnostics::{ElabError, GoalReport, GoalSource, IndexedRoute, KernelSite, LintFix, Warning};
pub use heather_syntax::Span;
use crate::codata::Codata;
use crate::host::Host;
use crate::indexed::IndexedFamilies;
use crate::iwf_family::IwfFamily;
use crate::quote::Quotation;
use crate::application::Callables;
use crate::constructor::Constructors;
use crate::defaults::Defaults;
use crate::dispatch::Dictionaries;
use crate::interfaces::InterfaceDefs;
use crate::measure_context::MeasureContext;
use crate::dispatch::Operators;
use crate::application::Polymorphic;
use crate::dispatch::Projections;
use crate::matching::Routes;
use crate::traits::Classes;
use crate::gendefs::GeneratedDefs;
use crate::inductive::Inductives;
use crate::name_lookup::NameLookup;
use crate::declarations::Declarations;
use crate::checking::Checking;
use crate::mismatch_notes::MismatchNotes;
use crate::inference::Inference;
use crate::app_unify::AppUnify;
use crate::module_delta::DeltasMut;
use crate::traits::ClassesMut;
use crate::declarations::DeclarationsMut;
use crate::module_pass::ModulePassMut;

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
/// (docs/language/classes/traits-type-projection-design.md §7). `None` for anything else, which
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
/// will infer, and they will not (docs/language/implicit-binders-design.md §3.4).
pub(crate) const IMPLICIT_MARK_REFUSED: &str = "implicit binders take effect in parameter types, `let` annotations, field \
     types, and lambdas; this position cannot use one — see \
     issues/implicit-binders-in-function-types.md";

/// The receiver-shaped builtins: names that a `.` call reaches without any
/// declaration behind them, so [`Elaborator::shadowed`] cannot see them. Read
/// only by receiver dispatch (docs/language/classes/traits-receiver-dispatch-design.md §3),
/// which needs to know whether a call *had* another reading before it claims
/// one — a class field named `map` must make `xs.map(f)` ambiguous, never
/// silently the class's.
const BUILTIN_METHODS: [&str; 8] = [
    "map", "fold", "head", "tail", "cons", "cong", "inj", "absurd",
];

/// Where a resolved dictionary came from, when it came by **upcast**: the
/// *child* dictionary and its class type ([`Resolution::resolve_goal_from`](crate::resolve::Resolution::resolve_goal_from),
/// `docs/language/classes/traits-named-upcast-design.md` §2.1). `None` for every other answer,
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
    /// (`docs/tactics/bv-omega-design.md` §7).
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
/// ([`Refusals::kernel_refusal`](crate::refusals::Refusals::kernel_refusal)): reported as its own probe would have
/// reported it, had the probe's budget reached the verdict.
enum RecordedSite {
    /// A written `refl`, with its two sides when both spell.
    Refl { span: Span, sides: Option<(String, String)> },
    /// A checking site, with its two types when both spell and differ.
    Check { span: Span, types: Option<(String, String)> },
    /// A checking site with a message of its own: a `partial fn`'s call
    /// where its result is expected ([`Partial::partial_use_note`](crate::partial::Partial::partial_use_note)).
    Named { span: Span, msg: String },
}

impl RecordedSite {
    fn into_error(self, decl: &str, err: TypeError, with_op: impl Fn(String) -> String) -> ElabError {
        match self {
            RecordedSite::Check { span, types: Some((g, w)) } => ElabError::Elab {
                msg: with_op(format!("this has type `{g}`, but `{w}` is expected here")),
                span,
            },
            RecordedSite::Named { span, msg } => ElabError::Elab { msg: with_op(msg), span },
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
/// ([`MismatchNotes::probed_check_note`]).
enum MismatchNote {
    /// Both types, in surface: the message replaces the kernel's report.
    Spelled(String),
    /// The site, and what can be shown of the types: the kernel's verdict
    /// stays and the span moves here, as a `refl` note's does.
    Located(String),
}

/// What a `p.f` turned out to be (docs/language/surface-records.md §4.2).
enum DotResolution {
    /// An already inferred intrinsic selected by its receiver.
    Inferred(Term, Type, Level),
    /// A record field: the projection, its type and level, plus the field's
    /// implicitness skeleton, derived on demand from the *stored surface*
    /// field type — no new storage, keyed positionally by the same index the
    /// kernel Σ-walk uses (docs/language/implicit-binders-design.md §3.1).
    Project(Term, Type, Level, Option<Rc<Skel>>),
    /// A **class member reached through an instance**
    /// (docs/language/classes/traits-receiver-dispatch-design.md §2): the projection of a
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
        !AppUnify(self).is_checking_only(cx, expression)
            && self.probe(|| self.elab_infer(cx, expression).is_ok())
    }

    fn type_endpoint_infers_by_fallback(&self, cx: &Cx, expression: &Expr) -> bool {
        AppUnify(self).deferral_can_fall_back(cx, expression) && self.probe(|| self.elab_infer(cx, expression).is_ok())
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
                    || !heads.contains(&(part as *const Expr)) && AppUnify(self).is_checking_only(cx, part))
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
        Inductives(self).lower_named(cx, name, arguments, span)
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
        Operators(self).op_rewrite(cx, expression, None)
    }

    fn lower_declared_expression_type(
        &self,
        cx: &Cx,
        expression: &Expr,
        span: Span,
    ) -> R<Option<(Type, Level)>> {
        if let Some(lowered) = Codata(self).try_codata_indexed_ty(cx, expression, span)? {
            return Ok(Some(lowered));
        }
        if let Some(lowered) = IndexedFamilies(self).try_indexed_ty(cx, expression, span)? {
            return Ok(Some(lowered));
        }
        if let Some(lowered) = Inductives(self).try_type_value_app(cx, expression, span)? {
            return Ok(Some(lowered));
        }
        Inductives(self).try_valparam_ty(cx, expression, span)
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
        // By path: written as a method call, this would fall through the
        // view's dereference to the trait method being defined, and recurse,
        // the day the view's own method were out of sight from here.
        MismatchNotes::note_refl_mismatch(&MismatchNotes(self), cx, lhs, rhs, ty, level, span);
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
            .map_err(|error| AppUnify(self).let_ty_hint(cx, annotation, error))
    }

    fn check_let_value(
        &self,
        cx: &Cx,
        expression: &Expr,
        expected: &Type,
        level: &Level,
        skeleton: Option<&Skel>,
    ) -> R<Term> {
        Checking(self).elab_check_skel(cx, expression, expected, level, None, skeleton)
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
        let reference = Classes(self).class_ref_of_ty(annotation)?;
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
        Checking(self).elab_check_skel_slots(cx, result, expected, level, hint, skeleton, capture_slots)
    }
}

impl matching::MotiveSynthesisElab for Elaborator {
    fn generalizes_an_index(&self, cx: &Cx, scrutinee_type: &Type) -> bool {
        let var = |idx: &Term| matches!(idx, Term::Var(_));
        IwfFamily(self).iwf_of_at(cx, scrutinee_type).is_some_and(|(_, fam)| var(&fam.idx))
            || IndexedFamilies(self).indexed_of_at(cx, scrutinee_type).is_some_and(|(_, fam)| var(&fam.idx))
    }

    fn read_motive_type(&self, cx: &Cx, ty: &Type, span: Span) -> Option<Type> {
        self.whnf(cx, ty, span).ok()
    }

    fn read_motive_term(&self, cx: &Cx, term: &Term, _span: Span) -> Option<Rc<Term>> {
        self.semantic_oracle().whnf_term_probing(&cx.gamma, term).ok().map(Rc::new)
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
        // (docs/kernel/metatheory-ch07-extensions.md §28). So a hit stands only once
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

    fn motive_well_formed(&self, cx: &Cx, motive: &Type, scrutinee_type: &Type, scrutinee_level: &Level) -> bool {
        let mut inner = cx.clone();
        inner.push("__motive_z".to_string(), scrutinee_type.clone(), scrutinee_level.clone());
        let oracle = self.goal_oracle();
        typing::infer_type(oracle.world(), 0, Layer::Prog, &inner.gamma, motive, self.policy.fuel).is_ok()
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
        Inference(self).elab_convoy(
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
        Routes(self).elab_match(
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
    fn whnf_for_application(&self, cx: &Cx, ty: &Type, scratch: u32, span: Span) -> R<Type> {
        self.whnf_in(cx, ty, scratch, span)
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
        // (`docs/elaborator/annotation-component-respell-design.md` §2.5); `cod` binds
        // the argument, hence depth 1.
        let nd = GeneratedDefs(self).emit_ty_in(cx, dom, 0, scratch);
        let nc = GeneratedDefs(self).emit_ty_in(cx, cod, 1, scratch);
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
        Checking(self).elab_check_skel(cx, arg, expected, level, hint, skel)
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
        Defaults(self).elab_param_default(cx, args, expected, level, arg.span, earlier)
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

    fn same_index(&self, cx: &Cx, expected: &Term, got: &Term, ty: &Type, level: &Level) -> bool {
        expected == got
            || self
                .semantic_oracle()
                .convert_term(&cx.gamma, heather_kernel::layer::Layer::Prog, expected, got, ty, level)
                .is_ok()
    }

    fn self_call_application_params(&self, name: &str) -> Rc<Vec<ParamMeta>> {
        Callables(self).params_of(name)
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
        Quotation(self).try_code_template(cx, slot, ingredients, span)
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
        // `9` is a byte (docs/archive/native-programs-read-like-programs-design.md S3).
        let literal = matches!(&argument.kind, ExprKind::Num(_) | ExprKind::Scaled(_) | ExprKind::Char(_));
        // A binding statement's continuation (`Bind::seq(e, λ #bindN => rest)`,
        // docs/language/sequencing-surface-design.md §2.2) waits for the expected type:
        // the rest of the block is checked at the carrier's `M(B)`, never
        // inferred from its first token, so that `Pure(match … { … })` at the
        // end of a block checks as it would without the bind.
        let continuation = matches!(&argument.kind, ExprKind::Lam { binders, .. }
            if binders.len() == 1 && binders[0].name.starts_with("#bind"));
        application::ArgumentClass {
            checking_only: annotated_lambda || literal || continuation || AppUnify(self).is_checking_only(cx, argument),
            fallback_infer: annotated_lambda || literal || continuation || AppUnify(self).deferral_can_fall_back(cx, argument),
        }
    }

    fn infer_application_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)> {
        self.elab_infer(cx, argument)
    }

    fn infer_polymorphic_argument(
        &self, cx: &Cx, argument: &Expr, parameter: &Type, n: u32, sols: &[Sol],
    ) -> Option<R<(Term, Type, Level)>> {
        Polymorphic(self).infer_bare_polymorphic_argument(cx, argument, parameter, n, sols)
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
        AppUnify(self).unify_arg_ty(cx, parameter, argument, n, sols, meta_doms, guesses, span)
    }

    fn note_argument_mismatch(&self, cx: &Cx, got: &Type, expected: &Type, level: &Level, span: Span, clash: Option<application::SlotClash>) {
        if self.policy.owed_checks_forgotten {
            return;
        }
        MismatchNotes(self).note_check_clash(cx, got, expected, level, span, clash)
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
        AppUnify(self).solve_from_expected(cx, result, expected, n, sols, meta_doms, guesses, span)
    }

    fn result_agrees(&self, cx: &Cx, result: &Type, expected: &Type, level: &Level) -> bool {
        self.conv_types(cx, result, expected, level)
    }

    fn learn_from_solution_types(
        &self,
        cx: &Cx,
        meta_doms: &[Type],
        n: u32,
        sols: &mut [Sol],
        span: Span,
    ) -> bool {
        Elaborator::learn_from_solution_types(self, cx, meta_doms, n, sols, span)
    }

    fn resolve_application_obligation(
        &self,
        cx: &Cx,
        name: &str,
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
            let changed = Dictionaries(self).fill_index_from_scope(cx, name, written, params, slot_param, sols)
                || Dictionaries(self).fill_index_from_designation(
                    cx, name, written, params, slot_param, sols, meta_doms, n,
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
        // the callee's `0 < n` (docs/library/positivity-evidence-design.md §3). Spelled,
        // not decoded: decoding reduces `0 < 0` to `False`, which hides the
        // goal the caller asked for. Operator notation in it is
        // issues/diagnostic-operator-resugaring.md's.
        let display = written
            .map(|w| traits::render_goal_symbols(w, params).0)
            .unwrap_or_else(|| "a solver parameter".to_string());
        let applied = obligation
            .applied
            .as_ref()
            .map(|t| zonked_tm(t, n, sols).unwrap_or_else(|| t.clone()));
        let prefer = written
            .zip(applied.as_ref())
            .and_then(|(w, applied)| Classes(self).solver_carrier_head(w, params, applied));
        // A class over a type constructor shows the constructor the call
        // solved, `Bind<List>`, not the parameter it was written with.
        let display = written
            .zip(prefer.as_deref())
            .and_then(|(w, key)| {
                // Spelled only once committed: a scratch-world spine's globals
                // sit `n` places over.
                let committed = obligation.applied.as_ref().and_then(|t| zonked_tm(t, n, sols));
                Classes(self).kinded_goal_display(cx, w, params, key, committed.as_ref())
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
            // 5`, not the callee's `0 < n` (docs/library/positivity-evidence-design.md
            // §3). Spelled, not decoded: decoding reduces `0 < 0` to `False`,
            // which hides the goal the caller asked for. Operator notation in
            // it is issues/diagnostic-operator-resugaring.md's. Spelled only
            // here, on failure: a resolved goal never needs it. Which kind
            // the goal was is the search's own verdict, its outermost
            // `no-class` record (a class goal arrives in spellings the
            // display path cannot classify).
            // The trace's own first `goal:` line is the same goal, written
            // as the parameter declared it (`b.Apart`, a rule's `x.Positive`
            // before its `x` was solved); it takes the spelled goal too. A
            // nested search's lines were spelled where its own refusal was
            // made, so each goal is spelled once.
            None => {
                let mut trace = trace;
                let spelled = if trace.first().is_some_and(|top| {
                    trace.iter().any(|l| l.key == "no-class" && l.depth == top.depth)
                }) {
                    self.spell_type_clean(cx, &goal)
                } else {
                    None
                };
                if let Some(spelled) = &spelled
                    && let Some(top) = trace.first_mut()
                    && top.key == "goal"
                {
                    top.value = spelled.clone();
                }
                Err(ElabError::Resolution { goal: spelled.unwrap_or(display), span, trace })
            }
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
        let (goal, symbolic) = params
            .get(obligation.param)
            .and_then(|parameter| parameter.solver.as_deref())
            .map(|written| traits::render_goal_symbols(written, params))
            .unwrap_or_else(|| ("a solver parameter".to_string(), false));
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
            && let Some(reference) = Classes(self).class_ref_of_ty(solver)
            && let Some(class) = Classes(self).lookup_class(&reference.name)
            && !class.valparams.is_empty()
        {
            return Dictionaries(self).value_slot_refusal(&class, None, name, None, span);
        }
        // A class over a type constructor (issues/higher-kinded-classes.md):
        // its carrier is a value implicit, so `<…>` cannot give it. Name it,
        // and say what would have pinned it.
        if let Some(solver) = params
            .get(obligation.param)
            .and_then(|parameter| parameter.solver.as_deref())
            && let Some(reference) = Classes(self).class_ref_of_ty(solver)
            && let Some(class) = Classes(self).lookup_class(&reference.name)
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
/// recursive call to make at all (docs/metaprogramming/value-definitions-design.md §2.1).
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
/// [`NameLookup::self_shadow_note`]'s; errors other than a surface refusal
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
        Item::PrefixedRecord(p) => format!("record {}", p.record.name),
    }
}

impl Default for Elaborator {
    fn default() -> Self {
        Self::new()
    }
}

/// What a lifted obligation quantifies its arm binders at
/// (`docs/language/recursion/decreases-unfolding-design.md` §4): the constructor's stored field
/// types, instantiated at the scrutinee's type arguments.
impl measure::BinderTys for Elaborator {
    fn local_evidence(&self, decl: &Decl, scope: &[measure::Binder], goal: &Ty, arithmetic: bool) -> Option<Expr> {
        MeasureContext(self).measure_local_evidence(decl, scope, goal, arithmetic)
    }
    fn ctor_fields(&self, scrut: &Ty, ctor: &str) -> Option<Vec<Ty>> {
        Declarations(self).ctor_fields_of(scrut, ctor)
    }
    fn infer_local(&self, decl: &Decl, signatures: &[(String, Ty)], scope: &[measure::Binder], expr: &Expr) -> Option<Ty> {
        MeasureContext(self).infer_measure_local(decl, signatures, scope, expr)
    }
    fn default_goals(&self, decl: &Decl, signatures: &[(String, Ty)], scope: &[measure::Binder], call: &Expr) -> Vec<measure::FoundGoal> {
        MeasureContext(self).measure_default_goals(decl, signatures, scope, call).unwrap_or_default()
    }
    fn member_has_context_default(&self, name: &str) -> bool {
        self.names.has_searched_member_base(name)
    }
    fn has_context_default(&self, callee: &str) -> bool {
        NameLookup(self).key_of_kinds(callee, &[NameKind::Global])
            .and_then(|key| self.names.global(&key).map(|g| g.params.iter()
                .any(|p| p.default.as_ref().is_some_and(|d| defaults::is_context_search(&d.expr)))))
            .unwrap_or(false)
    }
}

/// Kernel workers a fresh elaborator uses when `HEATHER_KERNEL_WORKERS` is
/// unset. Eight: on the reused_callee certificate total CPU was flat from one
/// to eight workers and the wall was bounded by the serial elaborator past
/// four, so a wider default costs nothing but memory (peak RSS roughly tripled
/// at eight; the suite's per-process rail is sized for that). The width is
/// never a semantic decision — `docs/kernel/parallel-kernel-gate-design.md` §5.1 is
/// what makes a default above 1 safe to ship.
pub const DEFAULT_KERNEL_WORKERS: usize = 8;

/// The kernel worker count `HEATHER_KERNEL_WORKERS` asks for, if it names a
/// usable one (`docs/kernel/parallel-kernel-gate-design.md` §4).
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
    /// `docs/infrastructure/cache-v1-design.md` §6 is where the argument for the one shipped
    /// implementation lives.
    pub fn set_gate(&mut self, gate: Arc<dyn gate::KernelGate>) {
        self.policy.gate = Some(gate);
    }

    /// How many kernel worker threads a module's proof obligations are checked
    /// on (`docs/kernel/parallel-kernel-gate-design.md`).
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
    /// (`docs/kernel/parallel-kernel-gate-design.md` §5). Idempotent: with nothing
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
        // rows below (`docs/kernel/parallel-kernel-gate-design.md` §7).
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
    /// `recursion-meaning`, which reports a structurally recursive `fn` whose
    /// meaning check could not be settled (`meaning.rs`). Off by default;
    /// `heather check --review` sets it.
    pub fn set_review_lints(&mut self, on: bool) {
        self.policy.review_lints = on;
    }

    /// Check every structurally recursive `fn` against its source and refuse
    /// one whose compiled definition does not unfold to it (`meaning.rs`,
    /// issues/recursion-meaning-check.md). Off by default, where review mode
    /// still runs the check and reports a difference as a lint; `heather
    /// check --meaning-check` sets it.
    pub fn set_meaning_check(&mut self, on: bool) {
        self.policy.meaning_check = on;
    }

    /// Keep every theorem's proof from here on, for an exporter
    /// (`docs/library/export-fragment-design.md` §1). Off by default: an ordinary
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
        // (`docs/infrastructure/instrumentation-design.md` §3).
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
    /// (`docs/infrastructure/instrumentation-design.md` §3). Collection is per *thread*, not
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
    /// (`emission_walk`; docs/elaborator/annotation-component-respell-design.md §2.5).
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
    /// The degenerate module call (docs/language/modules-design.md §10.2): the prelude
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
    /// that produced it (`docs/native/repr-access-spellings-design.md` §6).
    ///
    /// The standing customer is the perturbed-emission mutation control: it
    /// re-checks generated text with one byte changed, and through the user
    /// entry point it would be refused for spelling a generated name instead
    /// of for the mutation — a control passing for the wrong reason.
    pub fn elab_generated_source(&mut self, src: &str) -> R<()> {
        self.session_transaction(|me| me.generated_mode(|me| me.elab_source(src)))
    }

    /// Elaborate a module, kernel-checking every declaration.
    ///
    /// A module's answer never depends on the worker count
    /// (`docs/kernel/parallel-kernel-gate-design.md` §5.1): the parallel pass is an
    /// accelerator for modules that are *accepted*, and any deferred failure
    /// discards it whole and re-runs the module serially, so what the caller
    /// receives is what the serial gate would have said — the same error, at
    /// the same declaration, with the same notes, over the same Ψ.
    pub fn elab_module_source(&mut self, module: &str, src: &str) -> R<()> {
        let mut deferred_failed = false;
        if self.gate_is_inline() {
            return ModulePassMut(self).elab_module_pass(module, src, &mut deferred_failed);
        }
        self.pass.kernel_replay.clear();
        let mark = self.module_pass_checkpoint();
        let parallel = ModulePassMut(self).elab_module_pass(module, src, &mut deferred_failed);
        if !deferred_failed {
            return parallel;
        }
        self.restore_module_pass(mark);
        ModulePassMut(self).serially(|me| me.elab_module_pass(module, src, &mut false))
    }

    // -- name resolution (docs/language/modules-design.md §4) -------------------------

    /// Resolve a written name to the module that declares it, by the §4
    /// regime. Every table lookup below goes through this.
    fn resolve_name(&self, name: &str) -> NameRes {
        // A generated name written in user source, and an access path naming
        // no declaration, are refused *here* — before anything can report them
        // as unknown, since "unknown" is exactly the wrong thing to say about
        // a name that exists and is not the surface
        // (docs/native/repr-access-spellings-design.md §6).
        if let Some(msg) = self.access_refusal(name) {
            return NameRes::Restricted(msg);
        }
        // `f::unfold` is the unfolding equation's designed spelling; the
        // equation is still declared as `f_unfold`, which stays a deprecated
        // spelling of it (docs/language/recursion/decreases-unfolding-design.md §2). A function
        // that declares a member `unfold` of its own keeps it.
        if let Some(base) = name.strip_suffix("::unfold") && self.access_alias(name).is_none() {
            let declared = NameLookup(self).resolve_declared(name);
            if matches!(declared, NameRes::Found(_)) {
                return declared;
            }
            return self.resolve_name(&format!("{base}_unfold"));
        }
        // A companion the walk declined to generate: say which body shape
        // stopped it (docs/language/recursion/decreases-unfolding-design.md §3, §6.1), since
        // "unknown name" — or "no member `step`" — is the wrong thing to say
        // about an equation the reader is right to expect. A name the module
        // declared itself is not one.
        let declared = NameLookup(self).resolve_declared(name);
        if matches!(declared, NameRes::Found(_)) {
            return declared;
        }
        if let Some(why) = self.pass.unfold_refusals.borrow().get(name) {
            // A reason that already names the document that explains it — a
            // group's, `docs/language/recursion/mutual-recursion-design.md` §6 — points there
            // instead.
            let see = if why.contains("docs/") {
                ""
            } else {
                ", see docs/language/recursion/decreases-unfolding-design.md §3"
            };
            if let Some(f) = name.strip_suffix("_unfold") {
                return NameRes::Restricted(format!("no unfolding equation for `{f}`: {why}{see}"));
            }
            // A branch equation is named by its arm's constructor
            // (`f::True`, `f::Succ`); a loop's are `f::step` and `f::done`.
            if name.rsplit("::").next().is_some_and(|last| last.starts_with(char::is_uppercase)) {
                return NameRes::Restricted(format!(
                    "no branch equation `{name}` (issues/definition-branch-equations.md): {why}"
                ));
            }
            return NameRes::Restricted(format!(
                "no step equation `{name}` (docs/language/recursion/decreases-unfolding-design.md §6.1): {why}"
            ));
        }
        if let Some(msg) = self.unknown_access_path(name) {
            return NameRes::Restricted(msg);
        }
        // A designed path whose generated declaration more than one imported
        // module made, for different declarations of one name: say so, since
        // "neither imported nor in scope" is wrong about a name two modules
        // declare (docs/tactics/functional-induction-design.md §6).
        if let Some(target) = self.access_alias(name)
            && let NameRes::Ambiguous(modules) = NameLookup(self).resolve_declared(target)
        {
            let list = modules.iter().map(|m| format!("`{m}`")).collect::<Vec<_>>().join(" and ");
            return NameRes::Restricted(format!(
                "`{name}` is ambiguous: {list} each generate it, for different declarations of the name"
            ));
        }
        declared
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

    /// The qualified table key a written name resolves to, if it resolves.
    ///
    /// A **designed access path** (`BinNat::abs`,
    /// `Impl(add, BinNat)::refines`) resolves to the declaration it names, and
    /// strictly as a *fallback*: only a name with no reading of its own takes
    /// it, so nothing that resolved before the alias existed can be
    /// reinterpreted by it (docs/native/repr-access-spellings-design.md §5).
    fn key_of(&self, name: &str) -> Option<String> {
        NameLookup(self).key_of_kinds(name, names::ANY_KIND)
    }

    pub(crate) fn lookup_global(&self, name: &str) -> Option<&GlobalInfo> {
        self.names.global(&self.key_of(NameLookup(self).instance_alias(name))?)
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
            .inductive(&NameLookup(self).key_of_kinds(name, &[NameKind::Inductive])?)
    }

    /// The mutual group member a name denotes in type position
    /// (docs/inductives/mutual-inductive-design.md §2): its family and its position
    /// among the family's members. A member is declared as an `Inductive`
    /// name, so it resolves, shadows and is imported exactly as a type does;
    /// it is found here and not by [`Self::lookup_inductive`] because it has
    /// no declaration of its own.
    pub(crate) fn lookup_member(&self, name: &str) -> Option<(Rc<Inductive>, usize)> {
        self.types
            .member(&NameLookup(self).key_of_kinds(name, &[NameKind::Inductive])?)
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
        // §8 of `docs/language/recursion/mutual-recursion-design.md`: a member whose run was
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
                     and they call *each other* (docs/language/recursion/mutual-recursion-design.md §1). \
                     A call that is not answered needs the callee declared first",
                );
            }
        }
        ElabError::Elab { msg, span }
    }

    /// Record a name as declared by the module being elaborated. Called at
    /// registration time — after the kernel gate — so that the index and the
    /// tables land together.
    pub(crate) fn add_name(&mut self, name: &str, kind: NameKind) {
        DeltasMut(self).semantic_commit_name(name, kind);
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
    /// (`docs/elaborator/diagnostic-warnings-design.md` §3). Draining rather than
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
        NameLookup(self).emit_lint_with_fix(lint, msg, span, None);
    }

    /// [`Self::check_source`] into a named module — what the CLI's loader
    /// calls once per file of the import closure, in topological order
    /// (docs/language/modules-design.md §3.2). A module whose imports are themselves
    /// broken reports that and checks nothing: there is no recovery point
    /// before the scope exists.
    pub fn check_module_source(&mut self, module: &str, src: &str) -> Vec<ElabError> {
        ModulePassMut(self).check_module_source_inner(module, src)
    }

    /// The canonical derived instances minted so far, in mint order
    /// (docs/language/classes/traits-layer2-design.md §8) — one per *derivation*, not per use
    /// site, which is the coherence invariant this table is.
    pub fn derived_instances(&self) -> Vec<&str> {
        self.traits
            .derived()
            .iter()
            .filter(|d| !crate::resolve::is_open_head(d.head.as_deref()))
            .map(|d| d.name.as_str())
            .collect()
    }

    /// The **open** derivations minted so far, in mint order: an upcast or a
    /// merged class's assembly at a class carrier, abstracted over the
    /// context prefix it was found in ([`Resolution::record_open`](crate::resolve::Resolution::record_open)).
    pub fn open_derivations(&self) -> Vec<&str> {
        self.traits
            .derived()
            .iter()
            .filter(|d| crate::resolve::is_open_head(d.head.as_deref()))
            .map(|d| d.name.as_str())
            .collect()
    }

    /// Assumptions reachable from one declaration, resolved by the same name
    /// judgment as an ordinary source reference.
    pub fn axiom_report(&self, name: &str) -> Result<AxiomReport, String> {
        let key = NameLookup(self)
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

    /// A global's binding index by written name — the Ψ coordinate
    /// [`Self::global_name_at`] inverts. Reflection-internal.
    pub(crate) fn global_abs(&self, name: &str) -> Option<usize> {
        Some(self.lookup_global(name)?.abs as usize)
    }

    /// The layer a term binding was bound at, by the name the current module
    /// resolves: `c` for every declaration, codata included
    /// (docs/kernel/kernel-m-codes-design.md §0).
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

    /// A name as the current module resolves it, qualified: what a producer
    /// asks of a name an author wrote.
    pub fn qualified_global(&self, name: &str) -> Option<String> {
        NameLookup(self).global_qualified_name_at(self.global_abs(name)?)
    }

    /// The absolute Ψ index a `GlobalVar` *occurring in a term being
    /// displayed* refers to. Same inversion as [`Self::gen_def_of`]'s, and for
    /// the same reason: the index counts from the innermost end of the padded
    /// Ψ, so the goal region and a `meta fn`'s pushed binders both shift it.
    /// Fully checked — a `GlobalVar` reaching here can be anything the term it
    /// came out of contains, including one that is out of scope.
    pub(crate) fn global_abs_of(&self, var: GlobalVar) -> Option<usize> {
        var.position(self.lowering_scope() as usize)
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
        DeclarationsMut(self).elab_decl_as(decl, owner)
    }

    /// One ordinary declaration, with `obligations` the measure-obligation
    /// table to reword errors through where this declaration was generated by
    /// [`measure`] (`None` for source declarations).
    fn elab_decl_one(&mut self, decl: &Decl, obligations: Option<&measure::Obligations>) -> R<()> {
        // Constraints sharing a symbol at one carrier become one dictionary
        // of a synthesized class, made here — between items, where Ψ may
        // grow — before the declaration's own attempts begin
        // (issues/constraints-sharing-indices.md).
        let merged = ClassesMut(self).merge_linked_constraints(decl)?;
        let decl = merged.as_ref().unwrap_or(decl);
        let warn_mark = self.pass.warnings.borrow().len();
        let mut reserved = 0;
        self.attempt.goal_arena.enable_restarts();
        let r = loop {
            self.attempt.prepare();
            self.pass.pending_derived.borrow_mut().clear();
            let r = DeclarationsMut(self).check_decl(decl, reserved);
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
                DeclarationsMut(self).commit_decl(pending);
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
                    self.attempt.goal_arena.solve_named(name, t);
                }
                // `on _: P := e;` — discharge *every* goal whose statement is
                // `P` (docs/archive/surface-v2.md §2: one bound proof feeding
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
                        self.attempt.goal_arena.solve(k, t);
                    }
                }
                // A `split` arm, consumed by the parser into an `Arm`
                // (docs/language/matching/match-equation-split-design.md §6); one that reaches a
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
    /// `L = |Ψ| + goal_base`, `GlobalVar::index(v)` is `bindings[L - 1 - v]`, so goal
    /// `k` at `GlobalVar::index(goal_base - 1 - k)` lands immediately after the
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
    /// payload for goal `k` at `GlobalVar::index(goal_base - 1 - k)`, matching
    /// `apply_global`'s convention. Reserved-but-unused slots (the pre-count
    /// is an upper bound) get a payload nothing can reach.
    fn goal_subst(&self) -> GlobalSubst {
        self.attempt.goal_arena.substitution()
    }

    // -- types --------------------------------------------------------------

    fn elab_ty(&self, cx: &Cx, ty: &Ty) -> R<(Type, Level)> {
        // A class over a type constructor, `Bind<Option>`, is its record
        // applied to the constructor (issues/higher-kinded-classes.md).
        if let Some(t) = Classes(self).kinded_class_ty(ty) {
            return self.elab_ty(cx, &t);
        }
        match &ty.kind {
            // A generated declaration's type (`host::Leaves::Member`).
            TyKind::Named { name, .. } if let Some(k) = host::leaf_index(name) => Host(self).host_ty_leaf(cx, k, ty.span),
            // An expression in type position: infer it, require its type to be
            // a universe, and decode (docs/language/surface-universe.md §4). `El` is the
            // kernel's own decoding, so nothing here is a coercion — the term
            // *is* a code, and `El ⌜T⌝ ⇝ T` makes a written type and a decoded
            // one convertible rather than merely equal-looking.
            TyKind::OfExpr(e) => self.expr_elab().lower_expression_type(self, cx, e, ty.span),
            // A `def`'s type, inferred from its value
            // (docs/metaprogramming/value-definitions-design.md §2.2). `check_decl` reads the
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
        Checking(self).elab_check_hinted(cx, e, expected, lvl, None)
    }

    /// Inference mode: returns the elaborated term with its canonical type
    /// and level.
    fn elab_infer(&self, cx: &Cx, e: &Expr) -> R<(Term, Type, Level)> {
        Inference(self).elab_infer_at(cx, e, None)
    }

    /// A global the source names: a declaration, not a minted accessor.
    fn named_head(&self, head: &Term) -> bool {
        let Term::GlobalTm { var, .. } = head else { return false };
        self.global_abs_of(*var).and_then(|abs| NameLookup(self).global_qualified_name_at(abs)).is_some()
    }

    /// A local variable by absolute position (outermost first), as
    /// [`Self::resolve`] would return it.
    pub(crate) fn local(&self, cx: &Cx, pos: usize) -> (Term, Type, Level) {
        let idx = (cx.names.len() - 1 - pos) as u32;
        let entry = &cx.gamma.entries[pos];
        let key = (Rc::as_ptr(&entry.ty) as usize, idx + 1);
        let known = self.attempt.weakened_entries.borrow().get(&key).map(|(_, ty)| Type::clone(ty));
        let ty = known.unwrap_or_else(|| {
            let ty = entry.ty.shift_local(idx + 1);
            self.attempt
                .weakened_entries
                .borrow_mut()
                .insert(key, (Rc::clone(&entry.ty), Rc::new(ty.clone())));
            ty
        });
        (Term::Var(LocalVar(idx)), ty, entry.level.clone())
    }

    /// Is this name bound by something the user wrote? Builtins give way to
    /// locals, `let` aliases and declarations, so none of them is a keyword.
    /// (Which of these readings races a type-owned member is finer than
    /// this: `member_head` asks `ambient_reading_survives`,
    /// docs/language/classes/receiver-member-resolution-design.md §2.)
    fn shadowed(&self, cx: &Cx, name: &str) -> bool {
        cx.names.iter_inner().any(|n| n == name)
            || cx.aliases.iter_inner().any(|a| a.name == *name)
            || self.lookup_global(name).is_some()
            // The declaration's own name. It is not in `globals` until it is
            // checked, so without this a `fn map` could not recurse: its
            // self-call took the built-in vector-`map` path instead
            // (found writing docs/language/surface-polymorphism.md §9's headline test).
            || cx.selfref.as_ref().is_some_and(|s| s.matches(name))
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
        // (docs/language/constructor-function-values.md §2.1). Unlike a declared
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
        if let Some((ind, i)) = self.ctor_of(name).or_else(|| Constructors(self).ctor_over_types(name)) {
            return Constructors(self).infer_ctor(cx, &ind, i, &[] as &[Expr], span);
        }
        // The enclosing declaration's own name: only a saturated, guarded
        // *call* means anything (it is the induction hypothesis, not a value).
        if let Some(selfref) = cx.selfref.as_ref().filter(|s| s.matches(name)) {
            let note = NameLookup(self).self_shadow_note(selfref, name);
            return err(self_name_refusal(selfref, name), span).map_err(|e| with_self_shadow_note(e, note.as_deref()));
        }
        let resolved_global = self
            .key_of(NameLookup(self).instance_alias(name))
            .and_then(|key| self.names.global(&key).map(|info| (key, info)));
        match resolved_global {
            Some((key, GlobalInfo { abs, .. })) => {
                // A committed binding is a constant: the same reference
                // under the goals, and under a `meta fn`'s Ψ-extending
                // binders (its `Ctx` binder, each hoisted letbox global, a
                // `match code` branch telescope), which are the variables
                // after it. A layer-m term *may* name a layer-c global
                // (`i' ≤ i`, typing.rs:756), which is what lets an analyzer's
                // arms call ordinary library functions
                // (docs/archive/certgen-transcriber-in-language-design.md §4).
                let var = GlobalVar::constant(*abs);
                let GlobalBinding::Tm { ty, level, .. } = &self.psi.bindings[*abs as usize] else {
                    unreachable!("global index points at a non-Trm binding");
                };
                // A constant's statement is read as stored (the kernel's own
                // lookup convention, typing.rs).
                let ty = Rc::clone(ty);
                // The binding is closed (· ⊢), so the delayed substitution
                // is the empty map out of the current Γ.
                let subst = LocalSubst {
                    tail: SubstTail::Empty,
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
            // absence (docs/language/modules-design.md §4).
            None => {
                // `G::AddCommMonoid` — a class **at a type**, resolved. Here
                // and not earlier: a registered instance is an ordinary global
                // and was found above, so this reaches only the carriers that
                // have none (docs/language/classes/traits-type-projection-design.md §5).
                if let Some(r) = Projections(self).class_at_type(cx, name, &[], span) {
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
                if name == "simp_only" || name == "simp_show" {
                    return err(
                        format!(
                            "`{name}(h, …)` needs an expected type: it simplifies a goal, so it \
                             only means anything where one is known (a `theorem` body, an \
                             annotated `let`, a `calc` step, an argument)"
                        ),
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

    /// [`Self::whnf`] for a type scoped in an application's **scratch
    /// world** of width `scratch`: `scratch` metavariables at the global
    /// indices below every committed binding (`application.rs`). At zero it
    /// is [`Self::whnf`].
    ///
    /// The reduction runs in the semantic world extended by `scratch` opaque
    /// bindings, so every index the type mentions names what it names in
    /// the scratch world: a committed definition unfolds as itself, and a
    /// metavariable is a stuck global. The bindings stand in only for their
    /// indices: δ reads a binding's body and nothing else (`Defs::body`), and
    /// these have none, so their declared type is never consulted. Reducing
    /// the type against the committed world instead read every committed
    /// global `scratch` bindings too deep: δ unfolded some other definition,
    /// and substituting its body — scoped in that definition's own context —
    /// by this occurrence's substitution aborted the kernel
    /// (issues/merged-call-through-upcast-panics.md).
    ///
    /// Of the inline respellings only the reference's is read here
    /// ([`Self::unspell_here`], a constant, so the same in the scratch
    /// world); the sum and `Wf` ones are not asked. A probe that
    /// meets a sum or a `Wf` wanted a `Π` and refuses either way.
    pub(crate) fn whnf_in(&self, cx: &Cx, ty: &Type, scratch: u32, span: Span) -> R<Type> {
        if scratch == 0 {
            return self.whnf(cx, ty, span);
        }
        if let Some(inline) = self.unspell_here(ty) {
            return Ok(inline);
        }
        let stand_in = GlobalBinding::Tm {
            ctx: cx.gamma.clone(),
            layer: Layer::Prog,
            ty: Rc::new(Type::Nat),
            level: Level::Zero,
            body: None,
        };
        let semantic = self.semantic_oracle();
        let world = semantic.world().extended((0..scratch).map(|_| stand_in.clone()));
        oracle::SemanticOracle::in_world(world, self.policy.fuel)
            .whnf_type(&cx.gamma, ty)
            .map_err(|_| ElabError::Elab {
                msg: "out of fuel reducing a type".into(),
                span,
            })
    }

    fn whnf(&self, cx: &Cx, ty: &Type, span: Span) -> R<Type> {
        // A reference to a registered lowering reduces back to the **registry's
        // own copy**, not to the kernel's lazy decode of it
        // (`docs/inductives/wf-shape-code-design.md` §3.3). The two are the same type; the
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
        Ok(GeneratedDefs(self)
            .unspell_sum_components(&head)
            .or_else(|| GeneratedDefs(self).unspell_wf_slots(&head))
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
    /// (`docs/elaborator/intro-by-type-design.md` §4.1)? Everywhere but inside a
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
        let withheld = InterfaceDefs(self).withheld_policy();
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

/// The universe an expected type is, read structurally: `Type<n>`, or its
/// decoded code `El(«Ty n»)`. No whnf, so the checking arm that asks costs
/// nothing at the expected types that are neither.
fn expected_universe(expected: &Type) -> Option<&Level> {
    match expected {
        Type::Ty(level) => Some(level),
        Type::El { tm, .. } => match &**tm {
            Term::TmTy(level) => Some(level),
            _ => None,
        },
        _ => None,
    }
}

/// The base name a declaration recurses under, as `Cx.selfref` uses it.
fn base_name(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// Does `block` call one of `names` at a position the measure walk rewrites —
/// the head of a saturated application (`docs/language/recursion/mutual-recursion-design.md` §1)?
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

/// The mutual groups of `docs/language/recursion/mutual-recursion-design.md` §1: within each
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
    /// (docs/language/recursion/mutual-recursion-design.md §1).
    Measure,
    /// Mutual `inductive` declarations (docs/inductives/mutual-inductive-design.md §1).
    Inductive,
    /// Declarations without a measure that call one another, one of them
    /// recursing over a mutual family (docs/inductives/mutual-inductive-design.md §6).
    Structural,
}

/// The reserved name of a match's anonymous equation once it is bound
/// (docs/language/matching/dependent-match-compiler-design.md §4.1). `__` names are the
/// machinery's; a certificate may spell it, a user does not write it.
pub(crate) const MATCH_EQ: &str = "__match_eq";

/// An indexed family as [`Inference::elab_convoy_packed`] reads it: its index
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


/// Why [`DeclarationsMut::try_recursion_at_top`] runs: as the lowering of an
/// ordinary Nat recursion, or in place of a refusal or the measure route.
#[derive(Clone, Copy, PartialEq, Eq)]
enum TopAttempt {
    Default,
    Fallback,
}

/// Recursion at the top on a tier-1 `Wf` parameter `z`
/// (docs/language/recursion/recursion-at-the-top-design.md §4, slice 3), by hoisting: one
/// `match z` around the body, each arm rebinding `z` to its constructor
/// term, and every `match z` in the body replaced by its arm for that
/// constructor (a `match` on a known constructor, taken at the surface).
/// The arm binders are the body's own first `match z`'s, so its nested
/// `match`es on them are the chain the window reads, and a self-call on
/// one of them elaborates to the child the guard compares by term.
///
/// `None` (the plain lowering stands) where the rewrite cannot be stated
/// without tracking scopes: `z` rebound anywhere in the body, a `match z`
/// with an equation, a written motive or a nested pattern, or no
/// `match z` at all.
fn recursion_at_top_hoisted(decl: &Decl, dec: usize, ind: &inductive::Inductive) -> Option<Decl> {
    use heather_syntax::{Arm, Block, Pat, Stmt};
    let span = decl.span;
    let param = &decl.params[dec - decl.tyvars.len()];
    let z = param.name.clone();
    let whole = Expr { kind: ExprKind::Block(Box::new(decl.body.clone())), span: decl.body.span };
    // Every name the body binds: `z` among them is a scope this rewrite
    // does not track.
    let mut bound: Vec<String> = Vec::new();
    crate::surface::walk_expr(&whole, &mut |e| match &e.kind {
        ExprKind::Lam { binders, .. } => bound.extend(binders.iter().map(|b| b.name.clone())),
        ExprKind::Block(b) => {
            for st in &b.stmts {
                match st {
                    Stmt::Let { name, .. } | Stmt::LetCode { name, .. } => bound.push(name.clone()),
                    Stmt::LetRecord { fields, .. } => fields.iter().for_each(|f| measure::pat_names(&f.pat, &mut bound)),
                }
            }
        }
        ExprKind::Match { eqbind, arms, .. } => {
            bound.extend(eqbind.iter().cloned());
            arms.iter().for_each(|a| a.binders.iter().for_each(|p| measure::pat_names(p, &mut bound)));
        }
        ExprKind::MatchCode { arms, .. } => {
            arms.iter().for_each(|a| a.binders.iter().for_each(|p| measure::pat_names(p, &mut bound)));
        }
        _ => {}
    });
    if bound.contains(&z) {
        return None;
    }
    let ctor_of = |arm: &Arm, c: &inductive::Ctor| !arm.default && (arm.ctor == c.name || arm.ctor.ends_with(&format!("::{}", c.name)));
    let simple = |arm: &Arm, c: &inductive::Ctor| {
        arm.binders.len() == c.fields.len() && arm.binders.iter().all(|p| matches!(p, Pat::Var { .. }))
    };
    let is_z = |e: &Expr| matches!(&e.kind, ExprKind::Var(v) if *v == z);
    // The first `match z`, whose binders name the wrapper's.
    let mut first: Option<Vec<Arm>> = None;
    let mut refused = false;
    crate::surface::walk_expr(&whole, &mut |e| {
        if let ExprKind::Match { form, scrut, eqbind, motive, arms, .. } = &e.kind
            && is_z(scrut)
        {
            if *form != MatchForm::Match || eqbind.is_some() || motive.is_some() {
                refused = true;
            }
            if first.is_none() {
                first = Some(arms.clone());
            }
        }
    });
    let first = first?;
    if refused {
        return None;
    }
    // The body with every `match z` taken out, for capture: a hoisted name
    // the rest of the body mentions would be shadowed by the wrapper.
    let mut rest = whole.clone();
    crate::alpha::walk_expr_mut(&mut rest, &mut |e| {
        if let ExprKind::Match { scrut, .. } = &e.kind
            && is_z(scrut)
        {
            e.kind = ExprKind::Refl;
            return true;
        }
        false
    });
    let mut mentioned = Vec::new();
    crate::alpha::collect_names(&rest, &mut mentioned);
    // Whether the body reads `z` other than to take it apart: the
    // scrutinees of its `match z`s blanked, their arms kept.
    let mut unscrutinized = whole.clone();
    crate::alpha::walk_expr_mut(&mut unscrutinized, &mut |e| {
        if let ExprKind::Match { scrut, .. } = &mut e.kind
            && is_z(scrut)
        {
            scrut.kind = ExprKind::Refl;
        }
        false
    });
    let mut read = Vec::new();
    crate::alpha::collect_names(&unscrutinized, &mut read);
    let reads_z = read.contains(&z);
    let pat_name = |p: &Pat| match p {
        Pat::Var { name, .. } => name.clone(),
        _ => unreachable!("simple binders only"),
    };
    let mut arms = Vec::new();
    for (i, c) in ind.ctors.iter().enumerate() {
        let written = first.iter().find(|a| ctor_of(a, c) && simple(a, c));
        let names: Vec<String> = (0..c.fields.len())
            .map(|j| {
                written
                    .map(|a| pat_name(&a.binders[j]))
                    .filter(|n| n != "_" && *n != z && !mentioned.contains(n))
                    .unwrap_or_else(|| format!("{z}#{i}_{j}"))
            })
            .collect();
        let var = |n: &str| Expr { kind: ExprKind::Var(n.to_string()), span };
        let head = written.map_or_else(|| c.name.clone(), |a| a.ctor.clone());
        let value = if names.is_empty() {
            var(&head)
        } else {
            Expr {
                kind: ExprKind::App {
                    head: Box::new(var(&head)),
                    args: names.iter().map(|n| var(n)).collect(),
                    named: Vec::new(),
                    explicit: false,
                    goal_oriented: false,
                },
                span,
            }
        };
        // Each `match z` in the body, at this constructor, is its arm.
        let mut body = whole.clone();
        let mut ok = true;
        crate::alpha::walk_expr_mut(&mut body, &mut |e| loop {
            // A replacement that is itself a `match z` is taken again here:
            // the walk visits a replaced node's children, not the node.
            let ExprKind::Match { scrut, arms: inner, .. } = &e.kind else { return false };
            if !is_z(scrut) {
                return false;
            }
            let Some(arm) = inner.iter().find(|a| ctor_of(a, c)).or_else(|| inner.iter().find(|a| a.default)) else {
                ok = false;
                return true;
            };
            if !arm.default && !simple(arm, c) {
                ok = false;
                return true;
            }
            let mut stmts = Vec::new();
            if !arm.default {
                for (p, n) in arm.binders.iter().zip(&names) {
                    let b = pat_name(p);
                    if b != "_" && b != *n {
                        stmts.push(Stmt::Let { name: b, ty: None, expr: var(n), span, opaque: false });
                    }
                }
            }
            let result = arm.body.clone();
            *e = if stmts.is_empty() {
                result
            } else {
                let rspan = result.span;
                Expr {
                    kind: ExprKind::Block(Box::new(Block { stmts, result: Box::new(result), ons: Vec::new(), span: rspan })),
                    span: rspan,
                }
            };
            // The replacement's children are visited next, so a `match z`
            // inside the arm is this constructor's too.
        });
        if !ok {
            return None;
        }
        let ExprKind::Block(body) = body.kind else { unreachable!("the body is a block") };
        // `z` rebound only where the body still reads it, anywhere but as a
        // `match`'s scrutinee (inside the arms too): an unread binding still
        // costs its annotated elaboration and its term.
        let mut stmts = Vec::new();
        if reads_z {
            stmts.push(Stmt::Let { name: z.clone(), ty: Some(param.ty.clone()), expr: value, span, opaque: false });
        }
        stmts.extend(body.stmts);
        arms.push(Arm {
            ctor: head,
            default: false,
            binders: names.iter().map(|n| Pat::Var { name: n.clone(), span }).collect(),
            body: Expr {
                kind: ExprKind::Block(Box::new(Block { stmts, result: body.result, ons: body.ons, span: decl.body.span })),
                span: decl.body.span,
            },
            span,
        });
    }
    let mut lowered = decl.clone();
    lowered.body = heather_syntax::Block {
        stmts: Vec::new(),
        result: Box::new(Expr {
            kind: ExprKind::Match {
                form: MatchForm::Match,
                generated: true,
                scrut: Box::new(Expr { kind: ExprKind::Var(z), span }),
                eqbind: None,
                motive: None,
                arms,
            },
            span,
        }),
        ons: Vec::new(),
        span: decl.body.span,
    };
    Some(lowered)
}
