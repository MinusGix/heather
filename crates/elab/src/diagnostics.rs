//! Public diagnostics emitted by elaboration.
//!
//! Keeping these API types separate from the elaborator makes the boundary
//! explicit: diagnostics contain source data and rendered kernel values, never
//! live elaboration state.

use heather_kernel::typing::TypeError;
use heather_syntax::{ParseError, Span};

use crate::lint::Lint;
use crate::resolve;

#[derive(Debug)]
pub enum ElabError {
    Parse(ParseError),
    /// A surface-level elaboration failure (unbound name, unsupported form,
    /// arity mismatch, missing motive, …).
    Elab {
        msg: String,
        span: Span,
    },
    /// The kernel rejected an elaborated declaration.
    Kernel {
        decl: String,
        span: Span,
        err: TypeError,
        note: Option<String>,
    },
    /// Goals raised in a block that no `on` statement discharged.
    UnsolvedGoals {
        decl: String,
        goals: Vec<GoalReport>,
    },
    /// A solver parameter whose goal could not be resolved.
    Resolution {
        goal: String,
        span: Span,
        trace: Vec<resolve::TraceLine>,
    },
    /// Internal control flow for argument-slot abstraction.
    ArgSlotEscape {
        span: Span,
    },
}

/// One entry of the unsolved-goal listing.
#[derive(Debug)]
pub struct GoalReport {
    pub name: String,
    pub statement: String,
    pub context: Vec<(String, String)>,
    pub origin: Option<String>,
    pub source: Option<GoalSource>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GoalSource {
    Argument {
        callee: String,
        parameter: String,
    },
    ApplyImplicit {
        callee: String,
        parameter: String,
        parameter_index: usize,
        apply_span: Span,
    },
}

/// Diagnostics get a small, independent reduction allowance.
pub(crate) const DISPLAY_DECODE_STEPS: usize = 32;

/// The reduction allowance for a written `refl`'s mismatch note
/// (`issues/elab-refl-accepts-match-eta-kernel-rejects.md`). Deliberately far
/// below the kernel's own budget: the note repeats work the gate is about to
/// do, so it may only pay for the disagreements that are cheap to decide.
pub(crate) const REFL_NOTE_FUEL: u64 = 1 << 12;

/// Maximum stuck positions considered during goal motive synthesis.
pub(crate) const STUCK_CANDIDATES: u32 = 64;

/// The lowering selected for an indexed inductive declaration.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IndexedRoute {
    One,
    Forded,
}

#[derive(Debug, Clone)]
pub struct LintFix {
    pub span: Span,
    pub replacement: String,
}

#[derive(Debug, Clone)]
pub struct Warning {
    pub lint: Lint,
    pub msg: String,
    pub span: Span,
    pub fix: Option<LintFix>,
}

impl Warning {
    pub fn render(&self, src: &str) -> String {
        let (line, col) = line_col(src, self.span.start);
        format!("{line}:{col}: warning: {}", self.msg)
    }

    pub fn render_snippet(&self, src: &str, file: &str) -> String {
        headed("warning", &self.msg, self.span, src, file)
    }
}

fn headed(severity: &str, msg: &str, span: Span, src: &str, file: &str) -> String {
    let (line, col) = line_col(src, span.start);
    format!(
        "{severity}: {msg}\n  --> {file}:{line}:{col}\n{}",
        snippet(src, span)
    )
}

fn snippet(src: &str, span: Span) -> String {
    let offset = span.start.min(src.len());
    let line_start = src[..offset].rfind('\n').map_or(0, |nl| nl + 1);
    let line_end = src[offset..].find('\n').map_or(src.len(), |nl| offset + nl);
    let text = &src[line_start..line_end];
    let (line, _) = line_col(src, span.start);
    let col = src[line_start..offset].chars().count();
    let line_rest = text.chars().count().saturating_sub(col);
    let span_chars = src[offset..span.end.clamp(offset, src.len())]
        .chars()
        .count();
    let width = span_chars.clamp(1, line_rest.max(1));
    let num = line.to_string();
    let pad = " ".repeat(num.len());
    format!(
        "{pad} |\n{num} | {text}\n{pad} | {}{}\n",
        " ".repeat(col),
        "^".repeat(width),
    )
}

fn line_col(src: &str, offset: usize) -> (usize, usize) {
    let upto = &src[..offset.min(src.len())];
    let line = upto.matches('\n').count() + 1;
    let col = upto
        .rfind('\n')
        .map_or(upto.len(), |nl| upto.len() - nl - 1)
        + 1;
    (line, col)
}
