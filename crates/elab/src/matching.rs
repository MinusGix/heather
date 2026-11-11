//! Shared motive mechanics for surface eliminators.
//!
//! Route-specific lowering remains with the Nat, inductive, indexed, forded,
//! and `Wf` owners.  This module owns what all of them consume: reading a
//! written motive, synthesizing a motive from a checking goal, and the pure
//! syntax/core transformation used by convoy matching.

use heather_kernel::rc::Rc;

use heather_kernel::level::{Level, UnivVar};
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};
use heather_syntax::{Arm, Expr, ExprKind, LamBinder, MatchForm, Span, Ty, TyKind};

use crate::diagnostics::STUCK_CANDIDATES;
use crate::{Cx, ElabError, R, err};

mod routes;
pub(crate) use routes::Routes;
pub(crate) use routes::{ChainStep, cov_comps, cov_proj, cov_ty, cov_tuple};

/// Semantic reads required by the motive-synthesis ladder.
pub(crate) trait MotiveSynthesisElab {
    fn read_motive_type(&self, cx: &Cx, ty: &Type, span: Span) -> Option<Type>;
    fn read_motive_term(&self, cx: &Cx, term: &Term, span: Span) -> Option<Rc<Term>>;
    fn motive_candidate_converts(
        &self,
        cx: &Cx,
        candidate: &Term,
        scrutinee: &Term,
        scrutinee_type: &Type,
        scrutinee_level: &Level,
    ) -> bool;
    /// Whether the scrutinee's type is an indexed family whose index the
    /// route will generalize (`generalize_index`), which rewrites every
    /// occurrence of the index in the motive, annotations included.
    fn generalizes_an_index(&self, _cx: &Cx, _scrutinee_type: &Type) -> bool {
        false
    }
}

/// The declaration-local state which must disappear when a motive candidate
/// is declined. The mark is deliberately opaque to matching: its owner decides
/// which diagnostic and goal channels form one rollback boundary. Retained
/// mismatch evidence is intentionally not one of them.
pub(crate) trait MatchSpeculationState {
    type Mark: Copy;

    fn mark_match_state(&self) -> Self::Mark;
    fn rollback_match_state(&self, mark: Self::Mark);
    fn motive_probe_active(&self) -> bool;
    fn set_motive_probe_active(&self, active: bool);
}

/// Semantic operations used while discovering a constant motive.
///
/// Candidate policy belongs here; expression inference and final route
/// lowering remain capabilities supplied by the root elaborator. In
/// particular, matching gains neither declaration commit authority nor a
/// reference to the whole elaborator.
pub(crate) trait ConstantMotiveElab: MatchSpeculationState {
    fn infer_motive_expr(&self, cx: &Cx, expr: &Expr) -> R<(Term, Type, Level)>;
    fn lower_if_condition(&self, cx: &Cx, condition: &Ty) -> R<(Type, Level)>;

    #[allow(clippy::too_many_arguments)]
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
    ) -> R<Term>;

    /// [`Self::lower_constant_match`] with the arms' equation bound as `h`
    /// (a convoy). Only the elaborator implements it.
    #[allow(clippy::too_many_arguments)]
    fn lower_constant_convoy(
        &self,
        _cx: &Cx,
        _form: MatchForm,
        _generated: bool,
        _h: &str,
        _arms: &[Arm],
        _scrutinee: Term,
        _scrutinee_type: &Type,
        _scrutinee_level: &Level,
        _motive: Type,
        _motive_level: Level,
        _result: &Type,
        span: Span,
    ) -> R<Term> {
        err("an equation binding has no constant-motive lowering here", span)
    }
}

/// The sink of an arm-type probe (docs/dependent-match-compiler-design.md
/// §6). The probe lowers the match at a constant marker motive; the first arm
/// body checked against the marker whose inferred type lives outside the
/// arm's binders is recorded here, and the probe stops.
pub(crate) struct ArmTypeProbe {
    /// The context length at the `match`.
    pub(crate) base: usize,
    pub(crate) found: std::sync::Mutex<Option<(Type, Level)>>,
}

/// The marker level: a universe variable no declaration binds.
pub(crate) const ARM_PROBE_LEVEL: Level = Level::Var(UnivVar(u32::MAX - 1));

/// The marker motive's type, `Unit` at the marker level. Closed, so shifting
/// and substitution leave it alone, and in whnf.
pub(crate) fn arm_probe_marker() -> Type {
    Type::Unit { level: ARM_PROBE_LEVEL }
}

/// Whether `ty` mentions the marker level (an arm that returned its own
/// `ih`, whose type is the marker): such a type names no motive.
pub(crate) fn mentions_marker(ty: &Type) -> bool {
    ty.shift_univ_above(1, u32::MAX - 1) != *ty
}

/// `ty`, inferred under `extra` binders past the probe's base, strengthened
/// past them; `None` if it mentions one.
pub(crate) fn strengthen_past(ty: &Type, gamma: &heather_kernel::term::LocalCtx, extra: usize) -> Option<Type> {
    if extra == 0 {
        return Some(ty.clone());
    }
    let mut sub = LocalSubst::id(gamma);
    for _ in 0..extra {
        sub = sub.extended(Rc::new(Term::Zero));
    }
    let base = ty.apply_local(&sub);
    (base.shift_local(extra as u32) == *ty).then_some(base)
}

/// The outcome of trying to infer a constant match motive.
///
/// `Declined` means the caller should request a written motive. `Failed` means
/// the route was recognized and its error is authoritative rather than
/// speculative.
pub(crate) enum MotiveInference<T, E> {
    Declined,
    Accepted(T),
    Failed(E),
}

impl<T, E> MotiveInference<T, E> {
    pub(crate) fn decided(result: Result<T, E>) -> Self {
        match result {
            Ok(value) => Self::Accepted(value),
            Err(error) => Self::Failed(error),
        }
    }
}

/// A rollback scope for a tentative match interpretation.
///
/// Dropping the scope declines the interpretation and restores its state.
/// `commit` is the only path which preserves effects raised since the mark.
pub(crate) struct MatchRollback<'a, S: MatchSpeculationState + ?Sized> {
    state: &'a S,
    mark: S::Mark,
    committed: bool,
}

impl<'a, S: MatchSpeculationState + ?Sized> MatchRollback<'a, S> {
    pub(crate) fn new(state: &'a S) -> Self {
        Self {
            state,
            mark: state.mark_match_state(),
            committed: false,
        }
    }

    /// Restore the original mark while keeping the scope available for
    /// another candidate.
    pub(crate) fn rollback(&self) {
        self.state.rollback_match_state(self.mark);
    }

    pub(crate) fn commit(mut self) {
        self.committed = true;
    }
}

impl<S: MatchSpeculationState + ?Sized> Drop for MatchRollback<'_, S> {
    fn drop(&mut self) {
        if !self.committed {
            self.rollback();
        }
    }
}

/// The smaller dynamic scope in which an arm is being probed for a motive.
/// It is separate from [`MatchRollback`] because real lowering happens after
/// probing and may recursively contain an unrelated motive-less match.
pub(crate) struct MotiveProbe<'a, S: MatchSpeculationState + ?Sized> {
    state: &'a S,
}

impl<'a, S: MatchSpeculationState + ?Sized> MotiveProbe<'a, S> {
    pub(crate) fn begin(state: &'a S) -> Option<Self> {
        if state.motive_probe_active() {
            return None;
        }
        state.set_motive_probe_active(true);
        Some(Self { state })
    }
}

impl<S: MatchSpeculationState + ?Sized> Drop for MotiveProbe<'_, S> {
    fn drop(&mut self) {
        self.state.set_motive_probe_active(false);
    }
}

/// Replace the generic `Decide<P>` display of the parser-synthesized call in
/// an `if` with the condition the writer actually wrote. Resolution remains
/// the ordinary call path; this changes only the top-level diagnostic record.
pub(crate) fn if_resolution_error(
    form: MatchForm,
    scrutinee: &Expr,
    error: ElabError,
) -> ElabError {
    if form != MatchForm::If {
        return error;
    }
    let ExprKind::App {
        head, args, named, ..
    } = &scrutinee.kind
    else {
        return error;
    };
    if !args.is_empty() || !named.is_empty() {
        return error;
    }
    let ExprKind::TyApp { head, args } = &head.kind else {
        return error;
    };
    if !matches!(&head.kind, ExprKind::Var(name) if name == "decide" || name == "decide_bit") {
        return error;
    }
    let [condition] = args.as_slice() else {
        return error;
    };
    let display = format!("Decide<{}>", crate::traits::render_ty(condition));
    match error {
        ElabError::Resolution {
            span, mut trace, ..
        } => {
            if let Some(goal) = trace
                .iter_mut()
                .find(|line| line.depth == 0 && line.key == "goal")
            {
                goal.value.clone_from(&display);
            }
            ElabError::Resolution {
                goal: display,
                span,
                trace,
            }
        }
        other => other,
    }
}

/// Discover a constant motive for an ordinary motive-less match.
///
/// A non-binding arm may name the result type because its body lives in the
/// caller's context. Candidate failures are speculative: they leave no goals
/// or warnings and ultimately decline in favor of the written-motive
/// diagnostic. Once a candidate is found, every real arm is checked by its
/// ordinary route rather than joined here.
pub(crate) fn infer_match_constant_motive(
    elab: &(impl ConstantMotiveElab + ?Sized),
    cx: &Cx,
    form: MatchForm,
    scrutinee: &Expr,
    arms: &[Arm],
    generated: bool,
    span: Span,
) -> MotiveInference<(Term, Type, Level), ElabError> {
    infer_match_constant_motive_eq(elab, cx, form, scrutinee, arms, None, generated, span)
}

/// [`infer_match_constant_motive`], for a match that may bind its equation
/// (`match h: e { … }` in inference position, design §6): the motive is the
/// constant one and the arms are lowered as a convoy.
#[allow(clippy::too_many_arguments)]
pub(crate) fn infer_match_constant_motive_eq(
    elab: &(impl ConstantMotiveElab + ?Sized),
    cx: &Cx,
    form: MatchForm,
    scrutinee: &Expr,
    arms: &[Arm],
    eqbind: Option<&str>,
    generated: bool,
    span: Span,
) -> MotiveInference<(Term, Type, Level), ElabError> {
    // Match speculation's phase column (`docs/instrumentation-design.md` §5):
    // a motive probe elaborates the arms and rolls them back, and that work is
    // invisible in every other attribution.
    let _phase = crate::stats::guard(crate::stats::Timer::Matching);
    let Some(probe) = MotiveProbe::begin(elab) else {
        return MotiveInference::Declined;
    };
    let speculation = MatchRollback::new(elab);
    // A non-binding arm that does not infer teaches nothing. Step over it and
    // try the next candidate; each arm is elaborated at most once.
    let named = arms
        .iter()
        .filter(|arm| arm.binders.is_empty())
        .find_map(|arm| match elab.infer_motive_expr(cx, &arm.body) {
            Ok((_, ty, level)) => Some((ty, level)),
            Err(_) => {
                speculation.rollback();
                None
            }
        });
    // Any arm, in its own binder context: the match is lowered once at the
    // marker motive, and the first arm whose type lives outside its binders
    // names the motive (design §6).
    let named = named.or_else(|| {
        let found = probe_arm_type(elab, cx, form, scrutinee, arms, eqbind, generated, span);
        speculation.rollback();
        found
    });
    drop(probe);
    let Some((ty, level)) = named else {
        return MotiveInference::Declined;
    };
    let attempt: R<(Term, Type, Level)> = (|| {
        let (scrutinee_term, scrutinee_type, scrutinee_level) =
            elab.infer_motive_expr(cx, scrutinee)?;
        let term = match eqbind {
            None => elab.lower_constant_match(
                cx,
                form,
                generated,
                arms,
                scrutinee_term,
                &scrutinee_type,
                &scrutinee_level,
                ty.shift_local(1),
                level.clone(),
                span,
            )?,
            Some(h) => elab.lower_constant_convoy(
                cx,
                form,
                generated,
                h,
                arms,
                scrutinee_term,
                &scrutinee_type,
                &scrutinee_level,
                ty.shift_local(1),
                level.clone(),
                &ty,
                span,
            )?,
        };
        Ok((term, ty, level))
    })();
    match attempt {
        Ok(result) => {
            speculation.commit();
            MotiveInference::Accepted(result)
        }
        Err(_) => MotiveInference::Declined,
    }
}

/// Lower the match once at the marker motive with an [`ArmTypeProbe`] in
/// its context, and read back the first arm type that lives outside its
/// arm's binders. The lowering's result and effects are discarded by the
/// caller's rollback; a route that cannot run at the marker simply finds
/// nothing.
#[allow(clippy::too_many_arguments)]
fn probe_arm_type(
    elab: &(impl ConstantMotiveElab + ?Sized),
    cx: &Cx,
    form: MatchForm,
    scrutinee: &Expr,
    arms: &[Arm],
    eqbind: Option<&str>,
    generated: bool,
    span: Span,
) -> Option<(Type, Level)> {
    if eqbind.is_none() && arms.iter().all(|a| a.binders.is_empty()) {
        // The non-binding search above already tried every arm.
        return None;
    }
    let (scrutinee_term, scrutinee_type, scrutinee_level) =
        elab.infer_motive_expr(cx, scrutinee).ok()?;
    let sink = Rc::new(ArmTypeProbe {
        base: cx.gamma.len(),
        found: std::sync::Mutex::new(None),
    });
    let mut pcx = cx.clone();
    pcx.arm_type_probe = Some(Rc::clone(&sink));
    let marker = arm_probe_marker();
    let _ = match eqbind {
        None => elab.lower_constant_match(
            &pcx, form, generated, arms, scrutinee_term, &scrutinee_type, &scrutinee_level,
            marker, ARM_PROBE_LEVEL, span,
        ),
        Some(h) => elab.lower_constant_convoy(
            &pcx, form, generated, h, arms, scrutinee_term, &scrutinee_type, &scrutinee_level,
            marker.clone(), ARM_PROBE_LEVEL, &marker, span,
        ),
    };
    sink.found.lock().ok()?.take()
}

/// Discover a constant motive for the parser-generated `if` match.
///
/// The two evidence contexts are known from syntax, so either branch may name
/// a result type after proving syntactically that it does not depend on its
/// evidence binder. Recognizing `if` makes condition and final-lowering errors
/// authoritative; branch probes themselves remain fully speculative.
pub(crate) fn infer_if_constant_motive(
    elab: &(impl ConstantMotiveElab + ?Sized),
    cx: &Cx,
    scrutinee: &Expr,
    arms: &[Arm],
    generated: bool,
    span: Span,
) -> MotiveInference<(Term, Type, Level), ElabError> {
    // Match speculation's phase column (`docs/instrumentation-design.md` §5):
    // a motive probe elaborates the arms and rolls them back, and that work is
    // invisible in every other attribution.
    let _phase = crate::stats::guard(crate::stats::Timer::Matching);
    let ExprKind::App {
        head, args, named, ..
    } = &scrutinee.kind
    else {
        return MotiveInference::Declined;
    };
    if !args.is_empty() || !named.is_empty() {
        return MotiveInference::Declined;
    }
    let ExprKind::TyApp { head, args } = &head.kind else {
        return MotiveInference::Declined;
    };
    if !matches!(&head.kind, ExprKind::Var(name) if name == "decide") {
        return MotiveInference::Declined;
    }
    let [condition] = args.as_slice() else {
        return MotiveInference::Declined;
    };
    let (condition_type, condition_level) = match elab.lower_if_condition(cx, condition) {
        Ok(condition) => condition,
        Err(error) => return MotiveInference::Failed(error),
    };
    let negated_condition = Type::Pi {
        dom_level: condition_level.clone(),
        cod_level: Level::Zero,
        dom: Rc::new(condition_type.clone()),
        cod: Rc::new(Type::Empty { level: Level::Zero }),
    };

    let speculation = MatchRollback::new(elab);
    let mut inferred = None;
    for (arm, (evidence_type, evidence_level)) in arms.iter().zip([
        (&condition_type, &condition_level),
        (&negated_condition, &Level::Zero),
    ]) {
        let [binder] = arm.binders.as_slice() else {
            continue;
        };
        let mut arm_cx = cx.clone();
        arm_cx.push(
            binder.name().to_string(),
            evidence_type.clone(),
            evidence_level.clone(),
        );
        let Ok((_, branch_type, branch_level)) = elab.infer_motive_expr(&arm_cx, &arm.body) else {
            speculation.rollback();
            continue;
        };
        // Substitute an arbitrary disposable term for the evidence. Equality
        // with the re-weakened result is the syntactic proof that the type
        // actually lives in the caller's context.
        let branch_type0 =
            branch_type.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(Term::Zero)));
        if branch_type == branch_type0.shift_local(1) {
            inferred = Some((branch_type0, branch_level));
            break;
        }
        speculation.rollback();
    }
    let Some((ty, level)) = inferred else {
        return MotiveInference::Declined;
    };
    // Branch inference was only a type probe. Ordinary match lowering owns
    // all effects from the real pass, including those from nested matches.
    drop(speculation);
    let attempt = (|| {
        let (scrutinee_term, scrutinee_type, scrutinee_level) = elab
            .infer_motive_expr(cx, scrutinee)
            .map_err(|error| if_resolution_error(MatchForm::If, scrutinee, error))?;
        let term = elab.lower_constant_match(
            cx,
            MatchForm::If,
            generated,
            arms,
            scrutinee_term,
            &scrutinee_type,
            &scrutinee_level,
            ty.shift_local(1),
            level.clone(),
            span,
        )?;
        Ok((term, ty, level))
    })();
    MotiveInference::decided(attempt)
}

/// The mechanically convoyed motive and arms, ready for ordinary lowering.
pub(crate) struct ConvoyPlan {
    pub(crate) motive: Type,
    pub(crate) level: Level,
    pub(crate) arms: Vec<Arm>,
}

/// Decorate an ordinary motive and its arms with `scrutinee = pattern`.
pub(crate) fn plan_convoy(
    binder: &str,
    arms: &[Arm],
    scrutinee: &Term,
    scrutinee_type: &Type,
    scrutinee_level: &Level,
    motive: &Type,
    motive_level: &Level,
) -> ConvoyPlan {
    let equation = Type::Id {
        level: scrutinee_level.clone(),
        ty: Rc::new(scrutinee_type.shift_local(1)),
        lhs: Rc::new(scrutinee.shift_local(1)),
        rhs: Rc::new(Term::Var(LocalVar(0))),
    };
    let convoyed_motive = Type::Pi {
        dom_level: scrutinee_level.clone(),
        cod_level: motive_level.clone(),
        dom: Rc::new(equation),
        cod: Rc::new(motive.shift_local(1)),
    };
    let arms = arms
        .iter()
        .map(|arm| Arm {
            ctor: arm.ctor.clone(),
            default: arm.default,
            binders: arm.binders.clone(),
            body: Expr {
                kind: ExprKind::Lam {
                    binders: vec![LamBinder {
                        name: binder.to_string(),
                        ty: None,
                        implicit: false,
                        span: arm.body.span,
                    }],
                    body: Box::new(arm.body.clone()),
                },
                span: arm.body.span,
            },
            span: arm.span,
        })
        .collect();
    ConvoyPlan {
        motive: convoyed_motive,
        level: Level::max(scrutinee_level.clone(), motive_level.clone()),
        arms,
    }
}

/// Apply a convoyed eliminator to reflexivity, recovering the original type.
pub(crate) fn finish_convoy(
    eliminator: Term,
    scrutinee: Term,
    scrutinee_type: &Type,
    scrutinee_level: &Level,
    motive_level: &Level,
    result: &Type,
) -> Term {
    let scrutinee = Rc::new(scrutinee);
    let scrutinee_type = Rc::new(scrutinee_type.clone());
    crate::spelling::checked_app(
        Rc::new(eliminator),
        scrutinee_level.clone(),
        motive_level.clone(),
        Rc::new(Type::Id {
            level: scrutinee_level.clone(),
            ty: Rc::clone(&scrutinee_type),
            lhs: Rc::clone(&scrutinee),
            rhs: Rc::clone(&scrutinee),
        }),
        // The Π is non-dependent, so the result is weakened past its equation
        // binder.
        Rc::new(result.shift_local(1)),
        Rc::new(Term::Refl {
            level: scrutinee_level.clone(),
            ty: scrutinee_type,
            tm: scrutinee,
        }),
    )
}

/// Take apart a written motive lambda into its binders and type body.
pub(crate) fn motive_lam(expression: &Expr, arity: usize, advice: &str) -> R<(Vec<String>, Ty)> {
    let ExprKind::Lam { binders, body } = &expression.kind else {
        return err(format!("a motive is a lambda: {advice}"), expression.span);
    };
    if binders.len() != arity {
        return err(
            format!(
                "this motive binds {} name(s), but {arity} are needed: {advice}",
                binders.len()
            ),
            expression.span,
        );
    }
    if let Some(binder) = binders.iter().find(|binder| binder.ty.is_some()) {
        return err(
            format!(
                "a motive binder takes no annotation: `{}`'s type is fixed by what the \
                 motive is a motive for",
                binder.name
            ),
            expression.span,
        );
    }
    let names = binders.iter().map(|binder| binder.name.clone()).collect();
    let ty = crate::surface::expression_as_type(body).unwrap_or_else(|| Ty {
        kind: TyKind::OfExpr(body.clone()),
        span: body.span,
    });
    Ok((names, ty))
}

/// Synthesize a dependent motive for a motive-less match in checking mode.
pub(crate) fn synthesize_motive(
    elab: &impl MotiveSynthesisElab,
    cx: &Cx,
    scrutinee: &Term,
    scrutinee_type: &Type,
    scrutinee_level: &Level,
    expected: &Type,
    span: Span,
) -> Type {
    // Match speculation's phase column (`docs/instrumentation-design.md` §5):
    // a motive probe elaborates the arms and rolls them back, and that work is
    // invisible in every other attribution.
    let _phase = crate::stats::guard(crate::stats::Timer::Matching);
    let indexed = elab.generalizes_an_index(cx, scrutinee_type);
    let rewrap = field_rewrap(cx, scrutinee, indexed);
    if let Some(motive) = abstract_scrut(expected, scrutinee, &rewrap) {
        return motive;
    }
    let Some(exposed) = expose(elab, cx, expected, span) else {
        return expected.shift_local(1);
    };
    if let Some(motive) = abstract_stuck(
        elab,
        cx,
        &exposed,
        scrutinee,
        scrutinee_type,
        scrutinee_level,
    ) {
        return motive;
    }
    if let Some(motive) = abstract_scrut(&exposed, scrutinee, &rewrap) {
        return motive;
    }
    if let Some(motive) = abstract_below(elab, cx, expected, scrutinee, scrutinee_type, scrutinee_level, span) {
        return motive;
    }
    expected.shift_local(1)
}

/// How many type formers the last rung reads below: `Π w. (P → Q) × (Q → P)`
/// over stuck `P`, `Q` is four.
const BELOW_DEPTH: u32 = 6;

/// The last rung (`docs/goal-motive-synthesis-design.md` §4.5): the goal
/// read below its binders. A goal that is a relation or an `↔` over a call
/// (`alt(a, b) ≈ Alt(a, b)`) is, reduced, a `Π` or `Σ` whose stuck positions
/// sit in codomains and components, where §4.3's one layer does not look.
/// Each former is reduced in its own context, the positions it is stuck on
/// are brought back to `Γ` (one that mentions a binder it sits under is no
/// candidate), and those that convert to the scrutinee are abstracted in the
/// reduced goal. Reached only where every other rung found nothing, so no
/// motive they find changes.
fn abstract_below(
    elab: &impl MotiveSynthesisElab,
    cx: &Cx,
    expected: &Type,
    scrutinee: &Term,
    scrutinee_type: &Type,
    scrutinee_level: &Level,
    span: Span,
) -> Option<Type> {
    let mut candidates = Vec::new();
    let mut budget = STUCK_CANDIDATES;
    let below = expose_below(elab, cx, expected, span, BELOW_DEPTH, 0, &mut candidates, &mut budget);
    candidates.dedup();
    let hits: Vec<Term> = candidates
        .into_iter()
        .filter(|candidate| {
            candidate == scrutinee
                || elab.motive_candidate_converts(cx, candidate, scrutinee, scrutinee_type, scrutinee_level)
        })
        .collect();
    if hits.is_empty() {
        return None;
    }
    below.abstract_local_any(&hits)
}

/// `ty` with its term positions reduced, below `Π` codomains and `Σ`
/// components to `depth` formers; `under` counts the binders passed, and a
/// stuck position found below them is recorded as it reads in the outer
/// context. A position that does not reduce is left as written.
#[allow(clippy::too_many_arguments)]
fn expose_below(
    elab: &impl MotiveSynthesisElab,
    cx: &Cx,
    ty: &Type,
    span: Span,
    depth: u32,
    under: u32,
    out: &mut Vec<Term>,
    budget: &mut u32,
) -> Type {
    let Some(head) = elab.read_motive_type(cx, ty, span) else {
        return ty.clone();
    };
    let mut note = |term: &Term, budget: &mut u32| {
        let mut found = Vec::new();
        stuck_scrutinees(term, &mut found, budget);
        for candidate in found {
            if let Some(outer) = crate::unification::strengthen_tm(&cx.gamma, &candidate, under) {
                out.push(outer);
            }
        }
    };
    match head {
        Type::Id { level, ty, lhs, rhs } => {
            let lhs = elab.read_motive_term(cx, &lhs, span).unwrap_or(lhs);
            let rhs = elab.read_motive_term(cx, &rhs, span).unwrap_or(rhs);
            note(&lhs, budget);
            note(&rhs, budget);
            Type::Id { level, ty, lhs, rhs }
        }
        Type::El { level, tm } => {
            let tm = elab.read_motive_term(cx, &tm, span).unwrap_or(tm);
            note(&tm, budget);
            Type::El { level, tm }
        }
        Type::Pi { dom_level, cod_level, dom, cod } if depth > 0 => {
            let mut inner = cx.clone();
            inner.push(format!("__below_{under}"), (*dom).clone(), dom_level.clone());
            let new_dom = expose_below(elab, cx, &dom, span, depth - 1, under, out, budget);
            let new_cod = expose_below(elab, &inner, &cod, span, depth - 1, under + 1, out, budget);
            Type::Pi { dom_level, cod_level, dom: Rc::new(new_dom), cod: Rc::new(new_cod) }
        }
        Type::Sigma { fst_level, snd_level, fst, snd } if depth > 0 => {
            let mut inner = cx.clone();
            inner.push(format!("__below_{under}"), (*fst).clone(), fst_level.clone());
            let new_fst = expose_below(elab, cx, &fst, span, depth - 1, under, out, budget);
            let new_snd = expose_below(elab, &inner, &snd, span, depth - 1, under + 1, out, budget);
            Type::Sigma { fst_level, snd_level, fst: Rc::new(new_fst), snd: Rc::new(new_snd) }
        }
        head => head,
    }
}

fn abstract_stuck(
    elab: &impl MotiveSynthesisElab,
    cx: &Cx,
    exposed: &Type,
    scrutinee: &Term,
    scrutinee_type: &Type,
    scrutinee_level: &Level,
) -> Option<Type> {
    let mut candidates = Vec::new();
    let mut budget = STUCK_CANDIDATES;
    stuck_in_type(exposed, &mut candidates, &mut budget);
    candidates.dedup();
    let hits: Vec<Term> = candidates
        .into_iter()
        .filter(|candidate| {
            candidate == scrutinee
                || elab.motive_candidate_converts(
                    cx,
                    candidate,
                    scrutinee,
                    scrutinee_type,
                    scrutinee_level,
                )
        })
        .collect();
    exposed.abstract_local_any(&hits)
}

pub(crate) fn expose(elab: &impl MotiveSynthesisElab, cx: &Cx, ty: &Type, span: Span) -> Option<Type> {
    match elab.read_motive_type(cx, ty, span)? {
        Type::Id {
            level,
            ty,
            lhs,
            rhs,
        } => Some(Type::Id {
            level,
            ty,
            lhs: elab.read_motive_term(cx, &lhs, span)?,
            rhs: elab.read_motive_term(cx, &rhs, span)?,
        }),
        Type::El { level, tm } => Some(Type::El {
            level,
            tm: elab.read_motive_term(cx, &tm, span)?,
        }),
        Type::Pi {
            dom_level,
            cod_level,
            dom,
            cod,
        } => Some(Type::Pi {
            dom_level,
            cod_level,
            dom: Rc::new(expose(elab, cx, &dom, span)?),
            cod,
        }),
        head => Some(head),
    }
}

fn stuck_in_type(ty: &Type, out: &mut Vec<Term>, budget: &mut u32) {
    match ty {
        Type::Id { lhs, rhs, .. } => {
            stuck_scrutinees(lhs, out, budget);
            stuck_scrutinees(rhs, out, budget);
        }
        Type::El { tm, .. } => stuck_scrutinees(tm, out, budget),
        Type::Pi { dom, .. } => stuck_in_type(dom, out, budget),
        _ => {}
    }
}

fn stuck_scrutinees(term: &Term, out: &mut Vec<Term>, budget: &mut u32) {
    if *budget == 0 {
        return;
    }
    *budget -= 1;
    let scrutinee = match term {
        Term::ElimNat { scrut, .. }
        | Term::ElimEmpty { scrut, .. }
        | Term::ElimSEmpty { scrut, .. }
        | Term::Case { scrut, .. }
        | Term::ElimW { scrut, .. }
        | Term::ElimWf { scrut, .. } => Some(scrut),
        Term::Fst { pair, .. }
        | Term::Snd { pair, .. }
        | Term::FstAt { pair, .. }
        | Term::SndAt { pair, .. } => Some(pair),
        Term::J { proof, .. } => Some(proof),
        _ => None,
    };
    if let Some(scrutinee) = scrutinee {
        out.push((**scrutinee).clone());
        stuck_scrutinees(scrutinee, out, budget);
        return;
    }
    match term {
        Term::Succ(term) => stuck_scrutinees(term, out, budget),
        Term::Inl { val, .. }
        | Term::Inr { val, .. }
        | Term::InlAt { val, .. }
        | Term::InrAt { val, .. } => {
            stuck_scrutinees(val, out, budget);
        }
        Term::Pair { fst, snd, .. } | Term::PairAt { fst, snd, .. } => {
            stuck_scrutinees(fst, out, budget);
            stuck_scrutinees(snd, out, budget);
        }
        Term::Sup {
            label, children, ..
        }
        | Term::Supf {
            label, children, ..
        } => {
            stuck_scrutinees(label, out, budget);
            stuck_scrutinees(children, out, budget);
        }
        Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => {
            stuck_scrutinees(fun, out, budget);
            stuck_scrutinees(arg, out, budget);
        }
        _ => {}
    }
}

fn abstract_scrut(goal: &Type, scrutinee: &Term, rewrap: &Rewrap) -> Option<Type> {
    match rewrap {
        // A child read and the constructor value it reads from are two
        // spellings of one value, so both are abstracted under the one `z`: a
        // goal that names the child and the value together is specialized at
        // both, never half (`docs/goal-motive-synthesis-design.md` §4.4).
        Rewrap::Child(bases) => {
            let mut pats = vec![(scrutinee.clone(), Term::Var(LocalVar(0)))];
            pats.extend(bases.iter().cloned());
            goal.abstract_local_with_all(&pats)
        }
        Rewrap::Field(base, replacement) => goal
            .abstract_local(scrutinee)
            .or_else(|| goal.abstract_local_with(base, replacement)),
        Rewrap::None => goal.abstract_local(scrutinee),
    }
}

/// What a goal mentions in place of the scrutinee, rebuilt around `z`
/// (`docs/goal-motive-synthesis-design.md` §5).
#[derive(Debug)]
enum Rewrap {
    None,
    /// A tier-0 field: the value it projects from, rebuilt as a pair around
    /// `z`. Tried only when the scrutinee itself does not occur.
    Field(Term, Term),
    /// A recursive binder of a `Wf` or `W` arm, which is a read out of the
    /// arm's children and not a subterm of the goal's constructor value: each
    /// local the read is built from, rebuilt around `z`. Abstracted together
    /// with the scrutinee (docs/dependent-match-compiler-design.md §7.1).
    Child(Vec<(Term, Term)>),
}

/// A `Wf` arm's recursive binder: `nth^l(⟦D⟧; Succ^m(base); cs; ι_t)` over a
/// children tuple `cs` that is a local (docs/inductive-tier1-wf-lowering.md
/// §6.3). Recognized by rebuilding the schema and comparing, so nothing that
/// merely resembles it is taken apart. Returns the level, the element type,
/// the length, `cs` and `t`.
pub(crate) fn child_read(term: &Term) -> Option<(Level, Rc<Type>, Rc<Term>, Rc<Term>, usize)> {
    let Term::App { fun, arg: idx, .. } = term else { return None };
    let Term::App { fun: recursion, dom, arg: cs, .. } = &**fun else { return None };
    let Term::ElimNat { .. } = &**recursion else { return None };
    let Type::Vec { level, elem, len } = &**dom else { return None };
    if !matches!(&**cs, Term::Var(_)) {
        return None;
    }
    let mut t = 0;
    let mut at = &**idx;
    loop {
        match at {
            Term::Inr { val, .. } => {
                t += 1;
                at = val;
            }
            Term::Inl { .. } => break,
            _ => return None,
        }
    }
    let mut rest = &**len;
    for _ in 0..=t {
        let Term::Succ(k) = rest else { return None };
        rest = k;
    }
    let rebuilt = heather_kernel::term::nth(level, elem, len, Rc::clone(cs), Rc::clone(idx));
    (rebuilt == *term).then(|| (level.clone(), Rc::clone(elem), Rc::clone(len), Rc::clone(cs), t))
}

/// The children tuple `cs` rebuilt around `z` at position `t`, scoped in
/// `Γ, z`: `⟨fst cs, ⟨fst (snd cs), … ⟨z, snd^{t+1} cs⟩⟩⟩`. At `z := nth(cs;
/// ι_t)` it is `cs` again by `nth`'s reduction at a `Succ`-headed length and
/// Σ-η, which is the whole reason a `Wf` child needs no transport: the
/// children are a tuple, not a function, so no η at a function space is
/// asked for (contrast tier 2's leaf, docs/inductive-tier2-w-lowering.md
/// §2.1).
fn child_rewrap(term: &Term) -> Option<(Term, Term)> {
    let (level, elem, len, cs, t) = child_read(term)?;
    fn rebuild(level: &Level, elem: &Type, len: &Term, cs: Term, t: usize) -> Term {
        let Term::Succ(k) = len else { unreachable!("child_read checked t + 1 successors") };
        let fst_ty = Rc::new(elem.clone());
        let snd_ty = Rc::new(Type::Vec {
            level: level.clone(),
            elem: Rc::new(elem.shift_local(1)),
            len: Rc::new(k.shift_local(1)),
        });
        let proj = |snd: bool, pair: &Term| {
            let (fst_level, snd_level) = (level.clone(), level.clone());
            let (fst_ty, snd_ty, pair) = (Rc::clone(&fst_ty), Rc::clone(&snd_ty), Rc::new(pair.clone()));
            if snd {
                Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair }
            } else {
                Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair }
            }
        };
        let (fst, snd) = if t == 0 {
            (Term::Var(LocalVar(0)), proj(true, &cs))
        } else {
            (proj(false, &cs), rebuild(level, elem, k, proj(true, &cs), t - 1))
        };
        Term::Pair {
            fst_level: level.clone(),
            snd_level: level.clone(),
            fst_ty,
            snd_ty,
            fst: Rc::new(fst),
            snd: Rc::new(snd),
        }
    }
    let base = (*cs).clone();
    let tuple = rebuild(&level, &elem.shift_local(1), &len.shift_local(1), cs.shift_local(1), t);
    Some((base, tuple))
}

/// A `W` arm's plain recursive binder, `t := ⟨f' ⟨⟩, c⟩`
/// (docs/inductive-tier2-w-lowering.md §7): the children function `f'` and
/// the leaf-predicate proof `c` are locals, and the goal spells the value as
/// `⟨sup(ℓ; f'), c⟩`. Rebuilt around `z` as `f' := λ(y : P ℓ). fst z` and `c :=
/// snd z`. At `z := t` the first is `f'` again by Π-η and `Unit`-η (the
/// positions of a plain child are `Unit`, §2.3) and the second by Σ-β, and
/// `snd z : El(canon(fst z))` is the proof the rebuilt tree needs, since
/// `canon(sup(ℓ; λy. fst z))` takes its plain branch to `canon(fst z)`. No
/// leaf is involved, so no η at an `Empty` domain is asked for (§2.1): a
/// leaf has no recursive binder to match on.
fn w_child_rewrap(cx: &Cx, term: &Term) -> Option<Vec<(Term, Term)>> {
    let Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } = term else { return None };
    if !matches!(&**fst_ty, Type::W { .. }) {
        return None;
    }
    let (Term::AppAt { fun, arg } | Term::App { fun, arg, .. }) = &**fst else { return None };
    let (Term::Var(f), Term::Var(c)) = (&**fun, &**snd) else { return None };
    if !matches!(&**arg, Term::Triv { .. }) {
        return None;
    }
    let f_ty = cx.gamma.entries.nth_inner(f.0)?.ty.shift_local(f.0 + 1);
    let Type::Pi { dom_level, cod_level, dom, .. } = f_ty else { return None };
    let proj = |second: bool, by: u32| {
        let (fst_level, snd_level) = (fst_level.clone(), snd_level.clone());
        let (fst_ty, snd_ty) = (Rc::new(fst_ty.shift_local(by)), Rc::new(snd_ty.shift_local_above(by, 1)));
        let pair = Rc::new(Term::Var(LocalVar(by - 1)));
        if second {
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair }
        } else {
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair }
        }
    };
    let children = Term::Lam {
        dom_level,
        cod_level,
        dom: Rc::new(dom.shift_local(1)),
        body: Rc::new(proj(false, 2)),
    };
    Some(vec![(Term::Var(*f), children), (Term::Var(*c), proj(true, 1))])
}

fn field_rewrap(cx: &Cx, scrutinee: &Term, indexed: bool) -> Rewrap {
    if let Some((base, tuple)) = child_rewrap(scrutinee) {
        return Rewrap::Child(vec![(base, tuple)]);
    }
    if let Some(bases) = w_child_rewrap(cx, scrutinee) {
        return Rewrap::Child(bases);
    }
    match tier0_field_rewrap(cx, scrutinee, indexed) {
        Some((base, replacement)) => Rewrap::Field(base, replacement),
        None => Rewrap::None,
    }
}

/// [`tier0_field_rewrap`]'s rebuild in the unannotated spelling, from an
/// annotated projection chain `fst(sndⁿ(x))` on a local `x`: `⟨fst x, …
/// ⟨z, sndⁿ⁺¹ x⟩⟩` with `pair@`/`fst@`/`snd@`, the root annotated with `x`'s
/// own type.
fn unannotated_field_rewrap(cx: &Cx, scrutinee: &Term) -> Option<(Term, Term)> {
    let Term::Fst { pair, .. } = scrutinee else { return None };
    let mut depth = 0u32;
    let mut base = Rc::clone(pair);
    while let Term::Snd { pair, .. } = &*base {
        depth += 1;
        base = Rc::clone(pair);
    }
    let Term::Var(x) = &*base else { return None };
    let root_ty = cx.gamma.entries.nth_inner(x.0)?.ty.shift_local(x.0 + 2);
    let x1 = Term::Var(LocalVar(x.0 + 1));
    let snds = |n: u32| {
        let mut t = x1.clone();
        for _ in 0..n {
            t = Term::SndAt { pair: Rc::new(t) };
        }
        t
    };
    let mut replacement = Term::PairAt {
        ty: None,
        fst: Rc::new(Term::Var(LocalVar(0))),
        snd: Rc::new(Term::SndAt { pair: Rc::new(snds(depth)) }),
    };
    for k in (0..depth).rev() {
        replacement = Term::PairAt {
            ty: None,
            fst: Rc::new(Term::FstAt { pair: Rc::new(snds(k)) }),
            snd: Rc::new(replacement),
        };
    }
    if let Term::PairAt { ty, .. } = &mut replacement {
        *ty = Some(Rc::new(root_ty));
    }
    Some(((*base).clone(), replacement))
}

fn tier0_field_rewrap(cx: &Cx, scrutinee: &Term, indexed: bool) -> Option<(Term, Term)> {
    // A field of an indexed family's value, at an index the route is about to
    // generalize. The annotated rebuild would carry the value's own index in
    // every projection's annotation, and generalizing the index rewrites
    // those too, so `fst x` would claim a type at the new index while `x`
    // keeps the old one: a kernel refusal behind an accepted arm
    // (issues/indexed-deep-pattern-kernel-rejects.md). The unannotated
    // spelling has the index only in the root's annotation, which is the one
    // place it should move.
    if indexed && let Some(rewrap) = unannotated_field_rewrap(cx, scrutinee) {
        return Some(rewrap);
    }
    // The checked spelling's η-expansion is the same shape with **no**
    // annotation below the root (`docs/intro-by-type-design.md` §4.2): every
    // inner `pair@` is a field of the one above it, so it is in checking
    // position. The root replaces `base` wherever the goal mentions it,
    // including as the receiver of a projection, so it must infer — and the
    // only type it can carry without spelling a reduct is `base`'s own. That
    // is at hand for a local, which is the scrutinee a field match has; any
    // other root declines and the synthesis falls to its later strategies. A
    // chain is homogeneous — one `projection` call writes one spelling all
    // the way down — so the two loops do not have to interleave.
    if let Term::FstAt { pair } = scrutinee {
        let mut base = Rc::clone(pair);
        let mut replacement = Term::PairAt {
            ty: None,
            fst: Rc::new(Term::Var(LocalVar(0))),
            snd: Rc::new(Term::SndAt { pair: Rc::new(pair.shift_local(1)) }),
        };
        while let Term::SndAt { pair } = &*base {
            replacement = Term::PairAt {
                ty: None,
                fst: Rc::new(Term::FstAt { pair: Rc::new(pair.shift_local(1)) }),
                snd: Rc::new(replacement),
            };
            base = Rc::clone(pair);
        }
        let Term::Var(x) = &*base else { return None };
        let root_ty = cx.gamma.entries.nth_inner(x.0)?.ty.shift_local(x.0 + 2);
        if let Term::PairAt { ty, .. } = &mut replacement {
            *ty = Some(Rc::new(root_ty));
        }
        return Some(((*base).clone(), replacement));
    }
    let Term::Fst {
        fst_level,
        snd_level,
        fst_ty,
        snd_ty,
        pair,
    } = scrutinee
    else {
        return None;
    };
    let mut base = Rc::clone(pair);
    let mut replacement = Term::Pair {
        fst_level: fst_level.clone(),
        snd_level: snd_level.clone(),
        fst_ty: Rc::new(fst_ty.shift_local(1)),
        snd_ty: Rc::new(snd_ty.shift_local(1)),
        fst: Rc::new(Term::Var(LocalVar(0))),
        snd: Rc::new(Term::Snd {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: Rc::new(fst_ty.shift_local(1)),
            snd_ty: Rc::new(snd_ty.shift_local(1)),
            pair: Rc::new(pair.shift_local(1)),
        }),
    };
    while let Term::Snd {
        fst_level,
        snd_level,
        fst_ty,
        snd_ty,
        pair,
    } = &*base
    {
        let (fst_ty, snd_ty) = (
            Rc::new(fst_ty.shift_local(1)),
            Rc::new(snd_ty.shift_local(1)),
        );
        replacement = Term::Pair {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst_ty: Rc::clone(&fst_ty),
            snd_ty: Rc::clone(&snd_ty),
            fst: Rc::new(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty,
                snd_ty,
                pair: Rc::new(pair.shift_local(1)),
            }),
            snd: Rc::new(replacement),
        };
        base = Rc::clone(pair);
    }
    Some(((*base).clone(), replacement))
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use heather_syntax::Pat;

    use super::*;

    const SPAN: Span = Span { start: 0, end: 1 };

    struct Fake;

    impl MotiveSynthesisElab for Fake {
        fn read_motive_type(&self, _cx: &Cx, ty: &Type, _span: Span) -> Option<Type> {
            Some(ty.clone())
        }

        fn read_motive_term(&self, _cx: &Cx, term: &Term, _span: Span) -> Option<Rc<Term>> {
            Some(Rc::new(term.clone()))
        }

        fn motive_candidate_converts(
            &self,
            _cx: &Cx,
            candidate: &Term,
            scrutinee: &Term,
            _scrutinee_type: &Type,
            _scrutinee_level: &Level,
        ) -> bool {
            candidate == scrutinee
        }
    }

    #[derive(Default)]
    struct FakeSpeculation {
        warnings: Cell<usize>,
        goals: Cell<usize>,
        mismatch_evidence: Cell<usize>,
        probing: Cell<bool>,
        fail_lowering: Cell<bool>,
    }

    impl MatchSpeculationState for FakeSpeculation {
        type Mark = (usize, usize);

        fn mark_match_state(&self) -> Self::Mark {
            (self.warnings.get(), self.goals.get())
        }

        fn rollback_match_state(&self, mark: Self::Mark) {
            self.warnings.set(mark.0);
            self.goals.set(mark.1);
        }

        fn motive_probe_active(&self) -> bool {
            self.probing.get()
        }

        fn set_motive_probe_active(&self, active: bool) {
            self.probing.set(active);
        }
    }

    impl ConstantMotiveElab for FakeSpeculation {
        fn infer_motive_expr(&self, _cx: &Cx, _expr: &Expr) -> R<(Term, Type, Level)> {
            self.goals.set(self.goals.get() + 1);
            Ok((Term::Zero, Type::Nat, Level::Zero))
        }

        fn lower_if_condition(&self, _cx: &Cx, _condition: &Ty) -> R<(Type, Level)> {
            Ok((Type::Nat, Level::Zero))
        }

        fn lower_constant_match(
            &self,
            _cx: &Cx,
            _form: MatchForm,
            _generated: bool,
            _arms: &[Arm],
            _scrutinee: Term,
            _scrutinee_type: &Type,
            _scrutinee_level: &Level,
            _motive: Type,
            _motive_level: Level,
            _span: Span,
        ) -> R<Term> {
            self.warnings.set(self.warnings.get() + 1);
            if self.fail_lowering.get() {
                err("lowering failed", SPAN)
            } else {
                Ok(Term::Zero)
            }
        }
    }

    #[test]
    fn match_rollback_discards_or_commits_all_owned_channels() {
        let state = FakeSpeculation::default();
        state.warnings.set(2);
        state.goals.set(3);
        {
            let attempt = MatchRollback::new(&state);
            state.warnings.set(5);
            state.goals.set(8);
            state.mismatch_evidence.set(1);
            attempt.rollback();
            assert_eq!((state.warnings.get(), state.goals.get()), (2, 3));
            assert_eq!(state.mismatch_evidence.get(), 1);
            state.warnings.set(7);
            state.goals.set(11);
        }
        assert_eq!((state.warnings.get(), state.goals.get()), (2, 3));
        assert_eq!(state.mismatch_evidence.get(), 1);

        let attempt = MatchRollback::new(&state);
        state.warnings.set(13);
        state.goals.set(17);
        attempt.commit();
        assert_eq!((state.warnings.get(), state.goals.get()), (13, 17));
    }

    #[test]
    fn motive_probe_refuses_nesting_and_always_reopens_its_scope() {
        let state = FakeSpeculation::default();
        let probe = MotiveProbe::begin(&state).expect("outer probe");
        assert!(MotiveProbe::begin(&state).is_none());
        drop(probe);
        assert!(!state.probing.get());
        assert!(MotiveProbe::begin(&state).is_some());
    }

    #[test]
    fn constant_match_discovery_commits_only_an_accepted_candidate() {
        let arm = Arm {
            ctor: "Zero".into(),
            default: false,
            binders: Vec::new(),
            body: Expr {
                kind: ExprKind::Num(0u64.into()),
                span: SPAN,
            },
            span: SPAN,
        };
        let scrutinee = Expr {
            kind: ExprKind::Num(0u64.into()),
            span: SPAN,
        };

        let accepted = FakeSpeculation::default();
        assert!(matches!(
            infer_match_constant_motive(
                &accepted,
                &Cx::empty(),
                MatchForm::Match,
                &scrutinee,
                std::slice::from_ref(&arm),
                false,
                SPAN,
            ),
            MotiveInference::Accepted(_)
        ));
        assert_eq!((accepted.goals.get(), accepted.warnings.get()), (2, 1));
        assert!(!accepted.probing.get());

        let declined = FakeSpeculation::default();
        declined.goals.set(3);
        declined.warnings.set(5);
        declined.fail_lowering.set(true);
        assert!(matches!(
            infer_match_constant_motive(
                &declined,
                &Cx::empty(),
                MatchForm::Match,
                &scrutinee,
                std::slice::from_ref(&arm),
                false,
                SPAN,
            ),
            MotiveInference::Declined
        ));
        assert_eq!((declined.goals.get(), declined.warnings.get()), (3, 5));
        assert!(!declined.probing.get());
    }

    #[test]
    fn recognized_if_lowering_failures_are_authoritative() {
        let decide = Expr {
            kind: ExprKind::App {
                head: Box::new(Expr {
                    kind: ExprKind::TyApp {
                        head: Box::new(Expr {
                            kind: ExprKind::Var("decide".into()),
                            span: SPAN,
                        }),
                        args: vec![Ty {
                            kind: TyKind::Nat,
                            span: SPAN,
                        }],
                    },
                    span: SPAN,
                }),
                args: Vec::new(),
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span: SPAN,
        };
        let arm = Arm {
            ctor: "Left".into(),
            default: false,
            binders: vec![Pat::Var {
                name: "evidence".into(),
                span: SPAN,
            }],
            body: Expr {
                kind: ExprKind::Num(0u64.into()),
                span: SPAN,
            },
            span: SPAN,
        };
        let state = FakeSpeculation::default();
        state.fail_lowering.set(true);
        assert!(matches!(
            infer_if_constant_motive(
                &state,
                &Cx::empty(),
                &decide,
                std::slice::from_ref(&arm),
                true,
                SPAN,
            ),
            MotiveInference::Failed(_)
        ));
    }

    #[test]
    fn motive_synthesis_abstracts_or_weakens_without_an_elaborator() {
        let scrutinee = Term::Var(LocalVar(0));
        let expected = Type::Id {
            level: Level::Zero,
            ty: Rc::new(Type::Nat),
            lhs: Rc::new(scrutinee.clone()),
            rhs: Rc::new(Term::Zero),
        };
        let motive = synthesize_motive(
            &Fake,
            &Cx::empty(),
            &scrutinee,
            &Type::Nat,
            &Level::Zero,
            &expected,
            SPAN,
        );
        assert_ne!(motive, expected.shift_local(1));

        let constant = Type::Nat;
        assert_eq!(
            synthesize_motive(
                &Fake,
                &Cx::empty(),
                &scrutinee,
                &Type::Nat,
                &Level::Zero,
                &constant,
                SPAN,
            ),
            constant.shift_local(1)
        );
    }

    #[test]
    fn convoy_planning_is_a_pure_match_transformation() {
        let arm = Arm {
            ctor: "Zero".into(),
            default: false,
            binders: Vec::new(),
            body: Expr {
                kind: ExprKind::Num(0u64.into()),
                span: SPAN,
            },
            span: SPAN,
        };
        let plan = plan_convoy(
            "equation",
            &[arm],
            &Term::Zero,
            &Type::Nat,
            &Level::Zero,
            &Type::Nat,
            &Level::Zero,
        );
        assert!(matches!(plan.motive, Type::Pi { dom, .. } if matches!(&*dom, Type::Id { .. })));
        assert!(matches!(
            &plan.arms[0].body.kind,
            ExprKind::Lam { binders, .. } if binders[0].name == "equation"
        ));

        let finished = finish_convoy(
            Term::Zero,
            Term::Zero,
            &Type::Nat,
            &Level::Zero,
            &Level::Zero,
            &Type::Nat,
        );
        assert!(matches!(
            crate::spelling::app_of(&finished),
            Some((_, arg)) if matches!(&**arg, Term::Refl { .. })
        ));
    }
}
