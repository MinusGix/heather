//! Checking's part of the elaborator: a written expression against an expected type.

use heather_kernel::conv::ConvError;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{LocalSubst, Term, Type};

use heather_syntax::{Expr, ExprKind, Span, Ty, TyKind};

use crate::{
    DotResolution, Elaborator, R, application, binding, bv_omega, constructor, defaults, err,
    expected_universe, expr, generalize, goal_combinators, goals, host, inductive, matching, omega_cert,
    recursion, relational_context, statements, stats,
};
use crate::app_unify::AppUnify;
use crate::application::{Skel, skel_params};
use crate::binding::Bindings;
use crate::codata::{Codata, UpTo};
use crate::constructor::Constructors;
use crate::context::{Alias, Cx};
use crate::declarations::Declarations;
use crate::defaults::Defaults;
use crate::diagnostics::{ElabError, LintFix};
use crate::dispatch::{Members, Operators};
use crate::gendefs::GeneratedDefs;
use crate::generalize::Generalize;
use crate::host::Host;
use crate::inductive::Inductives;
use crate::inference::Inference;
use crate::linarith::Linarith;
use crate::lint::Lint;
use crate::literals::Literals;
use crate::matching::Routes;
use crate::mismatch_notes::MismatchNotes;
use crate::name_lookup::NameLookup;
use crate::quote::Quotation;
use crate::refusals::Refusals;
use crate::registered::Registered;
use crate::resolve::Resolution;
use crate::rewrite::Rewrites;
use crate::ring::Ring;
use crate::subst_local::LocalSubsts;
use crate::surface::{
    expression_as_type, for_each_free_slot, has_free_slots, lower_argument_slots, slot_profile,
};

/// Checking's part of the elaborator: a written expression against an expected type.
pub(crate) struct Checking<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Checking<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Checking<'_> {
    /// [`Elaborator::elab_check`] plus, where the caller knows it, the `(callee,
    /// parameter)` this expression is an argument for — the provenance and
    /// default name of any goal raised inside it.
    pub(crate) fn elab_check_hinted(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
        lvl: &Level,
        hint: Option<(&str, &str)>,
    ) -> R<Term> {
        self.elab_check_skel(cx, e, expected, lvl, hint, None)
    }

    /// A proof of `P` given where a condition `∥P∥` is expected
    /// (docs/language/strict-conditions-design.md §3): its term, checked at `P`, for
    /// the caller to wrap in `squash`; `None` where `e` is to check as
    /// written, because it is already a `∥P∥` or a `squash(…)`.
    ///
    /// A search, a tactic, `refl` or a hole runs at `P`, since none of them
    /// proves a squash. Anything else is inferred in a probe and wrapped
    /// only when it infers and what it proves is not itself a squash, so a
    /// condition passed on (`inside := inside`) stays as it is.
    fn check_condition_squashed(&self, cx: &Cx, e: &Expr, prop: &Rc<Type>, level: &Level) -> R<Option<Term>> {
        if let ExprKind::App { head, .. } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "squash")
        {
            return Ok(None);
        }
        let search = matches!(&e.kind, ExprKind::Hole(_))
            || (crate::surface::count_holes_expr(e) == 0 && crate::defaults::is_discharge(e));
        if !search {
            let squashed = self.probe(|| match self.elab_infer(cx, e) {
                Ok((_, got, _)) => self.whnf(cx, &got, e.span).ok().map(|w| matches!(w, Type::Squash { .. })),
                Err(_) => None,
            });
            if squashed != Some(false) {
                return Ok(None);
            }
        }
        self.elab_check(cx, e, prop, level).map(Some)
    }

    /// [`Self::elab_check_hinted`] plus, where the caller has one, the
    /// expected type's implicitness *skeleton*
    /// (docs/language/implicit-binders-design.md §6.1). Three caller classes supply
    /// it: argument checking in `apply_explicit`/`apply_implicit` (the
    /// callee parameter's own skeleton), an annotated `let`, and
    /// record-literal field checking. It is read by exactly two arms — a
    /// lambda (the §6.2 coherence rule) and the bare-reference suppression
    /// in the inference fallback (§5.3); everything else ignores it.
    pub(crate) fn elab_check_skel(
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
    pub(crate) fn elab_check_skel_slots(
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
                .map_err(|error| Bindings(self).restate_bind_error(cx, input, discards, error));
        }
        if binding::generated_loop(e) {
            return self
                .elab_check_skel_slots_written(cx, e, expected, lvl, hint, skel, capture_slots)
                .map_err(|error| Bindings(self).restate_loop_error(cx, e, Some(expected), error));
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
        Inference(self).refuse_value_call(cx, e)?;
        // `name_of(p)` and `registered(T)` (docs/metaprogramming/registered-values-design.md).
        if let Some(rewritten) = Registered(self).registry_rewrite(cx, e)? {
            return self.elab_check_skel_slots_written(cx, &rewritten, expected, lvl, hint, skel, capture_slots);
        }
        // A proof-taking call where a `When` is wanted, or a `match` on one
        // (docs/language/when-design.md §4).
        if let Some((bound, tested)) = crate::tested::Tested(self).tested_check(cx, e, expected)? {
            return self.elab_check_skel_slots_written(&bound, &tested, expected, lvl, hint, skel, capture_slots);
        }
        // A corecursive body's two positions, a node and a child
        // (docs/inductives/codata-elaborator-design.md §5.2).
        if let Some(site) = cx.corec.as_ref()
            && let Some(t) = Codata(self).corec_check(cx, site, e, expected, lvl)?
        {
            return Ok(t);
        }
        // A friend's body over a corecursive definition's free carrier
        // (docs/inductives/codata-elaborator-design.md §5.5).
        if let Some(mode) = cx.friend.as_ref()
            && let Some(t) = UpTo(self).friend_check(cx, mode, e, expected, lvl)?
        {
            return Ok(t);
        }
        if let Some(quoted) = Host(self).quote_for_by(cx, e, expected, lvl)? {
            return Ok(quoted);
        }
        // A call made only of facts about a scrutinee is taken as written
        // if it checks as written (docs/language/matching/arm-readings-design.md §3.4).
        if let Some(written) = crate::readings::Readings(self).as_written(cx, e, Some((expected, lvl))) {
            return self.elab_check_skel_slots_written(&written, e, expected, lvl, hint, skel, capture_slots);
        }
        // A name an enclosing match gave two readings is the one this
        // position asks for (docs/language/matching/arm-readings-design.md).
        if let ExprKind::Var(name) = &e.kind
            && cx.readings.iter_inner().any(|r| &r.name == name)
            && let Ok((t, got, _)) = self.probe(|| self.elab_infer(cx, e))
            && let Some((t, _)) = crate::readings::Readings(self).reread(cx, &t, &got, expected, lvl)
        {
            return Ok(t);
        }
        // A branch of a tactic's split (`host::Leaves`).
        if let ExprKind::Var(name) = &e.kind
            && let Some(k) = host::leaf_index(name)
        {
            return Host(self).host_leaf(cx, k, expected, lvl, e.span);
        }
        if let Some(receiver) = cx.dot_receiver.as_ref().and_then(|r| r.inference(cx, e))
            && let Some(Ok((t, got, _))) = receiver.get()
        {
            stats::count(stats::Counter::DotReceiverReuses);
            MismatchNotes(self).note_check_mismatch(cx, got, expected, lvl, e.span);
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
                NameLookup(self).emit_lint_with_fix(
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
        // (docs/language/classes/bare-symbol-checking-carrier-design.md §3.1). The expected type
        // is already in hand one line above the rewrite, and has been since the
        // operators round — nothing is plumbed from a call site.
        if let Some(rewritten) = NameLookup(self).owner_rewrite(cx, e)? {
            return self.elab_check_skel_slots(cx, &rewritten, expected, lvl, hint, skel, capture_slots);
        }
        if let Some(rewritten) = Operators(self).op_rewrite(cx, e, Some(expected))? {
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
        if let Type::Squash { level, ty } = expected
            && let Some(payload) = self.check_condition_squashed(cx, e, ty, level)?
        {
            return Ok(Term::Squash { level: level.clone(), ty: Rc::clone(ty), tm: Rc::new(payload) });
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
            // `induct f(ā); all_goals { body }` and `induct f(ā) { C => e, … }`
            // (crates/elab/src/function_induction.rs): the principle applied
            // at the goal, its leaves the markers below.
            ExprKind::App { head, args, named, explicit: false, goal_oriented: false }
                if matches!(&head.kind, ExprKind::Var(name) if name == heather_syntax::INDUCT_ALL_GOALS || name == heather_syntax::INDUCT_CASES)
                    && named.is_empty() =>
            {
                let (call, body) = match args.as_slice() {
                    [call, body] => (call, Ok(body)),
                    [Expr { kind: ExprKind::Match { scrut, arms, .. }, .. }] => (&**scrut, Err(arms.as_slice())),
                    _ => return err("internal `induct` form has the wrong arity", e.span),
                };
                let (built, inner) = crate::function_induction::FunctionInduction(self).induct_step(cx, call, body, expected, lvl, e.span)?;
                self.elab_check_skel_slots(&inner, &built, expected, lvl, hint, skel, capture_slots)
            }
            ExprKind::App { head, args, named, explicit: false, goal_oriented: false }
                if matches!(&head.kind, ExprKind::Var(name) if name == crate::function_induction::INDUCT_LEAF_ALL || name == crate::function_induction::INDUCT_LEAF || name == crate::function_induction::INDUCT_LEAF_DEFAULT)
                    && named.is_empty() =>
            {
                let discharge = matches!(&head.kind, ExprKind::Var(name) if name == crate::function_induction::INDUCT_LEAF_ALL || name == crate::function_induction::INDUCT_LEAF_DEFAULT);
                let is_default = matches!(&head.kind, ExprKind::Var(name) if name == crate::function_induction::INDUCT_LEAF_DEFAULT);
                crate::function_induction::FunctionInduction(self).induct_leaf(cx, args, discharge, is_default, expected, lvl, e.span)
            }
            ExprKind::App { head, args, named, explicit: false, goal_oriented: false }
                if matches!(&head.kind, ExprKind::Var(name) if name == constructor::FIELD_DEFAULT)
                    && named.is_empty() =>
            {
                Constructors(self).elab_field_default(cx, args, expected, lvl, e.span)
            }
            ExprKind::App { args, .. } if defaults::is_param_default(e) => {
                // Reached only off a spine walker's path, which hands the
                // call's earlier arguments to `check_param_default` instead.
                Defaults(self).elab_param_default(cx, args, expected, lvl, e.span, &[])
            }
            ExprKind::App { head, args, named, explicit: false, goal_oriented: false }
                if matches!(&head.kind, ExprKind::Var(name) if name.starts_with(heather_syntax::CASES_HYPOTHESIS))
                    && named.is_empty() =>
            {
                let ExprKind::Var(name) = &head.kind else { unreachable!("guarded above") };
                match crate::hypothesis_cases::step(self, cx, name, args, expected, lvl, e.span)? {
                    crate::hypothesis_cases::Stepped::Expr(step) => self.elab_check_skel_slots(cx, &step, expected, lvl, hint, skel, capture_slots),
                    // `Π(h). goal` split as `split_all` splits a goal, then
                    // applied to `h`.
                    crate::hypothesis_cases::Stepped::Split { split, premise, level, hypothesis } => {
                        let (scrut, ty, scrut_level) = self.elab_infer(cx, &split.scrut)?;
                        let mut split = split;
                        // The test as the split spells it may be written
                        // otherwise in the goal than where the search found
                        // it (`fits(b)` against a constructor's field read
                        // `fits(…)`): abstract it as written too.
                        if split.dependent.is_none()
                            && let Some(motive) = split.motive.inst_top(0, &scrut).abstract_local_any(std::slice::from_ref(&scrut))
                        {
                            split.motive = motive;
                        }
                        goal_combinators::restates(self, cx, &split.motive.inst_top(0, &scrut), &premise, &level, "case split's motive, at its scrutinee,", e.span)?;
                        goal_combinators::motive_is_a_type(self, cx, &split.motive, split.dependent.as_ref(), &premise, &scrut, &ty, &scrut_level, &level, e.span)?;
                        let split_term = match split.dependent {
                            None => Inference(self).elab_convoy(
                                cx, heather_syntax::MatchForm::Match, true, &split.equation, &split.arms,
                                scrut, &ty, &scrut_level, split.motive, &level, &premise, e.span,
                            )?,
                            Some(dependent) => {
                                let refl = Term::Refl { level: scrut_level.clone(), ty: Rc::new(ty.clone()), tm: Rc::new(scrut.clone()) };
                                let at = dependent.inst_top_above(0, 1, &scrut).inst_top(0, &refl);
                                goal_combinators::restates(self, cx, &at, &premise, &level, "case split's motive, at its scrutinee and `refl`,", e.span)?;
                                Inference(self).elab_convoy_dependent(
                                    cx, &split.equation, &split.arms, scrut, &ty, &scrut_level, split.motive, dependent, &level, &premise, e.span,
                                )?
                            }
                        };
                        let Type::Pi { dom_level, cod_level, dom, cod } = premise else { unreachable!("a step's premise is a Π") };
                        Ok(Term::App { fun: Rc::new(split_term), dom_level, cod_level, dom, cod, arg: Rc::new(hypothesis) })
                    }
                }
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
                        goal_combinators::motive_is_a_type(self, cx, &split.motive, split.dependent.as_ref(), &goal, &scrut, &ty, &level, lvl, e.span)?;
                        match split.dependent {
                            None => Inference(self).elab_convoy(
                                cx, heather_syntax::MatchForm::Match, true, &split.equation, &split.arms,
                                scrut, &ty, &level, split.motive, lvl, &goal, e.span,
                            ),
                            Some(dependent) => {
                                let refl = Term::Refl { level: level.clone(), ty: Rc::new(ty.clone()), tm: Rc::new(scrut.clone()) };
                                let at = dependent.inst_top_above(0, 1, &scrut).inst_top(0, &refl);
                                goal_combinators::restates(self, cx, &at, &goal, lvl, "case split's motive, at its scrutinee and `refl`,", e.span)?;
                                Inference(self).elab_convoy_dependent(
                                    cx, &split.equation, &split.arms, scrut, &ty, &level, split.motive, dependent, lvl, &goal, e.span,
                                )
                            }
                        }
                    }
                    goal_combinators::Step::Revert(positions) => {
                        let goal = goal_combinators::simplify_goal(self, cx, &inductive::decoded(expected));
                        goal_combinators::restates(self, cx, &goal, expected, lvl, "simplified goal", e.span)?;
                        let (reverted, reverted_lvl) = generalize::Generalize(self).generalize_expected(cx, &positions, &goal, lvl);
                        let proof = self.elab_check_skel_slots(cx, e, &reverted, &reverted_lvl, hint, skel, capture_slots)?;
                        Ok(generalize::Generalize(self).instantiate_generalized(cx, proof, reverted, &positions))
                    }
                    goal_combinators::Step::Leaf(goal) => {
                        goal_combinators::restates(self, cx, &goal, expected, lvl, "simplified goal", e.span)?;
                        goal_combinators::check_refl_leaf(self, cx, body, &goal, e.span)?;
                        // A leaf that fails says which case it failed in, as
                        // the source tests it.
                        // A hole in the block is this case's own goal.
                        let leaf = || self.elab_check_skel_slots(cx, body, &goal, lvl, hint, skel, capture_slots);
                        let checked = if crate::count_holes_expr(body) > 0 {
                            let names: Vec<&str> = cx.names.iter().collect();
                            let key = format!("{}|{}", goal_combinators::case_path(self, cx, e.span).unwrap_or_default(), names.join(","));
                            self.attempt.goal_arena.in_leaf(key, leaf)
                        } else {
                            leaf()
                        };
                        checked.map_err(|error| match error {
                            crate::ElabError::Elab { msg, span } if !msg.contains("in the case") => match goal_combinators::case_path(self, cx, e.span) {
                                Some(cases) => crate::ElabError::Elab { msg: format!("{msg}\n  in the `split_all` case {cases}"), span },
                                None => crate::ElabError::Elab { msg, span },
                            },
                            other => other,
                        })
                    }
                }
            }
            // **Rule 2** (docs/language/let-and-blocks-design.md §5.2): `refl` is a
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
                .check_form(self.0, cx, e, expected, lvl, hint)
                .expect("classified as an ExprElab checking form"),
            // `{ let x = e; … result }` — **checking**-transparent, which is
            // the property that makes the form useful: a block in a `match`
            // arm under a dependent motive is checked at the arm's type rather
            // than inferred and then converted
            // (docs/language/let-and-blocks-design.md §4.4). The hint travels with it,
            // so a hole in the result of a block in argument position still
            // reports the callee and parameter it belongs to.
            ExprKind::Block(block) => {
                statements::check_block(self.0, cx, block, expected, lvl, hint, skel, capture_slots)
            }
            // A quote against its `Code(g |- T)` type — checking-only, like
            // the kernel's `BoxTm` (docs/metaprogramming/in-language-map-design.md §5).
            ExprKind::Quote(payload) => Quotation(self).elab_quote(cx, payload, expected, e.span),
            ExprKind::Match {
                form,
                motive: None,
                scrut,
                arms,
                eqbind,
                generated,
            } => (|| {
                // Stage-2 motive synthesis (issues/elab-stage2-metas.md,
                // docs/elaborator/goal-motive-synthesis-design.md): abstract the
                // scrutinee out of the expected type so the motive is
                // genuinely dependent; the non-dependent motive (expected
                // under `z`) is what "no occurrence anywhere" falls back to.
                let (scrut_t, scrut_ty, scrut_lvl) = self
                    .elab_infer(cx, scrut)
                    .map_err(|error| matching::if_resolution_error(*form, scrut, error))?;
                // A recursion whose self-calls vary a parameter generalizes it
                // into the motive (docs/tactics/ih-generalization-design.md): the goal
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
                let top = Declarations(self).top_guard(e.span);
                let guard = top.or_else(|| recursion::guard_param(cx, &scrut_t, arms));
                let mut positions = match (top, guard) {
                    // A default attempt generalizes what the calls vary, as
                    // the plain lowering does: a parameter every call passes
                    // unchanged keeps the step a fold over values, which the
                    // kernel's run folds read (`eval/runs.rs`); generalizing
                    // it made `addr(m, n)`'s step a fold over functions. Too
                    // few positions refuse the call, and the plain lowering
                    // answers. A fallback generalizes every parameter.
                    (Some(dec), _) if self.scope.recursion_at_top.is_some_and(|(_, _, all)| all) => {
                        Declarations::top_positions(cx, dec)
                    }
                    (Some(dec), _) => Generalize(self).varying_params(cx, arms, dec),
                    (None, Some(dec)) => Generalize(self).varying_params(cx, arms, dec),
                    (None, None) => Vec::new(),
                };
                // The hypotheses the match refines, with `match h:` as
                // without: what the arms name and the goal mentions, but not
                // a hypothesis that takes an equation about the scrutinee,
                // which is what `h` is passed to, `g: (b = False) → A` at
                // `False => g(h)` (issues/match-eqbind-refines-hypothesis-it-is-passed-to.md,
                // issues/case-split-refines-hypotheses-under-calls.md).
                let mut refined = Generalize(self).refined_hypotheses(
                    cx, arms, (&scrut_t, &scrut_ty, &scrut_lvl), dec, expected, eqbind.as_deref(), e.span,
                );
                let unrefined = std::mem::take(&mut positions);
                // The equation's `refl` reading, and what the match could
                // not refine, are recorded whether or not it generalizes
                // anything (arm-readings-design §3.3, §3.5, §5).
                let kept_cx;
                let cx = if refined.kept.is_empty() && eqbind.is_none() {
                    cx
                } else {
                    let mut with = cx.clone();
                    crate::readings::Readings::register_kept(&mut with, &refined.kept);
                    let mut shadowed: Vec<&str> = Vec::new();
                    for arm in arms.iter() {
                        arm.binders.iter().for_each(|pat| generalize::pattern_names(pat, &mut shadowed));
                    }
                    crate::readings::Readings::register(&mut with, &[], &[], &shadowed, eqbind.as_deref());
                    kept_cx = with;
                    &kept_cx
                };
                // Lowered at most twice: a hypothesis generalized because an
                // arm names it, whose refined reading no arm then used, is
                // left out the second time (arm-readings-design §3.4).
                let mut again = false;
                loop {
                    let mut positions = unrefined.clone();
                    for &p in &refined.positions {
                        if !positions.contains(&p) {
                            positions.push(p);
                        }
                    }
                    positions.sort_unstable();
                    if positions.is_empty() {
                        break;
                    }
                    // A hypothesis read through a call is spelled with the
                    // scrutinee, which the syntactic rung finds first; the
                    // goal is spelled so too, at the motive it gets alone,
                    // or the rung that finds the hypothesis would leave a
                    // goal only a later rung reaches as it is.
                    let goal = if refined.retyped.is_empty() {
                        expected.clone()
                    } else {
                        matching::synthesize_motive(self.0, cx, &scrut_t, &scrut_ty, &scrut_lvl, expected, e.span)
                            .apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(scrut_t.clone())))
                    };
                    let (mut gen_ty, mut gen_lvl) =
                        Generalize(self).generalize_retyped(cx, &positions, &refined.retyped, &goal, lvl);
                    let mut motive = matching::synthesize_motive(
                        self.0, cx, &scrut_t, &scrut_ty, &scrut_lvl, &gen_ty, e.span,
                    );
                    // A hypothesis read through a call is abstracted by the
                    // syntactic rung, which checks nothing; if the motive
                    // that makes is ill-formed, the match refines what it
                    // did before (goal-motive-synthesis-design §4.7).
                    let mut kept: Vec<usize> = Vec::new();
                    if !refined.retyped.is_empty()
                        && !matching::MotiveSynthesisElab::motive_well_formed(self.0, cx, &motive, &scrut_ty, &scrut_lvl)
                    {
                        kept = positions.iter().copied().filter(|p| refined.retyped.iter().any(|(q, _)| q == p) && !unrefined.contains(p)).collect();
                        positions.retain(|p| !kept.contains(p));
                        (gen_ty, gen_lvl) = Generalize(self).generalize_expected(cx, &positions, expected, lvl);
                        motive = matching::synthesize_motive(
                            self.0, cx, &scrut_t, &scrut_ty, &scrut_lvl, &gen_ty, e.span,
                        );
                    }
                    // A refined hypothesis keeps its written reading in the
                    // arm, and the equation its `refl` one
                    // (docs/language/matching/arm-readings-design.md).
                    let mut shadowed: Vec<&str> = Vec::new();
                    for arm in arms.iter() {
                        arm.binders.iter().for_each(|pat| generalize::pattern_names(pat, &mut shadowed));
                    }
                    let mut gcx = cx.clone();
                    let registered = crate::readings::Readings::register(&mut gcx, &positions, &unrefined, &shadowed, None);
                    crate::readings::Readings::register_kept(&mut gcx, &kept);
                    let arms = Generalize(self).wrap_arms(cx, arms, &positions);
                    let positions = Rc::new(positions);
                    if let Some(dec) = guard {
                        gcx.generalized = Some(Rc::new(generalize::Generalization {
                            dec,
                            positions: Rc::clone(&positions),
                            span: e.span,
                        }));
                    }
                    let run = |mcx: &Cx, eq: Option<&str>| match eq {
                        None => Routes(self).elab_match(
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
                        Some(h) => Inference(self).elab_convoy(
                            mcx, *form, *generated, h, &arms, scrut_t.clone(), &scrut_ty,
                            &scrut_lvl, motive.clone(), &gen_lvl, &gen_ty, e.span,
                        ),
                    };
                    // A recursion's own match generalizes for its calls
                    // as well, which no use of a name shows.
                    let droppable = !again
                        && eqbind.is_some()
                        && !generalize::arms_call_self(cx, arms.as_slice())
                        && !generalize::arms_have_hole(arms.as_slice())
                        && registered.iter().any(|r| matches!(r.kind, crate::readings::ReadingKind::Written(_)));
                    let (elim, unused) = if !droppable {
                        let elim = match eqbind {
                            None => Inference(self).elab_match_pending(&gcx, &scrut_t, &scrut_ty, &run),
                            Some(h) => run(&gcx, Some(h)),
                        };
                        (elim, Vec::new())
                    } else { self.probe_unless(|| {
                        let elim = match eqbind {
                            None => Inference(self).elab_match_pending(&gcx, &scrut_t, &scrut_ty, &run),
                            Some(h) => run(&gcx, Some(h)),
                        };
                        let m = cx.names.len();
                        let mut unused: Vec<usize> = Vec::new();
                        if !again && elim.is_ok() {
                            for reading in &registered {
                                if let crate::readings::ReadingKind::Written(q) = reading.kind
                                    && reading.uses.get() == 0
                                    && expected.abstract_local(&Term::Var(heather_kernel::term::LocalVar((m - 1 - q) as u32))).is_none()
                                {
                                    unused.push(q);
                                }
                            }
                            // One a kept hypothesis's type mentions stays.
                            while let Some(i) = unused.iter().position(|&q| {
                                positions.iter().any(|&p| p > q && !unused.contains(&p) && generalize::mentions_binder(cx, p, q))
                            }) {
                                unused.remove(i);
                            }
                        }
                        let keep = unused.is_empty();
                        ((elim, unused), keep)
                    }) };
                    if !unused.is_empty() {
                        refined.positions.retain(|p| !unused.contains(p));
                        refined.retyped.retain(|(p, _)| !unused.contains(p));
                        again = true;
                        continue;
                    }
                    let elim = elim?;
                    // What this match generalizes it reads: a copy an
                    // enclosing match bound is used by being refined again.
                    positions.iter().for_each(|&p| crate::readings::Readings::note_use(cx, p));
                    return Ok(Generalize(self).instantiate_generalized(cx, elim, gen_ty, &positions));
                }
                // An alias whose type is about the scrutinee rides along as a
                // convoy, so each arm sees it at its constructor (design §7.2).
                let dependents = if eqbind.is_none() {
                    Generalize(self).dependent_aliases(cx, arms, &scrut_t)
                } else {
                    Vec::new()
                };
                if !dependents.is_empty() {
                    let (gen_ty, gen_lvl) = Generalize(self).alias_generalized(&dependents, expected, lvl);
                    let motive = matching::synthesize_motive(
                        self.0, cx, &scrut_t, &scrut_ty, &scrut_lvl, &gen_ty, e.span,
                    );
                    let arms = Generalize(self).wrap_alias_arms(arms, &dependents);
                    let run = |mcx: &Cx, eq: Option<&str>| match eq {
                        None => Routes(self).elab_match(
                            mcx, *form, *generated, &arms, scrut_t.clone(), &scrut_ty, &scrut_lvl,
                            motive.clone(), gen_lvl.clone(), e.span,
                        ),
                        Some(h) => Inference(self).elab_convoy(
                            mcx, *form, *generated, h, &arms, scrut_t.clone(), &scrut_ty,
                            &scrut_lvl, motive.clone(), &gen_lvl, &gen_ty, e.span,
                        ),
                    };
                    let elim = match eqbind {
                        None => Inference(self).elab_match_pending(cx, &scrut_t, &scrut_ty, &run)?,
                        Some(h) => run(cx, Some(h))?,
                    };
                    return Ok(Generalize(self).instantiate_aliases(cx, elim, gen_ty, &dependents));
                }
                let motive = matching::synthesize_motive(
                    self.0, cx, &scrut_t, &scrut_ty, &scrut_lvl, expected, e.span,
                );
                let run = |mcx: &Cx, eq: Option<&str>| match eq {
                    None => Routes(self).elab_match(
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
                    Some(h) => Inference(self).elab_convoy(
                        mcx, *form, *generated, h, arms, scrut_t.clone(), &scrut_ty, &scrut_lvl,
                        motive.clone(), lvl, expected, e.span,
                    ),
                };
                match eqbind {
                    None => Inference(self).elab_match_pending(cx, &scrut_t, &scrut_ty, &run),
                    Some(h) => run(cx, Some(h)),
                }
            })()
            // An arm refused at a use of a hypothesis the match could not
            // refine says so (arm-readings-design §3.5).
            .map_err(|error| crate::readings::Readings(self).explain(error)),
            // `absurd(p)`: from an equation between distinct constructors,
            // anything — so it needs the expected type
            // (docs/inductives/inductive-tier0-lowering.md §6.1).
            ExprKind::App { .. }
                if matches!(e.as_named(), Some((n, _, _))
                            if n == "absurd" && !self.shadowed(cx, n)) =>
            {
                let (_, args, _) = e.as_named().expect("just checked");
                let [arg] = args else {
                    return err("`absurd` takes exactly one argument", e.span);
                };
                Inductives(self).build_absurd(cx, arg, expected, lvl, e.span)
            }
            // A bracket literal is selected by its expected container type.
            // Primitive vectors are the bootstrap representation and retain
            // their intrinsic reading, just as `Nat` does for numerals. Every
            // other container opts in through the canonical prelude protocol.
            ExprKind::CollectionLit(elems) => {
                let expr = self.expr_elab();
                if let Some(vector) = expr.vector_literal_type(cx, expected, e.span)? {
                    expr.check_indexed_form(self.0, cx, e, &vector)
                        .expect("classified as an ExprElab indexed checking form")
                } else {
                    Inference(self).check_collection_literal(cx, e, elems, expected, lvl, e.span)
                }
            }
            // `FZ` / `FS(j)` against an expected `Fin`. Checking-only, like
            // `refl` and a collection literal: `FZ` inhabits `Fin(Succ k)` for
            // *every* `k`, and nothing in the term names one
            // (docs/language/surface-fin-indexing-design.md §3.1). Keyed on the
            // expected type and never on the name, so a user inductive with a
            // constructor called `FZ`/`FS` is untouched — hence the
            // `ctor_here` guard.
            ExprKind::Var(name)
                if name == "FZ"
                    && !self.shadowed(cx, name)
                    && Constructors(self).ctor_here_expected(cx, name, expected).is_none() =>
            {
                self.expr_elab()
                    .check_indexed_form(self.0, cx, e, expected)
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
                    && Constructors(self).ctor_here_expected(cx, name, expected).is_none() =>
            {
                self.expr_elab().check_unit_form(self.0, cx, expected, lvl, e.span)
            }
            // `decide` — proof by reflection at a decided goal
            // (docs/tactics/reflection-through-decide-instances-design.md §4). Sugar
            // for `bool::decide_yes(refl)`: resolution picks the `Decide`
            // instance, the kernel runs its decision and judges the `refl`.
            // The name is also `bool::decide`'s, so the shadowing guard is
            // narrower than `trivial`'s: a local, an alias, the declaration
            // itself, or a user global of that name wins; the library's own
            // `decide` does not, since a bare `decide` at a goal that is not
            // a function was never that value.
            ExprKind::Var(name)
                if name == "decide"
                    && !Refusals(self).decide_shadowed(cx)
                    && Constructors(self).ctor_here_expected(cx, name, expected).is_none() =>
            {
                Refusals(self).elab_decide(cx, expected, lvl, e.span)
            }
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if name == "rel_cong" || name == "rel_derive")
                && !self.shadowed(cx, e.as_named().unwrap().0)
                && Constructors(self).ctor_here_expected(cx, e.as_named().unwrap().0, expected).is_none() =>
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
                && Constructors(self).ctor_here_expected(cx, name, expected).is_none() => {
                relational_context::proof::derive(self, cx, expected, lvl, e.span)
            }
            // `by t` runs the tactic `t` against the expected type
            // (docs/metaprogramming/host-elaboration-interface-design.md, `host.rs`).
            ExprKind::App { head, args, .. }
                if matches!(&head.kind, ExprKind::Var(name) if name == heather_syntax::BY_TACTIC) =>
            {
                let [tactic] = args.as_slice() else {
                    return err("`by` runs one tactic", e.span);
                };
                Host(self).run_by(cx, tactic, expected, lvl, e.span)
            }
            // `rewrite(h, …, e)` rewrites the goal along equations, writing
            // `j`'s motive by abstracting each left side
            // (docs/tactics/equation-rewrite-design.md).
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if name == "rewrite")
                && !named.iter().any(|a| a.name == "in")
                && !self.shadowed(cx, "rewrite")
                && Constructors(self).ctor_here_expected(cx, "rewrite", expected).is_none() =>
            {
                Rewrites(self).elab_rewrite(cx, args, named, expected, lvl, e.span)
            }
            // `simp_only(r₁, …, rₙ)` normalises the goal by a list of laws and
            // closes it; `simp_show` reports the result (docs/tactics/simp-design.md).
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if (name == "simp_only" || name == "simp_show")
                && !self.shadowed(cx, name)
                && Constructors(self).ctor_here_expected(cx, name, expected).is_none()) =>
            {
                let show = matches!(&head.kind, ExprKind::Var(name) if name == "simp_show");
                crate::rewrite::Simps(self).elab_simp(cx, show, args, named, expected, lvl, e.span)
            }
            // `subst(h, e)` eliminates a local variable along `h`, reverting
            // the locals that depend on it (docs/tactics/equation-rewrite-design.md §8).
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if name == "subst")
                && !self.shadowed(cx, "subst")
                && Constructors(self).ctor_here_expected(cx, "subst", expected).is_none() =>
            {
                LocalSubsts(self).elab_subst(cx, args, named, expected, lvl, e.span)
            }
            // `ring` normalizes both sides of an equation at `Int` or `Nat`
            // by reflection; `ring(h, …)` also combines equations
            // (docs/tactics/ring-normalization-design.md).
            ExprKind::Var(name)
                if name == "ring"
                    && !self.shadowed(cx, name)
                    && Constructors(self).ctor_here_expected(cx, name, expected).is_none() =>
            {
                Ring(self).elab_ring(cx, &[], expected, lvl, e.span)
            }
            ExprKind::App {
                head,
                args,
                named,
                explicit: false,
                goal_oriented: false,
            } if matches!(&head.kind, ExprKind::Var(name) if name == "ring")
                && !self.shadowed(cx, "ring")
                && Constructors(self).ctor_here_expected(cx, "ring", expected).is_none() =>
            {
                if !named.is_empty() {
                    return err("`ring` takes its equations positionally", e.span);
                }
                Ring(self).elab_ring(cx, args, expected, lvl, e.span)
            }
            // `linarith` proves a linear order goal at an ordered field from
            // the facts, up to its `≈` (docs/tactics/linarith-design.md); `nlinarith`
            // multiplies the facts too (docs/tactics/nonlinear-arithmetic-design.md).
            ExprKind::Var(name)
                if matches!(name.as_str(), "linarith" | "nlinarith")
                    && !self.shadowed(cx, name)
                    && Constructors(self).ctor_here_expected(cx, name, expected).is_none() =>
            {
                Linarith(self).elab_linarith(cx, &[], expected, lvl, e.span, name == "nlinarith")
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
                && Constructors(self).ctor_here_expected(cx, name, expected).is_none() =>
            {
                if !named.is_empty() {
                    return err(format!("`{name}` takes its facts positionally"), e.span);
                }
                Linarith(self).elab_linarith(cx, args, expected, lvl, e.span, name == "nlinarith")
            }
            // `positivity` is `:= infer`'s proposition search run as a tactic,
            // with `omega` as the fallback at every subgoal the evidence rules
            // cannot close (docs/library/positivity-evidence-design.md §10).
            ExprKind::Var(name)
                if name == "positivity"
                    && !self.shadowed(cx, name)
                    && Constructors(self).ctor_here_expected(cx, name, expected).is_none() =>
            {
                Resolution(self).positivity(cx, expected, lvl, e.span)
            }
            // The obligation a `fn f(…) → Pos<A>` result states, restated at
            // its body by the parser (`result_fact`): the same search, with a
            // failure that names the way to prove it by hand.
            // A `Pos<A>` record field's fact, left out of a construction.
            ExprKind::Var(name) if name == heather_syntax::POS_SEARCH => {
                Resolution(self).infer_proposition(cx, expected, lvl, e.span)
            }
            ExprKind::Var(name) if name == heather_syntax::POS_RESULT => {
                Resolution(self).positivity(cx, expected, lvl, e.span).map_err(|e| match e {
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
            // A `decreases` obligation nobody discharges by hand: `omega`,
            // and where it is stuck on the `toNat` of a word, `bv_omega`
            // (issues/decreases-word-measures-by-hand.md). `omega`'s refusal
            // stays the diagnosis: it is what `Obligations::explain` rewords.
            ExprKind::Var(name) if name == crate::measure::CLOSER => {
                let tactic = |name: &str| Expr { kind: ExprKind::Var(name.into()), span: e.span };
                let mark = (self.pass.warnings.borrow().len(), self.attempt.goal_arena.mark());
                let stuck = match self.elab_check(cx, &tactic("omega"), expected, lvl) {
                    Ok(term) => return Ok(term),
                    Err(stuck) => stuck,
                };
                if self.key_of("bitvec_omega::add_form").is_none() || !bv_omega::mentions_word(self, expected) {
                    return Err(stuck);
                }
                self.pass.warnings.borrow_mut().truncate(mark.0);
                self.attempt.goal_arena.rollback(mark.1);
                match self.elab_check(cx, &tactic("bv_omega"), expected, lvl) {
                    Ok(term) => Ok(term),
                    Err(ElabError::Elab { msg: words, .. }) => match stuck {
                        ElabError::Elab { msg, span } => Err(ElabError::Elab {
                            msg: format!("{msg}; over the words, {}", words.lines().next().unwrap_or_default()),
                            span,
                        }),
                        stuck => Err(stuck),
                    },
                    Err(_) => Err(stuck),
                }
            }
            // `known`: a hypothesis, a side of a conjunction, then the
            // arithmetic searches (docs/language/when-design.md §5).
            ExprKind::Var(name)
                if name == crate::tested::KNOWN
                    && !self.shadowed(cx, name)
                    && Constructors(self).ctor_here_expected(cx, name, expected).is_none() =>
            {
                crate::tested::Tested(self).known(cx, expected, lvl, e.span)
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
                    && Constructors(self).ctor_here_expected(cx, name, expected).is_none() =>
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
                && Constructors(self).ctor_here_expected(cx, "omega", expected).is_none() =>
            {
                if !named.is_empty() {
                    return err("`omega` takes its facts positionally", e.span);
                }
                let (cx, facts) = self.omega_fact_context(cx, args)?;
                let proof = self.elab_omega(&cx, "omega", expected, lvl, e.span)?;
                Ok(statements::LetValue::discard_around(self.0, &cx, facts, proof, expected, lvl))
            }
            // `bv_omega` lifts word arithmetic to Nat (docs/tactics/bv-omega-design.md):
            // it writes a proof from the bridge lemmas and `omega`, and this
            // arm checks it at the goal like any other source.
            ExprKind::Var(name)
                if name == "bv_omega"
                    && !self.shadowed(cx, name)
                    && Constructors(self).ctor_here_expected(cx, name, expected).is_none() =>
            {
                if self.key_of("bitvec_omega::add_form").is_none() {
                    return err("`bv_omega` requires its lemmas; add `import bitvec_omega;`", e.span);
                }
                // A negated word fact (`¬(x < lo)`, `x = y → False`), such as
                // a branch equation's side condition: assume it and refute
                // the assumption, which the inner call reads as a fact in
                // scope, as `omega` does at a negated Nat relation.
                if omega_cert::negated_domain(self, cx, expected).is_some() {
                    let assumed = Expr {
                        kind: ExprKind::Lam {
                            binders: vec![heather_syntax::LamBinder { name: "__bv_assumed".into(), ty: None, implicit: false, span: e.span }],
                            body: Box::new(e.clone()),
                        },
                        span: e.span,
                    };
                    return self.elab_check(cx, &assumed, expected, lvl);
                }
                let _certificate_scope = omega_cert::CertificateScope::enter(&self.scope.omega_depth);
                let generate = |careful, opaque: &std::collections::HashSet<String>| {
                    bv_omega::generate(self, cx, expected, careful, opaque).map_err(|detail| ElabError::Elab {
                        msg: format!("`bv_omega` got stuck: {detail}"),
                        span: e.span,
                    })
                };
                let mut opaque = std::collections::HashSet::new();
                let mut generated = generate(false, &opaque)?;
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
                    generated = generate(true, &opaque)?;
                    checked = self.generated_scope(|me| me.elab_check(cx, &parse(&generated.source)?, expected, lvl));
                }
                // Each side condition alone, in the context its bundle had.
                let side = |obligation: &bv_omega::Obligation, prelude: &str| -> Result<Result<(), ElabError>, ElabError> {
                    let (statement, proof) = obligation.alone();
                    let probe = parse(&format!("{{\n{prelude}\nhave __bv_side: ({statement}) = {proof};\n__bv_side\n}}"))?;
                    let mark = (self.pass.warnings.borrow().len(), self.attempt.goal_arena.mark());
                    let result = self.generated_scope(|me| me.elab_infer(cx, &probe)).map(|_| ());
                    self.pass.warnings.borrow_mut().truncate(mark.0);
                    self.attempt.goal_arena.rollback(mark.1);
                    Ok(result)
                };
                // A word whose side conditions fail is kept as an atom, its
                // value bounded by its range and the facts that mention it
                // (docs/tactics/bv-omega-design.md §5.1), and the proof is
                // written again. Each round keeps more words whole, so this
                // ends; a refusal still diagnoses the first attempt's proof.
                // Past the first failing side condition (the diagnosis), only
                // those that would keep a word are probed.
                let diagnosed = generated.clone();
                let refused = checked.as_ref().err().cloned();
                let mut diagnosis: Option<(usize, ElabError)> = None;
                let mut kept = generated.clone();
                let mut rounds = 0;
                while checked.is_err() && rounds < bv_omega::ATOM_ROUNDS {
                    let mut more = Vec::new();
                    for (i, obligation) in kept.obligations.iter().enumerate() {
                        let first = rounds == 0 && diagnosis.is_none();
                        if !first && obligation.atoms.iter().all(|w| opaque.contains(w)) {
                            continue;
                        }
                        if let Err(failure) = side(obligation, &kept.prelude)? {
                            if first {
                                diagnosis = Some((i, failure));
                            }
                            for word in &obligation.atoms {
                                if !opaque.contains(word) && !more.contains(word) {
                                    more.push(word.clone());
                                }
                            }
                        }
                    }
                    rounds += 1;
                    if more.is_empty() {
                        break;
                    }
                    opaque.extend(more);
                    self.pass.warnings.borrow_mut().truncate(mark.0);
                    self.attempt.goal_arena.rollback(mark.1);
                    kept = generate(true, &opaque)?;
                    checked = self.generated_scope(|me| me.elab_check(cx, &parse(&kept.source)?, expected, lvl));
                }
                match checked {
                    // Lifted into a lemma of its own where the declaration
                    // reserved a slot (docs/tactics/bv-omega-design.md §7): the
                    // kernel checks it once, in its context, and the body
                    // carries only a reference.
                    Ok(term) => Ok(self
                        .attempt
                        .goal_arena
                        .allocate_proved(&Declarations(self).emitted_cx(cx), expected.clone(), lvl.clone(), term.clone(), e.span)
                        .unwrap_or(term)),
                    Err(last) => {
                        // Name the side condition that failed, not only the goal
                        // (§5).
                        let generated = diagnosed;
                        let error = refused.unwrap_or(last);
                        if let Some((i, failure)) = diagnosis {
                            let obligation = &generated.obligations[i];
                            return err(
                                format!("`bv_omega`: {}; `omega` could not prove `{}`:\n{failure}", obligation.why, obligation.shown),
                                e.span,
                            );
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
                    && Constructors(self).ctor_here_expected(cx, "FS", expected).is_none() =>
            {
                self.expr_elab()
                    .check_indexed_form(self.0, cx, e, expected)
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
                None => Inference(self).elab_overloaded_num_check(cx, e, expected, lvl, e.span),
            },
            // The two literals of docs/library/string-char-design.md §3, on the
            // numeral's ladder: the spec type's introduction form at `Char` /
            // `String`, and `CharLiteral` / `StringLiteral` at every other
            // carrier.
            ExprKind::Char(c) => Literals(self).elab_char_check(cx, *c, e, expected, lvl),
            ExprKind::Scaled(lit) => Literals(self).elab_scaled_check(cx, lit, e, expected, lvl),
            ExprKind::Str(text) => Literals(self).elab_string_check(cx, text, e, expected, lvl),
            ExprKind::ByteStr(bytes) => Literals(self).elab_byte_string_check(cx, bytes, e, expected),
            ExprKind::ByteChar(byte) => Literals(self).elab_byte_char_check(cx, *byte, e, expected),
            // A lambda against an expected Π: the *expected* domain is what
            // the binder is pushed with, so the emitted annotation always
            // matches the type it is checked against. A written annotation is
            // a readability aid and must be convertible with it
            // (docs/language/surface-function-types.md §5.2).
            // A type constructor written as a λ abstracting a declaration's
            // declared slot takes the canonical spelling the unifier learns
            // (docs/language/classes/lambda-carrier-instances-design.md §7.3).
            ExprKind::Lam { binders, body }
                if let Some(term) = GeneratedDefs(self).check_slot_lambda(cx, binders, body, expected, e.span)? =>
            {
                Ok(term)
            }
            ExprKind::Lam { binders, body } => self
                .expr_elab()
                .check_lambda(self.0, cx, binders, body, expected, lvl, skel, e.span),
            // A universe as the expected type: a *type* has been written where
            // a term is expected, so read it as one and quote it
            // (docs/language/surface-universe.md §4).
            //
            // `El(«Ty n»)` is that universe too, read off without a whnf: it
            // is what a codomain decoded from a type code arrives as, such as
            // a structural group's member whose result is `Type`, checked
            // against its motive's `(x̄) -> Type`
            // (issues/mutual-group-type-valued-members.md).
            _ if let Some(want) = expected_universe(expected) => {
                self.expr_elab()
                    .check_at_universe(self.0, cx, e, want, e.span)
            }
            // A declared type former, partially applied, against an expected
            // function type that ends in a universe: η-expand into the
            // type-valued function the remaining value parameters describe
            // (docs/language/record-type-partial-application.md §2). Sits here for the
            // same reason the universe arm above does — the reading has to be
            // chosen before the constructor arms see the same name — and
            // declines quietly for every other shape.
            _ if matches!(
                &e.kind,
                ExprKind::Var(_) | ExprKind::TyApp { .. } | ExprKind::App { .. }
            ) && let Some(term) = Inductives(self).check_type_former_value(cx, e, expected, e.span)? =>
            {
                Ok(term)
            }
            // A constructor in checking position: the expected type *is* the
            // encoding, so every annotation of the injection and the field
            // tuple is read off it (docs/inductives/inductive-tier0-lowering.md §4).
            // Unsaturated against an expected `Π`, it η-expands into a function
            // value (docs/language/constructor-function-values.md §2).
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
                let (ind, i) = Constructors(self).anonymous_ctor_expected(cx, name, expected, e.span)?;
                Inductives(self).build_ctor_value(cx, &ind, i, args, expected, lvl, e.span)
            }
            ExprKind::Var(name) if Constructors(self).ctor_here_expected(cx, name, expected).is_some() => {
                let (ind, i) = Constructors(self)
                    .ctor_here_expected(cx, name, expected)
                    .expect("just checked");
                Inductives(self).build_ctor_value(cx, &ind, i, &[] as &[Expr], expected, lvl, e.span)
            }
            ExprKind::App { .. } if Constructors(self).ctor_spine_expected(cx, e, expected).is_some() => {
                let (ind, i, args, named) = Constructors(self)
                    .ctor_spine_expected(cx, e, expected)
                    .expect("just checked");
                Constructors(self).lint_manual_list_construction(cx, e, &ind, i);
                let written: Vec<(&str, &Expr, Span)> = named.iter().map(|na| (na.name.as_str(), &na.expr, na.name_span)).collect();
                if let Some(filled) = Constructors(self).with_field_defaults(&ind, i, &args, &written, e.span)? {
                    return Inductives(self).build_ctor_value(cx, &ind, i, &filled, expected, lvl, e.span);
                }
                let permuted =
                    application::resolve_constructor_arguments(&ind, i, &args, &named, e.span)?;
                let args = permuted.unwrap_or(args);
                Inductives(self).build_ctor_value(cx, &ind, i, &args, expected, lvl, e.span)
            }
            // A record update is the record literal that keeps the other
            // fields (`record_update_expr`), checked as one.
            ExprKind::RecordUpdate { base, fields } => {
                let literal = Constructors(self).record_update_expr(cx, base, fields, e.span)?;
                self.elab_check_skel_slots(cx, &literal, expected, lvl, hint, skel, capture_slots)
            }
            // A record literal *is* a constructor application once its fields
            // are put in declaration order, so checking mode is the tier-0
            // constructor path — which is what lets the expected type supply
            // the instantiation and no annotation be written
            // (docs/language/surface-records.md §6).
            ExprKind::RecordLit {
                name,
                tyargs,
                fields,
            } if tyargs.is_empty() => {
                if let Some(ind) = self.lookup_inductive(name).cloned().filter(|ind| ind.is_record) {
                    let written: Vec<(&str, &Expr, Span)> = fields.iter().map(|f| (f.name.as_str(), &f.expr, f.span)).collect();
                    if let Some(filled) = Constructors(self).with_field_defaults(&ind, 0, &[], &written, e.span)? {
                        return Inductives(self).build_ctor_value(cx, &ind, 0, &filled, expected, lvl, e.span);
                    }
                }
                let args = Constructors(self).record_lit_args(name, fields, e.span)?;
                let Some(ind) = self.lookup_inductive(name).cloned() else {
                    return Err(self.name_miss(name, format!("unknown type `{name}`"), e.span));
                };
                Inductives(self).build_ctor_value(cx, &ind, 0, &args, expected, lvl, e.span)
            }
            // `.f` resolution has to exist in *both* modes: a projection
            // synthesizes, but the method fallback may be checking-only
            // (`p.absurd()`), and routing it through inference would break it.
            ExprKind::Dot { .. } if let Some(call) = Inference(self.0).list_receiver(cx, e) => {
                self.elab_check_skel_slots(cx, &call, expected, lvl, hint, skel, capture_slots)
            }
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
                    Members(self).resolve_dot(cx, recv, name, tyargs, args, named, e.span)?;
                if !tyargs.is_empty() && !matches!(&resolution, DotResolution::Method(_)) {
                    return err(
                        format!("type arguments after `.{name}` require a method call"),
                        e.span,
                    );
                }
                match resolution {
                    DotResolution::Inferred(t, got, _) => {
                        MismatchNotes(self).note_check_mismatch(cx, &got, expected, lvl, e.span);
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
                                        self.0,
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
                                    MismatchNotes(self).note_check_mismatch(cx, &got, expected, lvl, e.span);
                                    return Ok(t);
                                }
                            }
                            // A projection synthesizes; its field type is
                            // compared at the gate like any inferred type's.
                            MismatchNotes(self).note_check_mismatch(cx, &ty, expected, lvl, e.span);
                            Ok(t)
                        }
                        Some(args) => {
                            let (t, got, _) = AppUnify(self).apply_projection(
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
                            MismatchNotes(self).note_check_mismatch(cx, &got, expected, lvl, e.span);
                            Ok(t)
                        }
                    },
                    // Dispatch is a projection with its own arguments, so it
                    // takes the applied route unconditionally — there is no
                    // bare form (§4 rule 7).
                    DotResolution::Dispatch(t, ty, l, fskel, dargs) => {
                        let (t, got, _) = AppUnify(self).apply_projection(
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
                        MismatchNotes(self).note_check_mismatch(cx, &got, expected, lvl, e.span);
                        Ok(t)
                    }
                    DotResolution::Method(m) => self
                        .elab_check_skel_slots(cx, &m, expected, lvl, hint, skel, capture_slots)
                        .map_err(|e| Members(self).method_call_failure(cx, recv, &m, e)),
                }
            }
            _ => {
                // The universe arm above matches a *syntactic* `Ty`, but a
                // universe can hide under `El` of a quoted code — an indexed
                // family's field components arrive exactly so
                // (docs/inductives/inductive-indexed-lowering.md §4: the branch spine is
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
                        .check_at_universe(self.0, cx, e, want, e.span);
                }
                // Inference is the fallback, but the expected type is *not*
                // discarded on the way: an implicit-inserting call (or a bare
                // reference to a polymorphic declaration) with something
                // still unsolved consults it — the anti-unification hook and
                // the general expected-type harvest both live behind this
                // line (issues/congruence-by-anti-unification.md decision 7;
                // docs/elaborator/unifier-completeness-design.md §5). Nothing else reads
                // the hint, so every other expression elaborates exactly as
                // before.
                //
                // The §5.3 suppression rule (docs/language/implicit-binders-design.md):
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
                    Inference(self).elab_infer_at(cx, e, if suppress { None } else { Some(expected) })?;
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
                // A `When<T, P>` where a `T` is wanted takes its value
                // (docs/language/when-design.md §5).
                if let Some(value) = crate::tested::Tested(self).coerce(cx, e, &t, &got, &head, lvl)? {
                    return Ok(value);
                }
                // Inside an arm, a term stated with the match's test where
                // the arm's constructor is wanted, or the other way round,
                // is carried along the match's equation
                // (docs/language/matching/arm-readings-design.md §5).
                if let Some(crate::readings::Carried::Term(carried)) = crate::readings::Readings(self).coerce(cx, &t, &got, &head, lvl) {
                    return Ok(carried);
                }
                MismatchNotes(self).note_check_expr(cx, e, &got, &head, lvl);
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
            // fact (docs/language/matching/dependent-match-compiler-design.md §4.3.1).
            Inference(self).want_match_equations(written_cx);
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
                    .allocate_transparent(&Declarations(self).emitted_cx(cx), ty.clone(), level.clone(), atoms.clone());
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
    /// lives a level above the expected one), and [`Refusals::kernel_error`] reads
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
        let _rollback = matching::MatchRollback::new(self.0);
        self.elab_infer(cx, &call).is_ok()
    }
}
