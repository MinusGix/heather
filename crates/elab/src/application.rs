//! Callable surface metadata and application along an explicit Π spine.
//!
//! This module deliberately knows no elaborator state. The explicit engine
//! receives normalization and argument checking through [`ExplicitArgElab`].
//! The implicit engine owns its complete scratch-world lifecycle and receives
//! only the semantic effects in [`ImplicitApplicationElab`].

use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{GlobalVar, LocalSubst, Term, Type};
use heather_syntax::{Expr, ExprKind, LamBinder, Span, Ty, TyKind};

use crate::surface::is_projection_section;
use crate::unification::{DeferredArg, EarlierArg, Guesses, ResolveOb, Sol, zonked, zonked_tm};
use crate::{Cx, ElabError, R, err};

mod callable;
pub(crate) use callable::Callables;
mod polymorphic;
pub(crate) use polymorphic::Polymorphic;
pub(crate) use callable::subject_index_in;
mod named;
pub(crate) use named::{
    PARAM_DEFAULT, permute_by_name_refs, refuse_named, resolve_constructor_arguments, resolve_named,
};

/// The state-free schedule for one implicit-inserting call.
///
/// It fixes the scratch-world size before elaboration starts: one slot for
/// every implicit parameter and one reserved slot for every explicit argument
/// that may have to wait for a checking type. Keeping this calculation here
/// makes the static-size invariant independent of goal promotion and trait
/// resolution.
pub(crate) struct ImplicitPlan<'a> {
    mask: &'a [bool],
    scratch_len: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ParamStep {
    pub(crate) parameter: usize,
    pub(crate) implicit: bool,
}

impl<'a> ImplicitPlan<'a> {
    pub(crate) fn new(
        mask: &'a [bool],
        args: &[Expr],
        checking_only: impl Fn(&Expr) -> bool,
    ) -> Self {
        let implicit = mask.iter().filter(|&&b| b).count();
        let explicit = mask.len() - implicit;
        let deferred = args
            .iter()
            .take(explicit)
            .filter(|arg| checking_only(arg))
            .count();
        Self {
            mask,
            scratch_len: (implicit + deferred) as u32,
        }
    }

    pub(crate) fn scratch_len(&self) -> u32 {
        self.scratch_len
    }

    pub(crate) fn steps(&self, parameter_offset: usize) -> impl Iterator<Item = ParamStep> + '_ {
        self.mask
            .iter()
            .enumerate()
            .map(move |(index, &implicit)| ParamStep {
                parameter: index + parameter_offset,
                implicit,
            })
    }
}

/// Outcome of attempting one solver obligation in the scratch world.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ObligationProgress {
    /// Its goal still mentions an unsolved scratch slot.
    Blocked,
    /// Another slot was filled, but this obligation still needs another pass.
    Unblocked,
    /// The obligation itself was solved.
    Solved,
}

/// The comparisons one implicit-inserting call owes the gate
/// (`issues/implicit-argument-mismatch-reaches-kernel.md`).
///
/// A checked argument was compared with its domain when it was checked. An
/// *inferred* one only taught the call's metas from its type, and that
/// unification is learn-only: `f(a.le_refl())` at `hz: 0 <= ?a` learns
/// nothing from `Le(a, a)`, the expected type then solves `?a := a`, and
/// `Le(a, a)` against `Le(0, a)` was compared by nobody before the kernel,
/// which refused the declaration with no site. Every inferred argument's
/// learning goes through [`Self::learn`], which keeps the pair; the discharge
/// hands each one, under the call's final solutions, to
/// [`ImplicitApplicationElab::note_argument_mismatch`]. A call abandoned
/// before its discharge (a re-plan, an error) records nothing.
#[derive(Default)]
pub(crate) struct OwedChecks {
    /// Each owed comparison, with the implicit it has something to say
    /// about: a slot this argument's type disagreed with (`Some` subject), or
    /// one the guess pass guessed from it (`None`).
    owed: Vec<(Type, Type, Level, Span, Option<(usize, Option<Rc<Term>>)>)>,
    /// Set when a read left one of its guesses for later
    /// ([`Guesses::Postpone`]): the call then owes a guess pass.
    postponed: std::cell::Cell<bool>,
}

/// An implicit the unifier had already solved, met again by a later
/// argument's type with another subject (issues/unifier-checked-assignment.md):
/// the first write won, and this is the write it was never compared with. Kept
/// raw beside the argument's owed comparison and spelled only if the gate
/// refuses the call, so a call that elaborates pays for an `Rc` clone.
#[derive(Clone)]
pub(crate) struct SlotClash {
    /// The implicit's parameter name.
    pub(crate) name: String,
    /// Its solution was a guess the call took last ([`Guesses`]), not a
    /// consequence of the equation.
    pub(crate) guessed: bool,
    /// Its declared type, in the committed world (a `Ty` slot's solution is
    /// a code and is shown as the type it decodes to).
    pub(crate) dom: Option<Type>,
    /// What it was solved to, and what this argument's type would have made
    /// it, both committed-world terms. No `later` is a guess with no
    /// disagreement: the guess is what the argument's mismatch follows from.
    pub(crate) first: Rc<Term>,
    pub(crate) later: Option<Rc<Term>>,
}

impl OwedChecks {
    /// Learn from an inferred argument's type `got` at the scratch-world
    /// parameter type `dom`, and owe their comparison, reported at the
    /// argument's own span `at` (`span` is the learning's, as before). A
    /// guess the read meets waits for [`Self::guess`].
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn learn(
        &mut self,
        elab: &impl ImplicitApplicationElab,
        cx: &Cx,
        dom: &Type,
        level: &Level,
        got: Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        span: Span,
        at: Span,
    ) {
        let clash = elab
            .unify_application_argument_type(cx, dom, &got, n, sols, meta_doms, Guesses::Postpone(&self.postponed), span)
            .into_iter()
            .next()
            .map(|(slot, later)| (slot, Some(later)));
        self.owed.push((dom.clone(), got, level.clone(), at, clash));
    }

    /// The flag a read outside [`Self::learn`] — the expected type's —
    /// postpones its guesses into.
    pub(crate) fn postponed(&self) -> &std::cell::Cell<bool> {
        &self.postponed
    }

    /// The **guess pass** (docs/elaborator/elaborator-principles-survey.md P2,
    /// issues/unifier-guesses-postponed.md): every forced solution is in —
    /// each inferred argument's type and the expected type have been read
    /// with their guesses postponed — and a slot is still open. Read them
    /// again in the same order with the guesses taken, each recorded in
    /// `guessed`; an argument whose read made a guess, or met a slot that
    /// disagrees with one, keeps the slot to name if its comparison is
    /// refused. `expected` is the call's result type and its expected type,
    /// when the expected type was read. Nothing to do when no read
    /// postponed a guess.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn guess(
        &mut self,
        elab: &impl ImplicitApplicationElab,
        cx: &Cx,
        expected: Option<(&Type, &Type)>,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
        guessed: &std::cell::RefCell<Vec<usize>>,
        span: Span,
    ) -> R<()> {
        if !self.postponed.get() || !sols.iter().any(|s| matches!(s, Sol::Unsolved)) {
            return Ok(());
        }
        for (dom, got, _, _, said) in &mut self.owed {
            let before = guessed.borrow().len();
            let clash = elab
                .unify_application_argument_type(cx, dom, got, n, sols, meta_doms, Guesses::Record(guessed), span)
                .into_iter()
                .find(|(slot, _)| guessed.borrow().contains(slot));
            if said.is_none() {
                *said = clash
                    .map(|(slot, later)| (slot, Some(later)))
                    .or_else(|| guessed.borrow().get(before).map(|&slot| (slot, None)));
            }
        }
        if let Some((result, expected)) = expected
            && sols.iter().any(|s| matches!(s, Sol::Unsolved))
        {
            elab.solve_application_from_expected(cx, result, expected, n, sols, meta_doms, Guesses::Record(guessed), span)?;
        }
        Ok(())
    }

    /// Record every owed comparison, each domain under the call's solutions,
    /// with the implicit this argument disagreed about, if any (`clash`
    /// names a slot and gives what it was solved to and its type).
    fn discharge(
        self,
        elab: &impl ImplicitApplicationElab,
        cx: &Cx,
        substitution: &GlobalSubst,
        clash: impl Fn(usize, Option<Rc<Term>>) -> Option<SlotClash>,
    ) {
        for (dom, got, level, span, later) in self.owed {
            let clash = later.and_then(|(slot, later)| clash(slot, later));
            elab.note_argument_mismatch(cx, &got, &dom.apply_global(substitution), &level, span, clash);
        }
    }
}

/// Semantic capabilities used by the otherwise mechanical obligation queue.
///
/// The application module owns retry order and fixpoint termination. The
/// implementation owns the policies that genuinely need session state:
/// dictionary search, expression elaboration, unification, and declaration
/// goal creation.
pub(crate) trait ImplicitApplicationElab: ExplicitArgElab {
    /// Failure-only presentation of the selected head and partially solved
    /// explicit domains. Scratch variables must never escape as kernel syntax.
    fn deferred_argument_note(
        &self, _cx: &Cx, _head: &Term, _params: &[ParamMeta],
        _domains: &[(usize, Type)], _slot_param: &[usize], _sols: &[Sol],
    ) -> String { String::new() }

    fn classify_application_argument(&self, cx: &Cx, argument: &Expr) -> ArgumentClass;

    fn infer_application_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)>;

    /// The other readings of a name that elaborated to `term`
    /// (`readings.rs`): each a term and its type.
    fn argument_readings(&self, _cx: &Cx, _term: &Term) -> Vec<(Term, Type)> { Vec::new() }

    /// Do an argument's type and its parameter's convert?
    fn argument_type_converts(&self, _cx: &Cx, _got: &Type, _expected: &Type, _level: &Level) -> bool { true }

    /// Instantiate a bare polymorphic argument from the known parts of its
    /// parameter type. The returned term and type are fully committed.
    fn infer_polymorphic_argument(
        &self, _cx: &Cx, _argument: &Expr, _parameter: &Type, _n: u32, _sols: &[Sol],
    ) -> Option<R<(Term, Type, Level)>> { None }

    /// A λ with unannotated binders may infer its result once the call knows
    /// their domains — the parameter's leading Π domains are meta-free — as
    /// an annotated λ would: the body's type is what teaches the codomain.
    fn infer_lambda_at_known_domains(
        &self, _cx: &Cx, _argument: &Expr, _parameter: &Type, _n: u32, _sols: &[Sol],
    ) -> Option<R<(Term, Type, Level)>> { None }

    /// Learn this call's metas from an argument's type against its
    /// parameter's. **Learn-only**: a failure is silent and decides nothing,
    /// so an inferred argument placed after this has not been compared with
    /// its domain at all. Reach it through [`OwedChecks::learn`], which
    /// records that comparison for the gate; the one direct call teaches a
    /// literal's counted length before the literal itself is checked.
    /// `meta_doms` are the declared types of the slots allocated so far: a
    /// solution read at a slot whose domain is known is held to it. Returns
    /// the slots already solved that the argument's type met with another
    /// subject, and that subject ([`SlotClash`]).
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
    ) -> Vec<(usize, Rc<Term>)>;

    /// Record that the argument at `span`, of type `got`, sits at a parameter
    /// of type `expected` (both in the committed world) with nothing in the
    /// elaborator having compared the two: the gate compares them, and this is
    /// the site its refusal is reported at. Recording, not probing — the
    /// checking forms' [`MismatchNotes::note_check_mismatch`](crate::mismatch_notes::MismatchNotes::note_check_mismatch). `clash` is
    /// an implicit this argument's type disagreed about, said beside the
    /// mismatch if there is one.
    #[allow(clippy::too_many_arguments)]
    fn note_argument_mismatch(&self, cx: &Cx, got: &Type, expected: &Type, level: &Level, span: Span, clash: Option<SlotClash>);

    #[allow(clippy::too_many_arguments)]
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
    ) -> R<()>;

    #[allow(clippy::too_many_arguments)]
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
    ) -> R<ObligationProgress>;

    #[allow(clippy::too_many_arguments)]
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
    ) -> R<()>;

    /// The **emission spelling** of a solved type metavariable's code, at the
    /// discharge (`docs/inductives/per-instantiation-type-codes-design.md` §5, amended
    /// 2026-09-10): the solution is quoted from the type the emission sites
    /// would write, so `M := List<BitVec(8)>` enters the spine's annotations
    /// as `El (app(List#tycode_fn^δ; …))` and the kernel's own instantiation
    /// of the callee's codomain at it yields that same reference instead of a
    /// third spelling. `dom` is the metavariable's declared domain, so only a
    /// slot at `Ty l` is a type argument at all. `None` keeps the solution.
    ///
    /// The solution is scoped in the **committed** world, not the scratch one:
    /// `apply_global`'s payloads are the substitution's target, and the
    /// identity region below them is renumbered past the metavariables.
    fn respell_solution(&self, _cx: &Cx, _dom: &Type, _solution: &Term) -> Option<Term> {
        None
    }

    /// Is `result`, a call's result type with every slot solved, the
    /// expected type? Conversion, committed world: what keeps a read of the
    /// expected type ahead of the arguments ([`propagate_expected`]) from
    /// keeping what a learn-only unification got wrong.
    fn result_agrees(&self, _cx: &Cx, _result: &Type, _expected: &Type, _level: &Level) -> bool {
        false
    }

    fn blocked_solver_error(
        &self,
        name: &str,
        params: &[ParamMeta],
        obligation: &ResolveOb,
        span: Span,
    ) -> crate::ElabError;

    /// Learn open slots from the types of the solved slots whose declared
    /// types mention them (`?x := a` with `a : K` teaches `?K`). `true` when
    /// it solved something.
    fn learn_from_solution_types(
        &self,
        _cx: &Cx,
        _meta_doms: &[Type],
        _n: u32,
        _sols: &mut [Sol],
        _span: Span,
    ) -> bool {
        false
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ArgumentClass {
    /// Reserve a deferred slot when the parameter type is still unsolved.
    /// Includes arguments that prefer checking but permit inference below.
    pub(crate) checking_only: bool,
    pub(crate) fallback_infer: bool,
}

/// Retry solver and checking-only obligations to a fixpoint.
///
/// Solver obligations run first because dictionaries may unblock argument
/// domains, while checking an argument cannot instantiate a withheld solver
/// slot. Each continuing pass fills at least one slot, which bounds the loop
/// by the number of obligations. Before promotion, result-only calls and
/// annotated callbacks may use their compatibility inference fallback;
/// after promotion they may not.
#[allow(clippy::too_many_arguments)]
pub(crate) fn retry_obligations(
    elab: &impl ImplicitApplicationElab,
    cx: &Cx,
    name: &str,
    params: &[ParamMeta],
    slot_param: &[usize],
    meta_doms: &[Type],
    n: u32,
    sols: &mut [Sol],
    resolves: &[ResolveOb],
    deferred: &[DeferredArg<'_>],
    owed: &mut OwedChecks,
    allow_fallback: bool,
    span: Span,
) -> R<()> {
    loop {
        // A solution's own type may pin a slot no read reached: the carrier
        // of a class theorem whose points a hypothesis solved
        // (issues/generic-theorem-implicit-points.md). Before the solver
        // obligations, whose goals it is what closes.
        let mut progressed = !resolves.is_empty()
            && elab.learn_from_solution_types(cx, meta_doms, n, sols, span);
        let mut blocked = false;
        for obligation in resolves {
            if !matches!(sols[obligation.slot], Sol::Withheld) {
                continue;
            }
            match elab.resolve_application_obligation(
                cx, name, params, slot_param, meta_doms, n, sols, obligation, span,
            )? {
                ObligationProgress::Blocked => blocked = true,
                ObligationProgress::Unblocked => {
                    progressed = true;
                    blocked = true;
                }
                ObligationProgress::Solved => progressed = true,
            }
        }
        for obligation in deferred {
            if !matches!(sols[obligation.slot], Sol::Withheld) {
                continue;
            }
            let Some(dom) = zonked(&obligation.dom, n, sols) else {
                blocked = true;
                continue;
            };
            let term = if crate::defaults::is_param_default(obligation.expr) {
                let Some(mentioned) = earlier_for_default(params, obligation.param, &obligation.earlier, n, sols) else {
                    blocked = true;
                    continue;
                };
                elab.check_param_default(cx, obligation.expr, &dom, &obligation.dom_level, &mentioned)?
            } else {
                let hint = params
                    .get(obligation.param)
                    .map(|p| (name, p.name.as_str()));
                let skel = params.get(obligation.param).and_then(|p| p.skel.as_deref());
                elab.check_explicit_argument(
                    cx,
                    obligation.expr,
                    &dom,
                    &obligation.dom_level,
                    hint,
                    skel,
                )?
            };
            sols[obligation.slot] = Sol::Solved(Rc::new(term));
            progressed = true;
        }
        if !progressed || !blocked {
            if allow_fallback && blocked {
                for obligation in deferred {
                    if !matches!(sols[obligation.slot], Sol::Withheld) { continue; }
                    let inferred = elab.infer_polymorphic_argument(cx, obligation.expr, &obligation.dom, n, sols)
                        .or_else(|| elab.infer_lambda_at_known_domains(cx,obligation.expr,&obligation.dom,n,sols));
                    if let Some(inferred) = inferred {
                        // A λ body that does not infer (`λ x => Nil`) is the
                        // body's error, but the cause the writer can act on is
                        // still the codomain nothing in the call pins.
                        let (term,ty,_) = match inferred {
                            Err(ElabError::Elab { msg, span: at }) if matches!(obligation.expr.kind, ExprKind::Lam { .. }) => {
                                return Err(ElabError::Elab {
                                    msg: unpinned_domain_message(name, params, slot_param, sols, obligation.param, &msg),
                                    span: at,
                                });
                            }
                            other => other?,
                        };
                        owed.learn(elab,cx,&obligation.dom,&obligation.dom_level,ty,n,sols,meta_doms,obligation.expr.span,obligation.expr.span);
                        sols[obligation.slot] = Sol::Solved(Rc::new(term));
                        progressed = true;
                        break;
                    }
                }
                if progressed { continue; }
            }
            // A literal falls back first: it always has its own type (`Nat`,
            // `Char`), and that may be what teaches an earlier argument its
            // domain (`first_then(Nil, 3)`), where the earlier one alone
            // would only fail.
            let waiting = |obligation: &&DeferredArg<'_>| obligation.fallback_infer && matches!(sols[obligation.slot], Sol::Withheld);
            let literal = |obligation: &&DeferredArg<'_>| matches!(obligation.expr.kind, ExprKind::Num(_) | ExprKind::Scaled(_) | ExprKind::Char(_));
            if allow_fallback
                && blocked
                && let Some(obligation) = deferred.iter().filter(waiting).find(literal).or_else(|| deferred.iter().find(waiting))
            {
                let (term, ty, _) = match elab.infer_application_argument(cx, obligation.expr) {
                    Err(ElabError::Elab { msg, span: at }) if obligation.replanned => {
                        return Err(ElabError::Elab {
                            msg: unpinned_domain_message(name, params, slot_param, sols, obligation.param, &msg),
                            span: at,
                        });
                    }
                    other => other?,
                };
                owed.learn(elab, cx, &obligation.dom, &obligation.dom_level, ty, n, sols, meta_doms, span, obligation.expr.span);
                sols[obligation.slot] = Sol::Solved(Rc::new(term));
                continue;
            }
            return Ok(());
        }
    }
}

/// Read the expected type into this call's slots before an argument that
/// would otherwise be inferred at a domain still waiting on them, as a
/// checked call's result is read in the end anyway: the argument is then
/// checked, and a literal or a λ inside it is elaborated knowing what it is
/// for (issues/surface-gaps-from-sha256-proof.md item 2). `true` when the
/// domain `dom` is solved by it, and the solutions are kept; otherwise every
/// slot is as it was, and the argument is inferred as before.
///
/// The result type is the callee's codomain past the remaining parameters:
/// an implicit is its slot, an argument that may wait is its reserved slot,
/// and any other argument is unknown here. So the read is made only when the
/// result does not mention those, which is checked by building it twice with
/// two different stand-ins and comparing; a call with arguments left over
/// for its result (a spill) or too few is not read either. The slots the
/// call holds back from unification (a solver's implicit, an argument that
/// will be checked) are held back here too.
#[allow(clippy::too_many_arguments)]
fn propagate_expected(
    elab: &impl ImplicitApplicationElab,
    cx: &Cx,
    params: &[ParamMeta],
    first_param: usize,
    rest_mask: &[bool],
    mut rest_args: std::slice::Iter<'_, Expr>,
    cod: &Type,
    cod_level: &Level,
    waits: &dyn Fn(&Expr) -> bool,
    next_meta: u32,
    n: u32,
    sols: &mut [Sol],
    meta_doms: &[Type],
    expected: &Type,
    owed: &OwedChecks,
    dom: &Type,
    span: Span,
) -> bool {
    let gamma = || LocalSubst::id(&cx.gamma);
    // How each remaining parameter is filled here: a slot, held back or
    // not; a local variable's or a `let`'s own term, whose type is known
    // without elaborating anything; or unknown.
    enum Take {
        Slot(bool),
        Local(Term, Type, Level),
        Unknown,
    }
    let mut takes = Vec::with_capacity(rest_mask.len());
    for (i, &implicit) in rest_mask.iter().enumerate() {
        if implicit {
            let solver = params.get(first_param + i).is_some_and(|p| p.solver.is_some());
            takes.push(Take::Slot(solver));
        } else {
            let Some(arg) = rest_args.next() else { return false };
            takes.push(if waits(arg) {
                Take::Slot(true)
            } else if let ExprKind::Var(name) = &arg.kind
                && (cx.names.contains(name) || cx.aliases.iter_inner().any(|alias| alias.name == *name))
                && let Ok((term, ty, level)) = elab.infer_application_argument(cx, arg)
            {
                Take::Local(term, ty, level)
            } else {
                Take::Unknown
            });
        }
    }
    if rest_args.next().is_some() {
        return false;
    }
    // The result past the remaining parameters, the slots' domains, the
    // held slots, and each local argument's domain beside its type.
    type Walked = (Type, Level, Vec<Type>, Vec<usize>, Vec<(Type, Type, Level)>);
    let walk = |stand_in: u64| -> Option<Walked> {
        let stand_in = Rc::new(Term::NatLit(stand_in.into()));
        let mut ty = cod.apply_local(&gamma().extended(Rc::clone(&stand_in)));
        let mut doms = meta_doms.to_vec();
        let mut held = Vec::new();
        let mut locals = Vec::new();
        let mut slot = next_meta;
        let mut level = cod_level.clone();
        for take in &takes {
            let Type::Pi { dom, cod, cod_level, dom_level } = elab.whnf_for_application(cx, &ty, n, span).ok()? else { return None };
            level = cod_level;
            let argument = match take {
                Take::Slot(hold) => {
                    doms.push((*dom).clone());
                    if *hold { held.push(slot as usize); }
                    slot += 1;
                    Rc::new(Term::GlobalTm { var: GlobalVar::index(slot - 1), subst: gamma() })
                }
                Take::Local(term, got, _) => {
                    locals.push(((*dom).clone(), got.clone(), dom_level));
                    Rc::new(term.shift_global(n))
                }
                Take::Unknown => Rc::clone(&stand_in),
            };
            ty = cod.apply_local(&gamma().extended(argument));
        }
        Some((ty, level, doms, held, locals))
    };
    let Some((result, level, doms, held, locals)) = walk(u64::MAX - 1) else { return false };
    let Some((other, _, other_doms, _, other_locals)) = walk(u64::MAX - 2) else { return false };
    if result != other || doms != other_doms || locals != other_locals || !slots_bare(cx, &result, n, sols) {
        return false;
    }
    let before = sols.to_vec();
    let postponed = owed.postponed().get();
    for &slot in &held {
        if matches!(sols[slot], Sol::Unsolved) { sols[slot] = Sol::Withheld; }
    }
    // A later local's type is read first, as its own turn will read it
    // (`trans(cong_fn(λ t => Pair(t, 48), p), q)`, where `q` says what the
    // first equation ends at); each read must settle its domain to the
    // local's type, or none is kept.
    let mut learned = true;
    for (dom, got, level) in &locals {
        elab.unify_application_argument_type(cx, dom, got, n, sols, &doms, Guesses::Postpone(owed.postponed()), span);
        if !zonked(dom, n, sols).is_some_and(|dom| elab.result_agrees(cx, &dom, got, level)) {
            learned = false;
            break;
        }
    }
    let read = if learned {
        elab.solve_application_from_expected(cx, &result, expected, n, sols, &doms, Guesses::Postpone(owed.postponed()), span)
    } else {
        Ok(())
    };
    for &slot in &held {
        if matches!(sols[slot], Sol::Withheld) && matches!(before[slot], Sol::Unsolved) { sols[slot] = Sol::Unsolved; }
    }
    // Unification here is learn-only, and may have kept half of a pairing
    // that failed (`?b ++ X` against `ys ++ D` solving `?b := ys`): kept only
    // when the result it solved is the expected type.
    if learned
        && read.is_ok()
        && zonked(dom, n, sols).is_some()
        && zonked(&result, n, sols).is_some_and(|result| elab.result_agrees(cx, &result, expected, &level))
    {
        return true;
    }
    sols.clone_from_slice(&before);
    owed.postponed().set(postponed);
    false
}

/// Does `e` hold a `·` that belongs to an enclosing section? Such a call's
/// expected type is the section's, after the slots are bound, and an
/// argument slot must fail to infer to escape to it.
fn has_free_slot(e: &Expr) -> bool {
    let mut found = false;
    crate::surface::for_each_free_slot(e, &mut |_, _| found = true);
    found
}

/// Does every slot `result` still waits on stand bare where it occurs, as an
/// endpoint of an equation or its type, or as a type itself? Only such a
/// slot is read off the expected type and not guessed at: `a = ?c` against
/// `a = mk(b)` says `?c` is `mk(b)`, but `BitVec(?m + ?n)` against
/// `BitVec(63 + 1)` does not say `?n` is `1`, though unifying the sums
/// pairwise would conclude it and the conversion would agree.
fn slots_bare(cx: &Cx, result: &Type, n: u32, sols: &[Sol]) -> bool {
    let term = |t: &Term| {
        zonked_tm(t, n, sols).is_some()
            || matches!(t, Term::GlobalTm { var, subst }
                if var.innermost(n).is_some() && *subst == LocalSubst::id(&cx.gamma))
    };
    fn ty(t: &Type, term: &dyn Fn(&Term) -> bool, n: u32, sols: &[Sol]) -> bool {
        match t {
            Type::Id { ty: of, lhs, rhs, .. } => ty(of, term, n, sols) && term(lhs) && term(rhs),
            Type::El { tm, .. } => term(tm),
            other => zonked(other, n, sols).is_some(),
        }
    }
    ty(result, &term, n, sols)
}

/// The earlier arguments `param`'s default mentions, out of the scratch
/// world: `None` while one of them, or its type, still waits on this call's
/// metas — an implicit not yet learned, or an earlier default not yet
/// filled — so the default waits with it (docs/language/named-arguments-design.md
/// §9.6). A default that mentions no parameter is ready at once and
/// allocates nothing.
fn earlier_for_default(
    params: &[ParamMeta],
    param: usize,
    earlier: &[EarlierArg],
    n: u32,
    sols: &[Sol],
) -> Option<Vec<EarlierArg>> {
    let mentioned = crate::defaults::mentioned_parameters(params, param);
    earlier
        .iter()
        .filter(|e| mentioned.contains(&e.param))
        .map(|e| {
            Some(EarlierArg {
                param: e.param,
                term: Rc::new(zonked_tm(&e.term, n, sols)?),
                ty: zonked(&e.ty, n, sols)?,
                level: e.level.clone(),
            })
        })
        .collect()
}

/// The error for a re-planned argument whose domain never resolved. The
/// argument is already where the inference error's advice would put it, so
/// the note names the cause that advice cannot: the callee's implicit that
/// nothing in the call pinned
/// (issues/record-partial-application-under-inferred-callee.md).
fn unpinned_domain_message(
    name: &str,
    params: &[ParamMeta],
    slot_param: &[usize],
    sols: &[Sol],
    param: usize,
    inner: &str,
) -> String {
    let pending: Vec<&ParamMeta> = slot_param
        .iter()
        .enumerate()
        .filter(|&(slot, _)| matches!(sols.get(slot), Some(Sol::Unsolved)))
        .filter_map(|(_, &p)| params.get(p))
        .filter(|p| p.implicit && p.solver.is_none())
        .collect();
    let unpinned: Vec<String> = pending.iter().map(|p| format!("`{}`", p.name)).collect();
    let spelling = written_implicits(name, &pending);
    let what = match unpinned.as_slice() {
        [] => "an implicit argument".to_string(),
        [one] => format!("the implicit {one}"),
        many => format!("the implicits {}", many.join(", ")),
    };
    let param = params.get(param).map_or("its parameter".to_string(), |p| format!("`{}`", p.name));
    // The inner error leads: an unbound name is still read first. The note
    // is true wherever this runs — the domain never resolved.
    format!(
        "{inner}. Here the argument is checked against {param}'s type in `{name}`, and \
         that type still mentions {what}, which nothing in the call determines: \
         write it (`{spelling}`) or pass an argument that fixes it"
    )
}

/// How a call writes the implicits it could not infer: a type argument in
/// `<…>`, a value implicit by name (`Float::Le(F := …, …)`) — `<…>` is refused
/// for a value, so suggesting it for one sends the writer to a second error
/// (issues/value-param-constructor-implicit-inference.md, ask 2).
fn written_implicits(name: &str, pending: &[&ParamMeta]) -> String {
    let types = pending.is_empty() || pending.iter().any(|p| p.is_type);
    let values: Vec<String> =
        pending.iter().filter(|p| !p.is_type).map(|p| format!("{} := …", p.name)).collect();
    match (types, values.is_empty()) {
        (_, true) => format!("{name}<…>(…)"),
        (false, false) => format!("{name}({}, …)", values.join(", ")),
        (true, false) => format!("{name}<…>({}, …)", values.join(", ")),
    }
}

/// The implicitness skeleton of a surface-written function type
/// (`docs/language/implicit-binders-design.md` §2).
///
/// Positional entry `i` speaks for the `i`-th Π along the written spine and
/// for no Π past `params.len()`. A reduced codomain can expose further Πs,
/// but those are explicit by the degradation rule. Skeletons contain no terms,
/// de Bruijn indices, or resolved names, so substitution and shifting have
/// nothing to update (§3.2).
#[derive(Clone, Debug)]
pub(crate) struct Skel {
    pub(crate) params: Vec<SkelBinder>,
}

#[derive(Clone, Debug)]
pub(crate) struct SkelBinder {
    /// Written binder name, used only for diagnostics and goal-name hints.
    pub(crate) name: Option<String>,
    pub(crate) implicit: bool,
    /// Whether the written domain was `Type<n>`.
    pub(crate) is_type: bool,
    /// The written domain's own callable skeleton.
    pub(crate) dom: Option<Rc<Skel>>,
}

impl Skel {
    pub(crate) fn leading_implicit(&self) -> usize {
        self.params.iter().take_while(|b| b.implicit).count()
    }
}

/// Derive a type's skeleton, purely syntactically.
///
/// Sparse by rule: an anonymous, entirely explicit arrow allocates nothing.
/// The codomain chain flattens while domain skeletons remain nested.
pub(crate) fn skel_of_ty(ty: &Ty) -> Option<Rc<Skel>> {
    let mut params = Vec::new();
    let mut any = false;
    let mut cur = ty;
    while let TyKind::Fn {
        binder,
        implicit,
        dom,
        cod,
    } = &cur.kind
    {
        let dom_skel = skel_of_ty(dom);
        any |= binder.is_some() || *implicit || dom_skel.is_some();
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

/// The skeleton of a written lambda's binder marks. Prefix authority applies:
/// it describes only the binders the lambda writes, not a callable result its
/// body may return.
pub(crate) fn skel_of_lam_binders(binders: &[LamBinder]) -> Option<Rc<Skel>> {
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

/// Does an implicit mark occur anywhere in this surface type? Callers use this
/// when no skeleton consumer exists and silently dropping a mark is forbidden.
pub(crate) fn has_implicit_mark(ty: &Ty) -> bool {
    match &ty.kind {
        TyKind::Fn {
            implicit, dom, cod, ..
        } => *implicit || has_implicit_mark(dom) || has_implicit_mark(cod),
        TyKind::Named { args, .. } => args.iter().any(has_implicit_mark),
        TyKind::Vec { elem, .. } => has_implicit_mark(elem),
        TyKind::Squash(inner) => has_implicit_mark(inner),
        TyKind::Code { ty, .. } => has_implicit_mark(ty),
        TyKind::Nat
        | TyKind::Eq(..)
        | TyKind::Univ { .. }
        | TyKind::OfExpr(_)
        | TyKind::TypeOf(_)
        | TyKind::Fin(_)
        | TyKind::Ctx
        | TyKind::TyCode { .. }
        | TyKind::Splice { .. } => false,
    }
}

/// One parameter of a callable global, in declaration/telescope order.
///
/// The name is API: a hole in this argument position defaults to that name.
pub(crate) struct ParamMeta {
    pub(crate) name: String,
    /// A `{}` parameter filled by unification at call sites.
    pub(crate) implicit: bool,
    /// A leading `<A, B>` type parameter, distinct from other implicits.
    pub(crate) is_type: bool,
    /// Written `self p: T`, identifying the method receiver position.
    pub(crate) is_self: bool,
    /// Callable metadata for the parameter's own written domain.
    pub(crate) skel: Option<Rc<Skel>>,
    /// A `requires`/`:= infer` parameter filled by trait resolution.
    pub(crate) solver: Option<Rc<Ty>>,
    /// A `p: T := e` parameter filled from its default when a call leaves
    /// it out (docs/language/named-arguments-design.md §9).
    pub(crate) default: Option<Rc<ParamDefault>>,
}

/// A parameter's default as the declaration wrote it: the expression and
/// the name-resolution scope it was written in, which is where its names
/// resolve at every call (docs/language/named-arguments-design.md §9.4).
pub(crate) struct ParamDefault {
    pub(crate) expr: Expr,
    pub(crate) scope: Rc<crate::names::Scope>,
    /// The declaring global's key and this parameter's index in its table:
    /// what a call's omitted-default marker carries, so the default is found
    /// again without resolving any name at the call.
    pub(crate) owner: String,
    pub(crate) index: usize,
}

/// Synthesize the parameter table a value callee offers from its skeleton.
pub(crate) fn skel_params(skel: &Skel) -> Rc<Vec<ParamMeta>> {
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
                default: None,
            })
            .collect(),
    )
}

/// The only expression-elaboration capabilities an explicit application uses.
pub(crate) trait ExplicitArgElab {
    /// The weak head of a callee's (remaining) type, to read its next `Π`
    /// off. `scratch` is the width of the world `ty` is scoped in: zero for
    /// the committed world, `n` inside an implicit application, whose `n`
    /// metavariables sit at the global indices below every committed
    /// binding. The width is part of the question, not a detail of it: δ
    /// reads a global's body by index, so a scratch-world type reduced as
    /// if it were committed unfolds a *different* definition for every
    /// global it mentions — `u9` names the binding nine deep, not the
    /// definition two deep that the call meant — and substitutes a body
    /// built for another context into this one
    /// (issues/merged-call-through-upcast-panics.md).
    fn whnf_for_application(&self, cx: &Cx, ty: &Type, scratch: u32, span: Span) -> R<Type>;

    /// The emission spelling of an `App`'s `dom`/`cod` annotations
    /// (issues/emission-site-respell-audit.md): every component that is a
    /// registered declaration's lowering as its `El (D#tycode^δ)` reference.
    /// A global callee's annotations arrive that way already, off its
    /// respelled Ψ statement; a **local** callee's arrive off the binder's
    /// inline type, and an inline annotation embedded in a statement — the
    /// `equation: … = operation(…)` of a lemma, a record field's
    /// `run(state.gprs)` — then met its respelled twin at every use
    /// (`Sigma`/`Sigma` 450 and `Pi`/`Pi` 150 queries of the five-node
    /// FunctionIR/x86 module, 2026-09-06). `scratch` is the width of the
    /// application's metavariable world, zero in the committed one. `None`
    /// keeps the originals; only the emitted term changes — the type the
    /// application continues with stays the structural copy.
    fn respell_application_annotations(
        &self,
        _cx: &Cx,
        _dom: &Type,
        _cod: &Type,
        _scratch: u32,
    ) -> Option<(Option<Type>, Option<Type>)> {
        None
    }

    fn check_explicit_argument(
        &self,
        cx: &Cx,
        arg: &Expr,
        expected: &Type,
        level: &Level,
        hint: Option<(&str, &str)>,
        skel: Option<&Skel>,
    ) -> R<Term>;

    /// An omitted default's marker ([`PARAM_DEFAULT`]), checked at the
    /// parameter's instantiated domain with the call's `earlier` arguments,
    /// which a default that mentions an earlier parameter reads by that
    /// parameter's name (docs/language/named-arguments-design.md §9.6). The fakes have
    /// no defaults and check it as any other argument.
    fn check_param_default(
        &self,
        cx: &Cx,
        arg: &Expr,
        expected: &Type,
        level: &Level,
        _earlier: &[EarlierArg],
    ) -> R<Term> {
        self.check_explicit_argument(cx, arg, expected, level, None, None)
    }

    /// Whether an application is written `app@(f; a)` here
    /// (`docs/elaborator/app-by-head-type-design.md` §6.1): outside a quotation. The
    /// fakes answer `false` and keep the annotated form their tests read.
    fn emits_checked_applications(&self, _cx: &Cx) -> bool {
        false
    }
}

/// One node of an application spine as it is written
/// (`docs/elaborator/app-by-head-type-design.md` §6.1): `app@(f; a)`, whose Π is the one
/// `f` infers, wherever the checked spellings are admitted and the head is
/// not a λ (a λ infers only if its body does); otherwise the annotated `app`
/// with its annotations respelled. `scratch` is the width of the
/// application's metavariable world. The Π the caller walked is unchanged
/// either way — only the written node differs, and with `app@` goes the
/// per-node respell of `dom` and `cod` that the annotated form pays.
#[allow(clippy::too_many_arguments)]
fn emit_app(
    elab: &impl ExplicitArgElab,
    cx: &Cx,
    fun: Term,
    dom_level: Level,
    cod_level: Level,
    dom: Rc<Type>,
    cod: Rc<Type>,
    arg: Rc<Term>,
    scratch: u32,
) -> Term {
    if elab.emits_checked_applications(cx) && !matches!(fun, Term::Lam { .. }) {
        return Term::AppAt { fun: Rc::new(fun), arg };
    }
    let (dom, cod) = emitted_annotations(elab, cx, dom, cod, scratch);
    Term::App { fun: Rc::new(fun), dom_level, cod_level, dom, cod, arg }
}

/// `dom`/`cod` as an emitted `App` spells them
/// ([`ExplicitArgElab::respell_application_annotations`]), sharing the
/// originals wherever nothing respells.
fn emitted_annotations(
    elab: &impl ExplicitArgElab,
    cx: &Cx,
    dom: Rc<Type>,
    cod: Rc<Type>,
    scratch: u32,
) -> (Rc<Type>, Rc<Type>) {
    match elab.respell_application_annotations(cx, &dom, &cod, scratch) {
        Some((nd, nc)) => (
            nd.map_or(dom, Rc::new),
            nc.map_or(cod, Rc::new),
        ),
        None => (dom, cod),
    }
}

/// Apply an already-elaborated head to explicit surface arguments.
///
/// This is the stage-1 path reused by `@` calls and callees with no implicit
/// parameters. Fewer arguments than Πs is partial application. `params` comes
/// from the caller that resolved the head rather than being recovered here, so
/// a local value can never borrow a same-named global's metadata.
/// `param_offset` records Πs already consumed by written type arguments and
/// keeps argument-hole hints aligned with their source parameters.
#[allow(clippy::too_many_arguments)]
pub(crate) fn apply_explicit(
    elab: &impl ExplicitArgElab,
    cx: &Cx,
    name: Option<&str>,
    params: Rc<Vec<ParamMeta>>,
    param_offset: usize,
    head: Term,
    ty: Type,
    lvl: Level,
    args: &[Expr],
) -> R<(Term, Type, Level)> {
    let (mut term, mut ty, mut lvl) = (head, ty, lvl);
    let what = name.map_or_else(|| "this function".to_string(), |n| format!("`{n}`"));
    // The arguments so far, kept only for a call that leaves a default to
    // fill, which may mention them (§9.6).
    let defaults = args.iter().any(crate::defaults::is_param_default);
    let mut earlier: Vec<EarlierArg> = Vec::new();
    // Every node written `app@` (§6.1 of the app design): nothing needs a
    // node's own `dom`/`cod`, so while the telescope stays a syntactic Π the
    // arguments are held in `delta` and each domain is instantiated under
    // the ones before it, the codomain once at the end — not the remaining
    // telescope per argument, which copies every earlier argument once per
    // mention. `ty` is `ty[delta]` while `delta` is held. The whnf of a
    // syntactic Π is itself.
    if elab.emits_checked_applications(cx) && !matches!(term, Term::Lam { .. }) {
        let mut delta: Option<LocalSubst> = None;
        for (i, arg) in args.iter().enumerate() {
            let head = match (&delta, &ty) {
                (_, Type::Pi { .. }) => ty.clone(),
                (Some(held), _) => {
                    ty = ty.apply_local(held);
                    delta = None;
                    elab.whnf_for_application(cx, &ty, 0, arg.span)?
                }
                (None, _) => elab.whnf_for_application(cx, &ty, 0, arg.span)?,
            };
            let Type::Pi { dom_level, cod_level, dom, cod } = head else {
                return err(format!("{what} is applied to too many arguments"), arg.span);
            };
            let dom = match &delta {
                Some(held) => Rc::new(dom.apply_local(held)),
                None => dom,
            };
            let param = params.get(i + param_offset);
            let hint = name.zip(param).map(|(n, p)| (n, p.name.as_str()));
            let skel = param.and_then(|p| p.skel.as_deref());
            let arg = Rc::new(if crate::defaults::is_param_default(arg) {
                elab.check_param_default(cx, arg, &dom, &dom_level, &earlier)?
            } else {
                elab.check_explicit_argument(cx, arg, &dom, &dom_level, hint, skel)?
            });
            if defaults {
                earlier.push(EarlierArg { param: i + param_offset, term: Rc::clone(&arg), ty: (*dom).clone(), level: dom_level.clone() });
            }
            delta = Some(delta.take().unwrap_or_else(|| LocalSubst::id(&cx.gamma)).extended(Rc::clone(&arg)));
            ty = (*cod).clone();
            lvl = cod_level;
            term = Term::AppAt { fun: Rc::new(term), arg };
        }
        if let Some(held) = delta {
            ty = ty.apply_local(&held);
        }
        return Ok((term, ty, lvl));
    }
    for (i, arg) in args.iter().enumerate() {
        let head = elab.whnf_for_application(cx, &ty, 0, arg.span)?;
        let Type::Pi {
            dom_level,
            cod_level,
            dom,
            cod,
        } = head
        else {
            return err(format!("{what} is applied to too many arguments"), arg.span);
        };
        let param = params.get(i + param_offset);
        let hint = name.zip(param).map(|(n, p)| (n, p.name.as_str()));
        let skel = param.and_then(|p| p.skel.as_deref());
        let arg = if crate::defaults::is_param_default(arg) {
            elab.check_param_default(cx, arg, &dom, &dom_level, &earlier)?
        } else {
            elab.check_explicit_argument(cx, arg, &dom, &dom_level, hint, skel)?
        };
        let arg = Rc::new(arg);
        if defaults {
            earlier.push(EarlierArg { param: i + param_offset, term: Rc::clone(&arg), ty: (*dom).clone(), level: dom_level.clone() });
        }
        ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&arg)));
        lvl = cod_level.clone();
        term = emit_app(elab, cx, term, dom_level, cod_level, dom, cod, arg, 0);
    }
    Ok((term, ty, lvl))
}

/// Apply a callable while inserting its implicit and solver parameters.
///
/// This owns the complete scratch-world lifecycle: a static slot plan, the
/// Π walk, deferred arguments, spill-based and expected-type learning,
/// promotion, diagnostics, global discharge, and explicit overapplication.
/// Session and declaration state enter only through [`ImplicitApplicationElab`].
#[allow(clippy::too_many_arguments)]
pub(crate) fn apply_implicit(
    elab: &impl ImplicitApplicationElab,
    cx: &Cx,
    name: &str,
    params: Rc<Vec<ParamMeta>>,
    value_head: bool,
    param_offset: usize,
    bare_ref: bool,
    head: Term,
    callee_ty: Type,
    callee_lvl: Level,
    args: &[Expr],
    mask: &[bool],
    expected: Option<&Type>,
    promote_unsolved: bool,
    span: Span,
) -> R<(Term, Type, Level)> {
    // Arguments re-planned as deferrable after their inference failed at a
    // domain still waiting on this call's implicits. Each argument is added
    // at most once, so the restarts are bounded by the argument count, and a
    // call none of whose arguments fails this way runs exactly once.
    let mut forced: Vec<usize> = Vec::new();
    loop {
        let restart = std::cell::Cell::new(None);
        match apply_implicit_planned(
            elab,
            cx,
            name,
            Rc::clone(&params),
            value_head,
            param_offset,
            bare_ref,
            head.clone(),
            callee_ty.clone(),
            callee_lvl.clone(),
            args,
            mask,
            expected,
            promote_unsolved,
            span,
            &forced,
            &restart,
        ) {
            Err(e) => match restart.get() {
                Some(i) if !forced.contains(&i) => forced.push(i),
                _ => return Err(e),
            },
            done => return done,
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn apply_implicit_planned(
    elab: &impl ImplicitApplicationElab,
    cx: &Cx,
    name: &str,
    params: Rc<Vec<ParamMeta>>,
    value_head: bool,
    param_offset: usize,
    bare_ref: bool,
    head: Term,
    callee_ty: Type,
    callee_lvl: Level,
    args: &[Expr],
    mask: &[bool],
    expected: Option<&Type>,
    promote_unsolved: bool,
    span: Span,
    forced: &[usize],
    restart: &std::cell::Cell<Option<usize>>,
) -> R<(Term, Type, Level)> {
    let forced_at = |arg: &Expr| forced.iter().any(|&i| std::ptr::eq(&args[i], arg));
    let plan = ImplicitPlan::new(mask, args, |arg| {
        elab.classify_application_argument(cx, arg).checking_only || forced_at(arg)
    });
    let n = plan.scratch_len();
    let mut term = head.shift_global(n);
    let mut ty = callee_ty.shift_global(n);
    let mut level = callee_lvl;
    let mut sols = vec![Sol::Unsolved; n as usize];
    crate::unification::clear_level_declines();
    let mut meta_doms = Vec::with_capacity(n as usize);
    let mut meta_lvls = Vec::with_capacity(n as usize);
    let mut slot_param = Vec::with_capacity(n as usize);
    let mut explicit_doms = Vec::new();
    let mut deferred = Vec::new();
    let mut resolves = Vec::new();
    let mut owed = OwedChecks::default();
    let mut next_meta = 0u32;
    let mut arguments = args.iter();
    // The spine so far, scratch world, kept only for a call that leaves a
    // default to fill, which may mention an earlier argument (§9.6).
    let defaults = args.iter().any(crate::defaults::is_param_default);
    let mut earlier: Vec<EarlierArg> = Vec::new();
    // The expected type has been read into the slots ahead of the arguments
    // ([`propagate_expected`]); once is enough.
    let mut propagated = false;

    for step in plan.steps(param_offset) {
        let parameter = step.parameter;
        let head_ty = elab.whnf_for_application(cx, &ty, n, span)?;
        let Type::Pi {
            dom_level,
            cod_level,
            dom,
            cod,
        } = head_ty
        else {
            return err(format!("`{name}` is applied to too many arguments"), span);
        };
        let argument = if step.implicit {
            let meta = Term::GlobalTm {
                var: GlobalVar::index(next_meta),
                subst: LocalSubst::id(&cx.gamma),
            };
            if params
                .get(parameter)
                .is_some_and(|parameter| parameter.solver.is_some())
            {
                sols[next_meta as usize] = Sol::Withheld;
                resolves.push(ResolveOb {
                    slot: next_meta as usize,
                    dom: (*dom).clone(),
                    dom_level: dom_level.clone(),
                    param: parameter,
                    applied: Some(term.clone()),
                });
            }
            meta_doms.push((*dom).clone());
            meta_lvls.push(dom_level.clone());
            slot_param.push(parameter);
            next_meta += 1;
            Rc::new(meta)
        } else {
            let Some(argument) = arguments.next() else {
                // Out of arguments with only explicit parameters left: the
                // call is a partial application, the function of the rest
                // (issues/declaration-partial-application.md) — where a
                // function is what is wanted, which is any position that
                // states no result type or states a `Π`. A position that
                // states another type keeps the arity error, which says
                // more than a mismatch against the partial call's `Π` would.
                let rest = parameter - param_offset;
                let only_explicit = mask[rest..].iter().all(|&implicit| !implicit)
                    && params[parameter..].iter().all(|p| p.default.is_none() && p.solver.is_none());
                let wants_function = match expected {
                    None => true,
                    Some(expected) => {
                        matches!(elab.whnf_for_application(cx, expected, 0, span)?, Type::Pi { .. })
                    }
                };
                if only_explicit && wants_function {
                    break;
                }
                return err(format!("`{name}` is applied to too few arguments"), span);
            };
            explicit_doms.push((parameter, (*dom).clone()));
            let mut class = elab.classify_application_argument(cx, argument);
            // Re-planned after its inference failed: deferred, and inferred
            // again (reporting its own error) only if its domain never
            // resolves.
            if forced_at(argument) {
                class.checking_only = true;
                class.fallback_infer = true;
            }
            // A collection literal is checking-only, but its *length* is not
            // inferred — it is counted. At a vector domain whose length is
            // still a meta, `[a, b, c]` teaches `len := 3` before the deferral
            // decision below, so `from_bits([y, False, True])` checks where
            // nothing else pins the width
            // (issues/vector-literal-length-pins-implicit.md). The literal's
            // type is built in the committed world, so this needs the element
            // type solved already; learn-only, and the kernel judges.
            if class.checking_only
                && let ExprKind::CollectionLit(items) = &argument.kind
                && let Type::Vec { level, elem, .. } = &*dom
                && zonked(&dom, n, &sols).is_none()
                && let Some(elem) = zonked(elem, n, &sols)
            {
                let counted = Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(elem),
                    len: Rc::new(Term::NatLit((items.len() as u64).into())),
                };
                elab.unify_application_argument_type(cx, &dom, &counted, n, &mut sols, &meta_doms, Guesses::Take, span);
            }
            // A default waits for the earlier arguments it mentions as well
            // as for its domain.
            let is_default = crate::defaults::is_param_default(argument);
            let ready = zonked(&dom, n, &sols).and_then(|real_dom| {
                let mentioned = if is_default {
                    earlier_for_default(&params, parameter, &earlier, n, &sols)?
                } else {
                    Vec::new()
                };
                Some((real_dom, mentioned))
            });
            match ready {
                Some((real_dom, mentioned)) => {
                    let hint = params
                        .get(parameter)
                        .map(|parameter| (name, parameter.name.as_str()));
                    let skel = params
                        .get(parameter)
                        .and_then(|parameter| parameter.skel.as_deref());
                    let checked = if is_default {
                        elab.check_param_default(cx, argument, &real_dom, &dom_level, &mentioned)?
                    } else {
                        elab.check_explicit_argument(cx, argument, &real_dom, &dom_level, hint, skel)?
                    };
                    if class.checking_only {
                        sols[next_meta as usize] = Sol::Solved(Rc::new(checked.clone()));
                        meta_doms.push((*dom).clone());
                        meta_lvls.push(dom_level.clone());
                        slot_param.push(parameter);
                        next_meta += 1;
                    }
                    Rc::new(checked.shift_global(n))
                }
                None if class.checking_only => {
                    let meta = Term::GlobalTm {
                        var: GlobalVar::index(next_meta),
                        subst: LocalSubst::id(&cx.gamma),
                    };
                    sols[next_meta as usize] = Sol::Withheld;
                    deferred.push(DeferredArg {
                        slot: next_meta as usize,
                        expr: argument,
                        dom: (*dom).clone(),
                        dom_level: dom_level.clone(),
                        param: parameter,
                        fallback_infer: class.fallback_infer,
                        replanned: forced_at(argument),
                        earlier: if is_default { earlier.clone() } else { Vec::new() },
                    });
                    meta_doms.push((*dom).clone());
                    meta_lvls.push(dom_level.clone());
                    slot_param.push(parameter);
                    next_meta += 1;
                    Rc::new(meta)
                }
                // About to be inferred blind, though the expected type may
                // say what its domain is: `trans(h, cong_fn(λ t => Pair(t,
                // 48), p))`, whose `b = ?c` only the expected type completes.
                // Inferred, the λ's `48` defaults to `Nat` before anything
                // says the pair's second field is a word.
                // A name's type is its own, so only an argument that is
                // elaborated (a call, a block, a λ) has a use for it.
                None if !propagated
                    && !matches!(argument.kind, ExprKind::Var(_) | ExprKind::ArgSlot(_))
                    && let Some(expected) = expected
                    && !args.iter().any(has_free_slot)
                    && propagate_expected(
                        elab, cx, &params, parameter + 1, &mask[parameter - param_offset + 1..], arguments.clone(), &cod, &cod_level,
                        &|arg| elab.classify_application_argument(cx, arg).checking_only || forced_at(arg),
                        next_meta, n, &mut sols, &meta_doms, expected, &owed, &dom, span,
                    ) =>
                {
                    propagated = true;
                    let real_dom = zonked(&dom, n, &sols).expect("propagate_expected settled the domain");
                    let hint = params.get(parameter).map(|parameter| (name, parameter.name.as_str()));
                    let skel = params.get(parameter).and_then(|parameter| parameter.skel.as_deref());
                    let checked = elab.check_explicit_argument(cx, argument, &real_dom, &dom_level, hint, skel)?;
                    Rc::new(checked.shift_global(n))
                }
                None => {
                    let inferred = elab.infer_application_argument(cx, argument);
                    // A call that does not infer on its own may only be
                    // missing what this position's domain will say once a
                    // later argument, or the expected type, has pinned it:
                    // `band(iterate_increment(zero(), 3), y)`, where `y` fixes
                    // the width `zero()` needs. The scratch world's size is
                    // fixed by the plan, so the call is re-planned with this
                    // argument deferrable ([`apply_implicit`]'s restart) —
                    // on this failure path only, so a call that elaborates
                    // today is never re-planned
                    // (issues/nested-uninferable-argument-under-checking.md).
                    // A bare name is the same case with no arguments: a
                    // record's type former read at `?A -> Type` infers as its
                    // constructor and fails, and only the solved domain picks
                    // the type former — `takes(Grammar, 1)`
                    // (issues/record-partial-application-under-inferred-callee.md).
                    let (inferred, inferred_ty, _) = match inferred {
                        Err(e @ ElabError::Elab { .. })
                            if matches!(
                                argument.kind,
                                ExprKind::App { .. } | ExprKind::Dot { .. } | ExprKind::Var(_)
                            ) =>
                        {
                            restart.set(args.iter().position(|a| std::ptr::eq(a, argument)));
                            return Err(e);
                        }
                        // A projection section (`·.count`) at a function
                        // domain still waiting on this call's implicits:
                        // the position is function-typed whatever solves
                        // it, so it owns the slot, and the section waits
                        // like an unannotated lambda — `apply_to(·.count, c)`
                        // (issues/field-projection-sections.md). Projection
                        // sections only: a bare `·` here has always escaped
                        // to the enclosing section.
                        Err(e @ ElabError::ArgSlotEscape { .. })
                            if matches!(&*dom, Type::Pi { .. })
                                && is_projection_section(argument) =>
                        {
                            restart.set(args.iter().position(|a| std::ptr::eq(a, argument)));
                            return Err(e);
                        }
                        other => other?,
                    };
                    // A name with two readings (a hypothesis a match
                    // refined, its equation) is the one this parameter
                    // accepts (docs/language/matching/arm-readings-design.md).
                    let (inferred, inferred_ty) = match &argument.kind {
                        ExprKind::Var(name) if cx.readings.iter_inner().any(|r| &r.name == name) => {
                            // Where the parameter's type is known, conversion
                            // decides. Where implicits are still open, the
                            // name as it elaborated stands unless it clashes
                            // with one already solved, and another reading
                            // takes its place only if it settles the
                            // parameter's type at its own.
                            let learns = |ty: &Type| {
                                let mut trial = sols.to_vec();
                                let clashes = elab.unify_application_argument_type(
                                    cx, &dom, ty, n, &mut trial, &meta_doms,
                                    Guesses::Postpone(&std::cell::Cell::new(false)), span,
                                );
                                (clashes.is_empty(), zonked(&dom, n, &trial))
                            };
                            let fits = |ty: &Type, first: bool| match zonked(&dom, n, &sols) {
                                Some(real) => elab.argument_type_converts(cx, ty, &real, &dom_level),
                                None => match learns(ty) {
                                    (false, _) => false,
                                    (true, _) if first => true,
                                    (true, Some(real)) => elab.argument_type_converts(cx, ty, &real, &dom_level),
                                    (true, None) => false,
                                },
                            };
                            let readings = elab.argument_readings(cx, &inferred);
                            if readings.is_empty() || fits(&inferred_ty, true) {
                                (inferred, inferred_ty)
                            } else {
                                readings.into_iter().find(|(_, ty)| fits(ty, false)).unwrap_or((inferred, inferred_ty))
                            }
                        }
                        _ => (inferred, inferred_ty),
                    };
                    owed.learn(elab, cx, &dom, &dom_level, inferred_ty, n, &mut sols, &meta_doms, span, argument.span);
                    Rc::new(inferred.shift_global(n))
                }
            }
        };
        if defaults {
            earlier.push(EarlierArg { param: parameter, term: Rc::clone(&argument), ty: (*dom).clone(), level: dom_level.clone() });
        }
        ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&argument)));
        level = cod_level.clone();
        term = emit_app(elab, cx, term, dom_level, cod_level, dom, cod, argument, n);
    }

    // Arguments beyond the declared mask spill onto a callable result. While
    // an implicit remains unknown, an inferable spill may still teach it.
    let mut spill: Vec<Expr> = arguments.cloned().collect();
    if !spill.is_empty() && sols.iter().any(|solution| solution.solved().is_none()) {
        let mut taken = 0;
        while taken < spill.len() && sols.iter().any(|solution| solution.solved().is_none()) {
            let head_ty = elab.whnf_for_application(cx, &ty, n, span)?;
            let Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } = head_ty
            else {
                break;
            };
            let argument = &spill[taken];
            // A spilled argument whose domain is already known is checked
            // there and passed, so that a later one may still teach:
            // `pieces_add(4, 16, 16 * k, xs)`, whose `A` occurs only under
            // the result's binders, is fixed by `xs` after the `Nat`
            // (issues/surface-gaps-from-sha256-proof.md item 3).
            if let Some(real_dom) = zonked(&dom, n, &sols) {
                let checked = elab.check_explicit_argument(cx, argument, &real_dom, &dom_level, None, None)?;
                let argument = Rc::new(checked.shift_global(n));
                ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&argument)));
                level = cod_level.clone();
                term = emit_app(elab, cx, term, dom_level, cod_level, dom, cod, argument, n);
                taken += 1;
                continue;
            }
            if elab.classify_application_argument(cx, argument).checking_only {
                break;
            }
            // A spill only *teaches* here: the call does not need it to, since
            // every spilled argument is checked against its zonked domain
            // below. So an argument that does not infer on its own stops the
            // teaching instead of refusing the call — the restart's reading
            // of the same failure in the declared spine above, where the
            // argument is re-planned rather than reported. A constructor
            // value is the usual one: `not_apart_of_same(a, b, h, Inl(l))`,
            // whose `¬ Apart(a, b)` unfolds to a `Π` that `Inl` only checks
            // against.
            let (inferred, inferred_ty, _) = match elab.infer_application_argument(cx, argument) {
                Err(ElabError::Elab { .. })
                    if matches!(
                        argument.kind,
                        ExprKind::App { .. } | ExprKind::Dot { .. } | ExprKind::Var(_)
                    ) =>
                {
                    break;
                }
                other => other?,
            };
            owed.learn(elab, cx, &dom, &dom_level, inferred_ty, n, &mut sols, &meta_doms, span, argument.span);
            let argument = Rc::new(inferred.shift_global(n));
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&argument)));
            level = cod_level.clone();
            term = emit_app(elab, cx, term, dom_level, cod_level, dom, cod, argument, n);
            taken += 1;
        }
        spill.drain(..taken);
    }

    let expected = expected.filter(|_| spill.is_empty());
    if let Some(expected) = expected
        && sols.iter().any(|solution| solution.solved().is_none())
    {
        elab.solve_application_from_expected(cx, &ty, expected, n, &mut sols, &meta_doms, Guesses::Postpone(owed.postponed()), span)?;
    }
    // Every forced solution is in; a guess any read postponed is taken now,
    // and remembered so that a refusal names it.
    let guessed = std::cell::RefCell::new(Vec::new());
    owed.guess(elab, cx, expected.map(|e| (&ty, e)), n, &mut sols, &meta_doms, &guessed, span)?;
    retry_obligations(
        elab,
        cx,
        name,
        &params,
        &slot_param,
        &meta_doms,
        n,
        &mut sols,
        &resolves,
        &deferred,
        &mut owed,
        true,
        span,
    )?;
    if promote_unsolved {
        elab.promote_application_goals(
            cx,
            name,
            &params,
            &slot_param,
            &meta_doms,
            &meta_lvls,
            n,
            &mut sols,
            span,
        )?;
        retry_obligations(
            elab,
            cx,
            name,
            &params,
            &slot_param,
            &meta_doms,
            n,
            &mut sols,
            &resolves,
            &deferred,
            &mut owed,
            false,
            span,
        )?;
    }

    if let Some(obligation) = resolves
        .iter()
        .find(|obligation| matches!(sols[obligation.slot], Sol::Withheld))
    {
        return Err(elab.blocked_solver_error(name, &params, obligation, span));
    }
    for obligation in &deferred {
        if !matches!(sols[obligation.slot], Sol::Withheld) {
            continue;
        }
        let parameter = params
            .get(obligation.param)
            .map(|parameter| parameter.name.as_str())
            .unwrap_or("?");
        let escape = if value_head {
            format!("write the call fully explicitly (`@{name}(…)`)")
        } else {
            format!(
                "give the type arguments (`{name}<…>(…)`) or write \
                 the call fully explicitly (`@{name}(…)`)"
            )
        };
        let note = elab.deferred_argument_note(
            cx, &head, &params, &explicit_doms, &slot_param, &sols,
        );
        if let ExprKind::OpSymbol { symbol, .. } = &obligation.expr.kind {
            return err(
                format!(
                    "`{symbol}` is a bare operator symbol, so it needs the carrier \
                     this position expects — and the type of `{name}`'s parameter \
                     `{parameter}` still mentions an implicit that could not be inferred \
                     here. Name the operation instead of the symbol, or {escape}{note}"
                ),
                obligation.expr.span,
            );
        }
        return err(
            format!(
                "this argument of `{name}` was deferred — the type of its parameter \
                 `{parameter}` still mentions an implicit that could not be inferred; \
                 {escape}{note}"
            ),
            obligation.expr.span,
        );
    }

    let mut entries = Vec::with_capacity(n as usize);
    for reverse in 0..n {
        let slot = (n - 1 - reverse) as usize;
        let mut solution = sols[slot]
            .solved()
            .cloned()
            .ok_or_else(|| {
                let parameter = slot_param.get(slot).and_then(|&parameter| params.get(parameter));
                let msg = match (parameter, crate::unification::level_decline(slot as u32)) {
                    (Some(p), Some((want, got))) => format!(
                        "the type argument `{}` of `{name}` lives at `Type<{}>`, but the type \
                         this call offers it is at `Type<{}>` — universes in this system are \
                         non-cumulative, so a type does not also inhabit the universes above \
                         its own, and there is no lift",
                        p.name,
                        crate::show_level(&want),
                        crate::show_level(&got),
                    ),
                    _ => unsolved_message(name, parameter, value_head, bare_ref),
                };
                ElabError::Elab { msg, span }
            })?;
        // The discharge writes this solution through the whole spine's
        // annotations, so it is written in the emission spelling (§5).
        if let Some(dom) = meta_doms.get(slot)
            && let Some(respelled) = elab.respell_solution(cx, dom, &solution)
        {
            solution = Rc::new(respelled);
        }
        entries.push(GlobalEntry::Tm(solution));
    }
    let substitution = GlobalSubst { entries };
    let guessed = guessed.into_inner();
    owed.discharge(elab, cx, &substitution, |slot, later| {
        let first = Rc::clone(sols.get(slot)?.solved()?);
        let guessed = guessed.contains(&slot);
        let name = slot_param.get(slot).and_then(|&p| params.get(p))?.name.clone();
        // A slot's type is in the scratch world; only a meta-free one is
        // carried over, which is the one a message can spell.
        let dom = meta_doms.get(slot).and_then(|d| zonked(d, n, &sols));
        Some(SlotClash { name, guessed, dom, first, later })
    });
    let (term, ty) = (
        term.apply_global(&substitution),
        ty.apply_global(&substitution),
    );
    if spill.is_empty() {
        return Ok((term, ty, level));
    }
    let past = params.len();
    apply_explicit(elab, cx, Some(name), params, past, term, ty, level, &spill)
}

fn unsolved_message(
    name: &str,
    parameter: Option<&ParamMeta>,
    value_head: bool,
    bare_ref: bool,
) -> String {
    match parameter {
        Some(parameter) if value_head && bare_ref && parameter.is_type => format!(
            "cannot infer the type argument `{}` of `{name}` from the expected type here — \
             write the use fully explicitly (`@{name}(…)`) or eta-expand with the argument \
             written (`λ … => {name}(T, …)`)",
            parameter.name
        ),
        Some(parameter) if value_head && parameter.is_type => format!(
            "cannot infer the type argument `{}` of `{name}` here — no argument's type \
             mentions it; write the call fully explicitly (`@{name}(…)`) or eta-expand \
             with the argument written (`λ … => {name}(T, …)`)",
            parameter.name
        ),
        Some(parameter) if bare_ref && parameter.is_type => format!(
            "cannot infer the type argument `{}` of `{name}` from the expected type here — \
             write `{name}<…>` to give the type arguments",
            parameter.name
        ),
        Some(parameter) if bare_ref => format!(
            "could not infer the implicit argument `{}` of `{name}` from the expected type here",
            parameter.name
        ),
        Some(parameter) if parameter.is_type => format!(
            "cannot infer the type argument `{}` of `{name}` here — no argument's type \
             mentions it; write `{name}<…>(…)` to give the type arguments",
            parameter.name
        ),
        Some(parameter) => format!(
            "could not infer the implicit argument `{}` of `{name}`",
            parameter.name
        ),
        None => format!("could not infer an implicit argument of `{name}`"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    struct FakeExprElab;

    #[derive(Default)]
    struct FakeImplicitElab {
        events: RefCell<Vec<&'static str>>,
        /// The type every explicit argument infers at, when the fixture has
        /// an inferred argument at all.
        inferred: Option<Type>,
        notes: RefCell<Vec<(Type, Type)>>,
    }

    impl ExplicitArgElab for FakeExprElab {
        fn whnf_for_application(&self, _cx: &Cx, ty: &Type, _scratch: u32, _span: Span) -> R<Type> {
            Ok(ty.clone())
        }

        fn check_explicit_argument(
            &self,
            _cx: &Cx,
            _arg: &Expr,
            expected: &Type,
            _level: &Level,
            _hint: Option<(&str, &str)>,
            _skel: Option<&Skel>,
        ) -> R<Term> {
            assert_eq!(*expected, Type::Nat);
            Ok(Term::Zero)
        }
    }

    impl ExplicitArgElab for FakeImplicitElab {
        fn whnf_for_application(&self, _cx: &Cx, ty: &Type, _scratch: u32, _span: Span) -> R<Type> {
            Ok(ty.clone())
        }

        fn check_explicit_argument(
            &self,
            _cx: &Cx,
            _arg: &Expr,
            _expected: &Type,
            _level: &Level,
            _hint: Option<(&str, &str)>,
            _skel: Option<&Skel>,
        ) -> R<Term> {
            self.events.borrow_mut().push("check");
            Ok(Term::Zero)
        }
    }

    impl ImplicitApplicationElab for FakeImplicitElab {
        fn classify_application_argument(&self, _cx: &Cx, _argument: &Expr) -> ArgumentClass {
            ArgumentClass {
                checking_only: false,
                fallback_infer: false,
            }
        }

        fn infer_application_argument(&self, _cx: &Cx, _argument: &Expr) -> R<(Term, Type, Level)> {
            let ty = self.inferred.clone().expect("the fixture has no inference obligation");
            self.events.borrow_mut().push("infer");
            Ok((Term::Zero, ty, Level::Zero))
        }

        fn unify_application_argument_type(
            &self,
            _cx: &Cx,
            _parameter: &Type,
            _argument: &Type,
            _n: u32,
            _sols: &mut [Sol],
            _meta_doms: &[Type],
            _guesses: Guesses<'_>,
            _span: Span,
        ) -> Vec<(usize, Rc<Term>)> {
            assert!(self.inferred.is_some(), "the fixture has no inferred argument");
            // Learns nothing, as a failed unification does.
            self.events.borrow_mut().push("unify");
            Vec::new()
        }

        fn note_argument_mismatch(&self, _cx: &Cx, got: &Type, expected: &Type, _level: &Level, _span: Span, _clash: Option<SlotClash>) {
            self.events.borrow_mut().push("note");
            self.notes.borrow_mut().push((got.clone(), expected.clone()));
        }

        fn solve_application_from_expected(
            &self,
            _cx: &Cx,
            _result: &Type,
            _expected: &Type,
            _n: u32,
            sols: &mut [Sol],
            _meta_doms: &[Type],
            _guesses: Guesses<'_>,
            _span: Span,
        ) -> R<()> {
            self.events.borrow_mut().push("expected");
            for solution in sols {
                if matches!(solution, Sol::Unsolved) {
                    *solution = Sol::Solved(Rc::new(Term::Zero));
                }
            }
            Ok(())
        }

        fn resolve_application_obligation(
            &self,
            _cx: &Cx,
            _name: &str,
            _params: &[ParamMeta],
            _slot_param: &[usize],
            _meta_doms: &[Type],
            _n: u32,
            sols: &mut [Sol],
            obligation: &ResolveOb,
            _span: Span,
        ) -> R<ObligationProgress> {
            self.events.borrow_mut().push("resolve");
            sols[obligation.slot] = Sol::Solved(Rc::new(Term::Zero));
            Ok(ObligationProgress::Solved)
        }

        fn promote_application_goals(
            &self,
            _cx: &Cx,
            _name: &str,
            _params: &[ParamMeta],
            _slot_param: &[usize],
            _meta_doms: &[Type],
            _meta_lvls: &[Level],
            _n: u32,
            _sols: &mut [Sol],
            _span: Span,
        ) -> R<()> {
            panic!("obligation retry cannot promote declaration goals")
        }

        fn blocked_solver_error(
            &self,
            _name: &str,
            _params: &[ParamMeta],
            _obligation: &ResolveOb,
            span: Span,
        ) -> ElabError {
            ElabError::Elab {
                msg: "blocked solver".into(),
                span,
            }
        }
    }

    #[test]
    fn an_anonymous_arrow_has_no_metadata_allocation() {
        let ty = Ty {
            kind: TyKind::Fn {
                binder: None,
                implicit: false,
                dom: Box::new(Ty {
                    kind: TyKind::Nat,
                    span: Span { start: 0, end: 3 },
                }),
                cod: Box::new(Ty {
                    kind: TyKind::Nat,
                    span: Span { start: 7, end: 10 },
                }),
            },
            span: Span { start: 0, end: 10 },
        };
        assert!(skel_of_ty(&ty).is_none());
    }

    #[test]
    fn explicit_application_needs_no_elaborator_fixture() {
        let zero = Level::Zero;
        let pi = Type::Pi {
            dom_level: zero.clone(),
            cod_level: zero.clone(),
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Nat),
        };
        let arg = Expr {
            kind: heather_syntax::ExprKind::Num(0u64.into()),
            span: Span { start: 4, end: 5 },
        };
        let (term, ty, level) = apply_explicit(
            &FakeExprElab,
            &Cx::empty(),
            None,
            Rc::new(Vec::new()),
            0,
            Term::Zero,
            pi,
            zero.clone(),
            &[arg],
        )
        .expect("application");

        assert!(matches!(term, Term::App { arg, .. } if *arg == Term::Zero));
        assert_eq!(ty, Type::Nat);
        assert_eq!(level, zero);
    }

    #[test]
    fn implicit_schedule_fixes_slots_and_parameter_indices_without_a_session() {
        let checking = Expr {
            kind: heather_syntax::ExprKind::Hole(None),
            span: Span { start: 0, end: 1 },
        };
        let ordinary = Expr {
            kind: heather_syntax::ExprKind::Num(0u64.into()),
            span: Span { start: 2, end: 3 },
        };
        let plan = ImplicitPlan::new(&[true, false, true, false], &[checking, ordinary], |arg| {
            matches!(arg.kind, heather_syntax::ExprKind::Hole(_))
        });

        assert_eq!(plan.scratch_len(), 3);
        assert_eq!(
            plan.steps(2).collect::<Vec<_>>(),
            vec![
                ParamStep {
                    parameter: 2,
                    implicit: true
                },
                ParamStep {
                    parameter: 3,
                    implicit: false
                },
                ParamStep {
                    parameter: 4,
                    implicit: true
                },
                ParamStep {
                    parameter: 5,
                    implicit: false
                },
            ]
        );
    }

    #[test]
    fn obligation_fixpoint_needs_capabilities_not_an_elaborator() {
        let elab = FakeImplicitElab::default();
        let expr = Expr {
            kind: heather_syntax::ExprKind::Hole(None),
            span: Span { start: 0, end: 1 },
        };
        let resolves = [ResolveOb {
            slot: 0,
            dom: Type::Nat,
            dom_level: Level::Zero,
            param: 0,
            applied: None,
        }];
        let deferred = [DeferredArg {
            slot: 1,
            expr: &expr,
            dom: Type::Nat,
            dom_level: Level::Zero,
            param: 1,
            fallback_infer: false,
            replanned: false,
            earlier: vec![],
        }];
        let mut sols = [Sol::Withheld, Sol::Withheld];

        retry_obligations(
            &elab,
            &Cx::empty(),
            "f",
            &[],
            &[],
            &[],
            2,
            &mut sols,
            &resolves,
            &deferred,
            &mut OwedChecks::default(),
            true,
            Span { start: 0, end: 1 },
        )
        .expect("fixpoint");

        assert!(sols.iter().all(|sol| sol.solved().is_some()));
        assert_eq!(&*elab.events.borrow(), &["resolve", "check"]);
    }

    #[test]
    fn implicit_application_owns_its_scratch_world_without_an_elaborator() {
        let zero = Level::Zero;
        let ty = Type::Pi {
            dom_level: zero.clone(),
            cod_level: zero.clone(),
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Pi {
                dom_level: zero.clone(),
                cod_level: zero.clone(),
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Nat),
            }),
        };
        let params = Rc::new(vec![
            ParamMeta {
                name: "implicit".into(),
                implicit: true,
                is_type: false,
                is_self: false,
                skel: None,
                solver: None,
                default: None,
            },
            ParamMeta {
                name: "value".into(),
                implicit: false,
                is_type: false,
                is_self: false,
                skel: None,
                solver: None,
                default: None,
            },
        ]);
        let argument = Expr {
            kind: ExprKind::Num(0u64.into()),
            span: Span { start: 2, end: 3 },
        };
        let elab = FakeImplicitElab::default();

        let (term, result, level) = apply_implicit(
            &elab,
            &Cx::empty(),
            "f",
            params,
            false,
            0,
            false,
            Term::Zero,
            ty,
            zero.clone(),
            &[argument],
            &[true, false],
            Some(&Type::Nat),
            false,
            Span { start: 0, end: 4 },
        )
        .expect("implicit application");

        assert!(matches!(term, Term::App { .. }));
        assert_eq!(result, Type::Nat);
        assert_eq!(level, zero);
        assert_eq!(&*elab.events.borrow(), &["check", "expected"]);
    }

    /// An inferred argument that taught nothing, at a domain the expected
    /// type then solved, still owes its comparison: one note, of its own type
    /// against the domain under the final solution, made at the discharge
    /// (`issues/implicit-argument-mismatch-reaches-kernel.md`).
    #[test]
    fn an_inferred_argument_owes_its_comparison_at_the_discharge() {
        let zero = Level::Zero;
        let id_at = |rhs: Term| Type::Id {
            level: zero.clone(),
            ty: Rc::new(Type::Nat),
            lhs: Rc::new(Term::Zero),
            rhs: Rc::new(rhs),
        };
        // `f : Π(a: Nat). Π(h: 0 = a). Nat`, applied as `f(h)` with `a`
        // implicit and `h` inferring at `1 = 1`.
        let one = Term::Succ(Rc::new(Term::Zero));
        let got = Type::Id {
            level: zero.clone(),
            ty: Rc::new(Type::Nat),
            lhs: Rc::new(one.clone()),
            rhs: Rc::new(one),
        };
        let ty = Type::Pi {
            dom_level: zero.clone(),
            cod_level: zero.clone(),
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Pi {
                dom_level: zero.clone(),
                cod_level: zero.clone(),
                dom: Rc::new(id_at(Term::Var(heather_kernel::term::LocalVar(0)))),
                cod: Rc::new(Type::Nat),
            }),
        };
        let meta = |name: &str, implicit| ParamMeta {
            name: name.into(),
            implicit,
            is_type: false,
            is_self: false,
            skel: None,
            solver: None,
            default: None,
        };
        let params = Rc::new(vec![meta("a", true), meta("h", false)]);
        let argument = Expr {
            kind: ExprKind::Var("h".into()),
            span: Span { start: 2, end: 3 },
        };
        let elab = FakeImplicitElab {
            inferred: Some(got.clone()),
            ..FakeImplicitElab::default()
        };

        apply_implicit(
            &elab,
            &Cx::empty(),
            "f",
            params,
            false,
            0,
            false,
            Term::Zero,
            ty,
            zero.clone(),
            &[argument],
            &[true, false],
            Some(&Type::Nat),
            false,
            Span { start: 0, end: 4 },
        )
        .expect("implicit application");

        assert_eq!(&*elab.events.borrow(), &["infer", "unify", "expected", "note"]);
        assert_eq!(&*elab.notes.borrow(), &[(got, id_at(Term::Zero))]);
    }
}
