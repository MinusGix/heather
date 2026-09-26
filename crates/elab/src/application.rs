//! Callable surface metadata and application along an explicit Π spine.
//!
//! This module deliberately knows no elaborator state. The explicit engine
//! receives normalization and argument checking through [`ExplicitArgElab`].
//! The implicit engine owns its complete scratch-world lifecycle and receives
//! only the semantic effects in [`ImplicitApplicationElab`].

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{GlobalVar, LocalSubst, Term, Type};
use heather_syntax::{Expr, ExprKind, LamBinder, Span, Ty, TyKind};

use crate::unification::{DeferredArg, ResolveOb, Sol, zonked};
use crate::{Cx, ElabError, R, err};

mod callable;
pub(crate) use callable::subject_index_in;
mod named;
pub(crate) use named::{
    permute_by_name, refuse_named, resolve_constructor_arguments, resolve_named,
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

/// Semantic capabilities used by the otherwise mechanical obligation queue.
///
/// The application module owns retry order and fixpoint termination. The
/// implementation owns the policies that genuinely need session state:
/// dictionary search, expression elaboration, unification, and declaration
/// goal creation.
pub(crate) trait ImplicitApplicationElab: ExplicitArgElab {
    fn classify_application_argument(&self, cx: &Cx, argument: &Expr) -> ArgumentClass;

    fn infer_application_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)>;

    /// A generated propagation callback may infer its result once its input
    /// domain is known. Ordinary source lambdas retain the existing policy.
    fn infer_propagation_callback(
        &self, _cx: &Cx, _argument: &Expr, _parameter: &Type, _n: u32, _sols: &[Sol],
    ) -> Option<R<(Term, Type, Level)>> { None }

    fn unify_application_argument_type(
        &self,
        cx: &Cx,
        parameter: &Type,
        argument: &Type,
        n: u32,
        sols: &mut [Sol],
        span: Span,
    );

    #[allow(clippy::too_many_arguments)]
    fn solve_application_from_expected(
        &self,
        cx: &Cx,
        result: &Type,
        expected: &Type,
        n: u32,
        sols: &mut [Sol],
        meta_doms: &[Type],
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
    /// discharge (`docs/per-instantiation-type-codes-design.md` §5, amended
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

    fn blocked_solver_error(
        &self,
        name: &str,
        params: &[ParamMeta],
        obligation: &ResolveOb,
        span: Span,
    ) -> crate::ElabError;
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
    allow_fallback: bool,
    span: Span,
) -> R<()> {
    loop {
        let mut progressed = false;
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
            let hint = params
                .get(obligation.param)
                .map(|p| (name, p.name.as_str()));
            let skel = params.get(obligation.param).and_then(|p| p.skel.as_deref());
            let term = elab.check_explicit_argument(
                cx,
                obligation.expr,
                &dom,
                &obligation.dom_level,
                hint,
                skel,
            )?;
            sols[obligation.slot] = Sol::Solved(Rc::new(term));
            progressed = true;
        }
        if !progressed || !blocked {
            if allow_fallback && blocked {
                for obligation in deferred {
                    if !matches!(sols[obligation.slot], Sol::Withheld) { continue; }
                    if let Some(inferred) = elab.infer_propagation_callback(cx,obligation.expr,&obligation.dom,n,sols) {
                        let (term,ty,_) = inferred?;
                        elab.unify_application_argument_type(cx,&obligation.dom,&ty,n,sols,obligation.expr.span);
                        sols[obligation.slot] = Sol::Solved(Rc::new(term));
                        progressed = true;
                        break;
                    }
                }
                if progressed { continue; }
            }
            if allow_fallback
                && blocked
                && let Some(obligation) = deferred.iter().find(|obligation| {
                    obligation.fallback_infer && matches!(sols[obligation.slot], Sol::Withheld)
                })
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
                elab.unify_application_argument_type(cx, &obligation.dom, &ty, n, sols, span);
                sols[obligation.slot] = Sol::Solved(Rc::new(term));
                continue;
            }
            return Ok(());
        }
    }
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
    let unpinned: Vec<String> = slot_param
        .iter()
        .enumerate()
        .filter(|&(slot, _)| matches!(sols.get(slot), Some(Sol::Unsolved)))
        .filter_map(|(_, &p)| params.get(p))
        .filter(|p| p.implicit && p.solver.is_none())
        .map(|p| format!("`{}`", p.name))
        .collect();
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
         write it (`{name}<…>(…)`) or pass an argument that fixes it"
    )
}

/// The implicitness skeleton of a surface-written function type
/// (`docs/implicit-binders-design.md` §2).
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
            })
            .collect(),
    )
}

/// The only expression-elaboration capabilities an explicit application uses.
pub(crate) trait ExplicitArgElab {
    fn whnf_for_application(&self, cx: &Cx, ty: &Type, span: Span) -> R<Type>;

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

    /// Whether an application is written `app@(f; a)` here
    /// (`docs/app-by-head-type-design.md` §6.1): outside a quotation. The
    /// fakes answer `false` and keep the annotated form their tests read.
    fn emits_checked_applications(&self, _cx: &Cx) -> bool {
        false
    }
}

/// One node of an application spine as it is written
/// (`docs/app-by-head-type-design.md` §6.1): `app@(f; a)`, whose Π is the one
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
    for (i, arg) in args.iter().enumerate() {
        let head = elab.whnf_for_application(cx, &ty, arg.span)?;
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
        let arg = elab.check_explicit_argument(cx, arg, &dom, &dom_level, hint, skel)?;
        let arg = Rc::new(arg);
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
    let mut meta_doms = Vec::with_capacity(n as usize);
    let mut meta_lvls = Vec::with_capacity(n as usize);
    let mut slot_param = Vec::with_capacity(n as usize);
    let mut deferred = Vec::new();
    let mut resolves = Vec::new();
    let mut next_meta = 0u32;
    let mut arguments = args.iter();

    for step in plan.steps(param_offset) {
        let parameter = step.parameter;
        let head_ty = elab.whnf_for_application(cx, &ty, span)?;
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
                var: GlobalVar(next_meta),
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
            let argument = arguments.next().ok_or_else(|| ElabError::Elab {
                msg: format!("`{name}` is applied to too few arguments"),
                span,
            })?;
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
                elab.unify_application_argument_type(cx, &dom, &counted, n, &mut sols, span);
            }
            match zonked(&dom, n, &sols) {
                Some(real_dom) => {
                    let hint = params
                        .get(parameter)
                        .map(|parameter| (name, parameter.name.as_str()));
                    let skel = params
                        .get(parameter)
                        .and_then(|parameter| parameter.skel.as_deref());
                    let checked = elab
                        .check_explicit_argument(cx, argument, &real_dom, &dom_level, hint, skel)?;
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
                        var: GlobalVar(next_meta),
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
                    });
                    meta_doms.push((*dom).clone());
                    meta_lvls.push(dom_level.clone());
                    slot_param.push(parameter);
                    next_meta += 1;
                    Rc::new(meta)
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
                        other => other?,
                    };
                    elab.unify_application_argument_type(
                        cx,
                        &dom,
                        &inferred_ty,
                        n,
                        &mut sols,
                        span,
                    );
                    Rc::new(inferred.shift_global(n))
                }
            }
        };
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
            let head_ty = elab.whnf_for_application(cx, &ty, span)?;
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
            if zonked(&dom, n, &sols).is_some()
                || elab
                    .classify_application_argument(cx, argument)
                    .checking_only
            {
                break;
            }
            let (inferred, inferred_ty, _) = elab.infer_application_argument(cx, argument)?;
            elab.unify_application_argument_type(cx, &dom, &inferred_ty, n, &mut sols, span);
            let argument = Rc::new(inferred.shift_global(n));
            ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&argument)));
            level = cod_level.clone();
            term = emit_app(elab, cx, term, dom_level, cod_level, dom, cod, argument, n);
            taken += 1;
        }
        spill.drain(..taken);
    }

    if let Some(expected) = expected
        && spill.is_empty()
        && sols.iter().any(|solution| solution.solved().is_none())
    {
        elab.solve_application_from_expected(cx, &ty, expected, n, &mut sols, &meta_doms, span)?;
    }
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
        if let ExprKind::OpSymbol { symbol, .. } = &obligation.expr.kind {
            return err(
                format!(
                    "`{symbol}` is a bare operator symbol, so it needs the carrier \
                     this position expects — and the type of `{name}`'s parameter \
                     `{parameter}` still mentions an implicit that could not be inferred \
                     here. Name the operation instead of the symbol, or {escape}"
                ),
                obligation.expr.span,
            );
        }
        return err(
            format!(
                "this argument of `{name}` was deferred — the type of its parameter \
                 `{parameter}` still mentions an implicit that could not be inferred; \
                 {escape}"
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
            .ok_or_else(|| ElabError::Elab {
                msg: unsolved_message(
                    name,
                    slot_param
                        .get(slot)
                        .and_then(|&parameter| params.get(parameter)),
                    value_head,
                    bare_ref,
                ),
                span,
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
    }

    impl ExplicitArgElab for FakeExprElab {
        fn whnf_for_application(&self, _cx: &Cx, ty: &Type, _span: Span) -> R<Type> {
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
        fn whnf_for_application(&self, _cx: &Cx, ty: &Type, _span: Span) -> R<Type> {
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
            panic!("the fixture has no inference obligation")
        }

        fn unify_application_argument_type(
            &self,
            _cx: &Cx,
            _parameter: &Type,
            _argument: &Type,
            _n: u32,
            _sols: &mut [Sol],
            _span: Span,
        ) {
            panic!("the fixture has no inferred argument")
        }

        fn solve_application_from_expected(
            &self,
            _cx: &Cx,
            _result: &Type,
            _expected: &Type,
            _n: u32,
            sols: &mut [Sol],
            _meta_doms: &[Type],
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
            },
            ParamMeta {
                name: "value".into(),
                implicit: false,
                is_type: false,
                is_self: false,
                skel: None,
                solver: None,
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
}
