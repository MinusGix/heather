//! Callable surface metadata and application along an explicit Π spine.
//!
//! This module deliberately knows no elaborator state. The explicit engine
//! receives the two expression capabilities it needs through
//! [`ExplicitArgElab`]: normalize the current function type and check one
//! argument. Implicit solving can move behind the same boundary incrementally.

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalSubst, Term, Type};
use heather_syntax::{Expr, LamBinder, Span, Ty, TyKind};

use crate::unification::{DeferredArg, ResolveOb, Sol, zonked};
use crate::{Cx, R, err};

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
pub(crate) trait ImplicitApplicationElab {
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

    fn check_deferred_application_argument(
        &self,
        cx: &Cx,
        name: &str,
        params: &[ParamMeta],
        obligation: &DeferredArg<'_>,
        expected: &Type,
    ) -> R<Term>;

    fn infer_deferred_application_argument(
        &self,
        cx: &Cx,
        obligation: &DeferredArg<'_>,
        n: u32,
        sols: &mut [Sol],
        span: Span,
    ) -> R<Term>;

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
}

/// Retry solver and checking-only obligations to a fixpoint.
///
/// Solver obligations run first because dictionaries may unblock argument
/// domains, while checking an argument cannot instantiate a withheld solver
/// slot. Each continuing pass fills at least one slot, which bounds the loop
/// by the number of obligations. Before promotion, result-only calls may use
/// their compatibility inference fallback; after promotion they may not.
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
            let term =
                elab.check_deferred_application_argument(cx, name, params, obligation, &dom)?;
            sols[obligation.slot] = Sol::Solved(Rc::new(term));
            progressed = true;
        }
        if !progressed || !blocked {
            if allow_fallback
                && blocked
                && let Some(obligation) = deferred.iter().find(|obligation| {
                    obligation.fallback_infer && matches!(sols[obligation.slot], Sol::Withheld)
                })
            {
                let term =
                    elab.infer_deferred_application_argument(cx, obligation, n, sols, span)?;
                sols[obligation.slot] = Sol::Solved(Rc::new(term));
                continue;
            }
            return Ok(());
        }
    }
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

    fn check_explicit_argument(
        &self,
        cx: &Cx,
        arg: &Expr,
        expected: &Type,
        level: &Level,
        hint: Option<(&str, &str)>,
        skel: Option<&Skel>,
    ) -> R<Term>;
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
        term = Term::App {
            fun: Rc::new(term),
            dom_level,
            cod_level,
            dom,
            cod,
            arg,
        };
    }
    Ok((term, ty, lvl))
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

    impl ImplicitApplicationElab for FakeImplicitElab {
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

        fn check_deferred_application_argument(
            &self,
            _cx: &Cx,
            _name: &str,
            _params: &[ParamMeta],
            _obligation: &DeferredArg<'_>,
            _expected: &Type,
        ) -> R<Term> {
            self.events.borrow_mut().push("check");
            Ok(Term::Zero)
        }

        fn infer_deferred_application_argument(
            &self,
            _cx: &Cx,
            _obligation: &DeferredArg<'_>,
            _n: u32,
            _sols: &mut [Sol],
            _span: Span,
        ) -> R<Term> {
            panic!("the fixture has no fallback obligation")
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
            kind: heather_syntax::ExprKind::Num(0),
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
            kind: heather_syntax::ExprKind::Num(0),
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
        }];
        let deferred = [DeferredArg {
            slot: 1,
            expr: &expr,
            dom: Type::Nat,
            dom_level: Level::Zero,
            param: 1,
            fallback_infer: false,
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
}
