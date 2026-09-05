//! State carried while elaborating structurally recursive matches.

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{LocalCtx, LocalVar, Term, Type};
use heather_syntax::{Expr, Span, Ty, TyKind};

use crate::application::{self, ExplicitArgElab, ParamMeta};
use crate::{Cx, R, err, matching};

/// Semantic capabilities needed by guarded self-call lowering.
///
/// This module owns termination-guard interpretation and selection of the
/// induction hypothesis. The root elaborator retains recursive expression
/// inference and callable metadata, while explicit spill application reuses
/// the ordinary application engine.
pub(crate) trait SelfCallElab: ExplicitArgElab {
    fn infer_self_call_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)>;
    fn self_call_application_params(&self, name: &str) -> Rc<Vec<ParamMeta>>;
}

/// Is `scrut` (already elaborated) exactly one of the enclosing declaration's
/// parameters? Returns its parameter index — the argument position the
/// recursion descends on.
pub(crate) fn descends_on_param(cx: &Cx, scrut: &Term) -> Option<usize> {
    let s = cx.selfref.as_ref()?;
    let Term::Var(LocalVar(i)) = scrut else {
        return None;
    };
    let pos = cx.names.len() - 1 - *i as usize;
    (pos < s.params.len()).then_some(pos)
}

/// Validate the written type arguments of a self-call
/// (issues/recursive-self-call-type-arguments.md).
///
/// A self-call is always at the declaration's own type parameters: the
/// recursion becomes an eliminator whose type parameters are bound outside
/// it, so there is no place for a second instantiation.
pub(crate) fn check_self_tyargs(cx: &Cx, tyargs: &[Ty], span: Span) -> R<()> {
    let s = cx.selfref.as_ref().expect("checked by the caller");
    let name = &s.name;
    let own: Vec<&str> = s.params[..s.n_tyvars]
        .iter()
        .map(|(n, _)| n.as_str())
        .collect();
    if tyargs.len() != s.n_tyvars {
        return err(
            if s.n_tyvars == 0 {
                format!("`{name}` has no type parameters, so a recursive call takes none")
            } else {
                format!(
                    "the recursive call to `{name}` writes {} type argument(s), and \
                     `{name}` has {} (`{}`)",
                    tyargs.len(),
                    s.n_tyvars,
                    own.join(", ")
                )
            },
            span,
        );
    }
    for (a, want) in tyargs.iter().zip(&own) {
        let is_own = matches!(&a.kind, TyKind::Named { name, args }
            if args.is_empty() && name == want);
        if !is_own {
            return err(
                format!(
                    "a recursive call to `{name}` is always at `{name}`'s own type \
                     parameter(s) `{}`, and `{}` is not `{want}`: recursing at a \
                     *different* instantiation is polymorphic recursion, which this \
                     lowering cannot express — the recursion becomes an `elim` whose \
                     type parameters are bound outside it, so there is nowhere for a \
                     second instantiation to go (issues/match-recursion.md). Writing \
                     `{}` is the same call and so is dropping the type arguments \
                     entirely",
                    own.join(", "),
                    crate::traits::render_ty(a),
                    own.join(", ")
                ),
                a.span,
            );
        }
    }
    Ok(())
}

/// Lower a call to the enclosing declaration's own name to the induction
/// hypothesis supplied by its structurally recursive match.
///
/// The decreasing argument is checked first because indexed guards discover
/// the descendant before they can validate a rebound index. Every remaining
/// declared parameter must be passed unchanged. Arguments beyond the
/// declaration's arity are applied to the induction hypothesis's result by
/// the ordinary explicit-application engine.
pub(crate) fn elab_self_call(
    elab: &impl SelfCallElab,
    cx: &Cx,
    args: &[Expr],
    explicit: bool,
    span: Span,
) -> R<(Term, Type, Level)> {
    let self_ref = Rc::clone(
        cx.selfref
            .as_ref()
            .expect("self-call outside a declaration"),
    );
    let name = &self_ref.name;
    let Some(guard) = cx.guard.clone() else {
        return err(
            format!(
                "recursive call to `{name}` is not structurally guarded: it must occur \
                 inside a `match` on one of `{name}`'s own parameters"
            ),
            span,
        );
    };

    // Which parameter each written value argument fills. Leading type
    // parameters are never passed here; value implicits are omitted unless
    // the call is `@`-marked.
    let positions: Vec<usize> = (self_ref.n_tyvars..self_ref.params.len())
        .filter(|&position| explicit || !self_ref.params[position].1)
        .collect();
    if !positions.contains(&guard.dec) {
        return err(
            format!(
                "`{name}` recurses on its implicit parameter `{}`; pass it explicitly \
                 (`@{name}(…)`) to make the recursive call",
                self_ref.params[guard.dec].0
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

    let (args, spill) = args.split_at(positions.len());
    // A generalized parameter that the call cannot pass — an implicit one at
    // a call without `@` — has no argument to apply the ih to.
    if let Some(generalized) = &guard.generalized
        && let Some(&missing) = generalized.iter().find(|p| !positions.contains(p))
    {
        return err(
            format!(
                "`{name}` recurses at a varying value of its implicit parameter `{}`; \
                 pass it explicitly (`@{name}(…)`) to make the recursive call",
                self_ref.params[missing].0
            ),
            span,
        );
    }
    let mut descendant = 0usize;
    let mut cov_at = 0usize;
    // Arguments at generalized positions, in position order: applied to the
    // ih below, and checked there against its Π domains.
    let mut varied: Vec<&Expr> = Vec::new();
    let order = {
        let mut order: Vec<usize> = (0..args.len()).collect();
        if let Some(decreasing) = positions.iter().position(|&position| position == guard.dec) {
            order.swap(0, decreasing);
        }
        order
    };
    for (argument, position) in order.iter().map(|&index| (&args[index], positions[index])) {
        if position != guard.dec && guard.generalized.as_ref().is_some_and(|g| g.contains(&position)) {
            varied.push(argument);
            continue;
        }
        // Compare by binder for Nat and by term for Wf. Names are diagnostic
        // data only and cannot fake structural descent through shadowing.
        let (argument_term, _, _) = elab.infer_self_call_argument(cx, argument)?;
        let accepted = match (&guard.kind, position == guard.dec) {
            (GuardKind::Nat { preds, comps, .. }, true) => match argument_term {
                Term::Var(LocalVar(index)) => {
                    let absolute = cx.names.len() - 1 - index as usize;
                    match preds
                        .iter()
                        .position(|&predecessor| predecessor == absolute)
                    {
                        Some(depth) if depth < comps.len() => {
                            cov_at = depth;
                            true
                        }
                        _ => false,
                    }
                }
                _ => false,
            },
            (
                GuardKind::Wf {
                    depth, children, ..
                },
                true,
            ) => {
                let shift = (cx.names.len() - depth) as u32;
                match children
                    .iter()
                    .position(|(child, ..)| child.shift_local(shift) == argument_term)
                {
                    Some(index) => {
                        descendant = index;
                        true
                    }
                    None => false,
                }
            }
            (_, false) => {
                let is_original_binder = |absolute: usize| {
                    matches!(argument_term, Term::Var(LocalVar(index))
                        if cx.names.len() - 1 - index as usize == absolute)
                };
                is_original_binder(position)
                    || guard.rebind.as_ref().is_some_and(|(rebound, terms)| {
                        let depth = match &guard.kind {
                            GuardKind::Wf { depth, .. } => *depth,
                            GuardKind::Nat { .. } => return false,
                        };
                        let shift = (cx.names.len() - depth) as u32;
                        *rebound == position
                            && terms
                                .get(descendant)
                                .is_some_and(|term| term.shift_local(shift) == argument_term)
                    })
            }
        };
        if accepted {
            continue;
        }
        return if position == guard.dec {
            let (what, why) = match &guard.kind {
                GuardKind::Nat { preds, comps, .. } => {
                    let usable = preds.len().min(comps.len());
                    let names: Vec<String> = preds[..usable]
                        .iter()
                        .map(|predecessor| format!("`{}`", cx.names[*predecessor]))
                        .collect();
                    if usable == 1 {
                        (
                            format!("{}, the predecessor bound by", names[0]),
                            format!(
                                ". A deeper subterm is refused too, even though it is \
                                 genuinely smaller: this `match` compiles to a recursor \
                                 whose induction hypothesis is the value at {} and at \
                                 nothing else, so a call anywhere else has no term to \
                                 elaborate to. Reaching further needs the recursion to \
                                 carry its earlier values \
                                 (issues/recursion-at-deeper-subterms.md), which happens \
                                 only where an arm scrutinizes its own predecessor",
                                names[0]
                            ),
                        )
                    } else {
                        (
                            format!("one of {}, the predecessors bound by", names.join(", ")),
                            format!(
                                ". The recursion carries its last {usable} values, so \
                                 those are the subterms it can descend to; anything else \
                                 has no term to elaborate to, even when it is genuinely \
                                 smaller (issues/recursion-at-deeper-subterms.md)"
                            ),
                        )
                    }
                }
                GuardKind::Wf { .. } => (
                    "one of the recursive fields bound by".to_string(),
                    ". A deeper subterm is refused too, even though it is genuinely \
                     smaller: the induction hypothesis this `match` binds is the value \
                     at each recursive field and at nothing else, so a call anywhere \
                     else has no term to elaborate to"
                        .to_string(),
                ),
            };
            err(
                format!(
                    "recursive call to `{name}` must descend: argument `{}` has to be \
                     {what} the enclosing `match`{why}",
                    self_ref.params[position].0
                ),
                argument.span,
            )
        } else {
            err(
                format!(
                    "recursive call to `{name}` must pass `{}` unchanged: the induction \
                     hypothesis fixes every non-decreasing parameter. A parameter is \
                     generalized into the motive — so that a recursive call may vary it \
                     — only when the `match` is checked against a known result type \
                     and the varying call is visible in its arms \
                     (docs/ih-generalization-design.md); here it was not",
                    self_ref.params[position].0
                ),
                argument.span,
            )
        };
    }

    let (term, ty, level) = match &guard.kind {
        GuardKind::Nat {
            tuple,
            comps,
            mlvl,
            depth,
            ..
        } => {
            let shift = (cx.names.len() - depth) as u32;
            let term = matching::cov_proj(comps, mlvl, tuple.clone(), cov_at);
            (
                term.shift_local(shift),
                comps[cov_at].shift_local(shift),
                mlvl.clone(),
            )
        }
        GuardKind::Wf {
            depth, children, ..
        } => {
            let shift = (cx.names.len() - depth) as u32;
            let (_, ih, ty, level) = &children[descendant];
            (
                (**ih).shift_local(shift),
                ty.shift_local(shift),
                level.clone(),
            )
        }
    };
    // The ih is a Π over the generalized parameters (in position order, which
    // is `varied`'s order); the ordinary application engine checks each
    // argument against its domain, so a varied argument at the wrong type is
    // refused where it is written.
    let (term, ty, level) = if varied.is_empty() {
        (term, ty, level)
    } else {
        let generalized = guard.generalized.as_ref().expect("varied only fills at a generalized position");
        let metas: Vec<ParamMeta> = generalized
            .iter()
            .map(|&p| ParamMeta {
                name: self_ref.params[p].0.clone(),
                implicit: self_ref.params[p].1,
                is_type: false,
                is_self: false,
                skel: None,
                solver: None,
            })
            .collect();
        let varied: Vec<Expr> = varied.into_iter().cloned().collect();
        application::apply_explicit(elab, cx, Some(name), Rc::new(metas), 0, term, ty, level, &varied)?
    };
    if spill.is_empty() {
        return Ok((term, ty, level));
    }
    application::apply_explicit(
        elab,
        cx,
        Some(name),
        elab.self_call_application_params(name),
        self_ref.params.len(),
        term,
        ty,
        level,
        spill,
    )
}

/// The enclosing declaration, in scope throughout its own body so that a
/// structurally guarded self-call can lower to the induction hypothesis
/// (issues/match-recursion.md). Nothing else can reference it: the name is
/// only registered as a global once the declaration is checked.
pub(crate) struct SelfRef {
    pub(crate) name: String,
    /// `(parameter name, implicit?)` in declaration order. Parameter `j` is
    /// bound at position `j` of the body's `Cx` (the telescope goes first).
    pub(crate) params: Vec<(String, bool)>,
    /// How many leading entries of [`Self::params`] are `<A, …>` type
    /// parameters. They are never passed at a call site — neither implicitly
    /// nor under `@`, which now controls only the *value* implicits
    /// (issues/at-and-type-arguments.md) — so they are skipped wholesale
    /// rather than filtered by implicitness.
    pub(crate) n_tyvars: usize,
}

/// What a guarded self-call must look like inside a `match` arm, and what it
/// lowers to (issues/match-recursion.md).
pub(crate) struct Guard {
    /// Index of the parameter the recursion descends on.
    pub(crate) dec: usize,
    pub(crate) kind: GuardKind,
    /// An indexed `match`'s index parameter, *rebound* by the arm
    /// (docs/inductive-indexed-lowering.md §6): a self-call must pass the
    /// arm's pattern variable there, not the original parameter.
    ///
    /// `(parameter position, one index term per descendant)` — parallel to
    /// [`GuardKind::Wf`]'s `children` and scoped at the same `depth`, because
    /// a branching index constructor gives each recursive field its *own*
    /// pattern variable (`Bal(SNode(l, r))`), and the ih at descendant `t`
    /// lives at exactly that one. `None` for every non-indexed guard.
    pub(crate) rebind: Option<(usize, Vec<Rc<Term>>)>,
    /// The parameters this recursion's motive **generalizes**, ascending
    /// (`generalize.rs`; issues/ih-generalization.md). At each of them a
    /// self-call may pass anything: the ih is a Π over these, in this order,
    /// and the call applies it to the written arguments. `None` when nothing
    /// is generalized, which is every recursion written before this existed.
    pub(crate) generalized: Option<Rc<Vec<usize>>>,
}

/// The two arm shapes a self-call can sit in. They differ in how many
/// descendants an arm has — one for `Nat`, `mᵢ` for a branching constructor —
/// and correspondingly in whether the ih is a variable or a function of the
/// index (`docs/inductive-tier1-wf-lowering.md` §6.4).
pub(crate) enum GuardKind {
    /// A `Succ(k)` arm. Positions are *absolute* (indices into `cx.names`,
    /// outermost first) so they stay valid as inner binders are pushed.
    Nat {
        /// The chain of predecessors this arm makes available, outermost
        /// first: `preds[0]` is the `k` the arm itself binds, `preds[1]` the
        /// `l` a nested `match k` binds, and so on
        /// (issues/recursion-at-deeper-subterms.md). A self-call descending to
        /// `preds[i]` lowers to the `i`-th component of [`Self::tuple`].
        ///
        /// One entry for the ordinary one-step recursion; the chain grows only
        /// where the arm's own body scrutinizes the predecessor again, and
        /// only by being convoyed through that `match`
        /// (docs/course-of-values-recursion-design.md §5).
        preds: Vec<usize>,
        /// The window of past values in scope: the ih binder itself for the
        /// ordinary recursion, a Σ-tuple of the last `comps.len()` values
        /// above that. Scoped at [`Self::depth`] binders, like
        /// [`GuardKind::Wf`]'s `children`, so a call from deeper inside the
        /// arm shifts it by the difference.
        tuple: Term,
        /// Its component types, at the same scope. `comps.len()` is the depth
        /// the recursion was *elaborated* for: a call below the chain's end
        /// but within it is what a nested `match` unlocks, and a call below
        /// `comps.len()` has no component to become — the refusal
        /// `elab_self_call` reports.
        comps: Vec<Type>,
        /// The level every component lives at.
        mlvl: Level,
        /// Binder count at the arm's ih — the scope [`Self::tuple`] lives in.
        depth: usize,
        /// The recursion's motive, scoped in ([`Self::gamma`], z), kept so a
        /// nested `match` can rebuild the window's type at *its* scrutinee.
        /// The pair travels together because reindexing a family needs the
        /// context it was written in, which a shift cannot recover.
        motive: Rc<Type>,
        gamma: LocalCtx,
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
pub(crate) struct ContainerIh {
    /// The container binder's own term (`snd^m cs`), matched against the
    /// call's elaborated argument exactly as a plain child's term is.
    pub(crate) term: Rc<Term>,
    /// Its length.
    pub(crate) len: Rc<Term>,
    /// The ih function `Π(i : Fin (Succ^m len)). M`, as a term.
    pub(crate) ih: Rc<Term>,
    /// `m`: how many plain children precede the container, and so how far the
    /// container's indices are offset inside `Fin (Succ^m len)`.
    pub(crate) plain: usize,
    /// The motive, *strengthened* — a self-call over a container maps to a
    /// `Vec` of results, which requires a motive independent of the scrutinee
    /// (`docs/container-fields.md` §4.3). `None` when it depends, in which case
    /// [`ContainerIh::eq`] decides whether this is phase 3 or a diagnostic.
    pub(crate) result: Option<Type>,
    /// The motive read as an **equation**, when it is one — phase 3
    /// (`docs/container-proofs.md` §5). Set only when `result` is `None`: a
    /// dependent motive `Id^l(A; lhs(z); rhs(z))` whose *type* `A` does not
    /// mention `z` still relates the two children vectors pointwise, which is
    /// what `vec::tab_cong` turns into an equation between them.
    pub(crate) eq: Option<EqSplit>,
    /// The ih's own Π type, so a call site annotates its application with the
    /// codomain the eliminator actually gave rather than rebuilding it — the
    /// rebuild is only correct for a strengthened motive, and phase 3's is not.
    pub(crate) ih_ty: Type,
    /// `⟦D⟧`, the container's element type, for `nth` at the call site.
    pub(crate) elem: Type,
    /// `l`: the declaration's level, which is `⟦D⟧`'s. Not `mlvl`, which is the
    /// motive's — `nth` and the endpoint applications need this one.
    pub(crate) level: Level,
    pub(crate) mlvl: Level,
}

/// A dependent motive that is an equation, split into its two endpoints
/// (`docs/container-proofs.md` §5).
#[derive(Clone)]
pub(crate) struct EqSplit {
    /// The level `Id^l` is at, which is `A`'s.
    pub(crate) level: Level,
    /// `A`, the type the equation is at — strengthened, so it may not mention
    /// the scrutinee. A heterogeneous motive is out of scope and diagnosed
    /// (`issues/dependent-field-injectivity.md` holds the transport question).
    pub(crate) ty: Type,
    /// `λ(z : ⟦D⟧). lhs` and `λ(z : ⟦D⟧). rhs`. Kept as *functions* rather than
    /// as open terms so that a call site can shift them like any other term and
    /// apply them to a child; the β-redex this leaves is what conversion is for.
    pub(crate) lhs: Rc<Term>,
    pub(crate) rhs: Rc<Term>,
}

#[cfg(test)]
mod tests {
    use super::*;

    struct FakeSelfCall;

    impl ExplicitArgElab for FakeSelfCall {
        fn whnf_for_application(&self, _cx: &Cx, ty: &Type, _span: Span) -> R<Type> {
            Ok(ty.clone())
        }

        fn check_explicit_argument(
            &self,
            cx: &Cx,
            argument: &Expr,
            _expected: &Type,
            _level: &Level,
            _hint: Option<(&str, &str)>,
            _skeleton: Option<&crate::Skel>,
        ) -> R<Term> {
            Ok(self.infer_self_call_argument(cx, argument)?.0)
        }
    }

    impl SelfCallElab for FakeSelfCall {
        fn infer_self_call_argument(&self, cx: &Cx, argument: &Expr) -> R<(Term, Type, Level)> {
            let term = match &argument.kind {
                heather_syntax::ExprKind::Var(name) => {
                    let position = cx
                        .names
                        .iter()
                        .rposition(|candidate| candidate == name)
                        .ok_or_else(|| crate::ElabError::Elab {
                            msg: format!("unknown test local `{name}`"),
                            span: argument.span,
                        })?;
                    Term::Var(LocalVar((cx.names.len() - 1 - position) as u32))
                }
                heather_syntax::ExprKind::Num(0) => Term::Zero,
                _ => return err("unsupported test expression", argument.span),
            };
            Ok((term, Type::Nat, Level::Zero))
        }

        fn self_call_application_params(&self, _name: &str) -> Rc<Vec<ParamMeta>> {
            Rc::new(Vec::new())
        }
    }

    const SPAN: Span = Span { start: 0, end: 1 };

    fn nat_guarded_context(component: Type) -> Cx {
        let mut cx = Cx::empty();
        cx.push("n".into(), Type::Nat, Level::Zero);
        cx.push("predecessor".into(), Type::Nat, Level::Zero);
        cx.selfref = Some(Rc::new(SelfRef {
            name: "f".into(),
            params: vec![("n".into(), false)],
            n_tyvars: 0,
        }));
        cx.guard = Some(Rc::new(Guard {
            dec: 0,
            rebind: None,
            generalized: None,
            kind: GuardKind::Nat {
                preds: vec![1],
                tuple: Term::Var(LocalVar(0)),
                comps: vec![component],
                mlvl: Level::Zero,
                depth: 2,
                motive: Rc::new(Type::Nat),
                gamma: LocalCtx::nil(),
            },
        }));
        cx
    }

    #[test]
    fn descent_is_parameter_identity_not_a_shadowing_name() {
        let mut cx = Cx::empty();
        cx.push("n".into(), Type::Nat, Level::Zero);
        cx.selfref = Some(Rc::new(SelfRef {
            name: "f".into(),
            params: vec![("n".into(), false)],
            n_tyvars: 0,
        }));
        assert_eq!(descends_on_param(&cx, &Term::Var(LocalVar(0))), Some(0));

        cx.push("n".into(), Type::Nat, Level::Zero);
        assert_eq!(descends_on_param(&cx, &Term::Var(LocalVar(0))), None);
        assert_eq!(descends_on_param(&cx, &Term::Var(LocalVar(1))), Some(0));
    }

    #[test]
    fn guarded_self_call_selects_the_ih_without_an_elaborator() {
        let cx = nat_guarded_context(Type::Nat);
        let predecessor = Expr {
            kind: heather_syntax::ExprKind::Var("predecessor".into()),
            span: SPAN,
        };
        let (term, ty, level) = elab_self_call(
            &FakeSelfCall,
            &cx,
            std::slice::from_ref(&predecessor),
            false,
            SPAN,
        )
        .expect("guarded call");
        assert_eq!(term, Term::Var(LocalVar(0)));
        assert_eq!(ty, Type::Nat);
        assert_eq!(level, Level::Zero);
    }

    #[test]
    fn self_call_spill_reuses_explicit_application() {
        let result = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Nat),
        };
        let cx = nat_guarded_context(result);
        let args = [
            Expr {
                kind: heather_syntax::ExprKind::Var("predecessor".into()),
                span: SPAN,
            },
            Expr {
                kind: heather_syntax::ExprKind::Num(0),
                span: SPAN,
            },
        ];
        let (term, ty, level) =
            elab_self_call(&FakeSelfCall, &cx, &args, false, SPAN).expect("spilled call");
        assert!(matches!(term, Term::App { .. }));
        assert_eq!(ty, Type::Nat);
        assert_eq!(level, Level::Zero);
    }
}
