//! Refusals of binding statements that name their reason
//! (docs/language/sequencing-surface-design.md §10, layer-1 rows).
//!
//! The parser lowers `let x <- e;` and `e;` to the prelude call
//! `Bind::seq(e, λ #bindN => …)` (`heather_syntax::try_lower`), and ordinary
//! application elaboration finds the carrier and its instance. When that
//! fails *at the bound expression*, the solver's message is about the call
//! it sees (`Bind<M>`, `M`), not about the statement the author wrote. This
//! module recognizes the generated call and, on that failure path only,
//! restates the error in the statement's terms. Nothing here runs on a
//! success, so the lowering's terms and costs are untouched.

use heather_syntax::{BIND_SEQ, ITERATE_THEN, Expr, ExprKind, Stmt};

use crate::{Cx, ElabError, Elaborator};

/// The bound expression of a generated bind, and whether the statement was
/// an expression statement `e;` (its continuation re-binds the slot at a
/// private `#seq` name).
pub(crate) fn generated(e: &Expr) -> Option<(&Expr, bool)> {
    let ExprKind::App { head, args, named, .. } = &e.kind else { return None };
    if !named.is_empty() || args.len() != 2 {
        return None;
    }
    if !matches!(&head.kind, ExprKind::Var(n) if n == BIND_SEQ) {
        return None;
    }
    let ExprKind::Lam { binders, body } = &args[1].kind else { return None };
    let [binder] = binders.as_slice() else { return None };
    if !binder.name.starts_with("#bind") {
        return None;
    }
    let discards = matches!(&body.kind, ExprKind::Block(b)
        if matches!(b.stmts.first(), Some(Stmt::Let { name, expr, .. })
            if name.starts_with("#seq")
                && matches!(&expr.kind, ExprKind::Var(v) if *v == binder.name)));
    Some((&args[0], discards))
}

/// A `while` with no measure, lowered with the rest of its block to
/// `Iterate::then(init, step, λ #bindN => rest)`
/// (docs/language/sequencing-surface-design.md §18).
pub(crate) fn generated_loop(e: &Expr) -> bool {
    let ExprKind::App { head, args, named, .. } = &e.kind else { return false };
    named.is_empty()
        && args.len() == 3
        && matches!(&head.kind, ExprKind::Var(n) if n == ITERATE_THEN)
        && matches!(&args[2].kind, ExprKind::Lam { binders, .. }
            if binders.len() == 1 && binders[0].name.starts_with("#bind"))
}

/// Binding statements' part of the elaborator.
pub(crate) struct Bindings<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Bindings<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Bindings<'_> {
    /// `error`, from elaborating a lowered `while` with no measure `call`,
    /// restated when it is the carrier's iteration operator that is missing:
    /// the block is pure, or its carrier has no `Iterate` instance.
    pub(crate) fn restate_loop_error(&self, cx: &Cx, call: &Expr, expected: Option<&crate::Type>, error: ElabError) -> ElabError {
        let message = error.message();
        // With no carrier to learn, the step's generated `match` on the
        // condition is checked with its type unknown and is the first thing
        // to fail.
        let step_match = match &call.kind {
            ExprKind::App { args, .. } => match args.get(1).map(|a| &a.kind) {
                Some(ExprKind::Lam { body, .. }) => match &body.kind {
                    ExprKind::Block(b) => Some(b.result.span),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
        let at_step = step_match.is_some() && error.span() == step_match && message.contains("needs a motive");
        if error.span() != Some(call.span) && !at_step {
            return error;
        }
        let unbound = message.contains("`Iterate::then`") || message.contains("`Iterate`");
        if !at_step && !unbound && !message.contains("`Iterate<") && !message.contains("type constructor `M`") {
            return error;
        }
        let carrier = expected.filter(|_| !message.contains("is qualified by")).map(|t| self.display_type(cx, t));
        let msg = match carrier {
            Some(shown) => format!(
                "a `while` with no measure may go round forever, so it runs only in a block over a carrier \
                 that can iterate (an `Iterate` instance: `Partial`, `CoTree<_>(E)`), and `{shown}` has \
                 none: give the loop a measure, `while c decreases m {{ … }}`"
            ),
            None => "a `while` with no measure may go round forever, so it runs only in a block over a \
                     carrier that can iterate (an `Iterate` instance, `import itree`; `Partial` and \
                     `CoTree<_>(E)` have one): in pure code, give the loop a measure, `while c decreases m { … }`"
                .to_string(),
        };
        ElabError::Elab { msg, span: call.span }
    }

    /// `error`, from elaborating the generated bind `call`, restated when it
    /// is the carrier search failing at the bound expression `input`.
    pub(crate) fn restate_bind_error(
        &self,
        cx: &Cx,
        input: &Expr,
        discards: bool,
        error: ElabError,
    ) -> ElabError {
        if error.span() != Some(input.span) {
            return error;
        }
        let message = error.message();
        // The solver's goal (`Bind<M>`), its unsolved constructor, or the
        // continuation it could then neither check nor infer.
        if !message.contains("`Bind<")
            && !message.contains("type constructor `M`")
            && !message.contains("`#bind")
        {
            return error;
        }
        // The failure path only: a probe, so that it leaves no goal, warning
        // or instance behind.
        let Some(shown) = self.probe(|| {
            let (_, ty, _) = self.elab_infer(cx, input).ok()?;
            Some(self.display_type(cx, &ty))
        }) else {
            return error;
        };
        let msg = if discards {
            let assign = if matches!(input.kind, ExprKind::Eq(..)) {
                "; an equation is a proposition, so to assign, write `x := e`"
            } else {
                ""
            };
            format!(
                "a statement here discards a pure value: `e;` sequences a computation in a \
                 block over a carrier (a type with a `Bind` instance), and `{shown}` has none{assign}"
            )
        } else {
            format!(
                "`{shown}` has no `Bind` instance: this block is not over a carrier, so \
                 `let … <- e;` has nothing to bind in (write `let x = e;` for a pure value)"
            )
        };
        ElabError::Elab { msg, span: input.span }
    }

    /// Does `expected` WHNF to an application of the declared world type
    /// `world_name` (or the primitive `Squash`)?
    fn expected_is_world(
        &self,
        cx: &Cx,
        world_name: &str,
        expected: &heather_kernel::term::Type,
        span: heather_syntax::Span,
    ) -> bool {
        let Some(carrier) = crate::dispatch::Carriers(self.0).carrier_of_ty(cx, expected, span) else {
            return false;
        };
        if world_name == "Squash" {
            return carrier.key == "Squash";
        }
        if let Some(ind) = self.lookup_inductive(world_name) {
            return carrier.key == crate::names::qkey(&ind.scope.module, &ind.name);
        }
        carrier.written == world_name || carrier.key == world_name
    }

    fn call_unary(head: Expr, arg: Expr, span: heather_syntax::Span) -> Expr {
        Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args: vec![arg],
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        }
    }

    /// Does `expected` WHNF to `Dne<_>`?
    pub(crate) fn is_dne_expected(
        &self,
        cx: &Cx,
        expected: &heather_kernel::term::Type,
        span: heather_syntax::Span,
    ) -> bool {
        self.expected_is_world(cx, "Dne", expected, span)
    }

    /// Strip a parser-inserted `let h = decide_true<P>(e); body` (or
    /// `decide_false`) wrapper from an `if` branch so classical `Dne::em`
    /// can bind `h` directly in `Inl(h)` / `Inr(h)`.
    fn strip_if_evidence(body: &Expr, expected_head: &str) -> (String, Expr) {
        if let ExprKind::Block(b) = &body.kind
            && b.ons.is_empty()
            && b.stmts.len() == 1
            && let Stmt::Let { name, ty: None, expr, opaque: false, .. } = &b.stmts[0]
            && crate::surface::lowered_condition(expr)
                .is_some_and(|c| c.head == expected_head)
        {
            return (name.clone(), (*b.result).clone());
        }
        ("_".to_string(), body.clone())
    }

    /// Classical `if [h:] P { yes } else { no }` inside a `Dne<_>` goal
    /// (issues/proof-worlds-native-inside.md). Called only after decidable
    /// `if` elaboration (`Decide<P>` / `Bool` / mixed) fails, so decidable
    /// conditions are untouched. Lowers constructively to
    /// `Bind::seq(Dne::em(P), λ #dne_em => match #dne_em { Inl(h) => yes, Inr(h) => no })`.
    pub(crate) fn try_classical_if(
        &self,
        cx: &Cx,
        scrut: &Expr,
        arms: &[heather_syntax::Arm],
        expected: &heather_kernel::term::Type,
        lvl: &heather_kernel::level::Level,
        span: heather_syntax::Span,
    ) -> Option<crate::R<heather_kernel::term::Term>> {
        use heather_syntax::{Arm, LamBinder, MatchForm, Pat};

        if self.lookup_global("Dne::em").is_none() {
            return None;
        }
        let cond = crate::surface::lowered_condition(scrut)?;
        if cond.head != "decide_bit" {
            return None;
        }
        // Only fall back when the condition is actually a valid proposition
        // type, so ill-typed conditions like `if 5` keep their existing error.
        if !self.probe(|| self.elab_ty(cx, &cond.ty).is_ok()) {
            return None;
        }
        let yes_arm = arms.iter().find(|a| a.ctor == "True")?;
        let no_arm = arms.iter().find(|a| a.ctor == "False")?;
        let (yes_name, yes_body) = Self::strip_if_evidence(&yes_arm.body, "decide_true");
        let (no_name, no_body) = Self::strip_if_evidence(&no_arm.body, "decide_false");

        let em_var = "#dne_em".to_string();
        let prop_span = cond.ty.span;
        let em_call = Self::call_unary(
            Expr { kind: ExprKind::Var("Dne::em".into()), span: prop_span },
            Expr { kind: ExprKind::TyLit(Box::new(cond.ty)), span: prop_span },
            scrut.span,
        );
        let match_em = Expr {
            kind: ExprKind::Match {
                form: MatchForm::Match,
                generated: true,
                scrut: Box::new(Expr { kind: ExprKind::Var(em_var.clone()), span }),
                eqbind: None,
                motive: None,
                arms: vec![
                    Arm {
                        ctor: "Inl".into(),
                        default: false,
                        binders: vec![Pat::Var { name: yes_name, span: yes_arm.span }],
                        body: yes_body,
                        span: yes_arm.span,
                    },
                    Arm {
                        ctor: "Inr".into(),
                        default: false,
                        binders: vec![Pat::Var { name: no_name, span: no_arm.span }],
                        body: no_body,
                        span: no_arm.span,
                    },
                ],
                // A match on `Dne::em`'s `Or`, whose arms bind the
                // hypotheses in their own patterns: not the `if h:` match
                // that carries a test's name.
                test: None,
            },
            span,
        };
        let cont = Expr {
            kind: ExprKind::Lam {
                binders: vec![LamBinder { name: em_var, ty: None, implicit: false, span }],
                body: Box::new(match_em),
            },
            span,
        };
        let lowered = Self::call_args(
            Expr { kind: ExprKind::Var(heather_syntax::BIND_SEQ.into()), span },
            vec![em_call, cont],
            span,
        );
        Some(self.elab_check(cx, &lowered, expected, lvl))
    }

    /// Elaborate `within W { body }` in checking position
    /// (docs/language/proof-worlds-design.md §2.1).
    pub(crate) fn elab_within_check(
        &self,
        cx: &Cx,
        world: &Expr,
        body: &Expr,
        expected: &heather_kernel::term::Type,
        lvl: &heather_kernel::level::Level,
        span: heather_syntax::Span,
    ) -> crate::R<heather_kernel::term::Term> {
        if let ExprKind::Var(world_name) = &world.kind {
            if self.expected_is_world(cx, world_name, expected, span) {
                return self.elab_check(cx, body, expected, lvl);
            }
            let exit_name = format!("{world_name}::exit");
            if self.lookup_global(&exit_name).is_some() {
                let exit_call = Self::call_unary(
                    Expr { kind: ExprKind::Var(exit_name), span: world.span },
                    body.clone(),
                    span,
                );
                return self.elab_check(cx, &exit_call, expected, lvl);
            }
        }
        let exit_call = Self::call_unary(world.clone(), body.clone(), span);
        self.elab_check(cx, &exit_call, expected, lvl)
    }

    /// Elaborate `within W { body }` in inference position.
    pub(crate) fn elab_within_infer(
        &self,
        cx: &Cx,
        world: &Expr,
        body: &Expr,
        expected: Option<&heather_kernel::term::Type>,
        span: heather_syntax::Span,
    ) -> crate::R<(
        heather_kernel::term::Term,
        heather_kernel::term::Type,
        heather_kernel::level::Level,
    )> {
        if let ExprKind::Var(world_name) = &world.kind {
            if let Some(exp) = expected
                && self.expected_is_world(cx, world_name, exp, span)
            {
                return self.elab_infer(cx, body);
            }
            let exit_name = format!("{world_name}::exit");
            if self.lookup_global(&exit_name).is_some() {
                let exit_call = Self::call_unary(
                    Expr { kind: ExprKind::Var(exit_name), span: world.span },
                    body.clone(),
                    span,
                );
                return self.elab_infer(cx, &exit_call);
            }
        }
        let exit_call = Self::call_unary(world.clone(), body.clone(), span);
        self.elab_infer(cx, &exit_call)
    }

    fn call_args(head: Expr, args: Vec<Expr>, span: heather_syntax::Span) -> Expr {
        Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args,
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        }
    }

    /// Elaborate `within W for x { body }` in checking position
    /// (docs/language/proof-worlds-design.md §3).
    pub(crate) fn elab_within_for_check(
        &self,
        cx: &Cx,
        args: &[Expr],
        expected: &heather_kernel::term::Type,
        lvl: &heather_kernel::level::Level,
        span: heather_syntax::Span,
    ) -> crate::R<heather_kernel::term::Term> {
        let Some(world) = args.first() else {
            return crate::err("`within … for` expects a world and a block", span);
        };
        let ExprKind::Var(world_name) = &world.kind else {
            return crate::err(
                "a pointwise `within W for x { … }` needs a world name `W`",
                world.span,
            );
        };
        let stays_in_world = self.expected_is_world(cx, world_name, expected, span);
        let lowered = match args {
            [_, lam] => {
                let always = Self::call_unary(
                    Expr { kind: ExprKind::Var(format!("{world_name}::always")), span: world.span },
                    lam.clone(),
                    span,
                );
                if stays_in_world {
                    always
                } else {
                    Self::call_unary(
                        Expr {
                            kind: ExprKind::Var(format!("{world_name}::extract")),
                            span: world.span,
                        },
                        always,
                        span,
                    )
                }
            }
            [_, combined, lam] => {
                let callee = if stays_in_world {
                    format!("{world_name}::map")
                } else {
                    format!("{world_name}::extract_with")
                };
                Self::call_args(
                    Expr { kind: ExprKind::Var(callee), span: world.span },
                    vec![combined.clone(), lam.clone()],
                    span,
                )
            }
            _ => return crate::err("`within … for` expects a world and a block", span),
        };
        self.elab_check(cx, &lowered, expected, lvl)
    }

    /// Elaborate `within W for x { body }` in inference position: produces `W(Q)`.
    pub(crate) fn elab_within_for_infer(
        &self,
        cx: &Cx,
        args: &[Expr],
        span: heather_syntax::Span,
    ) -> crate::R<(
        heather_kernel::term::Term,
        heather_kernel::term::Type,
        heather_kernel::level::Level,
    )> {
        let Some(world) = args.first() else {
            return crate::err("`within … for` expects a world and a block", span);
        };
        let ExprKind::Var(world_name) = &world.kind else {
            return crate::err(
                "a pointwise `within W for x { … }` needs a world name `W`",
                world.span,
            );
        };
        let lowered = match args {
            [_, lam] => Self::call_unary(
                Expr { kind: ExprKind::Var(format!("{world_name}::always")), span: world.span },
                lam.clone(),
                span,
            ),
            [_, combined, lam] => Self::call_args(
                Expr { kind: ExprKind::Var(format!("{world_name}::map")), span: world.span },
                vec![combined.clone(), lam.clone()],
                span,
            ),
            _ => return crate::err("`within … for` expects a world and a block", span),
        };
        self.elab_infer(cx, &lowered)
    }

    /// Elaborate anonymous `suffices P by justify; <rest>`
    /// (issues/block-suffices-statement.md). Checks `<rest>` at `P`, then tries
    /// `justify` either at `expected` with an opaque local `__suffices : P` in
    /// scope (for tactics such as `omega`/`linarith`) or as a function
    /// `P → expected` applied to `<rest>`.
    pub(crate) fn elab_suffices(
        &self,
        cx: &Cx,
        args: &[Expr],
        expected: &heather_kernel::term::Type,
        lvl: &heather_kernel::level::Level,
        span: heather_syntax::Span,
    ) -> crate::R<heather_kernel::term::Term> {
        use heather_kernel::level::Level;
        use heather_kernel::rc::Rc;
        use heather_kernel::term::{Term, Type};

        let [prop_expr, justify, rest] = args else {
            return crate::err("internal `suffices` form has the wrong arity", span);
        };
        let ExprKind::TyLit(prop_ty) = &prop_expr.kind else {
            return crate::err("internal `suffices` form expects a type", prop_expr.span);
        };
        let (p_ty, p_lvl) = self.elab_ty(cx, prop_ty)?;
        let p_term = self.elab_check(cx, rest, &p_ty, &p_lvl)?;

        let mut inner_cx = cx.clone();
        inner_cx.push("__suffices".to_string(), p_ty.clone(), p_lvl.clone());
        let expected_in = expected.shift_local(1);

        let checks_at = |target_cx: &Cx, term: &Term, goal: &Type, goal_lvl: &Level| -> bool {
            let psi = self.goal_psi();
            crate::stats::time_kernel(|| {
                heather_kernel::typing::check_term(
                    &psi,
                    0,
                    heather_kernel::layer::Layer::Code,
                    &target_cx.gamma,
                    term,
                    goal,
                    goal_lvl,
                    self.policy.fuel,
                )
                .is_ok()
            })
        };

        let direct = self.probe_unless(|| {
            match self.elab_check(&inner_cx, justify, &expected_in, lvl) {
                Ok(t) if checks_at(&inner_cx, &t, &expected_in, lvl) => (Ok(Some(t)), true),
                Ok(_) => (Ok(None), false),
                Err(e) => (Err(e), false),
            }
        });
        if let Ok(Some(j_term)) = direct {
            let dom_ann = Rc::new(self.annotation_type(cx, &p_ty, 0));
            let cod_ann = Rc::new(expected_in);
            return Ok(Term::App {
                fun: Rc::new(Term::Lam {
                    dom_level: p_lvl.clone(),
                    cod_level: lvl.clone(),
                    dom: Rc::clone(&dom_ann),
                    body: Rc::new(j_term),
                }),
                dom_level: p_lvl,
                cod_level: lvl.clone(),
                dom: dom_ann,
                cod: cod_ann,
                arg: Rc::new(p_term),
            });
        }

        let fn_dom = Rc::new(self.annotation_type(cx, &p_ty, 0));
        let fn_cod = Rc::new(expected.shift_local(1));
        let fn_ty = Type::Pi {
            dom_level: p_lvl.clone(),
            cod_level: lvl.clone(),
            dom: Rc::clone(&fn_dom),
            cod: Rc::clone(&fn_cod),
        };
        let fn_lvl = Level::max(p_lvl.clone(), lvl.clone());
        let as_fn = self.probe_unless(|| {
            match self.elab_check(cx, justify, &fn_ty, &fn_lvl) {
                Ok(t) if checks_at(cx, &t, &fn_ty, &fn_lvl) => (Ok(Some(t)), true),
                Ok(_) => (Ok(None), false),
                Err(e) => (Err(e), false),
            }
        });
        if let Ok(Some(f_term)) = as_fn {
            return Ok(Term::App {
                fun: Rc::new(f_term),
                dom_level: p_lvl,
                cod_level: lvl.clone(),
                dom: fn_dom,
                cod: fn_cod,
                arg: Rc::new(p_term),
            });
        }
        // Neither reading checked: re-run the matching one unprobed so its
        // diagnostic or deferred checking note reaches the user.
        let is_fn = self.probe(|| {
            self.elab_infer(cx, justify)
                .ok()
                .is_some_and(|(_, t, _)| matches!(&*crate::inductive::decoded(&t), Type::Pi { .. }))
        });
        if is_fn {
            let f_term = self.elab_check(cx, justify, &fn_ty, &fn_lvl)?;
            Ok(Term::App {
                fun: Rc::new(f_term),
                dom_level: p_lvl,
                cod_level: lvl.clone(),
                dom: fn_dom,
                cod: fn_cod,
                arg: Rc::new(p_term),
            })
        } else {
            let j_term = self.elab_check(&inner_cx, justify, &expected_in, lvl)?;
            let dom_ann = Rc::new(self.annotation_type(cx, &p_ty, 0));
            let cod_ann = Rc::new(expected_in);
            Ok(Term::App {
                fun: Rc::new(Term::Lam {
                    dom_level: p_lvl.clone(),
                    cod_level: lvl.clone(),
                    dom: Rc::clone(&dom_ann),
                    body: Rc::new(j_term),
                }),
                dom_level: p_lvl,
                cod_level: lvl.clone(),
                dom: dom_ann,
                cod: cod_ann,
                arg: Rc::new(p_term),
            })
        }
    }
}
