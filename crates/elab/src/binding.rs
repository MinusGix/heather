//! Refusals of binding statements that name their reason
//! (docs/sequencing-surface-design.md §10, layer-1 rows).
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
/// (docs/sequencing-surface-design.md §18).
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
}
