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

use heather_syntax::{BIND_SEQ, Expr, ExprKind, Stmt};

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

impl Elaborator {
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
        // The failure path only: a scratch copy, so that the probe leaves no
        // goal, warning or instance behind.
        let probe = self.clone();
        let Ok((_, ty, _)) = probe.elab_infer(cx, input) else { return error };
        let shown = self.display_type(cx, &ty);
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
