//! Parameter defaults at a call (docs/named-arguments-design.md §9).
//!
//! A call that leaves a defaulted parameter out reaches the spine walkers
//! with [`application::PARAM_DEFAULT`]'s marker in that slot
//! (`application::resolve_named`), so the default is checked where a named
//! argument would be: at the parameter's domain as this call instantiates it,
//! once that domain is known. This module is what checking the marker does.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, ExprKind, Span};

use crate::{Cx, ElabError, Elaborator, R, ResolutionScope, application, err};

impl Elaborator {
    /// A defaulted parameter, filled: its default checked at `expected`, the
    /// parameter's domain with this call's earlier arguments substituted.
    ///
    /// The goal is open in the caller's locals, so the default is checked in
    /// the caller's context — made [`Cx::hygienic`], so that a tactic sees
    /// every hypothesis while no caller's name can capture one of the
    /// default's — and with names resolving in the declaration's own scope.
    /// A caller's local named `trivial` therefore cannot change what
    /// `h: True := trivial` means (§9.4).
    pub(crate) fn elab_param_default(&self, cx: &Cx, args: &[Expr], expected: &Type, lvl: &Level, span: Span) -> R<Term> {
        let (Some(ExprKind::Str(owner)), Some(ExprKind::Num(index))) =
            (args.first().map(|a| &a.kind), args.get(1).map(|a| &a.kind))
        else {
            return err("internal parameter default has the wrong form", span);
        };
        let params = self.names.global(owner).map(|g| Rc::clone(&g.params));
        let param = index.as_u64().and_then(|i| params.as_ref()?.get(usize::try_from(i).ok()?));
        let Some((name, default)) = param.and_then(|p| Some((p.name.clone(), Rc::clone(p.default.as_ref()?)))) else {
            return err("internal parameter default names no defaulted parameter", span);
        };
        let callee = owner.rsplit("::").next().unwrap_or(owner);
        let goal = self.spell_type_source(cx, expected).or_else(|| self.spell_type(cx, expected)).unwrap_or_else(|| "its type".into());
        let hidden = cx.hygienic();
        let _scope = self.use_scope(&default.scope);
        self.elab_check(&hidden, &default.expr, expected, lvl).map_err(|error| ElabError::Elab {
            msg: format!("`{callee}`'s `{name}` was left to its default, which did not give `{goal}` here: {}; \
                give it by name (`{name} := …`)", match error {
                    ElabError::Elab { msg, .. } => msg,
                    other => other.to_string(),
                }),
            span,
        })
    }

    /// Install a stored declaration scope for one read of stored syntax. The
    /// guard restores the caller's scope on every return path.
    pub(crate) fn use_scope<'a>(&'a self, scope: &Rc<crate::names::Scope>) -> ResolutionScope<'a> {
        self.resolution_scopes.borrow_mut().push(Rc::clone(scope));
        ResolutionScope { stack: &self.resolution_scopes }
    }
}

/// Is `e` an omitted default's marker? Such an argument is checking-only:
/// it has no type of its own until the parameter's domain gives it one.
pub(crate) fn is_param_default(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::App { head, named, .. }
        if named.is_empty() && matches!(&head.kind, ExprKind::Var(v) if v == application::PARAM_DEFAULT))
}
