//! Parameter defaults at a call (docs/named-arguments-design.md §9).
//!
//! A call that leaves a defaulted parameter out reaches the spine walkers
//! with [`application::PARAM_DEFAULT`]'s marker in that slot
//! (`application::resolve_named`), so the default is checked where a named
//! argument would be: at the parameter's domain as this call instantiates it,
//! once that domain is known. This module is what checking the marker does.
//!
//! A default may mention an earlier parameter (`k: Nat := n`). At the call
//! that name is bound to the call's argument for it, as a `let` binds an
//! alias, so the default reads the argument rather than any name the caller
//! can spell (§9.6).

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, ExprKind, Span};

use crate::application::ParamMeta;
use crate::context::Alias;
use crate::unification::EarlierArg;
use crate::{Cx, ElabError, Elaborator, R, ResolutionScope, application, datarepr, err};

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
    ///
    /// Each earlier parameter the default mentions is bound, under its own
    /// name, to this call's argument for it, out of `earlier`: the call's
    /// arguments before this parameter, committed world, with their
    /// instantiated domains. The bindings are aliases, like a `let`'s, so the
    /// default's term is the one it would be with the arguments written in.
    pub(crate) fn elab_param_default(
        &self,
        cx: &Cx,
        args: &[Expr],
        expected: &Type,
        lvl: &Level,
        span: Span,
        earlier: &[EarlierArg],
    ) -> R<Term> {
        let (Some(ExprKind::Str(owner)), Some(ExprKind::Num(index))) =
            (args.first().map(|a| &a.kind), args.get(1).map(|a| &a.kind))
        else {
            return err("internal parameter default has the wrong form", span);
        };
        let params = self.names.global(owner).map(|g| Rc::clone(&g.params));
        let index = index.as_u64().and_then(|i| usize::try_from(i).ok());
        let param = index.and_then(|i| params.as_ref()?.get(i));
        let (Some(params), Some(index), Some((name, default))) =
            (&params, index, param.and_then(|p| Some((p.name.clone(), Rc::clone(p.default.as_ref()?)))))
        else {
            return err("internal parameter default names no defaulted parameter", span);
        };
        let callee = owner.rsplit("::").next().unwrap_or(owner);
        let goal = self.spell_type_source(cx, expected).or_else(|| self.spell_type(cx, expected)).unwrap_or_else(|| "its type".into());
        let mut hidden = cx.hygienic();
        for j in mentioned_parameters(params, index) {
            let Some(arg) = earlier.iter().find(|e| e.param == j) else {
                return err(
                    format!("internal: `{callee}`'s `{name}` defaults to an expression mentioning `{}`, \
                        and this call did not hand its argument to the default", params[j].name),
                    span,
                );
            };
            hidden.aliases.push(Rc::new(Alias {
                name: params[j].name.clone(),
                depth: hidden.names.len(),
                term: Rc::clone(&arg.term),
                ty: arg.ty.clone(),
                level: arg.level.clone(),
                skel: params[j].skel.clone(),
                spliced: None,
            }));
        }
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

/// The earlier parameters `params[index]`'s default mentions, by index: the
/// value parameters before it whose names occur free in it. A type parameter
/// is never one, since the declaration refuses a default that mentions one.
/// Empty for a parameter with no default.
pub(crate) fn mentioned_parameters(params: &[ParamMeta], index: usize) -> Vec<usize> {
    let Some(default) = params.get(index).and_then(|p| p.default.as_ref()) else {
        return Vec::new();
    };
    (0..index)
        .filter(|&j| {
            !params[j].is_type
                && datarepr::mentions_free(&default.expr, std::slice::from_ref(&params[j].name), &mut Vec::new())
        })
        .collect()
}

/// Is `e` an omitted default's marker? Such an argument is checking-only:
/// it has no type of its own until the parameter's domain gives it one.
pub(crate) fn is_param_default(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::App { head, named, .. }
        if named.is_empty() && matches!(&head.kind, ExprKind::Var(v) if v == application::PARAM_DEFAULT))
}
