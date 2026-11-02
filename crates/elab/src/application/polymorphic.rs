//! Instantiate a deferred bare polymorphic argument from a partial domain.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{GlobalVar, LocalSubst, Term, Type};
use heather_syntax::{Expr, ExprKind};

use crate::{Cx, Elaborator, R};
use crate::unification::{Sol, U, partially_zonked, unify_ty_root, zonked};

impl Elaborator {
    /// Read a bare function's instance from a partially solved parameter.
    /// Its leading implicits live in a separate scratch world: only subject
    /// subterms that zonk in the enclosing call may become solutions here.
    /// Once the instance is fully known, ordinary checking emits the term;
    /// its committed type can then teach the enclosing call's remaining
    /// implicits. An incomplete instance stays deferred for later arguments.
    pub(crate) fn infer_bare_polymorphic_argument(
        &self, cx: &Cx, argument: &Expr, parameter: &Type, n: u32, sols: &[Sol],
    ) -> Option<R<(Term, Type, Level)>> {
        let ExprKind::Var(name) = &argument.kind else { return None; };
        let prefix = self.bare_implicit_prefix(cx, name)
            .or_else(|| self.value_skel(cx, name).map(|s| s.leading_implicit()).filter(|&k| k > 0))?;
        // A written polymorphic domain wants the uninstantiated value.
        if let Type::Pi { dom, .. } = parameter
            && zonked(dom, n, sols)
                .and_then(|t| self.whnf(cx, &t, argument.span).ok())
                .is_some_and(|t| matches!(t, Type::Ty(_)))
        {
            return None;
        }
        let attempt = || -> R<Option<(Term, Type, Level)>> {
            let (_, mut ty, mut level) = self.resolve_reading(cx, name, argument.span)?;
            let k = prefix as u32;
            ty = ty.shift_global(k);
            let mut inner = vec![Sol::Unsolved; prefix];
            for slot in 0..k {
                let Type::Pi { cod, cod_level, .. } = self.whnf(cx, &ty, argument.span)? else {
                    return Ok(None);
                };
                let meta = Rc::new(Term::GlobalTm {
                    var: GlobalVar(slot), subst: LocalSubst::id(&cx.gamma),
                });
                ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(meta));
                level = cod_level;
            }
            let pattern = self.unspell_deep_now(&ty, k).unwrap_or(ty);
            let subject = partially_zonked(parameter, n, sols, &cx.gamma);
            let subject = self.unspell_deep_now(&subject, n).unwrap_or(subject);
            let type_args = |t: &Term, d: u32| self.spine_type_args(cx, t, d, argument.span);
            let canonical_head = |t: &Term, d: u32| self.canonical_head(cx, t, d);
            let respell = |t: &Type| self.respell_ty(cx, t);
            let constructor = |t: &Type| self.constructor_spelling(cx, t, argument.span);
            let slot_view = |t: &Term| self.slot_view(t);
            let u = U {
                gamma: &cx.gamma, subject_metas: Some((n, sols)),
                type_args: &type_args, canonical_head: &canonical_head, respell: &respell,
                constructor: &constructor, slot_view: &slot_view,
            };
            unify_ty_root(&u, &pattern, &subject, k, 0, &mut inner);
            // Even an unused implicit must be determined; zonking only the
            // result type would miss it and let ordinary checking guess.
            if inner.iter().any(|s| s.solved().is_none()) { return Ok(None); }
            let Some(ty) = zonked(&pattern, k, &inner) else { return Ok(None); };
            let term = self.elab_check(cx, argument, &ty, &level)?;
            Ok(Some((term, ty, level)))
        };
        match attempt() {
            Ok(Some(result)) => Some(Ok(result)),
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        }
    }
}
