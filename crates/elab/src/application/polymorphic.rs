//! Instantiate a deferred bare polymorphic argument from a partial domain.

use heather_kernel::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{GlobalVar, LocalSubst, Term, Type};
use heather_syntax::{Expr, ExprKind};

use crate::{Cx, Elaborator, R, SolutionCheck};
use crate::unification::{Sol, U, partially_zonked, unify_ty_root, zonked};
use crate::application::Callables;
use crate::gendefs::GeneratedDefs;
use crate::app_unify::AppUnify;

/// Polymorphic application's part of the elaborator.
pub(crate) struct Polymorphic<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Polymorphic<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Polymorphic<'_> {
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
        let prefix = Callables(self).bare_implicit_prefix(cx, name)
            .or_else(|| Callables(self).value_skel(cx, name).map(|s| s.leading_implicit()).filter(|&k| k > 0))?;
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
            let mut doms = Vec::with_capacity(prefix);
            for slot in 0..k {
                let Type::Pi { dom, cod, cod_level, .. } = self.whnf_in(cx, &ty, k, argument.span)? else {
                    return Ok(None);
                };
                doms.push((*dom).clone());
                let meta = Rc::new(Term::GlobalTm {
                    var: GlobalVar::index(slot), subst: LocalSubst::id(&cx.gamma),
                });
                ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(meta));
                level = cod_level;
            }
            let pattern = GeneratedDefs(self).unspell_ty_deep(&ty).unwrap_or(ty);
            let subject = partially_zonked(parameter, n, sols, &cx.gamma);
            let subject = GeneratedDefs(self).unspell_ty_deep(&subject).unwrap_or(subject);
            let type_args = |t: &Term, d: u32| AppUnify(self).spine_type_args(cx, t, d, argument.span);
            let canonical_head = |t: &Term, d: u32| AppUnify(self).canonical_head(cx, t, d);
            let respell = |t: &Type| GeneratedDefs(self).respell_ty(cx, t);
            let constructor = |t: &Type| GeneratedDefs(self).constructor_spelling(cx, t, argument.span);
            let slot_view = |t: &Term| GeneratedDefs(self).slot_view(t);
            let check = SolutionCheck::new(self, cx, &doms, k);
            let admit = |i: usize, s: &Term, sols: &[Sol]| check.admit(i, s, sols);
            let slot_type = |i: usize, sols: &[Sol]| doms.get(i).and_then(|t| zonked(t, k, sols));
            let next_head = |t: &Term| AppUnify(self).next_head(cx, t);
            let unfold_constant = |t: &Term| AppUnify(self).unfold_constant(cx, t);
            let succ_pred = |t: &Term| AppUnify(self).succ_pred(t);
            let u = U {
                gamma: &cx.gamma, subject_metas: Some((n, sols)),
                type_args: &type_args, canonical_head: &canonical_head, respell: &respell,
                constructor: &constructor, slot_view: &slot_view, slot_type: &slot_type,
                admit: &admit, disagree: None, next_head: &next_head, unfold_constant: &unfold_constant,
                succ_pred: &succ_pred, guesses: crate::unification::Guesses::Take, clash: None,
            };
            unify_ty_root(&u, &pattern, &subject, k, 0, &mut inner);
            check.settle(&mut inner);
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
