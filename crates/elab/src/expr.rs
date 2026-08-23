//! The staged bidirectional-elaboration view.
//!
//! `ExprElab` is intentionally smaller than expression elaboration itself.
//! Each migration adds the capability it genuinely needs; it never receives
//! an `&Elaborator`, registry commit access, or a cloned session.

use std::cell::Cell;
use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::reduce::OutOfFuel;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, ExprKind, Span, Ty, TyKind};

use crate::goals::GoalAllocator;
use crate::oracle::SemanticOracle;
use crate::{Cx, ElabError, R, err};

/// The expression-layer capabilities migrated so far.
///
/// Local Γ is supplied per operation rather than stored: recursive descent
/// changes it constantly. Dynamic Ψ scope and fuel are already one value in
/// `semantic`; declaration effects are split into the two narrow operations
/// expression leaves currently need.
pub(crate) struct ExprElab<'a> {
    semantic: SemanticOracle,
    goals: GoalAllocator<'a>,
    slot_probe_target: &'a Cell<Option<Span>>,
}

impl<'a> ExprElab<'a> {
    pub(crate) fn new(
        semantic: SemanticOracle,
        goals: GoalAllocator<'a>,
        slot_probe_target: &'a Cell<Option<Span>>,
    ) -> Self {
        Self {
            semantic,
            goals,
            slot_probe_target,
        }
    }

    pub(crate) fn whnf_type(&self, cx: &Cx, ty: &Type) -> Result<Type, OutOfFuel> {
        self.semantic.whnf_type(&cx.gamma, ty)
    }

    pub(crate) fn whnf_term(&self, cx: &Cx, term: &Term) -> Result<Term, OutOfFuel> {
        self.semantic.whnf_term(&cx.gamma, term)
    }

    /// Closed type forms that need no name, term, or lowering service.
    pub(crate) fn type_leaf(&self, ty: &Ty) -> Option<R<(Type, Level)>> {
        match &ty.kind {
            TyKind::Nat => Some(Ok((Type::Nat, Level::Zero))),
            TyKind::Univ { level } => Some(Ok((
                Type::Ty(Level::constant(*level)),
                Level::constant(level + 1),
            ))),
            TyKind::Ctx | TyKind::TyCode { .. } | TyKind::Code { .. } => Some(err(
                "`Ctx`/`TyCode`/`Code` are meta-layer types: they belong in a \
                 `meta fn` signature (docs/in-language-map-design.md §3)",
                ty.span,
            )),
            _ => None,
        }
    }

    /// Inference leaves whose result is independent of session registries.
    pub(crate) fn infer_leaf(&self, e: &Expr) -> Option<R<(Term, Type, Level)>> {
        match &e.kind {
            ExprKind::ArgSlot(_) => Some(match self.slot_probe_target.get() {
                Some(target) if target != e.span => Ok((
                    Term::Var(heather_kernel::term::LocalVar(0)),
                    Type::Nat,
                    Level::Zero,
                )),
                _ => Err(ElabError::ArgSlotEscape { span: e.span }),
            }),
            ExprKind::Univ { level } => Some(Ok((
                Term::TmTy(Level::constant(*level)),
                Type::Ty(Level::constant(level + 1)),
                Level::constant(level + 2),
            ))),
            ExprKind::Hole(_) => Some(err(
                "a hole here has no expected type — annotate it (`let p: T = ?;`) \
                 or write the call fully explicitly (`@f(a, b, ?p)`)",
                e.span,
            )),
            ExprKind::Num(n) => {
                let mut term = Term::Zero;
                for _ in 0..*n {
                    term = Term::Succ(Rc::new(term));
                }
                Some(Ok((term, Type::Nat, Level::Zero)))
            }
            _ => None,
        }
    }

    /// Checking leaves whose only declaration effect is goal allocation.
    pub(crate) fn check_leaf(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
        level: &Level,
        hint: Option<(&str, &str)>,
    ) -> Option<R<Term>> {
        match &e.kind {
            ExprKind::ArgSlot(_) => Some(match self.slot_probe_target.get() {
                Some(target) if target != e.span => {
                    Ok(Term::Var(heather_kernel::term::LocalVar(0)))
                }
                _ => Err(ElabError::ArgSlotEscape { span: e.span }),
            }),
            ExprKind::Hole(name) => Some(self.goals.written_hole(
                cx,
                name.as_deref(),
                hint,
                expected.clone(),
                level.clone(),
                e.span,
            )),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use heather_kernel::term::{GlobalCtx, GlobalVar};

    use super::*;
    use crate::goals::GoalArena;

    const SPAN: Span = Span { start: 0, end: 1 };

    #[test]
    fn leaf_elaboration_needs_no_elaborator_or_session_fixture() {
        let mut goals = GoalArena::default();
        goals.configure(1, 0);
        let slot_probe = Cell::new(None);
        let expr = ExprElab::new(
            SemanticOracle::in_world(GlobalCtx::default(), 32),
            goals.allocator(),
            &slot_probe,
        );
        let cx = Cx::empty();

        let numeral = Expr {
            kind: ExprKind::Num(2),
            span: SPAN,
        };
        let (term, ty, level) = expr.infer_leaf(&numeral).unwrap().unwrap();
        assert!(matches!(term, Term::Succ(_)));
        assert_eq!((ty, level), (Type::Nat, Level::Zero));

        let hole = Expr {
            kind: ExprKind::Hole(Some("proof".into())),
            span: SPAN,
        };
        let term = expr
            .check_leaf(&cx, &hole, &Type::Nat, &Level::Zero, None)
            .unwrap()
            .unwrap();
        assert!(matches!(
            term,
            Term::GlobalTm {
                var: GlobalVar(0),
                ..
            }
        ));
    }

    #[test]
    fn slot_probe_state_is_an_explicit_capability() {
        let goals = GoalArena::default();
        let slot_probe = Cell::new(Some(SPAN));
        let expr = ExprElab::new(
            SemanticOracle::in_world(GlobalCtx::default(), 32),
            goals.allocator(),
            &slot_probe,
        );
        let slot = Expr {
            kind: ExprKind::ArgSlot(None),
            span: SPAN,
        };
        assert!(matches!(
            expr.infer_leaf(&slot).unwrap(),
            Err(ElabError::ArgSlotEscape { .. })
        ));
    }
}
