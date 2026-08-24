//! The staged bidirectional-elaboration view.
//!
//! `ExprElab` is intentionally smaller than expression elaboration itself.
//! Each migration adds the capability it genuinely needs; it never receives
//! an `&Elaborator`, registry commit access, or a cloned session.

use std::cell::Cell;
use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::reduce::OutOfFuel;
use heather_kernel::term::{LocalVar, Term, Type};
use heather_syntax::{Expr, ExprKind, Span, Ty, TyKind};

use crate::application::{has_implicit_mark, skel_of_ty};
use crate::goals::GoalAllocator;
use crate::oracle::SemanticOracle;
use crate::surface::expression_left_leaf_is_numeral;
use crate::{Cx, ElabError, IMPLICIT_MARK_REFUSED, R, TyVar, err};

/// Recursive services required by primitive structural type forms.
///
/// The mechanism receives these operations per call. It does not retain the
/// implementor or gain access to the session behind it.
pub(crate) trait StructuralTypeElab {
    fn lower_type(&self, cx: &Cx, ty: &Ty) -> R<(Type, Level)>;
    fn lower_named_type(
        &self,
        cx: &Cx,
        name: &str,
        arguments: &[Ty],
        span: Span,
    ) -> R<(Type, Level)>;
    fn infer_type_endpoint(&self, cx: &Cx, expression: &Expr) -> R<(Term, Type, Level)>;
    fn check_type_endpoint(
        &self,
        cx: &Cx,
        expression: &Expr,
        expected: &Type,
        level: &Level,
    ) -> R<Term>;
}

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

    /// Type forms admitted to the staged expression view so far.
    pub(crate) fn type_form(
        &self,
        elab: &impl StructuralTypeElab,
        cx: &Cx,
        ty: &Ty,
    ) -> Option<R<(Type, Level)>> {
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
            // Primitive indexed formation: the element recurses through the
            // type service and the length uses ordinary checking at `Nat`.
            TyKind::Vec { elem, len } => Some((|| {
                // This position has no callable skeleton consumer.
                if has_implicit_mark(elem) {
                    return err(IMPLICIT_MARK_REFUSED, elem.span);
                }
                let (elem, level) = elab.lower_type(cx, elem)?;
                let len = elab.check_type_endpoint(cx, len, &Type::Nat, &Level::Zero)?;
                Ok((
                    Type::Vec {
                        level: level.clone(),
                        elem: Rc::new(elem),
                        len: Rc::new(len),
                    },
                    level,
                ))
            })()),
            // `Fin` has no level parameter in the kernel, so its level is
            // zero regardless of the checked length.
            TyKind::Fin(len) => Some(
                elab.check_type_endpoint(cx, len, &Type::Nat, &Level::Zero)
                    .map(|len| (Type::Fin { len: Rc::new(len) }, Level::Zero)),
            ),
            TyKind::Fn {
                binder, dom, cod, ..
            } => Some((|| {
                let (dom_t, dom_level) = elab.lower_type(cx, dom)?;
                let mut inner = cx.clone();
                // Keep the written domain skeleton beside Γ: insertion in a
                // dependent codomain reads it from this binder.
                let name = binder.clone().unwrap_or_else(|| "#arrow".to_string());
                inner.push_skel(
                    name.clone(),
                    dom_t.clone(),
                    dom_level.clone(),
                    skel_of_ty(dom),
                );
                // A universe binder is also a surface type variable in its
                // codomain (`(A: Type<0>) -> A -> A`).
                if let Type::Ty(level) = &dom_t {
                    inner.tyvars.push(TyVar {
                        name,
                        ty: Type::El {
                            level: level.clone(),
                            tm: Rc::new(Term::Var(LocalVar(0))),
                        },
                        level: level.clone(),
                        depth: inner.names.len(),
                    });
                }
                let (cod_t, cod_level) = elab.lower_type(&inner, cod)?;
                Ok((
                    Type::Pi {
                        dom_level: dom_level.clone(),
                        cod_level: cod_level.clone(),
                        dom: Rc::new(dom_t),
                        cod: Rc::new(cod_t),
                    },
                    Level::max(dom_level, cod_level),
                ))
            })()),
            TyKind::Eq(lhs, rhs) => Some((|| {
                // Numerals have a `Nat` default, not an intrinsic carrier.
                // Infer the other endpoint first when it can direct checking.
                let (lhs_t, rhs_t, endpoint_ty, level) = if expression_left_leaf_is_numeral(lhs) {
                    let (rhs_t, endpoint_ty, level) = elab.infer_type_endpoint(cx, rhs)?;
                    let lhs_t = elab.check_type_endpoint(cx, lhs, &endpoint_ty, &level)?;
                    (lhs_t, rhs_t, endpoint_ty, level)
                } else {
                    let (lhs_t, endpoint_ty, level) = elab.infer_type_endpoint(cx, lhs)?;
                    let rhs_t = elab.check_type_endpoint(cx, rhs, &endpoint_ty, &level)?;
                    (lhs_t, rhs_t, endpoint_ty, level)
                };
                Ok((
                    Type::Id {
                        level: level.clone(),
                        ty: Rc::new(endpoint_ty),
                        lhs: Rc::new(lhs_t),
                        rhs: Rc::new(rhs_t),
                    },
                    level,
                ))
            })()),
            TyKind::Named { name, args } => Some((|| {
                if let Some(argument) = args.iter().find(|argument| has_implicit_mark(argument)) {
                    return err(IMPLICIT_MARK_REFUSED, argument.span);
                }
                elab.lower_named_type(cx, name, args, ty.span)
            })()),
            TyKind::Splice { name } => Some(err(
                format!(
                    "`${name}` cannot splice a type: type codes are layer p and cannot \
                     appear inside layer-c code — bind the type inside the quote instead \
                     (`fun (A: Type<0>) => …`, docs/in-language-map-design.md §3)"
                ),
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
    use std::cell::RefCell;

    use heather_kernel::term::{GlobalCtx, GlobalVar};

    use super::*;
    use crate::goals::GoalArena;

    const SPAN: Span = Span { start: 0, end: 1 };

    #[derive(Default)]
    struct StructuralFake {
        deepest_context: Cell<usize>,
        deepest_tyvars: Cell<usize>,
        inferred_numerals: RefCell<Vec<u64>>,
        checked_numerals: RefCell<Vec<u64>>,
    }

    impl StructuralTypeElab for StructuralFake {
        fn lower_type(&self, cx: &Cx, ty: &Ty) -> R<(Type, Level)> {
            self.deepest_context
                .set(self.deepest_context.get().max(cx.names.len()));
            self.deepest_tyvars
                .set(self.deepest_tyvars.get().max(cx.tyvars.len()));
            match ty.kind {
                TyKind::Nat => Ok((Type::Nat, Level::Zero)),
                TyKind::Univ { level } => {
                    Ok((Type::Ty(Level::constant(level)), Level::constant(level + 1)))
                }
                _ => panic!("the fixture only lowers closed leaves"),
            }
        }

        fn infer_type_endpoint(&self, _cx: &Cx, expression: &Expr) -> R<(Term, Type, Level)> {
            let ExprKind::Num(n) = expression.kind else {
                panic!("the fixture only infers numerals");
            };
            self.inferred_numerals.borrow_mut().push(n);
            Ok((Term::Zero, Type::Nat, Level::Zero))
        }

        fn lower_named_type(
            &self,
            _cx: &Cx,
            name: &str,
            arguments: &[Ty],
            _span: Span,
        ) -> R<(Type, Level)> {
            assert_eq!(name, "Fake");
            assert!(arguments.is_empty());
            Ok((Type::Nat, Level::Zero))
        }

        fn check_type_endpoint(
            &self,
            _cx: &Cx,
            expression: &Expr,
            expected: &Type,
            level: &Level,
        ) -> R<Term> {
            assert_eq!((expected, level), (&Type::Nat, &Level::Zero));
            let ExprKind::Num(n) = expression.kind else {
                panic!("the fixture only checks numerals");
            };
            self.checked_numerals.borrow_mut().push(n);
            Ok(Term::Zero)
        }
    }

    fn view<'a>(goals: &'a GoalArena, slot_probe: &'a Cell<Option<Span>>) -> ExprElab<'a> {
        ExprElab::new(
            SemanticOracle::in_world(GlobalCtx::default(), 32),
            goals.allocator(),
            slot_probe,
        )
    }

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

    #[test]
    fn structural_type_forms_need_only_recursive_lowering_and_term_modes() {
        let goals = GoalArena::default();
        let slot_probe = Cell::new(None);
        let expr = view(&goals, &slot_probe);
        let fake = StructuralFake::default();
        let cx = Cx::empty();

        let function = Ty {
            kind: TyKind::Fn {
                binder: Some("A".into()),
                implicit: false,
                dom: Box::new(Ty {
                    kind: TyKind::Univ { level: 0 },
                    span: SPAN,
                }),
                cod: Box::new(Ty {
                    kind: TyKind::Nat,
                    span: SPAN,
                }),
            },
            span: SPAN,
        };
        let (ty, level) = expr.type_form(&fake, &cx, &function).unwrap().unwrap();
        assert!(matches!(ty, Type::Pi { .. }));
        assert_eq!(level, Level::max(Level::constant(1), Level::Zero));
        assert_eq!(fake.deepest_context.get(), 1);
        assert_eq!(fake.deepest_tyvars.get(), 1);

        let equation = Ty {
            kind: TyKind::Eq(
                Box::new(Expr {
                    kind: ExprKind::Num(3),
                    span: SPAN,
                }),
                Box::new(Expr {
                    kind: ExprKind::Num(4),
                    span: SPAN,
                }),
            ),
            span: SPAN,
        };
        assert!(matches!(
            expr.type_form(&fake, &cx, &equation).unwrap().unwrap().0,
            Type::Id { .. }
        ));
        assert_eq!(*fake.inferred_numerals.borrow(), [4]);
        assert_eq!(*fake.checked_numerals.borrow(), [3]);

        let named = Ty {
            kind: TyKind::Named {
                name: "Fake".into(),
                args: Vec::new(),
            },
            span: SPAN,
        };
        assert_eq!(
            expr.type_form(&fake, &cx, &named).unwrap().unwrap(),
            (Type::Nat, Level::Zero)
        );
    }
}
