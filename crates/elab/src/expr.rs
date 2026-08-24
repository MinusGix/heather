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
use crate::code;
use crate::goals::GoalAllocator;
use crate::oracle::SemanticOracle;
use crate::surface::{expression_as_type, expression_left_leaf_is_numeral};
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

/// Registry-aware access to the expected type's structural spelling.
pub(crate) trait ExpectedTypeElab {
    /// Read an expected type through any registry-aware structural spelling.
    fn read_expected_type(&self, cx: &Cx, expected: &Type, span: Span) -> R<Type>;
}

/// The additional semantic decision required by equality checking.
pub(crate) trait EqualityCheckingElab: ExpectedTypeElab {
    /// Conversion in the real goal-statement world.
    fn goal_endpoints_convert(
        &self,
        cx: &Cx,
        lhs: &Term,
        rhs: &Term,
        ty: &Type,
        level: &Level,
    ) -> bool;
}

/// Diagnostic spelling required by the canonical Unit inhabitant.
pub(crate) trait UnitCheckingElab: ExpectedTypeElab {
    fn display_expected_type(&self, cx: &Cx, expected: &Type) -> String;
}

/// Recursive checking required by checking-only indexed constructors.
pub(crate) trait RecursiveCheckingElab {
    fn check_expression(
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
    fn natural_literal(n: u64) -> Term {
        let mut term = Term::Zero;
        for _ in 0..n {
            term = Term::Succ(Rc::new(term));
        }
        term
    }

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

    /// Inference forms admitted to the staged expression view so far.
    pub(crate) fn infer_form(
        &self,
        elab: &impl StructuralTypeElab,
        cx: &Cx,
        e: &Expr,
    ) -> Option<R<(Term, Type, Level)>> {
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
                Some(Ok((Self::natural_literal(*n), Type::Nat, Level::Zero)))
            }
            // A type in term position is its kernel code at the next universe.
            ExprKind::Eq(..) | ExprKind::TyLit(..) => Some((|| {
                let ty = expression_as_type(e).expect("classified as type syntax");
                let (ty, level) = elab.lower_type(cx, &ty)?;
                match code::code_of(&ty) {
                    Some(code) => Ok((code, Type::Ty(level.clone()), Level::succ(level))),
                    None => err("this equation has no code", e.span),
                }
            })()),
            ExprKind::VecLit(_) => Some(err(
                "a vector literal needs an expected type (it is checking-only, like \
                 `refl`): annotate it (`let xs: [T; 2] = [a, b];`) or use it as an \
                 argument",
                e.span,
            )),
            _ => None,
        }
    }

    /// Checking forms admitted to the staged expression view so far.
    ///
    /// Name-shadowing policy is settled before calling this method.
    pub(crate) fn check_form(
        &self,
        elab: &impl EqualityCheckingElab,
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
            ExprKind::Refl => Some((|| {
                let head = elab.read_expected_type(cx, expected, e.span)?;
                let Type::Id { level, ty, lhs, .. } = head else {
                    return err("`refl` needs an `=` expected type", e.span);
                };
                Ok(Term::Refl { level, ty, tm: lhs })
            })()),
            ExprKind::AutoRefl => Some({
                if let Ok(Type::Id {
                    level,
                    ty,
                    lhs,
                    rhs,
                }) = elab.read_expected_type(cx, expected, e.span)
                    && elab.goal_endpoints_convert(cx, &lhs, &rhs, &ty, &level)
                {
                    Ok(Term::Refl { level, ty, tm: lhs })
                } else {
                    self.goals
                        .written_hole(cx, None, hint, expected.clone(), level.clone(), e.span)
                }
            }),
            _ => None,
        }
    }

    /// Checking-only indexed forms whose result type supplies their missing
    /// shape. Name and constructor shadowing policy is settled by the caller.
    pub(crate) fn check_indexed_form(
        &self,
        elab: &impl RecursiveCheckingElab,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
    ) -> Option<R<Term>> {
        match &e.kind {
            ExprKind::VecLit(elems) => Some(self.check_vec_lit(elab, cx, elems, expected, e.span)),
            ExprKind::Var(name) if name == "FZ" => {
                Some(self.check_fin_index(elab, cx, None, expected, e.span))
            }
            ExprKind::App { args, .. }
                if matches!(e.as_named(), Some(("FS", _, false))) =>
            {
                Some(match args.as_slice() {
                    [index] => self.check_fin_index(elab, cx, Some(index), expected, e.span),
                    _ => err("`FS` takes exactly one argument, an index", e.span),
                })
            }
            _ => None,
        }
    }

    /// The non-overloaded numeral readings supplied by the core language.
    /// Other carriers remain the declaration/class resolver's policy.
    pub(crate) fn check_builtin_numeral(
        &self,
        cx: &Cx,
        numeral: u64,
        expected: &Type,
        span: Span,
    ) -> Option<R<Term>> {
        match &*crate::inductive::decoded(expected) {
            Type::Nat => Some(Ok(Self::natural_literal(numeral))),
            Type::Fin { len } => Some((|| {
                // Peel `numeral + 1` successors off the length; the residue
                // is the folded base used by the kernel's canonical schema.
                let mut base = Rc::clone(len);
                for peeled in 0..=numeral {
                    let reduced = self.whnf_term(cx, &base).map_err(|_| ElabError::Elab {
                        msg: "out of fuel reducing a term".into(),
                        span,
                    })?;
                    let Term::Succ(pred) = reduced else {
                        return err(
                            format!(
                                "`{numeral}` is not an index of this `Fin`: a numeral here \
                                 needs the length to reduce to at least {} successor(s), and \
                                 this one reduces to {peeled}",
                                numeral + 1
                            ),
                            span,
                        );
                    };
                    base = pred;
                }
                let numeral = numeral as usize;
                Ok(crate::wf::fin_index(numeral, numeral + 1, &base))
            })()),
            _ => None,
        }
    }

    /// The canonical inhabitant of Unit/True. Name and constructor shadowing
    /// have already been decided by root orchestration.
    pub(crate) fn check_unit_form(
        &self,
        elab: &impl UnitCheckingElab,
        cx: &Cx,
        expected: &Type,
        span: Span,
    ) -> R<Term> {
        match elab.read_expected_type(cx, expected, span)? {
            Type::Unit { level } => Ok(Term::Triv { level }),
            _ => err(
                format!(
                    "`trivial` proves `True`, but `{}` is expected here",
                    elab.display_expected_type(cx, expected)
                ),
                span,
            ),
        }
    }

    fn check_fin_index(
        &self,
        elab: &impl RecursiveCheckingElab,
        cx: &Cx,
        succ_of: Option<&Expr>,
        expected: &Type,
        span: Span,
    ) -> R<Term> {
        let what = if succ_of.is_some() { "FS" } else { "FZ" };
        let expected = &*crate::inductive::decoded(expected);
        let Type::Fin { len } = expected else {
            return err(format!("`{what}` needs an expected `Fin` type"), span);
        };
        let len_w = self.whnf_term(cx, len).map_err(|_| ElabError::Elab {
            msg: "out of fuel reducing a term".into(),
            span,
        })?;
        let Term::Succ(k) = &len_w else {
            return if matches!(&len_w, Term::Zero) {
                err("`Fin(0)` is empty, so it has no index", span)
            } else {
                err(
                    "the length has to reduce to a successor here; `Fin(n)` at an open \
                     `n` has no canonical index",
                    span,
                )
            };
        };
        let (lhs_level, rhs_level) = (Level::Zero, Level::Zero);
        let lhs = Rc::new(Type::Unit { level: Level::Zero });
        let rhs = Rc::new(Type::Fin { len: Rc::clone(k) });
        match succ_of {
            None => Ok(Term::Inl {
                lhs_level,
                rhs_level,
                lhs,
                rhs,
                val: Rc::new(Term::Triv { level: Level::Zero }),
            }),
            Some(index) => {
                let index = elab.check_expression(cx, index, &rhs, &Level::Zero)?;
                Ok(Term::Inr {
                    lhs_level,
                    rhs_level,
                    lhs,
                    rhs,
                    val: Rc::new(index),
                })
            }
        }
    }

    fn check_vec_lit(
        &self,
        elab: &impl RecursiveCheckingElab,
        cx: &Cx,
        elems: &[Expr],
        expected: &Type,
        span: Span,
    ) -> R<Term> {
        // Preserve the folded constructor: full WHNF would turn `Vec` into
        // its Unit/Sigma encoding before this checking-only form can see it.
        let expected = &*crate::inductive::decoded(expected);
        let Type::Vec { level, elem, len } = expected else {
            return err("a vector literal needs a `[T; n]` expected type", span);
        };
        let (level, elem) = (level.clone(), Rc::clone(elem));
        let len = self
            .semantic
            .whnf_term_opaque(&cx.gamma, len)
            .map_err(|_| ElabError::Elab {
                msg: "ran out of fuel reducing a vector literal's expected length".into(),
                span,
            })?;
        let Some(k) = crate::inductive::nat_value(&len) else {
            return err(
                "a vector literal needs a literal length here; a vector of a \
                 variable length has to come from a binder",
                span,
            );
        };
        if k != elems.len() {
            return err(
                format!(
                    "this vector literal has {} element(s) but {k} are expected",
                    elems.len()
                ),
                span,
            );
        }
        let mut acc = Term::Triv { level: level.clone() };
        for (j, element) in elems.iter().enumerate().rev() {
            let element = elab.check_expression(cx, element, &elem, &level)?;
            acc = Term::Pair {
                fst_level: level.clone(),
                snd_level: level.clone(),
                fst_ty: Rc::clone(&elem),
                snd_ty: Rc::new(Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(elem.shift_local(1)),
                    len: Rc::new(crate::inductive::nat_lit(elems.len() - 1 - j)),
                }),
                fst: Rc::new(element),
                snd: Rc::new(acc),
            };
        }
        Ok(acc)
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

    impl ExpectedTypeElab for StructuralFake {
        fn read_expected_type(&self, _cx: &Cx, expected: &Type, _span: Span) -> R<Type> {
            Ok(expected.clone())
        }
    }

    impl EqualityCheckingElab for StructuralFake {
        fn goal_endpoints_convert(
            &self,
            _cx: &Cx,
            lhs: &Term,
            rhs: &Term,
            _ty: &Type,
            _level: &Level,
        ) -> bool {
            lhs == rhs
        }
    }

    impl UnitCheckingElab for StructuralFake {
        fn display_expected_type(&self, _cx: &Cx, expected: &Type) -> String {
            format!("{expected:?}")
        }
    }

    impl RecursiveCheckingElab for StructuralFake {
        fn check_expression(
            &self,
            cx: &Cx,
            expression: &Expr,
            expected: &Type,
            level: &Level,
        ) -> R<Term> {
            self.check_type_endpoint(cx, expression, expected, level)
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
        let fake = StructuralFake::default();
        let (term, ty, level) = expr.infer_form(&fake, &cx, &numeral).unwrap().unwrap();
        assert!(matches!(term, Term::Succ(_)));
        assert_eq!((ty, level), (Type::Nat, Level::Zero));

        let hole = Expr {
            kind: ExprKind::Hole(Some("proof".into())),
            span: SPAN,
        };
        let term = expr
            .check_form(&fake, &cx, &hole, &Type::Nat, &Level::Zero, None)
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
            expr.infer_form(&StructuralFake::default(), &Cx::empty(), &slot)
                .unwrap(),
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

        let type_literal = Expr {
            kind: ExprKind::TyLit(Box::new(Ty {
                kind: TyKind::Nat,
                span: SPAN,
            })),
            span: SPAN,
        };
        assert!(matches!(
            expr.infer_form(&fake, &cx, &type_literal).unwrap().unwrap(),
            (Term::TmNat, Type::Ty(Level::Zero), _)
        ));
    }

    #[test]
    fn equality_checking_names_its_two_semantic_capabilities() {
        let mut goals = GoalArena::default();
        goals.configure(1, 0);
        let slot_probe = Cell::new(None);
        let expr = view(&goals, &slot_probe);
        let fake = StructuralFake::default();
        let cx = Cx::empty();
        let identity = Type::Id {
            level: Level::Zero,
            ty: Rc::new(Type::Nat),
            lhs: Rc::new(Term::Zero),
            rhs: Rc::new(Term::Zero),
        };
        let refl = Expr {
            kind: ExprKind::Refl,
            span: SPAN,
        };
        assert!(matches!(
            expr.check_form(&fake, &cx, &refl, &identity, &Level::Zero, None)
                .unwrap()
                .unwrap(),
            Term::Refl { .. }
        ));

        let unequal = Type::Id {
            level: Level::Zero,
            ty: Rc::new(Type::Nat),
            lhs: Rc::new(Term::Zero),
            rhs: Rc::new(Term::Succ(Rc::new(Term::Zero))),
        };
        let auto = Expr {
            kind: ExprKind::AutoRefl,
            span: SPAN,
        };
        assert!(matches!(
            expr.check_form(&fake, &cx, &auto, &unequal, &Level::Zero, None)
                .unwrap()
                .unwrap(),
            Term::GlobalTm { .. }
        ));
    }

    #[test]
    fn indexed_checking_needs_only_recursive_checking() {
        let goals = GoalArena::default();
        let slot_probe = Cell::new(None);
        let expr = view(&goals, &slot_probe);
        let fake = StructuralFake::default();
        let cx = Cx::empty();
        let vec_ty = Type::Vec {
            level: Level::Zero,
            elem: Rc::new(Type::Nat),
            len: Rc::new(crate::inductive::nat_lit(2)),
        };
        let literal = Expr {
            kind: ExprKind::VecLit(vec![
                Expr { kind: ExprKind::Num(3), span: SPAN },
                Expr { kind: ExprKind::Num(4), span: SPAN },
            ]),
            span: SPAN,
        };
        assert!(matches!(
            expr.check_indexed_form(&fake, &cx, &literal, &vec_ty)
                .unwrap()
                .unwrap(),
            Term::Pair { .. }
        ));
        assert_eq!(*fake.checked_numerals.borrow(), [4, 3]);

        let fz = Expr { kind: ExprKind::Var("FZ".into()), span: SPAN };
        let fin_ty = Type::Fin {
            len: Rc::new(Term::Succ(Rc::new(Term::Zero))),
        };
        assert!(matches!(
            expr.check_indexed_form(&fake, &cx, &fz, &fin_ty)
                .unwrap()
                .unwrap(),
            Term::Inl { .. }
        ));

        assert!(matches!(
            expr.check_builtin_numeral(&cx, 0, &Type::Nat, SPAN)
                .unwrap()
                .unwrap(),
            Term::Zero
        ));
        assert!(matches!(
            expr.check_builtin_numeral(&cx, 0, &fin_ty, SPAN)
                .unwrap()
                .unwrap(),
            Term::Inl { .. }
        ));
    }

    #[test]
    fn unit_checking_composes_expected_type_reading_with_diagnostics() {
        let goals = GoalArena::default();
        let slot_probe = Cell::new(None);
        let expr = view(&goals, &slot_probe);
        let fake = StructuralFake::default();
        assert!(matches!(
            expr.check_unit_form(
                &fake,
                &Cx::empty(),
                &Type::Unit { level: Level::constant(2) },
                SPAN,
            )
            .unwrap(),
            Term::Triv { level } if level == Level::constant(2)
        ));
    }
}
