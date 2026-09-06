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
use heather_syntax::{Expr, ExprKind, LamBinder, Span, Ty, TyKind};

use crate::application::{Skel, SkelBinder, has_implicit_mark, skel_of_ty};
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

/// Registry and dispatch policies needed by the surface-universe bridge.
///
/// `ExprElab` owns the bridge itself: expression-shaped types are decoded and
/// type-shaped expressions are quoted here.  These queries keep the policies
/// that identify declared families, rewrite operators, and respell registered
/// types with their existing owners.
pub(crate) trait UniverseElab: StructuralTypeElab {
    /// Rewrite an operator occurring in type position to its named call.
    fn rewrite_type_operator(&self, cx: &Cx, expression: &Expr) -> R<Option<Expr>>;

    /// Lower an indexed family or value-parameterized record application.
    fn lower_declared_expression_type(
        &self,
        cx: &Cx,
        expression: &Expr,
        span: Span,
    ) -> R<Option<(Type, Level)>>;

    /// Read the inferred type through registry-aware structural spelling.
    fn read_inferred_type(&self, cx: &Cx, inferred: &Type, span: Span) -> R<Type>;

    /// Shape of a visible declared type former used in expression position.
    fn visible_type_former(&self, cx: &Cx, name: &str) -> Option<TypeFormerShape>;
}

/// The declaration facts the universe bridge needs for `D(v̄)` routing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TypeFormerShape {
    pub(crate) indexed: bool,
    pub(crate) value_parameters: usize,
}

/// The one emission chokepoint, for the annotation slots this module fills in
/// (`docs/annotation-component-respell-design.md` §2.5). Its own trait rather
/// than a method on the two that need it: a `Refl`'s element type and a
/// `Lam`'s domain are reached through different services, and one method on
/// one supertrait is what keeps them one spelling.
pub(crate) trait EmissionElab {
    /// `None` keeps the caller's original. The structural view has no
    /// registry, so it keeps every original.
    fn emit_ty(&self, _cx: &Cx, _ty: &Type, _depth: u32) -> Option<Type> {
        None
    }
}

/// Registry-aware access to the expected type's structural spelling.
pub(crate) trait ExpectedTypeElab: EmissionElab {
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

/// Diagnostic spelling for checking forms that inspect an expected type.
pub(crate) trait ExpectedTypeDiagnosticsElab: ExpectedTypeElab {
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

/// Annotation lowering shared by the two lambda modes.
pub(crate) trait LambdaBinderElab: EmissionElab {
    fn lower_lambda_annotation(&self, cx: &Cx, annotation: &Ty) -> R<(Type, Level)>;
}

/// The root services required by checking a lambda against a function type.
pub(crate) trait LambdaCheckingElab:
    ExpectedTypeDiagnosticsElab + RecursiveCheckingElab + LambdaBinderElab
{
    fn lambda_domains_convert(
        &self,
        cx: &Cx,
        annotation: &Type,
        expected: &Type,
        level: &Level,
    ) -> bool;
}

/// Recursive synthesis required when a fully annotated lambda infers.
pub(crate) trait LambdaInferenceElab: LambdaBinderElab {
    fn infer_lambda_body(&self, cx: &Cx, body: &Expr) -> R<(Term, Type, Level)>;
}

/// Whether inferred implicit binder marks have a consumer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LambdaInferenceMode {
    Ordinary,
    LetSkeletonHarvest,
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
        if n == 0 { Term::Zero } else { Term::NatLit(n) }
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
            TyKind::Squash(inner) => Some(elab.lower_type(cx, inner).map(|(ty, level)| {
                (
                    Type::Squash {
                        level: level.clone(),
                        ty: Rc::new(ty),
                    },
                    level,
                )
            })),
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

    /// Lower an expression occupying a type-syntax slot.
    ///
    /// This is the decoding direction of the surface-universe bridge.  The
    /// registry-aware alternatives are tried before ordinary inference, just
    /// as declaration syntax requires; the final `El` is the kernel's own
    /// decoding operation rather than an elaborator coercion.
    pub(crate) fn lower_expression_type(
        &self,
        elab: &impl UniverseElab,
        cx: &Cx,
        expression: &Expr,
        span: Span,
    ) -> R<(Type, Level)> {
        if let Some(rewritten) = elab.rewrite_type_operator(cx, expression)? {
            return self.lower_expression_type(elab, cx, &rewritten, span);
        }
        if let Some(lowered) = elab.lower_declared_expression_type(cx, expression, span)? {
            return Ok(lowered);
        }
        let (term, inferred, _) = elab.infer_type_endpoint(cx, expression)?;
        let Type::Ty(level) = elab.read_inferred_type(cx, &inferred, span)? else {
            return err(
                "this is not a type: only an expression whose type is a \
                 universe (`Type<n>`) can be used where a type is expected",
                span,
            );
        };
        Ok((
            Type::El {
                level: level.clone(),
                tm: Rc::new(term),
            },
            level,
        ))
    }

    /// Check an expression where the expected type is `Type<want>`.
    ///
    /// Type syntax is an opportunistic second reading: declared applications
    /// commit to their formation diagnostics, ordinary type-shaped syntax is
    /// tried speculatively, and everything else retains ordinary inference.
    pub(crate) fn check_at_universe(
        &self,
        elab: &impl UniverseElab,
        cx: &Cx,
        expression: &Expr,
        want: &Level,
        span: Span,
    ) -> R<Term> {
        if let Some(ty) = self.type_former_application(elab, cx, expression)? {
            let (lowered, level) = elab.lower_type(cx, &ty)?;
            return Self::quote_type_at(&lowered, &level, want, span);
        }
        if let Some(ty) = expression_as_type(expression)
            && let Ok((lowered, level)) = elab.lower_type(cx, &ty)
        {
            return Self::quote_type_at(&lowered, &level, want, span);
        }
        let (term, _, _) = elab.infer_type_endpoint(cx, expression)?;
        Ok(term)
    }

    fn type_former_application(
        &self,
        elab: &impl UniverseElab,
        cx: &Cx,
        expression: &Expr,
    ) -> R<Option<Ty>> {
        let ExprKind::App { head, args, .. } = &expression.kind else {
            return Ok(None);
        };
        let Some((name, _)) = crate::inductive::named_head(head) else {
            return Ok(None);
        };
        let Some(shape) = elab.visible_type_former(cx, name) else {
            return Ok(None);
        };
        if !shape.indexed && shape.value_parameters == 0 {
            return err(
                format!(
                    "`{name}` takes 0 value argument(s), found {} — where a `Type` is \
                     expected, `{name}` names the type itself, so write it bare",
                    args.len()
                ),
                expression.span,
            );
        }
        Ok(Some(Ty {
            kind: TyKind::OfExpr(Box::new(expression.clone())),
            span: expression.span,
        }))
    }

    fn quote_type_at(elaborated: &Type, level: &Level, want: &Level, span: Span) -> R<Term> {
        if !level.equiv(want) {
            return err(
                format!(
                    "this type is at level {}, but a `Type<{}>` is expected \
                     here — universes in this system are non-cumulative, so a \
                     type does not also inhabit the universes above its own, \
                     and there is no lift",
                    crate::show_level(level),
                    crate::show_level(want),
                ),
                span,
            );
        }
        match code::code_of(elaborated) {
            Some(code) => Ok(code),
            None => err(
                "this type has no code, so it cannot be written where a term is \
                 expected (docs/surface-universe.md §7)",
                span,
            ),
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
            ExprKind::Num(n) => Some(Ok((Self::natural_literal(*n), Type::Nat, Level::Zero))),
            // A type in term position is its kernel code at the next universe.
            ExprKind::Eq(..) | ExprKind::TyLit(..) => Some((|| {
                let ty = expression_as_type(e).expect("classified as type syntax");
                let (ty, level) = elab.lower_type(cx, &ty)?;
                match code::code_of(&ty) {
                    Some(code) => Ok((code, Type::Ty(level.clone()), Level::succ(level))),
                    None => err("this equation has no code", e.span),
                }
            })()),
            ExprKind::CollectionLit(_) => Some(err(
                "a collection literal needs an expected container type (it is \
                 checking-only, like `refl`): annotate it (`let xs: List<T> = \
                 [a, b];`) or use it as an argument",
                e.span,
            )),
            // Root settles local/declaration shadowing before admitting these
            // bare canonical names to the staged view.
            ExprKind::Var(name) if name == "FZ" => Some(err(
                "`FZ` needs an expected `Fin` type (checking position, or an \
                 annotated `let`)",
                e.span,
            )),
            ExprKind::Var(name) if name == "trivial" => Some(Ok((
                Term::Triv { level: Level::Zero },
                Type::Unit { level: Level::Zero },
                Level::Zero,
            ))),
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
                // The element type is copied off the *whnf* of the expected
                // `Id`, i.e. off wherever the elaborator happened to read it,
                // while the kernel's expected is the cascade-respelled
                // statement: the slot goes through the chokepoint like every
                // other emitted one (design §2.5).
                let ty = elab.emit_ty(cx, &ty, 0).map_or(ty, Rc::new);
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
                    // Same slot, same chokepoint as `refl`'s above; the
                    // conversion check just above reads the structural `ty`.
                    let ty = elab.emit_ty(cx, &ty, 0).map_or(ty, Rc::new);
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
            ExprKind::CollectionLit(elems) => {
                Some(self.check_vec_lit(elab, cx, elems, expected, e.span))
            }
            ExprKind::Var(name) if name == "FZ" => {
                Some(self.check_fin_index(elab, cx, None, expected, e.span))
            }
            ExprKind::App { args, .. } if matches!(e.as_named(), Some(("FS", _, false))) => {
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
                    let pred = match crate::inductive::nat_head(&reduced) {
                        crate::inductive::NatHead::Succ(pred) => pred,
                        _ => {
                            return err(
                                format!(
                                    "`{numeral}` is not an index of this `Fin`: a numeral here \
                                 needs the length to reduce to at least {} successor(s), and \
                                 this one reduces to {peeled}",
                                    numeral + 1
                                ),
                                span,
                            );
                        }
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
        elab: &impl ExpectedTypeDiagnosticsElab,
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

    /// Check a written lambda against an expected function spine.
    ///
    /// Binder traversal, skeleton advancement, local context extension, and
    /// term construction are mechanism. The collaborator supplies only the
    /// semantic operations that cross the expression boundary.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_lambda(
        &self,
        elab: &impl LambdaCheckingElab,
        cx: &Cx,
        binders: &[LamBinder],
        body: &Expr,
        expected: &Type,
        level: &Level,
        skel: Option<&Skel>,
        span: Span,
    ) -> R<Term> {
        self.check_lambda_at(
            elab,
            cx,
            binders,
            body,
            expected,
            level,
            skel.map(|s| s.params.as_slice()),
            span,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn check_lambda_at(
        &self,
        elab: &impl LambdaCheckingElab,
        cx: &Cx,
        binders: &[LamBinder],
        body: &Expr,
        expected: &Type,
        level: &Level,
        skel_at: Option<&[SkelBinder]>,
        span: Span,
    ) -> R<Term> {
        let Some((binder, rest)) = binders.split_first() else {
            return elab.check_expression(cx, body, expected, level);
        };
        let head = elab.read_expected_type(cx, expected, span)?;
        let Type::Pi {
            dom_level,
            cod_level,
            dom,
            cod,
        } = head
        else {
            return err(
                format!(
                    "a lambda needs a function type here, found `{}`",
                    elab.display_expected_type(cx, expected)
                ),
                span,
            );
        };

        // An implicit mark promises insertion at uses, so it must agree with
        // a written expected skeleton. Explicit lambda binders remain valid at
        // implicit positions; insertion belongs to the expected type.
        let position = skel_at.and_then(|positions| positions.first());
        if binder.implicit {
            match position {
                Some(position) if position.implicit => {}
                Some(_) => {
                    return err(
                        "this binder is marked implicit, but the expected function \
                         type spells this parameter explicit — the two must agree \
                         position by position",
                        binder.span,
                    );
                }
                None => {
                    return err(
                        "this binder is marked implicit, but the function type \
                         expected here carries no implicitness — it was computed, \
                         not written, and a computed type offers no implicit \
                         insertion (issues/implicit-binders-in-function-types.md)",
                        binder.span,
                    );
                }
            }
        }

        if let Some(annotation) = &binder.ty {
            let (annotation_ty, _) = elab.lower_lambda_annotation(cx, annotation)?;
            if !elab.lambda_domains_convert(cx, &annotation_ty, &dom, &dom_level) {
                return err(
                    format!(
                        "`{}` is annotated with a type that is not the one expected here",
                        binder.name
                    ),
                    annotation.span,
                );
            }
        }

        let binder_skel = position
            .and_then(|position| position.dom.clone())
            .or_else(|| binder.ty.as_ref().and_then(skel_of_ty));
        let inner = Self::extend_lambda_context(cx, binder, &dom, &dom_level, binder_skel);

        let body = if rest.is_empty() {
            elab.check_expression(&inner, body, &cod, &cod_level)?
        } else {
            let rest_skel = skel_at.map(|positions| positions.get(1..).unwrap_or(&[]));
            self.check_lambda_at(elab, &inner, rest, body, &cod, &cod_level, rest_skel, span)?
        };
        // The binder's own annotation is copied off the expected `Π`, which is
        // itself emitted — so this agreed by luck rather than by rule, and the
        // luck ran out wherever the `Π` was not the cascade-respelled one
        // (`emission_walk` listed the site on `lib/ir_v1.hthr`; the numbers
        // are on issues/emission-spelling-chokepoint.md). The context
        // extended above keeps the structural copy, per §3.1's line.
        let dom = elab.emit_ty(cx, &dom, 0).map_or(dom, Rc::new);
        Ok(Term::Lam {
            dom_level,
            cod_level,
            dom,
            body: Rc::new(body),
        })
    }

    /// Infer a fully annotated lambda and synthesize its Π type.
    pub(crate) fn infer_lambda(
        &self,
        elab: &impl LambdaInferenceElab,
        cx: &Cx,
        binders: &[LamBinder],
        body: &Expr,
        mode: LambdaInferenceMode,
    ) -> R<(Term, Type, Level)> {
        let Some((binder, rest)) = binders.split_first() else {
            return elab.infer_lambda_body(cx, body);
        };
        if binder.implicit && mode == LambdaInferenceMode::Ordinary {
            return err(
                "an implicit lambda binder needs a checking position, or a `let` — \
                 its implicitness has nowhere to go from here",
                binder.span,
            );
        }
        let Some(annotation) = &binder.ty else {
            return err(
                format!(
                    "this lambda's binder `{}` needs a type annotation, or the lambda \
                     needs a checking position (`let f: A -> B = λ {} => …;`)",
                    binder.name, binder.name
                ),
                binder.span,
            );
        };
        let (dom, dom_level) = elab.lower_lambda_annotation(cx, annotation)?;
        let inner =
            Self::extend_lambda_context(cx, binder, &dom, &dom_level, skel_of_ty(annotation));
        let (body, cod, cod_level) = self.infer_lambda(elab, &inner, rest, body, mode)?;
        // The λ's emitted domain takes the chokepoint; the `Π` this
        // synthesizes is the type the caller continues with and stays
        // structural (§2.5, §3.1).
        let dom_e = elab.emit_ty(cx, &dom, 0).unwrap_or_else(|| dom.clone());
        Ok((
            Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::new(dom_e),
                body: Rc::new(body),
            },
            Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::new(dom),
                cod: Rc::new(cod),
            },
            Level::max(dom_level, cod_level),
        ))
    }

    fn extend_lambda_context(
        cx: &Cx,
        binder: &LamBinder,
        dom: &Type,
        dom_level: &Level,
        skel: Option<Rc<Skel>>,
    ) -> Cx {
        let mut inner = cx.clone();
        inner.push_skel(binder.name.clone(), dom.clone(), dom_level.clone(), skel);
        if let Type::Ty(universe) = dom {
            inner.tyvars.push(TyVar {
                name: binder.name.clone(),
                ty: Type::El {
                    level: universe.clone(),
                    tm: Rc::new(Term::Var(LocalVar(0))),
                },
                level: universe.clone(),
                depth: inner.names.len(),
            });
        }
        inner
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
        let k = match crate::inductive::nat_head(&len_w) {
            crate::inductive::NatHead::Succ(k) => k,
            crate::inductive::NatHead::Zero => {
                return err("`Fin(0)` is empty, so it has no index", span);
            }
            crate::inductive::NatHead::Neutral => {
                return err(
                    "the length has to reduce to a successor here; `Fin(n)` at an open \
                     `n` has no canonical index",
                    span,
                );
            }
        };
        let (lhs_level, rhs_level) = (Level::Zero, Level::Zero);
        let lhs = Rc::new(Type::Unit { level: Level::Zero });
        let rhs = Rc::new(Type::Fin { len: k });
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
        let mut acc = Term::Triv {
            level: level.clone(),
        };
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

        fn infer_type_endpoint(&self, cx: &Cx, expression: &Expr) -> R<(Term, Type, Level)> {
            self.deepest_context
                .set(self.deepest_context.get().max(cx.names.len()));
            self.deepest_tyvars
                .set(self.deepest_tyvars.get().max(cx.tyvars.len()));
            match &expression.kind {
                ExprKind::Num(n) => {
                    self.inferred_numerals.borrow_mut().push(*n);
                    Ok((Term::Zero, Type::Nat, Level::Zero))
                }
                ExprKind::Var(name) if name == "code" => {
                    Ok((Term::TmNat, Type::Ty(Level::Zero), Level::constant(1)))
                }
                _ => panic!("the fixture only infers numerals and `code`"),
            }
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
            cx: &Cx,
            expression: &Expr,
            expected: &Type,
            level: &Level,
        ) -> R<Term> {
            self.deepest_context
                .set(self.deepest_context.get().max(cx.names.len()));
            assert_eq!((expected, level), (&Type::Nat, &Level::Zero));
            let ExprKind::Num(n) = expression.kind else {
                panic!("the fixture only checks numerals");
            };
            self.checked_numerals.borrow_mut().push(n);
            Ok(Term::Zero)
        }
    }

    impl UniverseElab for StructuralFake {
        fn rewrite_type_operator(&self, _cx: &Cx, _expression: &Expr) -> R<Option<Expr>> {
            Ok(None)
        }

        fn lower_declared_expression_type(
            &self,
            _cx: &Cx,
            _expression: &Expr,
            _span: Span,
        ) -> R<Option<(Type, Level)>> {
            Ok(None)
        }

        fn read_inferred_type(&self, _cx: &Cx, inferred: &Type, _span: Span) -> R<Type> {
            Ok(inferred.clone())
        }

        fn visible_type_former(&self, _cx: &Cx, name: &str) -> Option<TypeFormerShape> {
            (name == "Plain").then_some(TypeFormerShape {
                indexed: false,
                value_parameters: 0,
            })
        }
    }

    impl EmissionElab for StructuralFake {}

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

    impl ExpectedTypeDiagnosticsElab for StructuralFake {
        fn display_expected_type(&self, _cx: &Cx, expected: &Type) -> String {
            format!("{expected:?}")
        }
    }

    impl LambdaBinderElab for StructuralFake {
        fn lower_lambda_annotation(&self, cx: &Cx, annotation: &Ty) -> R<(Type, Level)> {
            self.lower_type(cx, annotation)
        }
    }

    impl LambdaCheckingElab for StructuralFake {
        fn lambda_domains_convert(
            &self,
            _cx: &Cx,
            annotation: &Type,
            expected: &Type,
            level: &Level,
        ) -> bool {
            annotation == expected && level == &Level::Zero
        }
    }

    impl LambdaInferenceElab for StructuralFake {
        fn infer_lambda_body(&self, cx: &Cx, body: &Expr) -> R<(Term, Type, Level)> {
            self.infer_type_endpoint(cx, body)
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
        assert_eq!(term, Term::NatLit(2));
        assert_eq!((ty, level), (Type::Nat, Level::Zero));

        assert_eq!(ExprElab::natural_literal(u64::MAX), Term::NatLit(u64::MAX));

        let trivial = Expr {
            kind: ExprKind::Var("trivial".into()),
            span: SPAN,
        };
        assert!(matches!(
            expr.infer_form(&fake, &cx, &trivial).unwrap().unwrap(),
            (Term::Triv { .. }, Type::Unit { .. }, Level::Zero)
        ));
        let fz = Expr {
            kind: ExprKind::Var("FZ".into()),
            span: SPAN,
        };
        assert!(expr.infer_form(&fake, &cx, &fz).unwrap().is_err());

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
    fn universe_bridge_owns_decoding_quoting_and_fallback() {
        let goals = GoalArena::default();
        let slot_probe = Cell::new(None);
        let expr = view(&goals, &slot_probe);
        let fake = StructuralFake::default();
        let cx = Cx::empty();

        let code = Expr {
            kind: ExprKind::Var("code".into()),
            span: SPAN,
        };
        assert!(matches!(
            expr.lower_expression_type(&fake, &cx, &code, SPAN).unwrap(),
            (Type::El { tm, .. }, Level::Zero) if matches!(&*tm, Term::TmNat)
        ));

        let nat = Expr {
            kind: ExprKind::TyLit(Box::new(Ty {
                kind: TyKind::Nat,
                span: SPAN,
            })),
            span: SPAN,
        };
        assert!(matches!(
            expr.check_at_universe(&fake, &cx, &nat, &Level::Zero, SPAN)
                .unwrap(),
            Term::TmNat
        ));
        assert!(
            expr.check_at_universe(&fake, &cx, &nat, &Level::constant(1), SPAN)
                .is_err()
        );

        let numeral = Expr {
            kind: ExprKind::Num(7),
            span: SPAN,
        };
        assert!(matches!(
            expr.check_at_universe(&fake, &cx, &numeral, &Level::Zero, SPAN)
                .unwrap(),
            Term::Zero
        ));

        let plain_application = Expr {
            kind: ExprKind::App {
                head: Box::new(Expr {
                    kind: ExprKind::Var("Plain".into()),
                    span: SPAN,
                }),
                args: vec![numeral],
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span: SPAN,
        };
        let error = expr
            .check_at_universe(&fake, &cx, &plain_application, &Level::Zero, SPAN)
            .unwrap_err();
        assert!(error.message().contains("takes 0 value argument"));
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
            kind: ExprKind::CollectionLit(vec![
                Expr {
                    kind: ExprKind::Num(3),
                    span: SPAN,
                },
                Expr {
                    kind: ExprKind::Num(4),
                    span: SPAN,
                },
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

        let fz = Expr {
            kind: ExprKind::Var("FZ".into()),
            span: SPAN,
        };
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

    #[test]
    fn lambda_checking_owns_binder_traversal_and_construction() {
        let goals = GoalArena::default();
        let slot_probe = Cell::new(None);
        let expr = view(&goals, &slot_probe);
        let fake = StructuralFake::default();
        let binder = LamBinder {
            name: "x".into(),
            ty: Some(Ty {
                kind: TyKind::Nat,
                span: SPAN,
            }),
            implicit: false,
            span: SPAN,
        };
        let body = Expr {
            kind: ExprKind::Num(4),
            span: SPAN,
        };
        let expected = Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Nat),
        };
        assert!(matches!(
            expr.check_lambda(
                &fake,
                &Cx::empty(),
                &[binder],
                &body,
                &expected,
                &Level::Zero,
                None,
                SPAN,
            )
            .unwrap(),
            Term::Lam { .. }
        ));
        assert_eq!(fake.deepest_context.get(), 1);
        assert_eq!(*fake.checked_numerals.borrow(), [4]);
    }

    #[test]
    fn lambda_inference_names_its_skeleton_harvest_mode() {
        let goals = GoalArena::default();
        let slot_probe = Cell::new(None);
        let expr = view(&goals, &slot_probe);
        let fake = StructuralFake::default();
        let binder = LamBinder {
            name: "A".into(),
            ty: Some(Ty {
                kind: TyKind::Univ { level: 0 },
                span: SPAN,
            }),
            implicit: true,
            span: SPAN,
        };
        let body = Expr {
            kind: ExprKind::Num(1),
            span: SPAN,
        };
        assert!(
            expr.infer_lambda(
                &fake,
                &Cx::empty(),
                std::slice::from_ref(&binder),
                &body,
                LambdaInferenceMode::Ordinary,
            )
            .is_err()
        );
        let (_, ty, _) = expr
            .infer_lambda(
                &fake,
                &Cx::empty(),
                &[binder],
                &body,
                LambdaInferenceMode::LetSkeletonHarvest,
            )
            .unwrap();
        assert!(matches!(ty, Type::Pi { .. }));
        assert_eq!(fake.deepest_context.get(), 1);
        assert_eq!(fake.deepest_tyvars.get(), 1);
    }
}
