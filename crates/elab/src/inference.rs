//! Inference's part of the elaborator: a written expression's term and type.

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{LocalSubst, LocalVar, Term, Type};

use heather_syntax::{Arm, Expr, ExprKind, MatchForm, Span, Ty, TyKind};

use crate::{
    ConditionType, DotResolution, Elaborator, MATCH_EQ, PRELUDE_MODULE, PackedFamily, R, application,
    binding, err, expr, inductive, iwf_family, literals, matching, names, recursion, statements, stats,
    surface, vec,
};
use crate::app_unify::AppUnify;
use crate::application::{Callables, skel_params};
use crate::binding::Bindings;
use crate::constructor::Constructors;
use crate::context::Cx;
use crate::diagnostics::ElabError;
use crate::dispatch::{Carriers, Members, Operators, Projections};
use crate::gendefs::GeneratedDefs;
use crate::indexed::IndexedFamilies;
use crate::inductive::Inductives;
use crate::iwf_family::IwfFamily;
use crate::literals::Literals;
use crate::matching::Routes;
use crate::mismatch_notes::MismatchNotes;
use crate::name_lookup::NameLookup;
use crate::names::NameRes;
use crate::oracle::Unfold;
use crate::patterns::Patterns;
use crate::quote::Quotation;
use crate::registered::Registered;
use crate::rewrite::Rewrites;
use crate::surface::{
    Condition, condition_connective, condition_expression, decide_call, is_true_of, lowered_condition,
    rebuild_connective,
};
use crate::traits::Classes;

/// Inference's part of the elaborator: a written expression's term and type.
pub(crate) struct Inference<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Inference<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Inference<'_> {
    fn elab_squash_ind(
        &self,
        cx: &Cx,
        scrut: &Expr,
        motive: &Expr,
        case: &Expr,
    ) -> R<(Term, Type, Level)> {
        let (mbinders, mbody) =
            matching::motive_lam(motive, 1, "write `squash_ind(q, λ z => B, λ x => b)`")?;
        let (scrut_t, scrut_ty, _) = self.elab_infer(cx, scrut)?;
        let head = self.whnf(cx, &scrut_ty, scrut.span)?;
        let squash_ty = head.clone();
        let Type::Squash {
            level: src_level,
            ty: src_ty,
        } = head
        else {
            return err("`squash_ind` needs a scrutinee of type `∥A∥`", scrut.span);
        };
        let mut mcx = cx.clone();
        mcx.push(mbinders[0].clone(), squash_ty, src_level.clone());
        let (motive_t, dst_level) = self.elab_ty(&mcx, &mbody)?;

        let ExprKind::Lam { binders, body } = &case.kind else {
            return err(
                "the `squash_ind` case is a lambda: write `λ x => b`",
                case.span,
            );
        };
        if binders.len() != 1 || binders[0].ty.is_some() {
            return err(
                "the `squash_ind` case binds one unannotated witness: `λ x => b`",
                case.span,
            );
        }
        let mut bcx = cx.clone();
        bcx.push(
            binders[0].name.clone(),
            (*src_ty).clone(),
            src_level.clone(),
        );
        let packed = Rc::new(Term::Squash {
            level: src_level.clone(),
            ty: Rc::new(src_ty.shift_local(1)),
            tm: Rc::new(Term::Var(LocalVar(0))),
        });
        let inner =
            motive_t.apply_local(&LocalSubst::id(&cx.gamma).shift_local(1).extended(packed));
        let branch_ty = Type::Squash {
            level: dst_level.clone(),
            ty: Rc::new(inner),
        };
        let case_t = self.elab_check(&bcx, body, &branch_ty, &dst_level)?;
        let scrut_t = Rc::new(scrut_t);
        let result_inner =
            motive_t.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&scrut_t)));
        let result = Type::Squash {
            level: dst_level.clone(),
            ty: Rc::new(result_inner),
        };
        Ok((
            Term::ElimSquash {
                src_level,
                dst_level: dst_level.clone(),
                src_ty,
                motive: Rc::new(motive_t),
                case: Rc::new(case_t),
                scrut: scrut_t,
            },
            result,
            dst_level,
        ))
    }

    /// [`Elaborator::elab_infer`] plus, when the caller is in **checking** position
    /// and inference is the fallback, the expected type it would otherwise
    /// discard (already whnf'd).
    ///
    /// One consumer: [`application::apply_implicit`], which uses it to solve
    /// implicits that no argument's type mentions — the congruence rule of
    /// `issues/congruence-by-anti-unification.md`, whose whole premise is
    /// that the information is in the expected type and nowhere else. Every
    /// other arm ignores it; inference stays inference, and this is a hint
    /// for one hook rather than a second checking mode.
    pub(crate) fn elab_infer_at(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<(Term, Type, Level)> {
        if let Some((input, discards)) = binding::generated(e) {
            return self
                .elab_infer_at_written(cx, e, expected)
                .map_err(|error| Bindings(self).restate_bind_error(cx, input, discards, error));
        }
        if binding::generated_loop(e) {
            return self
                .elab_infer_at_written(cx, e, expected)
                .map_err(|error| Bindings(self).restate_loop_error(cx, e, expected, error));
        }
        self.elab_infer_at_written(cx, e, expected)
    }

    /// [`Self::elab_infer_at`], below the binding-statement restatement.
    fn elab_infer_at_written(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<(Term, Type, Level)> {
        if let Some(receiver) = cx.dot_receiver.as_ref().and_then(|r| r.inference(cx, e)) {
            if let Some(result) = receiver.get() {
                // A failed inference must still be allowed to check against
                // a domain supplied by the enclosing call.
                if result.is_ok() || expected.is_none() {
                    stats::count(stats::Counter::DotReceiverReuses);
                    return result.clone();
                }
            } else if expected.is_none() {
                stats::count(stats::Counter::DotReceiverInferences);
                let result = self.elab_infer_uncached(cx, e, None);
                let _ = receiver.set(result.clone());
                return result;
            }
        }
        self.elab_infer_uncached(cx, e, expected)
    }

    /// `x()` where `x` is a `def`: a value is used as `x`, so the empty call
    /// is refused rather than read as the value
    /// (docs/value-definitions-design.md §2.3). A call with arguments applies
    /// a function-typed value and is not this.
    pub(crate) fn refuse_value_call(&self, cx: &Cx, e: &Expr) -> R<()> {
        let ExprKind::App { head, args, named, .. } = &e.kind else { return Ok(()) };
        if !args.is_empty() || !named.is_empty() {
            return Ok(());
        }
        let ExprKind::Var(name) = &head.kind else { return Ok(()) };
        if cx.names.iter_inner().any(|n| n == name)
            || cx.aliases.iter_inner().any(|a| a.name == *name)
            || cx.selfref.as_ref().is_some_and(|s| s.matches(name))
        {
            return Ok(());
        }
        let NameRes::Found(module) = self.resolve_name(name) else { return Ok(()) };
        let base = name.strip_prefix(&format!("{module}::")).unwrap_or(name);
        if self.names.is_value(&module, base) {
            return err(
                format!("`{name}` is a value (a `def`), not a function: write `{name}`, without `()`"),
                e.span,
            );
        }
        Ok(())
    }

    fn elab_infer_uncached(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<(Term, Type, Level)> {
        self.refuse_value_call(cx, e)?;
        if let ExprKind::App { head, .. } = &e.kind {
            if matches!(&head.kind, ExprKind::Var(name) if name == heather_syntax::BY_TACTIC) {
                return err(
                    "`by` runs a tactic against the statement it must prove, and there is none here; \
                     use it where the expected type is known, or annotate: `let p: P = by t;`",
                    e.span,
                );
            }
        }
        if let Some(site) = cx.corec.as_ref()
            && recursion::surface_self_call(&site.selfref, e).is_some()
        {
            let name = &site.selfref.written_name;
            return err(
                format!(
                    "this call to `{name}` is not guarded: a corecursive call must be a child of the \
                     constructor the definition returns — `C(…, {name}(…), …)` or \
                     `C(…, λ y => {name}(…), …)` (docs/codata-elaborator-design.md §5)"
                ),
                e.span,
            );
        }
        if let Some(condition) = lowered_condition(e) {
            return self.elab_condition(cx, e, &condition, expected);
        }
        let (term, ty, level) = self.elab_infer_written(cx, e, expected)?;
        Ok((self.reduced_decision(cx, e, term), ty, level))
    }

    /// An `if`'s (or a `while`'s) condition, which the parser lowered to
    /// `decide_bit<c>()` (`decide<c>()` with an evidence binder) before any
    /// type was known (issues/bool-conditions-and-literals.md). The
    /// condition's type picks the reading:
    ///
    /// - a **proposition**: its `Decide` instance's bit, as always — this
    ///   reading is tried first and is the whole cost when it succeeds;
    /// - a **`Bool`**: the Bool itself. `decide_bit<b.IsTrue()>()` is `b` by
    ///   the `IsTrue` instance's own `bit := b`, so `if b` is the match on `b`
    ///   that the frontends and `rt` read, with nothing to unfold; with
    ///   evidence (`if h: b`) it is `decide<b.IsTrue()>()`, so `h: b.IsTrue()`;
    /// - a **connective mixing the two** (`b ∧ n = 0`, `(n = 0) && b`): the
    ///   proposition with each `Bool` operand read as `b.IsTrue()`
    ///   ([`Self::mixed_condition`]).
    ///
    /// A condition that is none of these is refused naming the readings; one
    /// that does not elaborate as a term, or is a type, keeps the proposition
    /// reading's own error.
    fn elab_condition(&self, cx: &Cx, e: &Expr, c: &Condition, expected: Option<&Type>) -> R<(Term, Type, Level)> {
        let as_proposition = matching::MatchRollback::new(self.0);
        let proposition_error = match self.elab_infer_written(cx, e, expected) {
            Ok((term, ty, level)) => {
                as_proposition.commit();
                return Ok((self.reduced_decision(cx, e, term), ty, level));
            }
            Err(error) => error,
        };
        drop(as_proposition);
        let mut not_bool = None;
        if let Some(condition) = &c.expr {
            match self.condition_type(cx, condition, !c.evidence) {
                ConditionType::Bool(term, bool_ty) => {
                    if !c.evidence {
                        return Ok((term, bool_ty, Level::Zero));
                    }
                    // The Bool read as the proposition its `IsTrue` instance decides.
                    let span = condition.span;
                    let is_true = Ty { kind: TyKind::OfExpr(Box::new(is_true_of(condition))), span };
                    return self.elab_infer_written(cx, &decide_call(is_true, true, span), expected).map_err(|_| proposition_error);
                }
                ConditionType::Other(got) => not_bool = Some((got, condition.span)),
                ConditionType::Unread => {}
            }
        }
        if let Some(mixed) = self.mixed_condition(cx, c, expected) {
            return mixed;
        }
        if let Some((got, span)) = not_bool {
            return err(
                format!(
                    "a condition is a proposition, decided by its `Decide` instance, or a `Bool`; \
                     this is a value of `{got}`"
                ),
                span,
            );
        }
        Err(proposition_error)
    }

    /// What a condition's expression elaborates to: a `Bool` (the term and
    /// the elaborated `Bool` type), a value of another type (spelled), or
    /// nothing the `Bool` reading can use (no elaboration, or a type). Every
    /// trace of the attempt is rolled back unless `keep` and it is a `Bool`.
    fn condition_type(&self, cx: &Cx, condition: &Expr, keep: bool) -> ConditionType {
        let attempt = matching::MatchRollback::new(self.0);
        let bool_ty = Ty { kind: TyKind::Named { name: "bool::Bool".to_string(), args: Vec::new() }, span: condition.span };
        let Ok((term, ty, _)) = self.elab_infer(cx, condition) else { return ConditionType::Unread };
        let Ok((bool_ty, _)) = self.elab_ty(cx, &bool_ty) else { return ConditionType::Unread };
        let Ok(head) = self.whnf(cx, &ty, condition.span) else { return ConditionType::Unread };
        if matches!(head, Type::Ty(_)) {
            return ConditionType::Unread;
        }
        if self.goal_oracle().convert_type(&cx.gamma, Layer::Prog, &head, &bool_ty, &Level::Zero).is_err() {
            return ConditionType::Other(self.display_type_clean(cx, &ty).unwrap_or_else(|| "this type".into()));
        }
        if keep {
            attempt.commit();
        }
        ConditionType::Bool(term, bool_ty)
    }

    /// A connective whose operands are not all of one kind
    /// (issues/mixed-bool-prop-condition.md): the condition read on the
    /// proposition side, each `Bool` operand as `b.IsTrue()`, so
    /// `if b ∧ n = 0` decides `b.IsTrue() ∧ n = 0`, whose bit is
    /// `b && n.same(0)` by the instances, and `if h: b ∧ n = 0` binds the
    /// evidence of both. The proposition side is the one that keeps evidence
    /// available. A `Bool` subtree is one operand (`(a && b).IsTrue()`), and
    /// `&&`, `||` and `!` between a proposition and a `Bool` are read as
    /// `∧`, `∨` and `¬`. `None` when the condition is no connective or no
    /// operand is a `Bool`: the readings already tried own the error.
    ///
    /// `&&` binds tighter than `=`, so `b && n = 0` is `(b && n) = 0`, never
    /// this reading; it is written `b ∧ n = 0` or `b && (n = 0)`.
    fn mixed_condition(&self, cx: &Cx, c: &Condition, expected: Option<&Type>) -> Option<R<(Term, Type, Level)>> {
        condition_connective(&c.ty)?;
        let mut bools = 0;
        let proposition = self.mixed_operand(cx, &c.ty, true, &mut bools);
        if bools == 0 {
            return None;
        }
        let call = decide_call(proposition, c.evidence, c.ty.span);
        let attempt = matching::MatchRollback::new(self.0);
        let read = self.elab_infer_written(cx, &call, expected);
        if read.is_ok() {
            attempt.commit();
        }
        Some(read.map(|(term, ty, level)| (self.reduced_decision(cx, &call, term), ty, level)))
    }

    /// One operand of [`Self::mixed_condition`], rebuilt: a `Bool` as its
    /// `IsTrue`, a connective over its rebuilt operands, anything else as
    /// written. `root` is the whole condition, already known not to be a
    /// `Bool`.
    fn mixed_operand(&self, cx: &Cx, ty: &Ty, root: bool, bools: &mut usize) -> Ty {
        if !root
            && let Some(operand) = condition_expression(ty)
            && let ConditionType::Bool(..) = self.condition_type(cx, &operand, false)
        {
            *bools += 1;
            return Ty { kind: TyKind::OfExpr(Box::new(is_true_of(&operand))), span: ty.span };
        }
        match condition_connective(ty) {
            Some((name, operands)) => {
                let operands = operands.iter().map(|o| self.mixed_operand(cx, o, false, bools)).collect();
                rebuild_connective(name, operands, ty.span)
            }
            None => ty.clone(),
        }
    }

    /// `decide_bit<P>()` at a resolved instance, read as the instance's own
    /// bit (issues/native-frontend-decided-matches.md): `b.eq_bit(10)` for
    /// `b = '\n'`, `x || y` for a disjunction with each operand read the same
    /// way. An evidence-free `if` matches on this term, so the frontend, the
    /// kernel and `split_all` see the comparisons a step branches on, never
    /// the dictionary record whose proofs mention them. The way a literal's
    /// embedding is read (`reduced_embedding`): the projection unfolds only
    /// as far as the field's body. A local dictionary does not unfold.
    fn reduced_decision(&self, cx: &Cx, e: &Expr, term: Term) -> Term {
        let ExprKind::App { head, args, named, .. } = &e.kind else { return term };
        let ExprKind::TyApp { head: callee, .. } = &head.kind else { return term };
        if !matches!(&callee.kind, ExprKind::Var(name) if name == "decide_bit") || !args.is_empty() || !named.is_empty() {
            return term;
        }
        let Term::GlobalTm { var, .. } = crate::spelling::app_spine(&term).0 else { return term };
        if self.global_abs_of(*var).and_then(|abs| NameLookup(self).global_qualified_name_at(abs)).as_deref() != Some("bool::decide_bit") {
            return term;
        }
        self.instance_bit(cx, &term).unwrap_or(term)
    }

    /// The first reduct of a bit that is a constructor or another
    /// definition's call, with each projected argument (a connective's
    /// operand, itself an instance's bit) read the same way.
    fn instance_bit(&self, cx: &Cx, term: &Term) -> Option<Term> {
        let oracle = self.goal_oracle();
        for reduct in oracle.unfold(&cx.gamma, term, Unfold::InstanceBit) {
            if crate::spelling::is_inj(&reduct) {
                return Some(reduct);
            }
            let (head, _) = crate::spelling::app_spine(&reduct);
            // A global the source cannot name (a class field's accessor) is a
            // step of the instance's own reduction.
            if !self.named_head(head) {
                continue;
            }
            fn operands(elab: &Elaborator, cx: &Cx, term: &Term) -> Term {
                let mut output = term.clone();
                if let Term::App { fun, arg, .. } | Term::AppAt { fun, arg } = &mut output {
                    *fun = Rc::new(operands(elab, cx, fun));
                    let (head, _) = crate::spelling::app_spine(arg);
                    let accessor = matches!(head, Term::GlobalTm { .. }) && !elab.named_head(head);
                    if (accessor || crate::spelling::proj_of(arg).is_some()) && let Some(bit) = Inference(elab).instance_bit(cx, arg) {
                        *arg = Rc::new(bit);
                    }
                }
                output
            }
            return Some(operands(self, cx, &reduct));
        }
        None
    }

    fn elab_infer_written(&self, cx: &Cx, e: &Expr, expected: Option<&Type>) -> R<(Term, Type, Level)> {
        let _depth = expr::ExprDepthGuard::enter(&self.scope.expr_depth, e.span)?;
        // An operator symbol resolves to a name *first*, and then this whole
        // function is the path the written name already took
        // (docs/operators-onto-classes-design.md §4).
        //
        // `None`, deliberately, and not this function's `expected`: that one is
        // the expected type of a *call's result*, reached only from
        // `elab_check_skel`'s inference fallback — i.e. only after the rewrite
        // at the top of `elab_check_skel` has already run. A symbol arrives
        // here unrewritten exactly when the position is genuinely inference,
        // which is the whole of what "a bare symbol has no carrier" still means
        // (docs/bare-symbol-checking-carrier-design.md §5).
        if let Some(rewritten) = Operators(self).op_rewrite(cx, e, None)? {
            return self.elab_infer_at(cx, &rewritten, expected);
        }
        if let Some(rewritten) = NameLookup(self).owner_rewrite(cx, e)? {
            return self.elab_infer_at(cx, &rewritten, expected);
        }
        if let Some(rewritten) = Registered(self).registry_rewrite(cx, e)? {
            return self.elab_infer_at(cx, &rewritten, expected);
        }
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "squash")
            && args.len() == 1
            && named.is_empty()
            && !self.shadowed(cx, "squash")
        {
            let (tm, ty, level) = self.elab_infer(cx, &args[0])?;
            return Ok((
                Term::Squash {
                    level: level.clone(),
                    ty: Rc::new(ty.clone()),
                    tm: Rc::new(tm),
                },
                Type::Squash {
                    level: level.clone(),
                    ty: Rc::new(ty),
                },
                level,
            ));
        }
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "emit_code")
            && !self.shadowed(cx, "emit_code")
            && Constructors(self).ctor_here(cx, "emit_code").is_none()
        {
            if args.len() != 1 || !named.is_empty() {
                return err("`emit_code` takes one positional meta function name", e.span);
            }
            return Quotation(self).elab_emit_code(cx, &args[0], e.span);
        }
        if matches!(e.as_named(), Some(("rel_cong" | "rel_derive", _, false)))
            && !self.shadowed(cx, e.as_named().unwrap().0)
            && Constructors(self).ctor_here(cx, e.as_named().unwrap().0).is_none()
        {
            return err(format!("`{}` needs an expected relation goal; annotate this proof position", e.as_named().unwrap().0), e.span);
        }
        // `rewrite(h, …, in := hyp)` transports a hypothesis: its type is
        // what it proves (docs/equation-rewrite-design.md §7). In checking
        // position it arrives here through the inference fallback.
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "rewrite")
            && named.iter().any(|a| a.name == "in")
            && !self.shadowed(cx, "rewrite")
            && Constructors(self).ctor_here(cx, "rewrite").is_none()
        {
            return Rewrites(self).elab_rewrite_in(cx, args, named, e.span);
        }
        if let ExprKind::App {
            head,
            args,
            named,
            explicit: false,
            goal_oriented: false,
        } = &e.kind
            && matches!(&head.kind, ExprKind::Var(name) if name == "squash_ind")
            && args.len() == 3
            && named.is_empty()
            && !self.shadowed(cx, "squash_ind")
        {
            return self.elab_squash_ind(cx, &args[0], &args[1], &args[2]);
        }
        match &e.kind {
            ExprKind::ArgSlot(_)
            | ExprKind::Univ { .. }
            | ExprKind::Hole(_)
            | ExprKind::Num(_)
            | ExprKind::Eq(..)
            | ExprKind::TyLit(..)
            | ExprKind::CollectionLit(_) => self
                .expr_elab()
                .infer_form(self.0, cx, e)
                .expect("classified as an ExprElab inference form"),
            // `{ let x = e; … result }` — the block's statements extend a
            // clone of `cx`, and its result is inferred there
            // (docs/let-and-blocks-design.md §4.4). Inference-transparent:
            // the block contributes no term of its own, because a `let` is an
            // alias.
            ExprKind::Char(c) => Literals(self).elab_char_infer(cx, *c, e),
            ExprKind::Scaled(lit) => Literals(self).elab_scaled_infer(cx, lit, e),
            ExprKind::Str(text) => Literals(self).elab_string_infer(cx, text, e),
            ExprKind::Block(block) => statements::infer_block(self.0, cx, block),
            ExprKind::RecordUpdate { base, fields } => {
                let literal = Constructors(self).record_update_expr(cx, base, fields, e.span)?;
                self.elab_infer(cx, &literal)
            }
            // Intensional analysis: the result type is written, so unlike a
            // quote this one *infers*
            // (docs/certgen-transcriber-in-language-design.md §3).
            ExprKind::MatchCode {
                scrut,
                motive,
                arms,
            } => Quotation(self).elab_match_code(cx, scrut, motive, arms, e.span),
            // `FZ` cannot infer: it inhabits `Fin(Succ k)` for every `k`
            // (docs/surface-fin-indexing-design.md §3.1). Said only where the
            // name is neither shadowed nor some declaration's constructor.
            ExprKind::Var(name)
                if name == "FZ"
                    && !self.shadowed(cx, name)
                    && Constructors(self).ctor_here(cx, name).is_none() =>
            {
                self.expr_elab()
                    .infer_form(self.0, cx, e)
                    .expect("classified as an ExprElab inference form")
            }
            // `trivial` **infers**, unlike `FZ` and `refl`: the surface spells
            // exactly one `True` and it is `Unit^0`, so there is no level to
            // recover and nothing the expected type could tell this term
            // (`issues/true-prop-trivial-hypotheses.md`).
            ExprKind::Var(name)
                if name == "trivial"
                    && !self.shadowed(cx, name)
                    && Constructors(self).ctor_here(cx, name).is_none() =>
            {
                self.expr_elab()
                    .infer_form(self.0, cx, e)
                    .expect("classified as an ExprElab inference form")
            }
            // A bare reference to a polymorphic declaration, met in
            // *checking* position, is the zero-explicit-argument case of
            // expected-type-directed instantiation
            // (docs/unifier-completeness-design.md §5.3): `app1(id, n)` at
            // `app1(f: Nat -> Nat, n: Nat)` dies as a bare kernel
            // `LevelMismatch` without it, because the polymorphic value's
            // leading `Π (A : Ty 0)` fails the Π–Π `dom_level` comparison
            // before the domains are even looked at. Inference position is
            // unchanged: with nothing to solve from, the reference still
            // resolves to the polymorphic value verbatim.
            //
            // Insertion is *suppressed* when the expected type itself still
            // quantifies over a type (a Π with a universe domain): the
            // parameter asked for the polymorphic function, and instantiating
            // the reference's type parameters can only mis-teach — `El ?A ≟
            // Ty 0` "solves" `?A := ⌜Type 0⌝` and the kernel rejects a term
            // nobody wrote. Passing verbatim is exactly the pre-insertion
            // behavior, and the kernel judges it as before. This is the
            // erased-type approximation of the skeleton suppression rule
            // (docs/implicit-binders-design.md §5.3), which refines it once
            // implicitness travels with the type.
            ExprKind::Var(name) => {
                // Which bare-reference route (if either) is live: the global
                // one, or the value analog. Decided before the whnf so a
                // name with neither pays nothing.
                let global_prefix = if expected.is_some() {
                    Callables(self).bare_implicit_prefix(cx, name)
                } else {
                    None
                };
                let value_skel = if expected.is_some() && global_prefix.is_none() {
                    Callables(self).value_skel(cx, name)
                        .filter(|s| s.leading_implicit() > 0)
                } else {
                    None
                };
                if let Some(expected) = expected
                    && (global_prefix.is_some() || value_skel.is_some())
                    && !matches!(
                        self.whnf(cx, expected, e.span)?,
                        Type::Pi { dom, .. } if matches!(*dom, Type::Ty(_))
                    )
                {
                    if let Some(prefix) = global_prefix {
                        let (head, ty, lvl) = self.resolve(cx, name, e.span)?;
                        let mask = vec![true; prefix];
                        return application::apply_implicit(
                            self.0,
                            cx,
                            name,
                            Callables(self).params_of(name),
                            false,
                            0,
                            true,
                            head,
                            ty,
                            lvl,
                            &[],
                            &mask,
                            Some(expected),
                            false,
                            e.span,
                        );
                    }
                    // The value analog (docs/implicit-binders-design.md
                    // §5.2): a bare local/alias whose *skeleton* opens with
                    // an implicit prefix takes the same route, with the
                    // parameter table synthesized from the skeleton. The
                    // §5.3 skeleton suppression happens one level up (the
                    // checking fallback withholds `expected`), so reaching
                    // here means insertion is wanted.
                    if let Some(skel) = value_skel {
                        let prefix = skel.leading_implicit();
                        let (head, ty, lvl) = self.resolve(cx, name, e.span)?;
                        let mask = vec![true; prefix];
                        return application::apply_implicit(
                            self.0,
                            cx,
                            name,
                            skel_params(&skel),
                            true,
                            0,
                            true,
                            head,
                            ty,
                            lvl,
                            &[],
                            &mask,
                            Some(expected),
                            false,
                            e.span,
                        );
                    }
                }
                self.resolve(cx, name, e.span)
            }
            // `xs[i]` — infers, since the element type comes off the receiver
            // (docs/surface-fin-indexing-design.md §5.2).
            ExprKind::Index { recv, idx } => vec::elab_nth(self.0, cx, recv, idx, e.span),
            ExprKind::Dot {
                recv,
                name,
                tyargs,
                args,
                named,
            } => {
                let receiver_cx = cx.with_dot_receiver(recv);
                let cx = &receiver_cx;
                let resolution =
                    Members(self).resolve_dot(cx, recv, name, tyargs, args, named, e.span)?;
                if !tyargs.is_empty() && !matches!(&resolution, DotResolution::Method(_)) {
                    return err(
                        format!("type arguments after `.{name}` require a method call"),
                        e.span,
                    );
                }
                match resolution {
                DotResolution::Inferred(t, ty, l) => Ok((t, ty, l)),
                DotResolution::Project(t, ty, l, fskel) => match args {
                    None => Ok((t, ty, l)),
                    Some(args) => AppUnify(self)
                        .apply_projection(cx, name, t, ty, l, fskel, args, named, expected, e.span),
                },
                DotResolution::Dispatch(t, ty, l, fskel, dargs) => AppUnify(self)
                    .apply_projection(cx, name, t, ty, l, fskel, &dargs, named, expected, e.span),
                DotResolution::Method(m) => self
                    .elab_infer_at(cx, &m, expected)
                    .map_err(|e| Members(self).method_call_failure(cx, recv, &m, e)),
                }
            }
            // A record literal in inference position: the fields are permuted
            // into declaration order and the instantiation is recovered from
            // them, exactly as for any constructor application
            // (docs/inductive-tier0-lowering.md §2).
            ExprKind::RecordLit {
                name,
                tyargs,
                fields,
            } => {
                let args = Constructors(self).record_lit_args(name, fields, e.span)?;
                let Some(ind) = self.lookup_inductive(name).cloned() else {
                    return Err(self.name_miss(name, format!("unknown type `{name}`"), e.span));
                };
                if tyargs.is_empty() {
                    Constructors(self).infer_ctor(cx, &ind, 0, &args, e.span)
                } else {
                    let head = Expr {
                        kind: ExprKind::Var(name.clone()),
                        span: e.span,
                    };
                    Constructors(self).ctor_at(cx, &head, tyargs, &args, e.span)
                        .unwrap_or_else(|| err(format!("unknown type `{name}`"), e.span))
                }
            }
            // A lambda in inference position needs every binder annotated:
            // with no expected type there is nothing else to take the domain
            // from (docs/surface-function-types.md §5.2).
            ExprKind::Lam { binders, body } => self.expr_elab().infer_lambda(
                self.0,
                cx,
                binders,
                body,
                expr::LambdaInferenceMode::Ordinary,
            ),
            // `f<T, …>` — explicit type application, with or without a call
            // after it (docs/surface-polymorphism.md §1).
            ExprKind::TyApp { head, args } => {
                // A fully instantiated type such as `And<P, Q>` also has a
                // code in inference position (`let result = P ∧ Q`). A
                // same-named constructor with fields cannot infer without
                // arguments; a nullary constructor can, and keeps its term
                // reading. Checking at a universe already chooses the type
                // reading, including that ambiguous nullary case.
                if let ExprKind::Var(name) = &head.kind
                    && let Some(shape) = expr::UniverseElab::visible_type_former(self.0, cx, name)
                    && !shape.indexed && shape.value_parameters == 0
                    && Constructors(self).ctor_here(cx, name)
                        .is_none_or(|(ind, i)| !ind.ctors[i].fields.is_empty())
                {
                    let written = surface::expression_as_type(e).expect("named type application");
                    let (ty, level) = self.elab_ty(cx, &written)?;
                    let term = expr::ExprElab::quote_type_at(self.0, cx, &ty, &level, &level, e.span)?;
                    return Ok((term, Type::Ty(level.clone()), Level::succ(level)));
                }
                if let Some(r) = Constructors(self).ctor_at(cx, head, args, &[] as &[Expr], e.span) {
                    return r;
                }
                let (name, t, ty, lvl, mask) = AppUnify(self).elab_ty_app(cx, head, args, e.span)?;
                // `f<A, B>` with nothing after it, where the parameters that
                // follow the type arguments start with a **solver** parameter:
                // the bare-reference route of
                // docs/unifier-completeness-design.md §5.3, one step along.
                // This is what makes an instance's assembled value work at
                // layer 2 — `op<A, B>` is the member with its `requires`
                // binders still to fill, and filling them is resolution's job
                // (docs/traits-layer2-design.md §9.3).
                //
                // Deliberately narrow: only a leading prefix that *contains a
                // solver parameter* takes it.
                let params = Callables(self).params_of(&name);
                let prefix = mask.iter().take_while(|&&b| b).count();
                let solver_here = (0..prefix).any(|k| {
                    params
                        .get(args.len() + k)
                        .is_some_and(|p| p.solver.is_some())
                });
                // With nothing expected the solvers are filled all the same:
                // the dictionary-awaiting function is no value anything
                // reads, and a receiver (`(Hurwitz::zero<A>).coeff(0)`) or an
                // argument needs the series itself
                // (issues/applied-field-source-spelling-level-mismatch.md).
                if solver_here {
                    return application::apply_implicit(
                        self.0,
                        cx,
                        &name,
                        Rc::clone(&params),
                        false,
                        args.len(),
                        true,
                        t,
                        ty,
                        lvl,
                        &[],
                        &mask[..prefix],
                        expected,
                        false,
                        e.span,
                    );
                }
                Ok((t, ty, lvl))
            }
            ExprKind::App { head, .. }
                if matches!(
                    &head.kind,
                    ExprKind::Var(name)
                        if matches!(
                            name.as_str(),
                            heather_syntax::ANON_CTOR_ONLY
                                | heather_syntax::ANON_CTOR_LEFT
                                | heather_syntax::ANON_CTOR_RIGHT
                        )
                ) =>
            {
                err(
                    "anonymous constructor notation is checking-only: give it an expected type",
                    e.span,
                )
            }
            // `f<T, …>(a, b)` and `@f<T, …>(a, b)`. The type arguments are
            // applied first; what happens to the remaining `{}`-implicits is
            // `@`'s business and not `<…>`'s — the two are orthogonal knobs
            // (issues/at-and-type-arguments.md).
            ExprKind::App {
                head,
                args,
                named,
                explicit,
                goal_oriented,
            } if matches!(head.kind, ExprKind::TyApp { .. }) => {
                let ExprKind::TyApp {
                    head: callee,
                    args: tyargs,
                } = &head.kind
                else {
                    unreachable!("just matched")
                };
                // `Cons<Nat>(1, xs)` — a constructor at a written
                // instantiation. Not a Π-typed head, so it cannot go down the
                // application path at all; the type arguments *are* the
                // instantiation, which is what `infer_ctor` otherwise has to
                // guess (docs/surface-polymorphism.md §10.3).
                if let ExprKind::Var(cn) = &callee.kind
                    && let Some((ind, ci)) = Constructors(self).ctor_here(cx, cn)
                {
                    let borrowed: Vec<&Expr> = args.iter().collect();
                    let named: Vec<_> = named.iter().collect();
                    let permuted =
                        application::resolve_constructor_arguments(&ind, ci, &borrowed, &named, e.span)?;
                    let args = permuted.as_deref().unwrap_or(&borrowed);
                    if let Some(r) = Constructors(self).ctor_at(cx, callee, tyargs, args, e.span) {
                        return r;
                    }
                } else if let Some(r) = Constructors(self).ctor_at(cx, callee, tyargs, args, e.span) {
                    return r;
                }
                // `map<A, B>(f, tail)` — the recursive call *with its type
                // arguments written* (issues/recursive-self-call-type-arguments.md).
                // The self-name is not a global yet, so `elab_ty_app` would
                // report that the declaration takes no type arguments, of a
                // declaration that visibly takes some.
                if let ExprKind::Var(n) = &callee.kind
                    && cx.selfref.as_ref().is_some_and(|s| s.matches(n))
                {
                    recursion::check_self_tyargs(cx, tyargs, head.span)?;
                    application::refuse_named(
                        &format!("a recursive call to `{n}`"),
                        "the termination guard reads *which position* decreases, so a                          self-call's arguments stay where the declaration put them",
                        named,
                    )?;
                    return NameLookup(self).self_call_noted(cx, n, args, *explicit, e.span);
                }
                let (name, t, ty, lvl, mask) = AppUnify(self).elab_ty_app(cx, callee, tyargs, head.span)?;
                let params = Callables(self).params_of(&name);
                let flat;
                let full = if !*explicit && mask.iter().any(|&b| b) {
                    &mask[..]
                } else {
                    flat = vec![false; mask.len()];
                    &flat[..]
                };
                let r = application::resolve_named(
                    &name,
                    false,
                    &params,
                    tyargs.len(),
                    full,
                    args,
                    named,
                    e.span,
                )?;
                let (args, mask): (&[Expr], &[bool]) = match &r {
                    Some((a, m)) => (&a[..], &m[..]),
                    None => (&args[..], &mask[..]),
                };
                if !*explicit && mask.iter().any(|&b| b) {
                    application::apply_implicit(
                        self.0,
                        cx,
                        &name,
                        Rc::clone(&params),
                        false,
                        tyargs.len(),
                        false,
                        t,
                        ty,
                        lvl,
                        args,
                        mask,
                        expected,
                        *goal_oriented,
                        e.span,
                    )
                } else {
                    // The type arguments have consumed the leading parameters,
                    // so argument `i` is now parameter `i + |tyargs|` — which
                    // is what the offset keeps honest for goal-name hints.
                    application::apply_explicit(
                        self.0,
                        cx,
                        Some(&name),
                        params,
                        tyargs.len(),
                        t,
                        ty,
                        lvl,
                        args,
                    )
                }
            }
            // A constructor applied in the curried spelling — `Cons(1)(xs)`.
            // Re-associated into one saturated application, which is what lets
            // it infer: the head alone (`Cons(1)`) has no inferable type, but
            // the whole spine does (docs/constructor-function-values.md §3).
            ExprKind::App { .. } if e.as_named().is_none() && Constructors(self).ctor_spine(cx, e).is_some() => {
                let (ind, i, args, named) = Constructors(self).ctor_spine(cx, e).expect("just checked");
                Constructors(self).lint_manual_list_construction(cx, e, &ind, i);
                if let Some(r) = Constructors(self).infer_defaulted_ctor(cx, &ind, i, args.len() + named.len(), e) {
                    return r;
                }
                let permuted =
                    application::resolve_constructor_arguments(&ind, i, &args, &named, e.span)?;
                let args = permuted.unwrap_or(args);
                Constructors(self).infer_ctor(cx, &ind, i, &args, e.span)
            }
            // An application whose head is *not* a name: no parameter
            // metadata exists for it, so it is always explicit.
            ExprKind::App {
                head,
                args,
                named,
                explicit,
                ..
            } if e.as_named().is_none() => {
                application::refuse_named(
                    "a call whose head is an expression",
                    "named arguments need a callee whose parameters have names, and only a                      *name* has a parameter table here (docs/named-arguments-design.md §7)",
                    named,
                )?;
                if *explicit {
                    return err(
                        "`@` suppresses implicit-argument insertion, which only applies \
                         to a named callee",
                        e.span,
                    );
                }
                let (h, hty, hlvl) = self.elab_infer(cx, head)?;
                application::apply_explicit(
                    self.0,
                    cx,
                    None,
                    Rc::new(Vec::new()),
                    0,
                    h,
                    hty,
                    hlvl,
                    args,
                )
            }
            ExprKind::App {
                args,
                named,
                explicit,
                goal_oriented,
                ..
            } => {
                let (name, _, _) = e.as_named().expect("head is a name");
                let name = &name.to_string();
                // Named arguments (docs/named-arguments-design.md §8.2). Only
                // four of this arm's paths have a parameter table — a
                // constructor, a value head, a global, and the self-call — and
                // everything else in it is a *builtin*: an elaborator form
                // rather than a declaration, with no names to be called by.
                // The test is `shadowed`'s own, which is exactly the guard
                // every builtin arm below already carries, so the two cannot
                // drift apart.
                if !named.is_empty() {
                    if cx.selfref.as_ref().is_some_and(|s| s.matches(name)) {
                        return err(
                            format!(
                                "a recursive call to `{name}` takes positional arguments only:                                  the termination guard reads *which position* decreases, so a                                  self-call's arguments stay where the declaration put them"
                            ),
                            named[0].name_span,
                        );
                    }
                    if !self.shadowed(cx, name) && Constructors(self).ctor_here(cx, name).is_none() {
                        return err(
                            format!(
                                "`{name}` is a built-in form rather than a declaration, so it                                  has no parameter names: write its arguments positionally"
                            ),
                            named[0].name_span,
                        );
                    }
                }
                // `Nat::Monoid(add)` — a class at a type, at its index
                // (docs/operation-indexed-classes-design.md §5.1). Before the
                // ordinary application path, because an indexed class's
                // qualified name is not a callable global: `Bool::Monoid#or`
                // is, and this is what names it.
                if !self.shadowed(cx, name)
                    && name.contains("::")
                    && let Some(r) = Projections(self).class_at_type(cx, name, args, e.span)
                {
                    return r;
                }
                if name == "Succ" {
                    let [arg] = args.as_slice() else {
                        return err("`Succ` takes exactly one argument", e.span);
                    };
                    let arg = self.elab_check(cx, arg, &Type::Nat, &Level::Zero)?;
                    return Ok((Term::Succ(Rc::new(arg)), Type::Nat, Level::Zero));
                }
                // `Fin(n)` where a *term* is expected: the type's code,
                // `TmFin n : Ty 0` — which is what makes
                // `fn Idx(n: Nat) -> Type { Fin(n) }` an ordinary `fn`
                // (docs/surface-fin-indexing-design.md §2.3). Guarded by
                // shadowing, so a local binder or a global still wins *in
                // expression position*, as for `map`/`head`/`cons`; type
                // position is unguarded, and that asymmetry is deliberate.
                if name == "Fin" && !self.shadowed(cx, name) {
                    let [arg] = args.as_slice() else {
                        return err(
                            "`Fin` takes exactly one argument, a length at `Nat`",
                            e.span,
                        );
                    };
                    let len = self.elab_check(cx, arg, &Type::Nat, &Level::Zero)?;
                    return Ok((
                        Term::TmFin { len: Rc::new(len) },
                        Type::Ty(Level::Zero),
                        Level::constant(1),
                    ));
                }
                // `FS(j)` is checking-only, like `refl` and a collection literal:
                // it inhabits `Fin(Succ k)` for every `k`, and nothing in the
                // term names one (§3.1). Said only where `FS` is not some
                // other declaration's constructor and is not shadowed, so a
                // user `FS` still resolves.
                if name == "FS" && !self.shadowed(cx, name) && Constructors(self).ctor_here(cx, name).is_none() {
                    return err(
                        "`FS` needs an expected `Fin` type (checking position, or an \
                         annotated `let`)",
                        e.span,
                    );
                }
                // `xs.map(f)` / `xs.fold(z, f)` — the vector eliminators
                // (docs/container-fields.md §4.2). These are Rust rather than
                // declarations, so they have no `self` to write and take the
                // default subject position: the receiver arrives *first*, as
                // `map(xs, f)` and `fold(xs, z, f)`, which is also how the
                // direct spelling reads best
                // (issues/method-receiver-position.md).
                if name == "map" && !self.shadowed(cx, name) {
                    // Ambiguous declarations are not an absent builtin name.
                    // Dot calls may select by receiver; a bare call retains
                    // the ordinary module ambiguity rule.
                    if matches!(self.resolve_name(name), NameRes::Ambiguous(_)) {
                        return Err(self.name_miss(name, String::new(), e.span));
                    }
                    let [xs, f] = args.as_slice() else {
                        return vec::method_arity_error(self.0, cx, args, name, "`(f)`", e.span);
                    };
                    return vec::elab_map(self.0, cx, f, xs, e.span);
                }
                // `head(v)` / `tail(v)` / `cons(h, t)` — the vector at a
                // successor length *is* a `Σ` (`Vec` computes on its length),
                // so these are its projections and pairing, annotated from
                // the receiver's element type (docs/in-language-map-design.md
                // — the payload of the first in-language artifact is what
                // wanted spellings for them).
                if (name == "head" || name == "tail") && !self.shadowed(cx, name) {
                    let [v] = args.as_slice() else {
                        return vec::method_arity_error(
                            self.0,
                            cx,
                            args,
                            name,
                            "no arguments",
                            e.span,
                        );
                    };
                    return vec::elab_head_tail(self.0, cx, v, name == "head", e.span);
                }
                if name == "cons" && !self.shadowed(cx, name) {
                    let [h, t] = args.as_slice() else {
                        return err("`cons` takes `(head, tail)`", e.span);
                    };
                    return vec::elab_cons(self.0, cx, h, t, e.span);
                }
                // `xs.cong(self)` — the phase-3 lifting
                // (docs/container-proofs.md §6). Recognized by its *self-name*
                // argument rather than by the name `cong`, so a user-defined
                // `cong` theorem still resolves for the ordinary `p.cong(f)`:
                // the self-name is not a value, so it can never be an argument
                // to one (issues/match-recursion.md).
                if name == "cong"
                    && let [xs, f] = args.as_slice()
                    && let ExprKind::Var(f_name) = &f.kind
                    && cx.selfref.as_ref().is_some_and(|s| s.matches(f_name))
                {
                    let (xs_t, xs_ty, _) = self.elab_infer(cx, xs)?;
                    // Decoded, as in `vec::elab_map`: a coded `Vec` is one.
                    if !matches!(*crate::inductive::decoded(&xs_ty), Type::Vec { .. }) {
                        return err("`cong`'s receiver has to be a vector", e.span);
                    }
                    return vec::elab_container_ih(self.0, cx, f_name, &xs_t, true, e.span);
                }
                if name == "fold" && !self.shadowed(cx, name) {
                    let [xs, z, f] = args.as_slice() else {
                        return vec::method_arity_error(
                            self.0,
                            cx,
                            args,
                            name,
                            "`(init, f)`",
                            e.span,
                        );
                    };
                    return vec::elab_fold(self.0, cx, z, f, xs, e.span);
                }
                // `inj(p)` / `inj(p, k)`: the field equations of an equation
                // between the same constructor (§6.2). The field index is a
                // literal, so `p.inj(1)` reads as the second field's equation.
                // The proof comes first in the direct spelling too, so the two
                // spellings are one order rather than two
                // (issues/method-receiver-position.md).
                if name == "inj" && !self.shadowed(cx, name) {
                    let (k, arg) = match args.as_slice() {
                        [arg] => (0, arg),
                        [arg, k] => match &k.kind {
                            ExprKind::Num(n) => match n.as_u64() {
                                Some(n) => (n as usize, arg),
                                None => return err("`inj`'s field index must fit in 64 bits", k.span),
                            },
                            _ => return err("`inj`'s field index must be a numeral", k.span),
                        },
                        _ => return err("`inj` takes `(proof)` or `(proof, field)`", e.span),
                    };
                    return Inductives(self).build_inj(cx, k, arg, e.span);
                }
                if name == "absurd" && !self.shadowed(cx, name) {
                    return err(
                        "`absurd` needs an expected type: use it in checking position \
                         (a `theorem` body, an annotated `let`, or an argument)",
                        e.span,
                    );
                }
                if let Some((ind, i)) = Constructors(self).ctor_here(cx, name) {
                    Constructors(self).lint_manual_list_construction(cx, e, &ind, i);
                    if let Some(r) = Constructors(self).infer_defaulted_ctor(cx, &ind, i, args.len() + named.len(), e) {
                        return r;
                    }
                    let borrowed: Vec<&Expr> = args.iter().collect();
                    let named: Vec<_> = named.iter().collect();
                    let permuted =
                        application::resolve_constructor_arguments(&ind, i, &borrowed, &named, e.span)?;
                    let args = permuted.as_deref().unwrap_or(&borrowed);
                    return Constructors(self).infer_ctor(cx, &ind, i, args, e.span);
                }
                if cx.selfref.as_ref().is_some_and(|s| s.matches(name)) {
                    return NameLookup(self).self_call_noted(cx, name, args, *explicit, e.span);
                }
                // A *value* head — a local, or an alias. With a skeleton it
                // applies with skeleton-directed insertion
                // (docs/implicit-binders-design.md §5.1): same machinery as
                // a named global, with the parameter table synthesized from
                // the skeleton and `param_offset = 0` (a value has no
                // consumed type-argument prefix). `@f(…)` clears the whole
                // mask (§7.1): a value has no `f<…>` spelling, so narrowing
                // to type parameters would leave no complete escape.
                // Without one it is today's explicit application — and never
                // a same-named *global*'s mask or hint table, which is the
                // §4.2 params-passed-not-recovered rule (a local `f` must
                // not borrow a global `f`'s metadata).
                if cx.names.iter_inner().any(|n| n == name) || cx.aliases.iter_inner().any(|a| a.name == *name)
                {
                    let (head, ty, lvl) = self.resolve(cx, name, e.span)?;
                    let skel = Callables(self).value_skel(cx, name);
                    let params = skel
                        .as_deref()
                        .map_or_else(|| Rc::new(Vec::new()), skel_params);
                    let implicit = skel
                        .as_deref()
                        .filter(|s| !*explicit && s.params.iter().any(|b| b.implicit));
                    let Some(skel) = implicit else {
                        let flat = vec![false; params.len()];
                        let r = application::resolve_named(
                            name, true, &params, 0, &flat, args, named, e.span,
                        )?;
                        let args: &[Expr] = r.as_ref().map_or(&args[..], |(a, _)| &a[..]);
                        return application::apply_explicit(
                            self.0,
                            cx,
                            Some(name),
                            params,
                            0,
                            head,
                            ty,
                            lvl,
                            args,
                        );
                    };
                    let mask: Vec<bool> = skel.params.iter().map(|b| b.implicit).collect();
                    let r = application::resolve_named(
                        name, true, &params, 0, &mask, args, named, e.span,
                    )?;
                    let (args, mask): (&[Expr], &[bool]) = match &r {
                        Some((a, m)) => (&a[..], &m[..]),
                        None => (&args[..], &mask[..]),
                    };
                    return application::apply_implicit(
                        self.0,
                        cx,
                        name,
                        params,
                        true,
                        0,
                        false,
                        head,
                        ty,
                        lvl,
                        args,
                        mask,
                        expected,
                        *goal_oriented,
                        e.span,
                    );
                }
                let mask = Callables(self).implicit_mask(name);
                let (head, ty, lvl) = self.resolve(cx, name, e.span)?;
                // `@f(…)` makes the **value** implicits positional and leaves
                // the *type* parameters inferred; `f<T, …>(…)` is the knob for
                // those, and the two compose
                // (issues/at-and-type-arguments.md). So `@` narrows the mask
                // rather than clearing it: without that, adding `<A>` to a
                // declaration would break every `@`-call to it, at the call
                // sites rather than at the declaration.
                let mask = if *explicit {
                    Callables(self).params_of(name)
                        .iter()
                        .map(|p| p.implicit && p.is_type)
                        .collect()
                } else {
                    mask
                };
                let params = Callables(self).params_of(name);
                // The named arguments are permuted into declaration order and
                // the mask is adjusted here, once, so both walkers below see
                // the positional call they have always seen (§8.3).
                let r = application::resolve_named(
                    name, false, &params, 0, &mask, args, named, e.span,
                )?;
                let (args, mask): (&[Expr], &[bool]) = match &r {
                    Some((a, m)) => (&a[..], &m[..]),
                    None => (&args[..], &mask[..]),
                };
                if !mask.iter().any(|&b| b) {
                    application::apply_explicit(
                        self.0,
                        cx,
                        Some(name),
                        params,
                        0,
                        head,
                        ty,
                        lvl,
                        args,
                    )
                } else {
                    application::apply_implicit(
                        self.0,
                        cx,
                        name,
                        params,
                        false,
                        0,
                        false,
                        head,
                        ty,
                        lvl,
                        args,
                        mask,
                        expected,
                        *goal_oriented,
                        e.span,
                    )
                }
            }
            ExprKind::Match {
                form,
                motive: Some(m),
                scrut,
                arms,
                eqbind,
                generated,
            } => {
                let (scrut_t, scrut_ty, scrut_lvl) = self.elab_infer(cx, scrut)?;
                // An indexed scrutinee's motive binds the index too
                // (docs/inductive-indexed-lowering.md §6.1).
                // Route 2b's forded family (docs/inductive-fording-lowering.md
                // §12.1): the same two-binder motive rule as route 1's, over
                // the Σ+`sEq` form instead of the eliminator's.
                if let Some((ind, fam)) = IwfFamily(self).iwf_of_at(cx, &scrut_ty) {
                    let (binders, body) = matching::motive_lam(
                        m,
                        2,
                        "write `as \u{3bb} n z => T` (index, then value)",
                    )?;
                    let mut mcx = cx.clone();
                    mcx.push(binders[0].clone(), fam.ity.clone(), fam.ilvl.clone());
                    mcx.push(
                        binders[1].clone(),
                        fam.ty_at(Term::Var(LocalVar(0)), 1),
                        fam.lvl(),
                    );
                    let (motive2, mlvl) = self.elab_ty(&mcx, &body)?;
                    let result = motive2.apply_local(
                        &LocalSubst::id(&cx.gamma)
                            .extended(Rc::clone(&fam.idx))
                            .extended(Rc::new(scrut_t.clone())),
                    );
                    // §9: the two direct entries into a family lowering need
                    // the preprocessing too — otherwise a `_` arm reaches it
                    // as an unknown constructor. The motive here binds *two*
                    // things (index, then value), so non-dependence is a shift
                    // by two (docs/nested-match-patterns-design.md §5.1).
                    let indep = motive2 == result.shift_local(2);
                    let prepared = Patterns(self).prepare_arms(
                        cx, *form, *generated, arms, &scrut_t, &scrut_ty, &scrut_lvl, &result,
                        indep, &mlvl, e.span,
                    )?;
                    let (acx, arms) = match &prepared {
                        Some((c, a)) => (c, a.as_slice()),
                        None => (cx, arms.as_slice()),
                    };
                    let t = IwfFamily(self).elab_match_iwf(
                        acx,
                        *form,
                        &ind,
                        &fam,
                        arms,
                        scrut_t,
                        motive2,
                        mlvl.clone(),
                        crate::iwf_family::IndexMotive::Plain,
                        e.span,
                    )?;
                    return Ok((t, result, mlvl));
                }
                if let Some((ind, fam)) = IndexedFamilies(self).indexed_of_at(cx, &scrut_ty) {
                    let (binders, body) = matching::motive_lam(
                        m,
                        2,
                        "write `as \u{3bb} n z => T` (index, then value)",
                    )?;
                    let (ity, ilvl) = IndexedFamilies(self).index_type_of(cx, &ind, e.span)?;
                    let mut mcx = cx.clone();
                    mcx.push(binders[0].clone(), ity, ilvl);
                    mcx.push(
                        binders[1].clone(),
                        fam.el_at(Term::Var(LocalVar(0)), 1),
                        fam.level.clone(),
                    );
                    let (motive2, mlvl) = self.elab_ty(&mcx, &body)?;
                    let result = motive2.apply_local(
                        &LocalSubst::id(&cx.gamma)
                            .extended(Rc::clone(&fam.idx))
                            .extended(Rc::new(scrut_t.clone())),
                    );
                    let indep = motive2 == result.shift_local(2);
                    let prepared = Patterns(self).prepare_arms(
                        cx, *form, *generated, arms, &scrut_t, &scrut_ty, &scrut_lvl, &result,
                        indep, &mlvl, e.span,
                    )?;
                    let (acx, arms) = match &prepared {
                        Some((c, a)) => (c, a.as_slice()),
                        None => (cx, arms.as_slice()),
                    };
                    let t = IndexedFamilies(self).elab_match_indexed(
                        acx,
                        *form,
                        &ind,
                        &fam,
                        arms,
                        scrut_t,
                        motive2,
                        mlvl.clone(),
                        e.span,
                    )?;
                    return Ok((t, result, mlvl));
                }
                let (binders, body) = matching::motive_lam(m, 1, "write `as \u{3bb} z => T`")?;
                let mut mcx = cx.clone();
                mcx.push(binders[0].clone(), scrut_ty.clone(), scrut_lvl.clone());
                let (motive, mlvl) = self.elab_ty(&mcx, &body)?;
                let result = motive
                    .apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(scrut_t.clone())));
                // `match h : e as \u{3bb} z => M { … }`: the equation decorates the
                // *user's* motive rather than replacing it, and the result type
                // is unchanged — the convoy is type-transparent
                // (docs/match-equation-split-design.md \u{a7}3.3).
                if let Some(h) = eqbind {
                    let t = self.elab_convoy(
                        cx, *form, *generated, h, arms, scrut_t, &scrut_ty, &scrut_lvl, motive,
                        &mlvl, &result, e.span,
                    )?;
                    return Ok((t, result, mlvl));
                }
                let t = Routes(self).elab_match(
                    cx,
                    *form,
                    *generated,
                    arms,
                    scrut_t,
                    &scrut_ty,
                    &scrut_lvl,
                    motive,
                    mlvl.clone(),
                    e.span,
                )?;
                Ok((t, result, mlvl))
            }
            // A motive-less `match` whose branches do not depend on the
            // scrutinee: one arm names the type, and the motive is that type,
            // constant (issues/match-arg-of-polymorphic-callee-needs-motive.md).
            // Tried before the message below, and only ever *replaced* by it —
            // a synthesis that does not go through leaves no trace.
            ExprKind::Match {
                form,
                motive: None,
                scrut,
                arms,
                eqbind,
                generated,
            } => {
                if *form == MatchForm::If && eqbind.is_none() {
                    match matching::infer_if_constant_motive(
                        self.0, cx, scrut, arms, *generated, e.span,
                    ) {
                        matching::MotiveInference::Accepted(result) => return Ok(result),
                        matching::MotiveInference::Failed(error) => return Err(error),
                        matching::MotiveInference::Declined => {}
                    }
                }
                match matching::infer_match_constant_motive_eq(
                    self.0, cx, *form, scrut, arms, eqbind.as_deref(), *generated, e.span,
                ) {
                    matching::MotiveInference::Accepted(result) => return Ok(result),
                    matching::MotiveInference::Failed(error) => return Err(error),
                    matching::MotiveInference::Declined => {}
                }
                err(
                    format!(
                        "`{}` in inference position needs a motive: `{}`",
                        form.keyword(),
                        match form {
                            MatchForm::Match => "match e as \u{3bb} z => T { … }",
                            MatchForm::Split => "split e as \u{3bb} z => T;",
                            MatchForm::If =>
                                "give the `if` an expected result type, for \
                                              example with an annotated `let`",
                            MatchForm::IfLet =>
                                "give the `if let` an expected result type, for \
                                                 example with an annotated `let`",
                        }
                    ),
                    e.span,
                )
            }
            // Both the form and the *suggested spelling* are the written
            // one: `match e as \u{3bb} z => T { … }` is not a thing a writer who
            // typed `split` can paste (issues/diagnostics-name-the-written-form.md).
            ExprKind::Match {
                form, motive: None, ..
            } => err(
                format!(
                    "`{}` in inference position needs a motive: `{}`",
                    form.keyword(),
                    match form {
                        MatchForm::Match => "match e as \u{3bb} z => T { … }",
                        MatchForm::Split => "split e as \u{3bb} z => T;",
                        MatchForm::If =>
                            "give the `if` an expected result type, for \
                                          example with an annotated `let`",
                        MatchForm::IfLet =>
                            "give the `if let` an expected result type, for \
                                             example with an annotated `let`",
                    }
                ),
                e.span,
            ),
            ExprKind::J {
                proof,
                motive,
                case,
            } => {
                let (mbinders, mbody) =
                    matching::motive_lam(motive, 2, "write `j(p, \u{3bb} y q => T, case)`")?;
                let (y, p) = (&mbinders[0], &mbinders[1]);
                let (proof_t, proof_ty, _) = self.elab_infer(cx, proof)?;
                let head = self.whnf(cx, &proof_ty, proof.span)?;
                let Type::Id {
                    level,
                    ty,
                    lhs,
                    rhs,
                } = head
                else {
                    return err("`j` needs a proof of an `=` type", proof.span);
                };
                // Motive context: Γ, y : S, p : Id(S, a, y).
                let mut mcx = cx.clone();
                mcx.push(y.clone(), (*ty).clone(), level.clone());
                let p_ty = Type::Id {
                    level: level.clone(),
                    ty: Rc::new(ty.shift_local(1)),
                    lhs: Rc::new(lhs.shift_local(1)),
                    rhs: Rc::new(Term::Var(LocalVar(0))),
                };
                mcx.push(p.clone(), p_ty, level.clone());
                let (motive_t, mlvl) = self.elab_ty(&mcx, &mbody)?;
                // case : M[a/y, refl/p]
                let refl = Term::Refl {
                    level: level.clone(),
                    ty: Rc::clone(&ty),
                    tm: Rc::clone(&lhs),
                };
                let case_ty = motive_t.apply_local(
                    &LocalSubst::id(&cx.gamma)
                        .extended(Rc::clone(&lhs))
                        .extended(Rc::new(refl)),
                );
                let case_t = self.elab_check(cx, case, &case_ty, &mlvl)?;
                // result : M[b/y, proof/p]
                let proof_rc = Rc::new(proof_t);
                let result = motive_t.apply_local(
                    &LocalSubst::id(&cx.gamma)
                        .extended(Rc::clone(&rhs))
                        .extended(Rc::clone(&proof_rc)),
                );
                let t = Term::J {
                    ty_level: level.clone(),
                    motive_level: mlvl.clone(),
                    ty,
                    lhs,
                    motive: Rc::new(motive_t),
                    case: Rc::new(case_t),
                    rhs,
                    proof: proof_rc,
                };
                Ok((t, result, mlvl))
            }
            // Rule 2 again, in inference position: a bound `refl` is the
            // binding, and only an unbound one is the form.
            ExprKind::Refl if self.shadowed(cx, "refl") => self.elab_infer(
                cx,
                &Expr {
                    kind: ExprKind::Var("refl".to_string()),
                    span: e.span,
                },
            ),
            ExprKind::Refl => err(
                "`refl` needs an expected type (checking position or `as` motive)",
                e.span,
            ),
            // Checking-only, like `refl` and for the same reason: with no
            // expected type there is no goal to close and nothing to guess.
            // This is where "ignored for values" falls out rather than being
            // enforced (issues/auto-refl-empty-block.md).
            ExprKind::AutoRefl => err(
                "an empty block `{}` needs an expected type: it is the one \
                 speculative `refl`, so it only means anything where a goal is \
                 known (a `theorem` body, an annotated `let`, an argument)",
                e.span,
            ),
            // Checking-only, mirroring the kernel: `BoxTm` is `NotInferable`
            // by design (docs/in-language-map-design.md §5). And a quote is
            // only meaningful at layer m, so outside a `meta fn` the pointer
            // is to the declaration form, not to an annotation.
            ExprKind::Quote(_) => err(
                "a `code { … }` quote needs an expected `Code(g |- T)` type, inside \
                 a `meta fn` (docs/in-language-map-design.md §3)",
                e.span,
            ),
            ExprKind::Splice(inner) => Quotation(self).elab_splice(cx, inner, e.span),
            // Unreachable: [`Self::op_rewrite`] runs at the top of this
            // function and rewrites every symbol, bare or applied, to a name.
            ExprKind::OpSymbol { symbol: s, .. } => {
                err(format!("`{s}` reached elaboration unresolved"), e.span)
            }
        }
    }

    /// A motive-less `match` with no equation binding, whose arms see the
    /// equation `e = pattern` as **pending** (docs/dependent-match-compiler-
    /// design.md §4.3): the arms elaborate without it, and a reader of
    /// hypotheses that ran in them records that it wanted it. Only when the
    /// arms then fail is the match elaborated again as its convoy, with the
    /// equation bound under [`MATCH_EQ`]; a match that checks without the
    /// equation keeps its term, so function bodies and every conversion
    /// against a restated `match` are unchanged. If the convoy fails too, the
    /// first error is the one reported.
    ///
    /// An indexed family has no homogeneous equation yet (§9), so there the
    /// match is elaborated once, as before.
    pub(crate) fn elab_match_pending(
        &self,
        cx: &Cx,
        scrut_ty: &Type,
        run: &dyn Fn(&Cx, Option<&str>) -> R<Term>,
    ) -> R<Term> {
        if IwfFamily(self).iwf_of_at(cx, scrut_ty).is_some() || IndexedFamilies(self).indexed_of_at(cx, scrut_ty).is_some() {
            return run(cx, None);
        }
        let id = self.attempt.match_eq_next.get();
        self.attempt.match_eq_next.set(id.wrapping_add(1));
        let mark = matching::MatchSpeculationState::mark_match_state(self.0);
        let mut pcx = cx.clone();
        let mut pending = (*pcx.pending_eqs).clone();
        pending.push(id);
        pcx.pending_eqs = Rc::new(pending);
        let first = run(&pcx, None);
        let wanted = {
            let mut wanted = self.attempt.match_eq_wanted.borrow_mut();
            let had = wanted.contains(&id);
            wanted.retain(|w| *w != id);
            had
        };
        match first {
            Err(error) if wanted => {
                matching::MatchSpeculationState::rollback_match_state(self.0, mark);
                run(cx, Some(MATCH_EQ)).map_err(|_| {
                    matching::MatchSpeculationState::rollback_match_state(self.0, mark);
                    error
                })
            }
            other => other,
        }
    }

    /// A reader of hypotheses (`omega`, `linarith`) is about to list them:
    /// every pending match equation in scope is wanted (§4.3).
    pub(crate) fn want_match_equations(&self, cx: &Cx) {
        if cx.pending_eqs.is_empty() {
            return;
        }
        let mut wanted = self.attempt.match_eq_wanted.borrow_mut();
        for id in cx.pending_eqs.iter() {
            if !wanted.contains(id) {
                wanted.push(*id);
            }
        }
    }

    /// `match h : e { … }` — the convoy, written for the user
    /// (docs/match-equation-split-design.md §3.3).
    ///
    /// Three mechanical steps over the *unconvoyed* elaboration, and nothing
    /// below [`Routes::elab_match`] learns that any of them happened:
    ///
    /// 1. the motive `M` over `Γ, z` becomes `M' = Π (e = z). M`, so every arm
    ///    is checked at `Π fields. (e = C(fields)) -> M[C(fields)/z]`;
    /// 2. each arm's *surface* body `b` becomes `λ h => b`, unannotated — the
    ///    arm type supplies the domain, so no equation is written twice;
    /// 3. the eliminator is applied to `refl : e = e`, which is exactly `M'`
    ///    at `z := e` stripped back to `M[e/z]`.
    ///
    /// So the convoy is **type-transparent**: `result` is the type the
    /// unconvoyed `match` would have had, in both modes. The direction is
    /// `scrutinee = pattern` (§3.2): it is what the one live consumer wants,
    /// and it is the one `refl` inhabits without a `sym`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_convoy(
        &self,
        cx: &Cx,
        form: MatchForm,
        generated: bool,
        h: &str,
        arms: &[Arm],
        scrut_t: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        motive: Type,
        mlvl: &Level,
        result: &Type,
        span: Span,
    ) -> R<Term> {
        // An indexed family's arms live at *different* indices, so `e = z`
        // would relate two values at two types. The index packed with the
        // value is one type, `Σ(j: I). F(j)`, and that equation is the one
        // bound (docs/dependent-match-compiler-design.md §9).
        if let Some((ind, fam)) = IwfFamily(self).iwf_of_at(cx, scrut_ty) {
            let family = PackedFamily {
                ity: fam.ity.clone(),
                ilvl: fam.ilvl.clone(),
                flvl: fam.lvl(),
                idx: Rc::clone(&fam.idx),
                at: &|i, k| fam.ty_at(i, k),
                eliminate: &|acx: &Cx, arms: &[Arm], scrut: Term, motive: Type, level: Level| {
                    IwfFamily(self).elab_match_iwf(
                        acx, form, &ind, &fam, arms, scrut, motive, level,
                        iwf_family::IndexMotive::Plain, span,
                    )
                },
            };
            return self.elab_convoy_packed(
                cx, form, generated, h, arms, scrut_t, scrut_ty, scrut_lvl, &family, motive, mlvl,
                result, span,
            );
        }
        if let Some((ind, fam)) = IndexedFamilies(self).indexed_of_at(cx, scrut_ty) {
            let (ity, ilvl) = IndexedFamilies(self).index_type_of(cx, &ind, span)?;
            let family = PackedFamily {
                ity,
                ilvl,
                flvl: fam.level.clone(),
                idx: Rc::clone(&fam.idx),
                at: &|i, k| fam.el_at(i, k),
                eliminate: &|acx: &Cx, arms: &[Arm], scrut: Term, motive: Type, level: Level| {
                    IndexedFamilies(self).elab_match_indexed(acx, form, &ind, &fam, arms, scrut, motive, level, span)
                },
            };
            return self.elab_convoy_packed(
                cx, form, generated, h, arms, scrut_t, scrut_ty, scrut_lvl, &family, motive, mlvl,
                result, span,
            );
        }
        let plan = matching::plan_convoy(h, arms, &scrut_t, scrut_ty, scrut_lvl, &motive, mlvl);
        let elim = Routes(self).elab_match(
            cx,
            form,
            generated,
            &plan.arms,
            scrut_t.clone(),
            scrut_ty,
            scrut_lvl,
            plan.motive,
            plan.level,
            span,
        )?;
        Ok(matching::finish_convoy(
            elim, scrut_t, scrut_ty, scrut_lvl, mlvl, result,
        ))
    }

    /// [`Self::elab_convoy`] on an indexed family (design §9): each arm takes
    /// `h : ⟨i, e⟩ = ⟨idx(C, x̄), C(x̄)⟩` at `Σ(j: I). F(j)`, through the
    /// two-binder motive `λ j z => Π(p: ⟨i, e⟩ = ⟨j, z⟩). M(j, z)`, applied to
    /// `refl`. `M(j, z)` is the index generalized as route 1 does it; the
    /// equation's left side is not, since it is the scrutinee's own.
    #[allow(clippy::too_many_arguments)]
    fn elab_convoy_packed(
        &self,
        cx: &Cx,
        form: MatchForm,
        generated: bool,
        h: &str,
        arms: &[Arm],
        scrut_t: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        fam: &PackedFamily<'_>,
        motive: Type,
        mlvl: &Level,
        result: &Type,
        span: Span,
    ) -> R<Term> {
        let m2 = IndexedFamilies(self).generalize_index(cx, &motive, &fam.idx);
        let (ilvl, flvl) = (fam.ilvl.clone(), fam.flvl.clone());
        let slvl = Level::join(ilvl.clone(), flvl.clone());
        // `Σ(j: I). F(j)` and `⟨i, z⟩`, scoped `k` binders past Γ.
        let sigma = |k: u32| Type::Sigma {
            fst_level: ilvl.clone(),
            snd_level: flvl.clone(),
            fst: Rc::new(fam.ity.shift_local(k)),
            snd: Rc::new((fam.at)(Term::Var(LocalVar(0)), k + 1)),
        };
        let pack = |k: u32, i: Term, z: Term| Term::Pair {
            fst_level: ilvl.clone(),
            snd_level: flvl.clone(),
            fst_ty: Rc::new(fam.ity.shift_local(k)),
            snd_ty: Rc::new((fam.at)(Term::Var(LocalVar(0)), k + 1)),
            fst: Rc::new(i),
            snd: Rc::new(z),
        };
        let here = pack(0, (*fam.idx).clone(), scrut_t.clone());
        // Over `(Γ, j, z)`.
        let equation = Type::Id {
            level: slvl.clone(),
            ty: Rc::new(sigma(2)),
            lhs: Rc::new(here.shift_local(2)),
            rhs: Rc::new(pack(2, Term::Var(LocalVar(1)), Term::Var(LocalVar(0)))),
        };
        let convoyed = Type::Pi {
            dom_level: slvl.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(equation),
            cod: Rc::new(m2.shift_local(1)),
        };
        let clvl = Level::join(slvl.clone(), mlvl.clone());
        let at_scrut = Type::Id {
            level: slvl.clone(),
            ty: Rc::new(sigma(0)),
            lhs: Rc::new(here.clone()),
            rhs: Rc::new(here.clone()),
        };
        let convoyed_here = Type::Pi {
            dom_level: slvl.clone(),
            cod_level: mlvl.clone(),
            dom: Rc::new(at_scrut.clone()),
            cod: Rc::new(result.shift_local(1)),
        };
        let plan = matching::plan_convoy(h, arms, &scrut_t, scrut_ty, scrut_lvl, &motive, mlvl);
        let prepared = Patterns(self).prepare_arms(
            cx, form, generated, &plan.arms, &scrut_t, scrut_ty, scrut_lvl, &convoyed_here, false,
            &clvl, span,
        )?;
        let (acx, arms) = match &prepared {
            Some((c, a)) => (c, a.as_slice()),
            None => (cx, plan.arms.as_slice()),
        };
        let elim = (fam.eliminate)(acx, arms, scrut_t, convoyed, clvl)?;
        Ok(crate::spelling::checked_app(
            Rc::new(elim),
            slvl.clone(),
            mlvl.clone(),
            Rc::new(at_scrut),
            Rc::new(result.shift_local(1)),
            Rc::new(Term::Refl { level: slvl, ty: Rc::new(sigma(0)), tm: Rc::new(here) }),
        ))
    }

    /// [`Self::elab_convoy`] at a motive that reads the equation as well:
    /// `dependent` is scoped under the scrutinee's binder and then the
    /// equation's, and `motive` is it with the equation unused, as the other
    /// readers of a motive expect it. `split_all` builds one where a convoy
    /// in the goal takes the case's equation for its own `refl`
    /// (`goal_combinators::dependent_motive`).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn elab_convoy_dependent(
        &self,
        cx: &Cx,
        h: &str,
        arms: &[Arm],
        scrut_t: Term,
        scrut_ty: &Type,
        scrut_lvl: &Level,
        motive: Type,
        dependent: Type,
        mlvl: &Level,
        result: &Type,
        span: Span,
    ) -> R<Term> {
        let mut plan = matching::plan_convoy(h, arms, &scrut_t, scrut_ty, scrut_lvl, &motive, mlvl);
        if let Type::Pi { cod, .. } = &mut plan.motive {
            *cod = Rc::new(dependent);
        }
        let elim = Routes(self).elab_match(
            cx,
            heather_syntax::MatchForm::Match,
            true,
            &plan.arms,
            scrut_t.clone(),
            scrut_ty,
            scrut_lvl,
            plan.motive,
            plan.level,
            span,
        )?;
        Ok(matching::finish_convoy(
            elim, scrut_t, scrut_ty, scrut_lvl, mlvl, result,
        ))
    }

    /// A numeral at a user-defined carrier. Core `Nat` and `Fin` readings are
    /// already settled by `ExprElab`; this is declaration/class policy only.
    pub(crate) fn elab_overloaded_num_check(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
        expected_level: &Level,
        span: Span,
    ) -> R<Term> {
        // At another expected carrier, use the ordinary class resolver. The
        // class is optional at the language level: a program whose closure
        // does not hold the standard algebra module keeps the historical
        // Nat-only mismatch below. Once `algebra::Numeral` is in the closure,
        // however — read by identity, not by a name this module may not
        // import (issues/numerals-without-algebra-import.md) — a missing
        // instance is the useful diagnosis and not a later Nat-vs-carrier
        // conversion error.
        if let Some((ind, named)) = Classes(self).literal_class_record(literals::NUMERAL)
            && let Some(field) = ind.field_index("ofNat")
        {
            let targs = [(expected.clone(), expected_level.clone())];
            let (goal, goal_level) = self.lower_instance(cx, &ind, &targs, &[], span)?;
            let carrier = Carriers(self)
                .type_namespace(cx, expected, span)
                .unwrap_or_else(|| "the expected type".to_string());
            let display = format!("Numeral<{carrier}>");
            let mut trace = Vec::new();
            match self.resolve_goal(cx, &goal, &goal_level, &display, None, span, &mut trace) {
                Some(dict) => {
                    let (embed, embed_ty, embed_level) =
                        self.project_field(cx, &ind, &goal, Rc::new(dict), field, span)?;
                    let since = self.attempt.trivial_uses.borrow().len();
                    let (out, _, _) = application::apply_explicit(
                        self.0,
                        cx,
                        Some("ofNat"),
                        Rc::new(Vec::new()),
                        0,
                        embed,
                        embed_ty,
                        embed_level,
                        std::slice::from_ref(e),
                    )?;
                    Literals(self).settle_deferred_units(since)?;
                    return Ok(Literals(self).reduced_embedding(cx, out));
                }
                None if named => {
                    if let Some(at_class) = Literals(self).class_carrier_numeral(cx, e, expected, expected_level, span) {
                        return Ok(at_class);
                    }
                    if let Some(refusal) = Literals(self).class_numeral_refusal(cx, expected, span) {
                        return Err(refusal);
                    }
                    return Err(ElabError::Resolution {
                        goal: display,
                        span,
                        trace,
                    });
                }
                // Reached by identity only, and no instance: the `Nat`
                // reading below, as before the class was reachable.
                None => {}
            }
        }
        if let Some(at_class) = Literals(self).class_carrier_numeral(cx, e, expected, expected_level, span) {
            return Ok(at_class);
        }
        if let Some(refusal) = Literals(self).class_numeral_refusal(cx, expected, span) {
            return Err(refusal);
        }
        // A numeral is the leaf case of
        // `issues/check-fallback-discards-expected-type.md`: its inferred type
        // is `Nat` without any work at all, so comparing costs one conversion
        // against a type the caller already had.
        let (num, num_ty, _) = self.elab_infer(cx, e)?;
        MismatchNotes(self).note_check_mismatch(cx, &num_ty, expected, &Level::Zero, span);
        Ok(num)
    }

    /// Interpret `[…]` through the one protocol owned by the implicit
    /// prelude. The syntax supplies both class inputs: the expected container
    /// and the literal's statically known length. The dictionary's dependent
    /// `element` field then supplies the checking type for every entry, and
    /// `fromLiteral` consumes the primitive vector lowering.
    pub(crate) fn check_collection_literal(
        &self,
        cx: &Cx,
        literal: &Expr,
        elems: &[Expr],
        expected: &Type,
        expected_level: &Level,
        span: Span,
    ) -> R<Term> {
        let class_key = names::qkey(PRELUDE_MODULE, "CollectionLiteral");
        let class = self
            .traits
            .class(&class_key)
            .cloned()
            .ok_or_else(|| ElabError::Elab {
                msg: "internal: the prelude collection-literal protocol is missing".into(),
                span,
            })?;
        let ind = self
            .types
            .inductive(&class_key)
            .cloned()
            .ok_or_else(|| ElabError::Elab {
                msg: "internal: the prelude collection-literal dictionary is missing".into(),
                span,
            })?;
        if class.params.len() != 1 || class.valparams.len() != 1 {
            return err("internal: malformed prelude collection-literal protocol", span);
        }
        let Some(element_field) = ind.field_index("element") else {
            return err("internal: collection-literal protocol has no `element` field", span);
        };
        let Some(from_field) = ind.field_index("fromLiteral") else {
            return err(
                "internal: collection-literal protocol has no `fromLiteral` field",
                span,
            );
        };

        // The carrier by its code, when it has one: a field's `List<Instr>`
        // arrives as its inline lowering, and the goal and the two
        // conversions below would otherwise compare that against the
        // instance's code-spelled type by unfolding every code inside it —
        // each element type's whole sum, and every sum its fields name, per
        // literal (`issues/native-tool-test-cold-certificate-rail.md`, log).
        let respelled = GeneratedDefs(self).respell_ty(cx, expected);
        let expected = respelled.as_ref().unwrap_or(expected);
        let length = inductive::nat_lit(elems.len());
        let targs = [(expected.clone(), expected_level.clone())];
        let vargs = [(length.clone(), Type::Nat, Level::Zero)];
        let (goal, goal_level) = self.lower_instance(cx, &ind, &targs, &vargs, span)?;
        let carrier = self.display_type(cx, expected);
        let display = format!("CollectionLiteral<{carrier}>({})", elems.len());
        let mut trace = Vec::new();
        let Some(dict) = self.resolve_goal(cx, &goal, &goal_level, &display, None, span, &mut trace)
        else {
            return Err(ElabError::Resolution { goal: display, span, trace });
        };
        let dict = Rc::new(dict);

        let (element, element_universe, _) =
            self.project_field(cx, &ind, &goal, Rc::clone(&dict), element_field, span)?;
        // Projection from a resolved dictionary can retain the whole
        // dependent dictionary term. Normalize the field value before it is
        // embedded in every vector-element annotation below.
        let element = (*self.whnf_tm(cx, &element, span)?).clone();
        let Type::Ty(element_level) = self.whnf(cx, &element_universe, span)? else {
            return err(
                "internal: collection-literal `element` is not a type code",
                span,
            );
        };
        let element_ty = Type::El {
            level: element_level.clone(),
            tm: Rc::new(element),
        };
        // Build the compact domain before projecting `fromLiteral`: keeping
        // this independently rooted prevents the later dependent projection
        // from becoming part of the vector's annotations.
        let literal_dom = Type::Vec {
            level: element_level.clone(),
            elem: Rc::new(element_ty.clone()),
            len: Rc::new(length),
        };

        let (from, from_ty, _) =
            self.project_field(cx, &ind, &goal, dict, from_field, span)?;
        let from = (*self.whnf_tm(cx, &from, span)?).clone();
        let Type::Pi {
            dom_level: _,
            cod_level,
            dom,
            cod,
        } = self.whnf(cx, &from_ty, span)?
        else {
            return err(
                "internal: collection-literal `fromLiteral` is not a function",
                span,
            );
        };
        let Type::Vec { elem: vector_element, .. } = &*inductive::decoded(&dom) else {
            return err(
                "internal: collection-literal `fromLiteral` does not accept a vector",
                span,
            );
        };
        if !self.conv_types(cx, vector_element, &element_ty, &element_level) {
            return err(
                "internal: collection-literal element and conversion domain disagree",
                span,
            );
        }
        // Checking the same surface node directly through ExprElab is the
        // bootstrap boundary: it constructs the primitive vector and cannot
        // re-enter this protocol route.
        let vector = self
            .expr_elab()
            .check_indexed_form(self.0, cx, literal, &literal_dom)
            .expect("a collection literal is an indexed vector checking form")?;
        let vector = Rc::new(vector);
        let result_ty = cod.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::clone(&vector)));
        if !self.conv_types(cx, &result_ty, expected, &cod_level) {
            return err(
                "internal: collection-literal conversion does not return its carrier",
                span,
            );
        }
        let converted = crate::spelling::checked_app(
            Rc::new(from),
            element_level,
            expected_level.clone(),
            Rc::new(literal_dom),
            Rc::new(expected.shift_local(1)),
            vector,
        );
        let value = (*self.whnf_tm(cx, &converted, span)?).clone();
        Ok(Literals(self).collection_literal_spine(cx, value, elems.len()))
    }
}
