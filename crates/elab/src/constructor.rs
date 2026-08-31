//! Surface constructor recognition, inference, and application policy.
//!
//! This module decides when a surface name is a constructor, how checking
//! position disambiguates it, how curried applications flatten, and where an
//! instantiation comes from. The `inductive` module remains the owner of the
//! actual kernel encoding and constructor term construction.

use std::rc::Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{
    ANON_CTOR_LEFT, ANON_CTOR_ONLY, ANON_CTOR_RIGHT, Expr, ExprKind, NamedArg,
    RecordLitField, Span, Ty, TyKind,
};

use crate::inductive::{self, Inductive};
use crate::names::NameKind;
use crate::{Cx, Elaborator, IMPLICIT_MARK_REFUSED, R, application, err, has_implicit_mark};

impl Elaborator {
    /// A record literal (§6): permute the written fields into declaration
    /// order and hand the result to the ordinary tier-0 constructor path.
    /// Every diagnostic about *which* fields were written lives here, since
    /// the constructor path only ever sees a positional list.
    pub(super) fn record_lit_args(
        &self,
        name: &str,
        fields: &[RecordLitField],
        span: Span,
    ) -> R<Vec<Expr>> {
        let Some(ind) = self.lookup_inductive(name) else {
            return Err(self.name_miss(name, format!("unknown type `{name}`"), span));
        };
        if !ind.is_record {
            return err(
                format!(
                    "`{name}` is an `inductive`, not a `record`: write a constructor \
                     application (`{}(…)`) rather than `{name} {{ … }}`",
                    ind.ctors.first().map(|c| c.name.as_str()).unwrap_or("…")
                ),
                span,
            );
        }
        let decl: Vec<&str> = ind.ctors[0]
            .fields
            .iter()
            .map(|(n, _)| n.as_deref().unwrap_or("_"))
            .collect();
        let written: Vec<(&str, &Expr, Span)> = fields
            .iter()
            .map(|f| (f.name.as_str(), &f.expr, f.span))
            .collect();
        application::permute_by_name(name, "field", &decl, &[], &written, span)
    }

    /// The constructor this name refers to *here* — `None` when it is not a
    /// constructor, or when a local binder or `let` alias shadows it.
    pub(super) fn ctor_here(&self, cx: &Cx, name: &str) -> Option<(Rc<Inductive>, usize)> {
        if cx.names.iter().any(|n| n == name) || cx.aliases.iter().any(|a| a.name == *name) {
            return None;
        }
        self.ctor_of(name)
    }

    /// The declaration an expected type names, for the checking-position
    /// constructor route. A `Π` is peeled first: an **unsaturated**
    /// constructor is checked against the function type it η-expands into
    /// (docs/constructor-function-values.md §2), so the declaration is in the
    /// codomain, not the head.
    pub(super) fn expected_ind(&self, expected: &Type) -> Option<Rc<Inductive>> {
        let mut ty = expected;
        while let Type::Pi { cod, .. } = ty {
            ty = cod;
        }
        self.tag_of(ty)
    }

    /// Resolve anonymous constructor notation from its expected type. The
    /// product spelling is intentionally limited to a declaration with one
    /// constructor; the injection spellings to exactly two. This keeps the
    /// punctuation structural rather than turning declaration order in a
    /// large inductive into an implicit numeric API.
    pub(super) fn anonymous_ctor_expected(
        &self,
        cx: &Cx,
        written: &str,
        expected: &Type,
        span: Span,
    ) -> R<(Rc<Inductive>, usize)> {
        let expected = self.whnf(cx, expected, span)?;
        let Some(ind) = self.expected_ind(&expected) else {
            return err(
                "anonymous constructor notation needs an expected inductive or record type",
                span,
            );
        };
        let (want, index) = match written {
            ANON_CTOR_ONLY => (1, 0),
            ANON_CTOR_LEFT => (2, 0),
            ANON_CTOR_RIGHT => (2, 1),
            _ => unreachable!("not an anonymous constructor sentinel"),
        };
        if ind.ctors.len() != want {
            let form = match written {
                ANON_CTOR_ONLY => "`⟨…⟩`",
                ANON_CTOR_LEFT => "`⟨… |⟩`",
                ANON_CTOR_RIGHT => "`⟨| …⟩`",
                _ => unreachable!(),
            };
            return err(
                format!(
                    "{form} needs an expected type with {want} constructor(s), but `{}` has {}",
                    ind.name,
                    ind.ctors.len()
                ),
                span,
            );
        }
        Ok((ind, index))
    }

    /// [`Self::ctor_here`], plus the **expected type** as evidence
    /// (docs/modules-design.md §4's follow-up, §8's one resolution judgment).
    ///
    /// In checking position the expected type already names the declaration,
    /// so a bare `None` at an expected `Option<A>` is that `Option`'s `None`
    /// whatever else is in scope — the same judgment a `match` arm already
    /// makes through the scrutinee ([`inductive::arm_ctor_index`], which this
    /// shares, so
    /// the `Option::None` spelling costs nothing extra here either).
    ///
    /// Strictly a **fallback**: the global reading is tried first, so a name
    /// that resolves today keeps resolving to the same declaration, and the
    /// expected type only ever *shrinks* a candidate set that the name layer
    /// left ambiguous — never reinterprets one it settled. That is §8's second
    /// invariant, and it is the reason this is sound to add to a library that
    /// is still growing: a new declaration can turn a bare constructor from
    /// unique into ambiguous, and here that is where it stops being an error,
    /// not where it starts meaning something else.
    ///
    /// The shadowing guard is repeated rather than inherited from the `None`
    /// branch above: a local binder beats a constructor at *any* expected
    /// type, and the type evidence must not buy that precedence back.
    ///
    /// [`Self::only_ctors_visible`] is the other half of "shrink, never
    /// reinterpret", and the reason this is not simply "ask the expected
    /// type when the name did not resolve": a name may fail to resolve *as a
    /// constructor* because it resolved to something else entirely, or
    /// because a **function** is one of the things it is ambiguous between —
    /// and a `fn None() -> Option<Nat>` is as admissible at an expected
    /// `Option<Nat>` as the constructor is, so the type is not evidence there
    /// at all. Those keep the reading they have today.
    pub(super) fn ctor_here_expected(
        &self,
        cx: &Cx,
        name: &str,
        expected: &Type,
    ) -> Option<(Rc<Inductive>, usize)> {
        if let Some(hit) = self.ctor_here(cx, name) {
            return Some(hit);
        }
        if cx.names.iter().any(|n| n == name) || cx.aliases.iter().any(|a| a.name == *name) {
            return None;
        }
        if !self.only_ctors_visible(name) {
            return None;
        }
        // **Whnf first** (2026-08-16). The expected type reaches here in
        // whatever spelling its position had: a declared result type arrives
        // already structural, but a *parameter's* domain — which is what an
        // argument is checked against — can still be a reference that only
        // δ-unfolds to the lowering `tag_of` reads. Without this the route
        // fired for `theorem t(): Bool { False }` and stood down for
        // `idb(False)`, which is the same question asked twice
        // (issues/false-collides-with-bools-constructor.md). The cost is
        // confined to the fallback: this line is reached only after the
        // ordinary reading has already failed.
        // The span is only ever used for an out-of-fuel message, which this
        // discards along with every other failure — the route simply stands
        // down.
        let expected = self.whnf(cx, expected, Span { start: 0, end: 0 }).ok()?;
        let ind = self.expected_ind(&expected)?;
        let i = crate::inductive::arm_ctor_index(&ind, name)?;
        Some((ind, i))
    }

    /// Is every visible declaration of `name` a **constructor**?
    ///
    /// The precondition on the expected-type route. Reached only after the
    /// ordinary reading has already failed, so this is not asking "which
    /// declaration wins" — it is asking whether the type is allowed to be the
    /// tie-breaker at all, and it is allowed exactly when no candidate could
    /// have checked here *except* a constructor. One visible `fn` of the same
    /// name and the route stands down: that reading does not live in any
    /// declaration's constructor namespace and may well have the expected
    /// type, so picking the constructor over it would be a reinterpretation
    /// and not a shrink (docs/modules-design.md §8).
    ///
    /// **Amended 2026-08-16**: an `inductive`/`record` of the same name no
    /// longer stands the route down. See the body for the licence.
    ///
    /// Visibility is spelled out rather than taken from
    /// [`names::resolve`] because that function answers with *precedence*
    /// applied — a listed import or a local declaration hides the collision
    /// this has to see.
    fn only_ctors_visible(&self, name: &str) -> bool {
        // An `Inductive` candidate is admitted beside constructors because
        // the caller has already established an inductive expected type. A
        // type name has a universe type and cannot check there; dropping that
        // reading is therefore a shrink, while a `Global` or `Meta` may return
        // the expected type and must still make this route stand down.
        let scopes = self.resolution_scopes.borrow();
        self.names.visible_entries_are(
            scopes.last().map(Rc::as_ref),
            name,
            &[NameKind::Ctor, NameKind::Inductive],
        )
    }

    /// A constructor applied to its arguments, however the surface
    /// parenthesized them: `Cons(1, xs)` and `Cons(1)(xs)` flatten to the same
    /// `(declaration, index, arguments)`. Re-associating is sound because a
    /// constructor's function value *is* its η-expansion
    /// (docs/constructor-function-values.md §2), so the curried spelling is
    /// definitionally the saturated one — and flattening is what lets the
    /// curried spelling work in inference position, where the head alone
    /// (`Cons(1)`) has no type to infer.
    /// The named arguments of every level travel with the spine
    /// (docs/named-arguments-design.md §6); the caller permutes the whole lot
    /// into field order at once, so a name written at an inner level of a
    /// curried spelling lands where it says rather than being dropped.
    pub(super) fn ctor_spine(
        &self,
        cx: &Cx,
        e: &Expr,
    ) -> Option<(Rc<Inductive>, usize, Vec<Expr>, Vec<NamedArg>)> {
        let ExprKind::App {
            head,
            args,
            named,
            explicit,
            ..
        } = &e.kind
        else {
            return None;
        };
        if *explicit {
            return None;
        }
        match &head.kind {
            ExprKind::Var(name) => {
                let (ind, i) = self.ctor_here(cx, name)?;
                Some((ind, i, args.clone(), named.clone()))
            }
            ExprKind::App { .. } => {
                let (ind, i, mut prefix, mut pnamed) = self.ctor_spine(cx, head)?;
                prefix.extend(args.iter().cloned());
                pnamed.extend(named.iter().cloned());
                Some((ind, i, prefix, pnamed))
            }
            _ => None,
        }
    }

    /// [`Self::ctor_spine`] with the expected type as evidence at the head,
    /// which is the only place a *name* appears: the arguments are checked
    /// against their field types downstream, and a curried spelling
    /// (`Cons(1)(xs)`) flattens before the head is read, so the expected type
    /// is the saturated result either way.
    pub(super) fn ctor_spine_expected(
        &self,
        cx: &Cx,
        e: &Expr,
        expected: &Type,
    ) -> Option<(Rc<Inductive>, usize, Vec<Expr>, Vec<NamedArg>)> {
        let ExprKind::App {
            head,
            args,
            named,
            explicit,
            ..
        } = &e.kind
        else {
            return None;
        };
        if *explicit {
            return None;
        }
        match &head.kind {
            ExprKind::Var(name) => {
                let (ind, i) = self.ctor_here_expected(cx, name, expected)?;
                Some((ind, i, args.clone(), named.clone()))
            }
            ExprKind::App { .. } => {
                let (ind, i, mut prefix, mut pnamed) =
                    self.ctor_spine_expected(cx, head, expected)?;
                prefix.extend(args.iter().cloned());
                pnamed.extend(named.iter().cloned());
                Some((ind, i, prefix, pnamed))
            }
            _ => None,
        }
    }

    /// A constructor used where nothing is checking it. Only possible when the
    /// declaration has no type parameters — otherwise there is nothing to
    /// determine the instantiation, and an annotation is required (§2:
    /// parameters are monomorphized, not inferred).
    pub(super) fn infer_ctor(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        i: usize,
        args: &[Expr],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        // Type arguments are recovered only from a field whose type *is* a
        // parameter (`Some(A)`), by inferring that argument. Deliberately
        // narrow: anything deeper is unification, which belongs to
        // issues/elab-unifier-completeness.md, not here. A `None` on its own
        // is genuinely ambiguous and says so.
        // Value parameters are **not** inferred, by decision rather than by
        // omission (docs/surface-value-parameters.md §4, closing
        // `docs/surface-existential-investigation.md` §C.5): a parameter
        // appears only inside a *field type*, so recovering it from the
        // arguments is higher-order unification, not the narrow
        // field-type-is-a-parameter reading below. Checking position supplies
        // them; nothing else does.
        if !ind.valparams.is_empty() {
            return err(
                format!(
                    "cannot infer the value argument(s) of `{}` here — a value parameter \
                     appears only inside a field's type, so nothing in `{}(…)` determines \
                     it. Put the expression in a checking position: a `fn`/`theorem` \
                     body whose declared result is `{}(…)`, or an argument of a \
                     declaration that expects one",
                    ind.name, ind.name, ind.name
                ),
                span,
            );
        }
        let mut sols: Vec<Option<(Type, Level)>> = vec![None; ind.params.len()];
        for (f, arg) in self.ctor_fields(ind, i).iter().zip(args) {
            let TyKind::Named { name, args: targs } = &f.kind else {
                continue;
            };
            if !targs.is_empty() {
                continue;
            }
            let Some(p) = ind.params.iter().position(|p| p == name) else {
                continue;
            };
            if sols[p].is_none() {
                let (_, ty, lvl) = self.elab_infer(cx, arg)?;
                sols[p] = Some((ty, lvl));
            }
        }
        let mut targs = Vec::with_capacity(sols.len());
        for (p, sol) in ind.params.iter().zip(sols) {
            let Some(sol) = sol else {
                // A **child** argument determines the whole instance, and
                // determines it without recovering the instantiation at all:
                // its type *is* the family, at another index. `Node(n, m, l,
                // r)`'s `l : Tree<A>(n)` is `Σ(s : ⟦Skel<A>⟧). sEq(…)` with the
                // parameters already lowered into it, so re-indexing that type
                // is exactly the type `Node` builds
                // (docs/inductive-fording-lowering.md §14.7).
                //
                // Deliberately not the general case: a parameter that occurs
                // only *under* a field's type constructor (`xs: [A; n]`) still
                // needs unification, which is
                // issues/elab-unifier-completeness.md's and not this function's.
                if let Some(r) = self.ctor_from_child(cx, ind, i, args, span) {
                    return r;
                }
                return err(
                    format!(
                        "cannot infer the type argument `{p}` of `{}` here — no argument \
                         of `{}` determines it. Two ways out: put the expression in a \
                         checking position (a `fn`/`theorem` body whose declared result \
                         is `{}<…>(…)`, or an argument of a declaration that expects \
                         one), or write the type argument (`{}<…>(…)`)",
                        ind.name, ind.ctors[i].name, ind.name, ind.ctors[i].name
                    ),
                    span,
                );
            };
            targs.push(sol);
        }
        let (ty, lvl) = if ind.skel.is_some() && args.len() == ind.ctors[i].fields.len() {
            // Route 2b: the index is the constructor's *written* result index
            // at the arguments it was given (docs/inductive-fording-lowering.md
            // §2), which is the whole widening.
            let (idx, _, _) = self.forded_ctor_index(cx, ind, i, args, span)?;
            self.lower_forded_instance(cx, ind, &targs, idx, span)?
        } else if ind.index.is_some() && args.len() == ind.ctors[i].fields.len() {
            // The result index comes from the pattern and the written index
            // argument (docs/inductive-indexed-lowering.md §5); the wrong-
            // arity case falls through to `build_ctor`'s arity message.
            let (idx, _, _) = self.indexed_ctor_index(cx, ind, i, args, span)?;
            self.lower_indexed_instance(cx, ind, &targs, idx, span)?
        } else {
            self.lower_instance(cx, ind, &targs, &[], span)?
        };
        let t = self.build_ctor(cx, ind, i, args, &ty, &lvl, span)?;
        Ok((t, ty, lvl))
    }

    /// A constructor of an **indexed** family whose type-parameter
    /// instantiation is determined by a *child* argument
    /// (`docs/inductive-fording-lowering.md` §14.7, and route 1's same gap).
    ///
    /// The child's inferred type is the family at the child's own index, and
    /// both routes keep the family in a form that can be re-applied at another
    /// index — `FordedFam::ty_at` and `IndexedFam::el_at`, which is what
    /// `match` uses to name `fam 0` and `fam (S m)` from one read-back type. So
    /// there is nothing to *solve*: the instance comes back whole and the
    /// written result index says where to put it. `None` when no argument is a
    /// child, or when the first child's type is not this family.
    fn ctor_from_child(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        i: usize,
        args: &[Expr],
        span: Span,
    ) -> Option<R<(Term, Type, Level)>> {
        if ind.index.is_none() || args.len() != ind.ctors[i].fields.len() {
            return None;
        }
        let k = ind.ctors[i]
            .kind
            .iter()
            .position(|f| *f == inductive::FieldKind::Plain)?;
        let (_, cty, _) = self.elab_infer(cx, &args[k]).ok()?;
        let (ty, lvl) = if ind.skel.is_some() {
            let (found, fam) = self.forded_of_at(cx, &cty)?;
            if found.tag != ind.tag {
                return None;
            }
            let idx = match self.forded_ctor_index(cx, ind, i, args, span) {
                Ok((idx, _, _)) => idx,
                Err(e) => return Some(Err(e)),
            };
            (fam.ty_at(idx, 0), fam.lvl())
        } else {
            let (found, fam) = self.indexed_of_at(cx, &cty)?;
            if found.tag != ind.tag {
                return None;
            }
            let idx = match self.indexed_ctor_index(cx, ind, i, args, span) {
                Ok((idx, _, _)) => idx,
                Err(e) => return Some(Err(e)),
            };
            (fam.el_at(idx, 0), fam.level.clone())
        };
        Some(
            self.build_ctor(cx, ind, i, args, &ty, &lvl, span)
                .map(|t| (t, ty, lvl)),
        )
    }

    /// `C<T, …>(a⃗)` — a constructor at a *written* instantiation. `None` when
    /// the head is not a constructor, so the caller falls through to the
    /// ordinary type-application path.
    ///
    /// This is the direct spelling of what `infer_ctor` can only recover
    /// narrowly (from a field whose type *is* a parameter) and otherwise
    /// refuses to guess: `Nil` alone is genuinely ambiguous, `Nil<Nat>` is not.
    pub(super) fn ctor_at(
        &self,
        cx: &Cx,
        callee: &Expr,
        tyargs: &[Ty],
        args: &[Expr],
        span: Span,
    ) -> Option<R<(Term, Type, Level)>> {
        let ExprKind::Var(name) = &callee.kind else {
            return None;
        };
        let (ind, i) = self.ctor_here(cx, name)?;
        Some((|| {
            if tyargs.len() != ind.params.len() {
                return err(
                    format!(
                        "`{}` is a constructor of `{}`, which takes {} type argument(s), \
                         found {}",
                        name,
                        ind.name,
                        ind.params.len(),
                        tyargs.len()
                    ),
                    span,
                );
            }
            let mut lowered = Vec::with_capacity(tyargs.len());
            for a in tyargs {
                // Same refusal as `elab_ty_app`'s: the instantiation stores
                // kernel types, so a mark in it has no consumer (§3.4).
                if has_implicit_mark(a) {
                    return err(IMPLICIT_MARK_REFUSED, a.span);
                }
                lowered.push(self.elab_ty(cx, a)?);
            }
            // `R<Nat>(a, b)` is not a spelling: the type arguments are
            // explicit here but the value arguments are still only recoverable
            // from the checking type (docs/surface-value-parameters.md §4).
            if !ind.valparams.is_empty() {
                return err(
                    format!(
                        "`{}` takes value parameters, which `<…>` cannot supply — they \
                         are read off the expected type. Put the expression where a \
                         `{}(…)` is expected instead",
                        ind.name, ind.name
                    ),
                    span,
                );
            }
            // An **indexed** family at a written instantiation: the index is
            // not written — it is the constructor's own result index at the
            // arguments it was given, exactly as in `infer_ctor`. This is the
            // second escape the "cannot infer the type argument" message names,
            // and the only one a nullary constructor like `Leaf<Nat>` has
            // (`docs/inductive-fording-lowering.md` §14.7).
            if ind.index.is_some() {
                if args.len() != ind.ctors[i].fields.len() {
                    return err(
                        format!(
                            "`{}` takes {} argument(s), found {} — a constructor of an \
                             indexed family cannot be partially applied at a written \
                             instantiation, because its index is read off its arguments",
                            name,
                            ind.ctors[i].fields.len(),
                            args.len()
                        ),
                        span,
                    );
                }
                let (ty, lvl) = if ind.skel.is_some() {
                    let (idx, _, _) = self.forded_ctor_index(cx, &ind, i, args, span)?;
                    self.lower_forded_instance(cx, &ind, &lowered, idx, span)?
                } else {
                    let (idx, _, _) = self.indexed_ctor_index(cx, &ind, i, args, span)?;
                    self.lower_indexed_instance(cx, &ind, &lowered, idx, span)?
                };
                let t = self.build_ctor(cx, &ind, i, args, &ty, &lvl, span)?;
                return Ok((t, ty, lvl));
            }
            let (ty, lvl) = self.lower_instance(cx, &ind, &lowered, &[], span)?;
            let t = self.build_ctor_value(cx, &ind, i, args, &ty, &lvl, span)?;
            Ok((t, ty, lvl))
        })())
    }
}
