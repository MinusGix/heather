//! Surface constructor recognition, inference, and application policy.
//!
//! This module decides when a surface name is a constructor, how checking
//! position disambiguates it, how curried applications flatten, and where an
//! instantiation comes from. The `inductive` module remains the owner of the
//! actual kernel encoding and constructor term construction.

use std::borrow::Borrow;
use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{GlobalVar, LocalSubst, LocalVar, Term, Type};
use heather_syntax::{
    ANON_CTOR_LEFT, ANON_CTOR_ONLY, ANON_CTOR_RIGHT, Expr, ExprKind, NamedArg,
    RecordLitField, Span, Ty, TyKind,
};

use crate::inductive::{self, Inductive};
use crate::names::{NameKind, qkey};
use crate::traits::instance_key;
use crate::unification::{Sol, zonked};
use crate::{
    Alias, Cx, ElabError, Elaborator, IMPLICIT_MARK_REFUSED, PRELUDE_MODULE, R, TyVar,
    application, err, has_implicit_mark,
};

/// A defaulted field a construction left out: the marker's arguments are the
/// record's tag, the constructor and the field, and checking it runs the
/// field's default against the field's instantiated type. Like the parser's
/// markers, this head cannot collide with a source name.
pub(crate) const FIELD_DEFAULT: &str = "\0field-default";

impl Elaborator {
    const STANDARD_LIST_MODULE: &'static str = "list";

    /// A constructor's arguments with its defaulted fields filled
    /// (docs/named-arguments-design.md §9.2): the positional arguments fill
    /// the fields without a default, in order, or every field when they are
    /// all written; a named argument fills its field; a defaulted field left
    /// out gets [`FIELD_DEFAULT`]'s marker. `None` when the constructor has no
    /// defaulted field, which leaves every other construction as it was.
    pub(crate) fn with_field_defaults(
        &self,
        ind: &Inductive,
        i: usize,
        positional: &[&Expr],
        named: &[(&str, &Expr, Span)],
        span: Span,
    ) -> R<Option<Vec<Expr>>> {
        let ctor = &ind.ctors[i];
        if ctor.defaults.iter().all(Option::is_none) {
            return Ok(None);
        }
        let n = ctor.fields.len();
        let name_of = |k: usize| ctor.fields[k].0.as_deref().unwrap_or("_");
        let mut slots: Vec<Option<Expr>> = vec![None; n];
        let open: Vec<usize> = if positional.len() == n { (0..n).collect() }
            else { (0..n).filter(|&k| ctor.defaults[k].is_none()).collect() };
        if positional.len() > open.len() {
            return err(
                format!(
                    "`{}` takes {} field(s) by position, found {}; a field with a default is given by name (`{} := …`)",
                    ctor.name, open.len(), positional.len(),
                    (0..n).find(|&k| ctor.defaults[k].is_some()).map(name_of).unwrap_or("_"),
                ),
                span,
            );
        }
        for (&k, arg) in open.iter().zip(positional) {
            slots[k] = Some((*arg).clone());
        }
        for (name, value, at) in named {
            let Some(k) = (0..n).find(|&k| name_of(k) == *name) else {
                return err(format!("`{}` has no field `{name}`", ctor.name), *at);
            };
            if slots[k].is_some() {
                return err(format!("field `{name}` is given twice"), *at);
            }
            slots[k] = Some((*value).clone());
        }
        let missing: Vec<&str> = (0..n).filter(|&k| slots[k].is_none() && ctor.defaults[k].is_none()).map(name_of).collect();
        if !missing.is_empty() {
            return err(format!("`{}` is missing field(s): {}", ctor.name, missing.join(", ")), span);
        }
        let number = |value: u64| Expr { kind: ExprKind::Num(value.into()), span };
        Ok(Some(slots.into_iter().enumerate().map(|(k, slot)| slot.unwrap_or_else(|| Expr {
            kind: ExprKind::App {
                head: Box::new(Expr { kind: ExprKind::Var(FIELD_DEFAULT.into()), span }),
                args: vec![number(u64::from(ind.tag)), number(i as u64), number(k as u64)],
                named: vec![],
                explicit: false,
                goal_oriented: false,
            },
            span,
        })).collect()))
    }

    /// A defaulted field, filled: its default checked at the field's type as
    /// this construction instantiates it. The default sees that goal and the
    /// construction's hypotheses by type, but none of its locals by name, and
    /// its names resolve where the record was declared — so a caller's names
    /// cannot change what it means (docs/named-arguments-design.md §9.4).
    pub(crate) fn elab_field_default(&self, cx: &Cx, args: &[Expr], expected: &Type, lvl: &Level, span: Span) -> R<Term> {
        let number = |k: usize| match args.get(k).map(|arg| &arg.kind) {
            Some(ExprKind::Num(n)) => n.as_u64(),
            _ => None,
        };
        let (Some(tag), Some(i), Some(k)) = (number(0), number(1), number(2)) else {
            return err("internal field default has the wrong form", span);
        };
        let ind = u32::try_from(tag).ok().and_then(|tag| self.types.by_tag(tag)).cloned()
            .ok_or_else(|| crate::ElabError::Elab { msg: "internal field default names no record".into(), span })?;
        let ctor = &ind.ctors[i as usize];
        let field = ctor.fields[k as usize].0.as_deref().unwrap_or("_");
        let Some(default) = ctor.defaults[k as usize].as_ref() else {
            return err("internal field default names a field with none", span);
        };
        let goal = self.spell_type_source(cx, expected).or_else(|| self.spell_type(cx, expected)).unwrap_or_else(|| "its type".into());
        let _scope = self.use_inductive_scope(&ind);
        // The goal is open in the construction's locals, so the default is
        // checked under them — renamed out of reach, so that a tactic sees each
        // hypothesis and no local can capture one of the default's names
        // (`Cx::hygienic`; docs/named-arguments-design.md §9.6).
        self.elab_check(&cx.hygienic(), default, expected, lvl).map_err(|error| crate::ElabError::Elab {
            msg: format!("`{field}` was left to its default, which did not prove `{goal}` here: {}; \
                give it by name (`{field} := …`)", match error {
                    crate::ElabError::Elab { msg, .. } => msg,
                    other => other.to_string(),
                }),
            span,
        })
    }

    fn standard_list_literal_instance_registered(&self) -> bool {
        let protocol = qkey(PRELUDE_MODULE, "CollectionLiteral");
        let list = qkey(Self::STANDARD_LIST_MODULE, "List");
        // `A` is binder 0 and the generic literal length is binder 1 in the
        // standard instance.
        self.traits
            .has_instance(&instance_key(&protocol, &list, "#binder1"))
    }

    fn is_standard_list(&self, ind: &Inductive) -> bool {
        self.types
            .inductive(&qkey(Self::STANDARD_LIST_MODULE, "List"))
            .is_some_and(|standard| standard.tag == ind.tag)
    }

    fn list_ctor_indices(ind: &Inductive) -> Option<(usize, usize)> {
        if ind.params.len() != 1
            || !ind.valparams.is_empty()
            || ind.index.is_some()
        {
            return None;
        }
        let nil = ind.ctors.iter().position(|ctor| ctor.name == "Nil" && ctor.fields.is_empty())?;
        let cons = ind.ctors.iter().position(|ctor| ctor.name == "Cons" && ctor.fields.len() == 2)?;
        Some((nil, cons))
    }

    fn manual_list_spine(
        &self,
        cx: &Cx,
        expr: &Expr,
        list_tag: u32,
        nil: usize,
        cons: usize,
    ) -> bool {
        let mut expr = expr;
        loop {
            match &expr.kind {
                ExprKind::Var(name) => return self.ctor_here(cx, name)
                    .is_some_and(|(ind, ctor)| ind.tag == list_tag && ctor == nil),
                ExprKind::App { head, args, named, explicit: false, goal_oriented: false }
                    if named.is_empty() && matches!(&head.kind, ExprKind::Var(name) if self
                        .ctor_here(cx, name)
                        .is_some_and(|(ind, ctor)| ind.tag == list_tag && ctor == cons)) => {
                    let [_, tail] = args.as_slice() else { return false };
                    expr = tail;
                }
                _ => return false,
            }
        }
    }

    /// Warn once, at the outermost finite `Cons(…, …Nil)` spine, after
    /// constructor resolution has proved that it is the standard `List` and
    /// not merely another declaration using familiar constructor names.
    pub(super) fn lint_manual_list_construction(
        &self,
        cx: &Cx,
        expr: &Expr,
        ind: &Inductive,
        ctor: usize,
    ) {
        if !self.is_standard_list(ind) || !self.standard_list_literal_instance_registered() {
            return;
        }
        let Some((nil, cons)) = Self::list_ctor_indices(ind) else { return };
        if ctor != cons {
            return;
        }
        if self.pass.warnings.borrow().iter().any(|warning| {
            warning.lint == crate::Lint::ManualListConstruction
                && warning.span.start <= expr.span.start
                && expr.span.end <= warning.span.end
        }) {
            return;
        }
        if !self.manual_list_spine(cx, expr, ind.tag, nil, cons) { return; }
        self.emit_lint(
            crate::Lint::ManualListConstruction,
            "this builds a concrete list with a manual `Cons`/`Nil` spine; write `[…]` instead (your parentheses have suffered enough)",
            expr.span,
        );
    }

    /// A record literal (§6): permute the written fields into declaration
    /// order and hand the result to the ordinary tier-0 constructor path.
    /// Every diagnostic about *which* fields were written lives here, since
    /// the constructor path only ever sees a positional list.
    pub(super) fn record_lit_args<'a>(
        &self,
        name: &str,
        fields: &'a [RecordLitField],
        span: Span,
    ) -> R<Vec<&'a Expr>> {
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
        application::permute_by_name_refs(name, "field", &decl, &[], &written, span)
    }

    /// `base with { f = e, … }` (issues/record-update-syntax.md): the record
    /// literal that writes the given fields and keeps every other one as
    /// `base`'s projection, so it elaborates on the literal's path, checking
    /// and inference alike, and its term is the constructor over projections
    /// that every reader of a record already takes. A base that is not a
    /// local is bound once by a `let`, which is an alias: it is elaborated
    /// once, and the term is the same. A kept field whose type mentions a
    /// replaced one (a dependent record) is refused, since its old value is no
    /// longer about the new one: the update has to give it too.
    pub(super) fn record_update_expr(&self, cx: &Cx, base: &Expr, fields: &[RecordLitField], span: Span) -> R<Expr> {
        let (_, ty, _) = self.elab_infer(cx, base)?;
        let ty = self.whnf(cx, &ty, base.span)?;
        let Some(ind) = self.tag_of(&ty).filter(|ind| ind.is_record) else {
            return err(format!("`with` updates a record's fields, and this is `{}`", self.display_type(cx, &ty)), base.span);
        };
        let decl = &ind.ctors[0].fields;
        for (index, field) in fields.iter().enumerate() {
            if !decl.iter().any(|(name, _)| name.as_deref() == Some(field.name.as_str())) {
                return err(format!("`{}` has no field `{}`", ind.name, field.name), field.span);
            }
            if fields[..index].iter().any(|earlier| earlier.name == field.name) {
                return err(format!("`{}` is updated twice", field.name), field.span);
            }
        }
        for (name, field_ty) in decl {
            let Some(name) = name else {
                return err(format!("`{}` has an unnamed field, which `with` cannot keep", ind.name), span);
            };
            if fields.iter().any(|f| f.name == *name) {
                continue;
            }
            if let Some(replaced) = fields.iter().find(|f| crate::datarepr::mentions_free_ty(field_ty, std::slice::from_ref(&f.name), &mut Vec::new())) {
                return err(
                    format!("`{name}`'s type mentions `{}`, which this update replaces: give `{name}` a new value too", replaced.name),
                    replaced.span,
                );
            }
        }
        let local = matches!(&base.kind, ExprKind::Var(name) if cx.names.iter_inner().any(|n| n == name));
        let bound = "__with_base";
        let receiver = if local { base.clone() } else { Expr { kind: ExprKind::Var(bound.into()), span: base.span } };
        let written = decl
            .iter()
            .map(|(name, _)| {
                let name = name.clone().unwrap_or_default();
                fields.iter().find(|f| f.name == name).cloned().unwrap_or_else(|| RecordLitField {
                    expr: Expr {
                        kind: ExprKind::Dot { recv: Box::new(receiver.clone()), name: name.clone(), tyargs: Vec::new(), args: None, named: Vec::new() },
                        span: base.span,
                    },
                    name,
                    span: base.span,
                })
            })
            .collect();
        let literal = Expr { kind: ExprKind::RecordLit { name: ind.name.clone(), tyargs: Vec::new(), fields: written }, span };
        if local {
            return Ok(literal);
        }
        Ok(Expr {
            kind: ExprKind::Block(Box::new(heather_syntax::Block {
                stmts: vec![heather_syntax::Stmt::Let { name: bound.into(), ty: None, expr: base.clone(), span: base.span, opaque: false }],
                result: Box::new(literal),
                ons: Vec::new(),
                span,
            })),
            span,
        })
    }

    /// The constructor this name refers to *here* — `None` when it is not a
    /// constructor, or when a local binder or `let` alias shadows it.
    pub(super) fn ctor_here(&self, cx: &Cx, name: &str) -> Option<(Rc<Inductive>, usize)> {
        if cx.names.iter_inner().any(|n| n == name) || cx.aliases.iter_inner().any(|a| a.name == *name) {
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
        if cx.names.iter_inner().any(|n| n == name) || cx.aliases.iter_inner().any(|a| a.name == *name) {
            return None;
        }
        if !self.only_ctors_visible(name) {
            return None;
        }
        // `only_ctors_visible` holds vacuously of a name nothing declares —
        // a recursive call to the declaration being checked, which is not
        // registered until it is admitted — and `arm_ctor_index` can only
        // match a name some inductive registered as its constructor (or a
        // record as its own). Without this, every recursive call reduced its
        // expected type for nothing: most of `Prog::no_holes_fit`'s
        // elaboration, its seventeen arms each a self-call at an expected
        // type over `Asm` (issues/linux-wp-cold-rail.md).
        let base = name.split_once("::").map_or(name, |(_, ctor)| ctor);
        if !self.names.declares_any_as(base, &[NameKind::Ctor, NameKind::Inductive]) {
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
        //
        // A qualified spelling matches an arm only as `Ty::ctor` with `Ty`
        // the expected inductive itself (`arm_ctor_index`). When the
        // qualifier names no inductive at all — `omega::normalize_atom`,
        // every module-qualified lemma a generated certificate applies — the
        // route cannot fire, and reducing the expected type first would be
        // the whole cost of asking (issues/omega-per-goal-elaboration-cost.md:
        // seconds per lemma application, on `Le(x, dot(row, atoms))`).
        if let Some((qualifier, _)) = name.split_once("::")
            && !self.names.declares_any_as(qualifier, &[NameKind::Inductive])
        {
            return None;
        }
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
        let scopes = self.scope.resolution_scopes.borrow();
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
    pub(super) fn ctor_spine<'a>(
        &self,
        cx: &Cx,
        e: &'a Expr,
    ) -> Option<(Rc<Inductive>, usize, Vec<&'a Expr>, Vec<&'a NamedArg>)> {
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
                Some((ind, i, args.iter().collect(), named.iter().collect()))
            }
            ExprKind::App { .. } => {
                let (ind, i, mut prefix, mut pnamed) = self.ctor_spine(cx, head)?;
                prefix.extend(args.iter());
                pnamed.extend(named.iter());
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
    pub(super) fn ctor_spine_expected<'a>(
        &self,
        cx: &Cx,
        e: &'a Expr,
        expected: &Type,
    ) -> Option<(Rc<Inductive>, usize, Vec<&'a Expr>, Vec<&'a NamedArg>)> {
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
                Some((ind, i, args.iter().collect(), named.iter().collect()))
            }
            ExprKind::App { .. } => {
                let (ind, i, mut prefix, mut pnamed) =
                    self.ctor_spine_expected(cx, head, expected)?;
                prefix.extend(args.iter());
                pnamed.extend(named.iter());
                Some((ind, i, prefix, pnamed))
            }
            _ => None,
        }
    }

    /// Only the checking route for saturated constructors of the same plain
    /// recursive family can be suspended on the constructor work stack.
    pub(super) fn recursive_ctor_call<'a>(
        &self, cx: &Cx, expr: &'a Expr, family: &Inductive, expected: &Type,
    ) -> R<Option<(usize, Vec<&'a Expr>)>> {
        let call = match &expr.kind {
            ExprKind::Var(name) => self.ctor_here_expected(cx, name, expected)
                .map(|(ind, i)| (ind, i, Vec::new(), Vec::new())),
            ExprKind::App { head, args, named, explicit: false, goal_oriented: false }
                if named.is_empty() && matches!(&head.kind, ExprKind::Var(name) if matches!(
                    name.as_str(), ANON_CTOR_ONLY | ANON_CTOR_LEFT | ANON_CTOR_RIGHT,
                )) => {
                let ExprKind::Var(name) = &head.kind else { unreachable!() };
                let (ind, i) = self.anonymous_ctor_expected(cx, name, expected, expr.span)?;
                Some((ind, i, args.iter().collect(), Vec::new()))
            }
            ExprKind::App { explicit: false, goal_oriented: false, .. } =>
                self.ctor_spine_expected(cx, expr, expected),
            _ => None,
        };
        let Some((ind, i, args, named)) = call else { return Ok(None) };
        if ind.tag != family.tag { return Ok(None); }
        let args = application::resolve_constructor_arguments(&ind, i, &args, &named, expr.span)?
            .unwrap_or(args);
        if args.len() != ind.ctors[i].fields.len() { return Ok(None); }
        self.lint_manual_list_construction(cx, expr, &ind, i);
        Ok(Some((i, args)))
    }

    /// A construction that may leave a defaulted field out
    /// (docs/named-arguments-design.md §9.5), where nothing is checking it.
    /// A default is filled against the type the construction is built at, so
    /// a declaration without parameters is checked at its one instance; one
    /// with parameters has nothing here to fix them, and says so unless every
    /// field is written (the ordinary inference then applies). `None` leaves
    /// a constructor without defaults to the ordinary inference.
    pub(super) fn infer_defaulted_ctor(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        i: usize,
        written: usize,
        e: &Expr,
    ) -> Option<R<(Term, Type, Level)>> {
        let ctor = &ind.ctors[i];
        if ctor.defaults.iter().all(Option::is_none) {
            return None;
        }
        if ind.params.is_empty() && ind.valparams.is_empty() && ind.index.is_none() {
            return Some((|| {
                let (ty, lvl) = self.lower_instance(cx, ind, &[], &[], e.span)?;
                let t = self.elab_check(cx, e, &ty, &lvl)?;
                Ok((t, ty, lvl))
            })());
        }
        if written == ctor.fields.len() {
            return None;
        }
        Some(err(
            format!(
                "`{}` leaves a defaulted field to be filled, which needs the type it builds, \
                 and nothing here fixes `{}`'s parameters: put the construction where the \
                 expected type is `{}<…>`, or give every field",
                ctor.name, ind.name, ind.name
            ),
            e.span,
        ))
    }

    /// A constructor used where nothing is checking it. Only possible when the
    /// declaration has no type parameters — otherwise there is nothing to
    /// determine the instantiation, and an annotation is required (§2:
    /// parameters are monomorphized, not inferred).
    pub(super) fn infer_ctor<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        i: usize,
        args: &[A],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        // Type arguments are recovered only from a field whose type *is* a
        // parameter (`Some(A)`), by inferring that argument. Deliberately
        // narrow: anything deeper is unification, which belongs to
        // issues/elab-unifier-completeness.md, not here. A `None` on its own
        // is genuinely ambiguous and says so. Value parameters are solved
        // after these, by the call unifier ([`Self::infer_ctor_values`]).
        let mut sols: Vec<Option<(Type, Level)>> = vec![None; ind.params.len()];
        // A field that cannot be inferred on its own (`Nil` in `Cons(Nil,
        // xs)`) may still be fixed by a later child argument: its error is
        // kept and reported only if nothing else determines the instance.
        // `build_ctor` checks every argument against its field afterwards,
        // so an error in the argument itself is still reported, there.
        let mut deferred = None;
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
                match self.elab_infer(cx, arg.borrow()) {
                    Ok((_, ty, lvl)) => sols[p] = Some((ty, lvl)),
                    Err(e) => {
                        deferred.get_or_insert(e);
                    }
                }
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
                if let Some(e) = deferred {
                    return Err(e);
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
        if !ind.valparams.is_empty() {
            return self.infer_ctor_values(cx, ind, i, args, &targs, span);
        }
        let (ty, lvl) = if ind.skel.is_some() && args.len() == ind.ctors[i].fields.len() {
            // Route 2b: the index is the constructor's *written* result index
            // at the arguments it was given (docs/inductive-fording-lowering.md
            // §2), which is the whole widening.
            let (idx, _, _) = self.iwf_ctor_index(cx, ind, i, args, span)?;
            self.lower_iwf_instance(cx, ind, &targs, idx, span)?
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

    /// The value parameters of a constructor used where nothing is checking
    /// it, solved the way a call solves its implicits
    /// (issues/value-param-constructor-implicit-inference.md): the
    /// constructor's payload is lowered with the parameters as binders, the
    /// binders become the metas of a scratch world, and each field's type is
    /// unified with its argument's — `Fin(f)` at `f : Finite(F)` meets
    /// `Finite(?F)`, `Inf(b, h)` at `h : F.specials.has_inf().IsTrue()` meets
    /// that proposition at `?F`. A field whose type is already meta-free is
    /// checked rather than inferred, so `refl` and lambdas in it cost
    /// nothing; the walk stops once every parameter is solved, and the
    /// construction is then built at the solved instance by the checking
    /// route, which checks every argument against its field again. A wrong
    /// solution is therefore a type error there, never a mis-lowering.
    ///
    /// This replaces the old refusal (docs/surface-value-parameters.md §4),
    /// which read the problem as higher-order unification; it is the same
    /// first-order problem a call's domain `Float(?F)` poses, because the
    /// parameter's occurrences in the field types are rigid spines. A
    /// parameter no payload field fixes may still be fixed by a child, whose
    /// type is the whole instance ([`Self::ctor_from_child`]).
    fn infer_ctor_values<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        i: usize,
        args: &[A],
        targs: &[(Type, Level)],
        span: Span,
    ) -> R<(Term, Type, Level)> {
        let n = ind.valparams.len() as u32;
        // The value-parameter telescope as binders past `cx`, each declared
        // type read under the type arguments and the earlier parameters, as
        // `valparam_args` reads them at a written use.
        let mut tcx = cx.clone();
        let depth = cx.names.len();
        tcx.tyvars.extend(ind.params.iter().zip(targs).map(|(name, (ty, level))| TyVar {
            name: name.clone(),
            ty: ty.clone(),
            level: level.clone(),
            depth,
        }));
        tcx.op_locals.clear();
        let mut decls: Vec<(Type, Level)> = Vec::with_capacity(n as usize);
        for (j, (pname, pty)) in ind.valparams.iter().enumerate() {
            let (ty, level) = {
                let _scope = self.use_inductive_scope(ind);
                self.elab_ty(&tcx, pty)?
            };
            tcx.push(format!("#v{j}"), ty.clone(), level.clone());
            tcx.aliases.push(Rc::new(Alias {
                skel: None,
                name: pname.clone(),
                depth: tcx.names.len(),
                term: Rc::new(Term::Var(LocalVar(0))),
                ty: ty.shift_local(1),
                level: level.clone(),
                spliced: None,
                shifted: Default::default(),
            }));
            if let Some((sym, _)) = ind.op_symbols.iter().find(|(_, n)| n == pname) {
                tcx.op_locals.push((sym.clone(), pname.clone()));
            }
            decls.push((ty, level));
        }
        let open_targs: Vec<(Type, Level)> =
            targs.iter().map(|(t, l)| (t.shift_local(n), l.clone())).collect();
        let open_vargs: Vec<(Term, Type, Level)> = decls
            .iter()
            .enumerate()
            .map(|(j, (t, l))| {
                (Term::Var(LocalVar(n - 1 - j as u32)), t.shift_local(n - j as u32), l.clone())
            })
            .collect();
        let (shape, _) = self.lower_ctor(&tcx, ind, i, &open_targs, &open_vargs, span)?;
        // Into the scratch world: the parameter binders become metas `< n`,
        // exactly as a callee's `Π` binders do in `apply_implicit`.
        let to_scratch = (0..n).fold(LocalSubst::id(&cx.gamma), |s, j| {
            s.extended(Rc::new(Term::GlobalTm {
                var: GlobalVar(j),
                subst: LocalSubst::id(&cx.gamma),
            }))
        });
        let mut pat = shape.shift_global(n).apply_local(&to_scratch);
        let mut sols = vec![Sol::Unsolved; n as usize];
        let solved = |sols: &[Sol]| sols.iter().all(|s| s.solved().is_some());
        let step = |pat: &Type, tm: Term| match pat {
            Type::Sigma { snd, .. } => Some(
                snd.apply_local(&LocalSubst::id(&cx.gamma).extended(Rc::new(tm.shift_global(n)))),
            ),
            _ => None,
        };
        // Entry 0 of the payload is the tag, which no field type mentions.
        if let Type::Sigma { fst, .. } = &pat {
            let tag = inductive::tag_value(fst);
            pat = step(&pat, tag).unwrap_or(pat);
        }
        // A field whose argument did not infer while its type waited on a
        // parameter: named in the refusal if nothing else fixes it.
        let mut stuck: Option<(usize, ElabError)> = None;
        let ctor = &ind.ctors[i];
        for (k, arg) in args.iter().enumerate() {
            if ctor.kind.get(k) != Some(&inductive::FieldKind::Payload) {
                continue;
            }
            if solved(&sols) {
                break;
            }
            let Type::Sigma { fst, fst_level, .. } = &pat else { break };
            let tm = match zonked(fst, n, &sols) {
                Some(real) => self.elab_check(cx, arg.borrow(), &real, fst_level)?,
                None => match self.elab_infer(cx, arg.borrow()) {
                    Ok((tm, ty, _)) => {
                        self.unify_arg_ty(cx, fst, &ty, n, &mut sols, span);
                        tm
                    }
                    Err(e) => {
                        stuck = Some((k, e));
                        break;
                    }
                },
            };
            let Some(next) = step(&pat, tm) else { break };
            pat = next;
        }
        if !solved(&sols) {
            if let Some(r) = self.ctor_from_child(cx, ind, i, args, span) {
                return r;
            }
            let p = sols
                .iter()
                .position(|s| s.solved().is_none())
                .map_or("?", |j| ind.valparams[j].0.as_str());
            let why = match &stuck {
                Some((k, ElabError::Elab { msg, .. })) => format!(
                    " (its field `{}` would, but that argument does not infer on its own: {msg})",
                    ctor.fields[*k].0.as_deref().unwrap_or("_")
                ),
                _ => String::new(),
            };
            return err(
                format!(
                    "cannot infer the value argument `{p}` of `{}` here — no argument of \
                     `{}` determines it{why}. Put the expression in a checking position: a \
                     `fn`/`theorem` body whose declared result is `{}(…)`, an annotated \
                     `let`, or an argument of a declaration that expects one",
                    ind.name, ctor.name, ind.name
                ),
                span,
            );
        }
        let mut vargs: Vec<(Term, Type, Level)> = Vec::with_capacity(n as usize);
        let mut inst = LocalSubst::id(&cx.gamma);
        for (sol, (ty, level)) in sols.iter().zip(&decls) {
            let Some(v) = sol.solved() else { unreachable!() };
            vargs.push(((**v).clone(), ty.apply_local(&inst), level.clone()));
            inst = inst.extended(Rc::clone(v));
        }
        let (ty, lvl) = self.lower_instance(cx, ind, targs, &vargs, span)?;
        let t = self.build_ctor(cx, ind, i, args, &ty, &lvl, span)?;
        Ok((t, ty, lvl))
    }

    /// A constructor of an **indexed** family whose type-parameter
    /// instantiation is determined by a *child* argument
    /// (`docs/inductive-fording-lowering.md` §14.7, and route 1's same gap).
    ///
    /// The child's inferred type is the family at the child's own index, and
    /// both routes keep the family in a form that can be re-applied at another
    /// index — `IwfFam::ty_at` and `IndexedFam::el_at`, which is what
    /// `match` uses to name `fam 0` and `fam (S m)` from one read-back type. So
    /// there is nothing to *solve*: the instance comes back whole and the
    /// written result index says where to put it. `None` when no argument is a
    /// child, or when the first child's type is not this family.
    fn ctor_from_child<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        ind: &Rc<Inductive>,
        i: usize,
        args: &[A],
        span: Span,
    ) -> Option<R<(Term, Type, Level)>> {
        if args.len() != ind.ctors[i].fields.len() {
            return None;
        }
        // A family with no index: a child's type is the constructor's result
        // type itself (`Cons(Nil, xs)` is at `xs`'s type).
        if ind.index.is_none() && ind.skel.is_none() {
            let k = ind.ctors[i].kind.iter().position(|f| {
                matches!(f, inductive::FieldKind::Plain | inductive::FieldKind::FnChild)
            })?;
            let (_, ty, lvl) = self.elab_infer(cx, args[k].borrow()).ok()?;
            // A recursive function field (`k: A -> D`, tier 2) is at
            // `Π(y : A). D`, and the instance is its codomain — provided
            // that does not mention `y`.
            let (ty, lvl) = if ind.ctors[i].kind[k] == inductive::FieldKind::FnChild {
                match self.whnf(cx, &ty, span).ok()? {
                    Type::Pi { cod, cod_level, .. } => {
                        (crate::vec::strengthen(&cod, &cx.gamma)?, cod_level)
                    }
                    _ => return None,
                }
            } else {
                (ty, lvl)
            };
            if self.tag_of(&ty)?.tag != ind.tag {
                return None;
            }
            return Some(self.build_ctor(cx, ind, i, args, &ty, &lvl, span).map(|t| (t, ty, lvl)));
        }
        if ind.index.is_none() {
            return None;
        }
        let k = ind.ctors[i]
            .kind
            .iter()
            .position(|f| *f == inductive::FieldKind::Plain)?;
        let (_, cty, _) = self.elab_infer(cx, args[k].borrow()).ok()?;
        let (ty, lvl) = if ind.skel.is_some() {
            let (found, fam) = self.iwf_of_at(cx, &cty)?;
            if found.tag != ind.tag {
                return None;
            }
            let idx = match self.iwf_ctor_index(cx, ind, i, args, span) {
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
    pub(super) fn ctor_at<A: Borrow<Expr>>(
        &self,
        cx: &Cx,
        callee: &Expr,
        tyargs: &[Ty],
        args: &[A],
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
            // `R<Nat>(a, b)`: the type arguments are written, and the value
            // arguments are read off the fields as they are with none written
            // (docs/surface-value-parameters.md §4.1) — `<…>` cannot supply
            // them, and the refusal when nothing fixes one says what does.
            if !ind.valparams.is_empty() {
                return self.infer_ctor_values(cx, &ind, i, args, &lowered, span);
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
                    let (idx, _, _) = self.iwf_ctor_index(cx, &ind, i, args, span)?;
                    self.lower_iwf_instance(cx, &ind, &lowered, idx, span)?
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn curried_constructor_spines_borrow_the_original_arguments() {
        let mut e = Elaborator::with_prelude().expect("prelude");
        e.elab_source("inductive L { Nil, Cons(Nat, L) }").expect("type");
        let span = Span { start: 0, end: 1 };
        let var = |name: &str| Expr { kind: ExprKind::Var(name.into()), span };
        let app = |head: Expr, arg: Expr| Expr {
            kind: ExprKind::App {
                head: Box::new(head), args: vec![arg], named: Vec::new(),
                explicit: false, goal_oriented: false,
            }, span,
        };
        let expr = app(app(var("Cons"), Expr { kind: ExprKind::Num(0.into()), span }), var("Nil"));
        let ExprKind::App { head, args: outer, .. } = &expr.kind else { unreachable!() };
        let ExprKind::App { args: inner, .. } = &head.kind else { unreachable!() };
        let cx = Cx::empty();
        let (ind, _, args, _) = e.ctor_spine(&cx, &expr).expect("curried constructor");
        assert!(std::ptr::eq(args[0], &inner[0]));
        assert!(std::ptr::eq(args[1], &outer[0]));
        let (expected, _) = e.lower_instance(&cx, &ind, &[], &[], span).expect("instance");
        let (_, _, args, _) = e.ctor_spine_expected(&cx, &expr, &expected).expect("checking spine");
        assert!(std::ptr::eq(args[0], &inner[0]));
        assert!(std::ptr::eq(args[1], &outer[0]));
    }
}
