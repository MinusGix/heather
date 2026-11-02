//! Class-backed projection from a type subject.
//!
//! This owns declaring-class selection, type-subject recovery, competing
//! readings, and the explicit `T::Class(index)` dictionary spelling.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, ExprKind, Span, Ty, TyKind};

use crate::inductive::Inductive;
use crate::{
    BUILTIN_METHODS, Cx, DotResolution, ElabError, Elaborator, NameRes, R, Upcast, err,
    expression_as_type, names, resolve, skel_of_ty, subject_text, traits,
};

impl Elaborator {
    /// The classes that **declare** `name` — not the ones that merely inherit
    /// it — and are visible here, in sorted canonical-name order
    /// (docs/traits-owner-dispatch-design.md §2). Never `HashMap` order and
    /// never declaration order.
    ///
    /// "Visible here" is `key_of(C.name) == the key C is stored under`: the
    /// ordinary §4 name regime, asked by resolving the class's own name, and
    /// not a second visibility rule.
    pub(crate) fn declaring_classes(&self, name: &str) -> Vec<(String, Rc<traits::ClassInfo>)> {
        self.traits
            .classes_declaring(name)
            .into_iter()
            .filter(|(key, info)| self.key_of(&info.name).as_deref() == Some(key.as_str()))
            .collect()
    }

    /// The receiver read **as a type**, when it is one
    /// (docs/traits-type-projection-design.md §3.1). Two shapes, and they are
    /// exclusive by construction:
    ///
    /// - the receiver elaborates as a value whose type is a universe — a type
    ///   parameter `A`, or any binder at `Type<n>`; the carrier is `El` of
    ///   that code, which is what `lower_named` would have built for it;
    /// - the receiver does not elaborate as a value at all, but reads as a
    ///   type by shape (`Nat`, `Bool`, `Box<Z>`), through the same
    ///   [`surface::expression_as_type`] the universe round already uses.
    ///
    /// A value binder therefore **shadows** the type reading — `elab_infer`
    /// succeeds at a non-universe type and this answers `None` — which is what
    /// keeps a parameter named like a type from being reinterpreted.
    pub(crate) fn type_subject(&self, cx: &Cx, recv: &Expr, span: Span) -> Option<(Type, Level)> {
        match self.elab_infer(cx, recv) {
            Ok((tm, ty, _)) => {
                let Type::Ty(level) = self.whnf(cx, &ty, span).ok()? else {
                    return None;
                };
                Some((
                    Type::El {
                        level: level.clone(),
                        tm: Rc::new(tm),
                    },
                    level,
                ))
            }
            Err(_) => self.elab_ty(cx, &expression_as_type(recv)?).ok(),
        }
    }

    /// `T.f` / `T.f(…)` where the subject is a **type**
    /// (docs/traits-type-projection-design.md): `A.unit`, `G.plus(x, G.zero)`,
    /// `Nat.zero`.
    ///
    /// The rule is receiver dispatch's with one word changed: the goal is
    /// built at the class that **declares** `f`, with the *subject itself* as
    /// the carrier rather than the subject's type, and the subject is
    /// therefore **not** an argument. So the emitted term is an ordinary field
    /// projection — the very term `⟨dictionary⟩.f` elaborates to — and a
    /// proof field (`A.unit_r(x)`) needs nothing of its own.
    ///
    /// `None` is "this is not a type projection", and every `None` leaves
    /// every older reading to run exactly as it did.
    pub(crate) fn type_projection(
        &self,
        cx: &Cx,
        recv: &Expr,
        name: &str,
        args: &Option<Vec<Expr>>,
        span: Span,
    ) -> R<Option<DotResolution>> {
        // The cheap negative test, before anything is inferred or lowered: a
        // `.f` where `f` is nobody's class field costs one hash lookup, which
        // is what keeps every program that predates classes at its old price.
        if !self.traits.has_member(name) {
            return Ok(None);
        }
        let Some((carrier, clvl)) = self.type_subject(cx, recv, span) else {
            return Ok(None);
        };
        let ns = self.type_namespace(cx, &carrier, span);
        let other = self.other_reading_of_a_type_subject(cx, &ns, name, args, span);
        let with_field = self.declaring_classes(name);
        let cands: Vec<(String, Rc<traits::ClassInfo>)> = with_field
            .iter()
            .filter(|(_, i)| i.params.len() == 1)
            .cloned()
            .collect();
        // A local dictionary already fixes every type argument. For a
        // multi-parameter class, use that complete dictionary rather than
        // guessing the missing arguments from the subject or global instances.
        let mut scoped_hits: Vec<(Rc<Inductive>, Type, Term, String, Upcast)> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for d in cx.dicts.iter_inner() {
            if !seen.insert(d.name.clone()) {
                continue;
            }
            let Some(dkey) = self.key_of(&d.class) else {
                continue;
            };
            let Some(dinfo) = self.traits.class(&dkey) else {
                continue;
            };
            let Ok((dc, dlvl)) = self.elab_ty(cx, &d.carrier) else {
                continue;
            };
            if dlvl != clvl || !self.conv_types(cx, &dc, &carrier, &clvl) {
                continue;
            }
            let Ok((dict, goal, _)) = self.resolve_reading(cx, &d.name, span) else {
                continue;
            };
            let Some(root) = self.lookup_inductive(&dinfo.name).cloned() else {
                continue;
            };
            if self
                .display_tag_of(&goal)
                .is_none_or(|tag| tag.tag != root.tag)
            {
                continue;
            }
            for (key, info) in with_field.iter().filter(|(_, info)| info.params.len() > 1) {
                let paths: Vec<Vec<String>> = if key == &dkey {
                    vec![Vec::new()]
                } else {
                    // A tagged parent carries a complete dictionary too. Only
                    // paths preserving the primary carrier can use this subject.
                    dinfo.ancestors.iter().filter(|ancestor|
                        !ancestor.path.is_empty() && self.key_of(&ancestor.name).as_deref() == Some(key.as_str())
                        && matches!(ancestor.args.first().map(|a| &a.kind), Some(TyKind::Named { name, args })
                            if args.is_empty() && dinfo.params.first() == Some(name)))
                        .map(|ancestor| ancestor.path.clone()).collect()
                };
                for path in paths {
                    let mut current = Some((root.clone(), goal.clone(), dict.clone()));
                    for component in &path {
                        current = current.and_then(|(ind, ty, term)| {
                            let idx = ind.field_index(component)?;
                            let (term, ty, _) = self
                                .project_field(cx, &ind, &ty, Rc::new(term), idx, span)
                                .ok()?;
                            let ind = self.display_tag_of(&ty)?;
                            Some((ind, ty, term))
                        });
                    }
                    if let Some((ind, ty, term)) = current {
                        if self.key_of(&ind.name) != self.key_of(&info.name) {
                            continue;
                        }
                        let display = self.display_type(cx, &ty);
                        scoped_hits.push((ind, ty, term, display, None));
                    }
                }
            }
        }
        if cands.is_empty() && scoped_hits.is_empty() {
            // The multi-parameter refusal, verbatim from receiver dispatch
            // (§4 rule 7) and for the same reason: the subject fixes the
            // carrier and nothing fixes the rest.
            if let Some((_, info)) = with_field.first()
                && other.is_none()
            {
                return err(
                    format!(
                        "`{name}` is a member of `{}`, which takes {} type parameters: a type \
                         projection builds its goal from the subject alone, so it reaches a \
                         one-parameter class only — write the projection \
                         (`⟨instance⟩.{name}`)",
                        info.name,
                        info.params.len()
                    ),
                    span,
                );
            }
            return Ok(None);
        }
        // What the trace calls the subject: the text that was written, since
        // an open carrier has no nominal tag to name (layer 2 §7).
        let subject = subject_text(recv)
            .or_else(|| ns.clone())
            .unwrap_or_else(|| "_".into());
        let mut trace: Vec<resolve::TraceLine> = Vec::new();
        let mut hits = scoped_hits;
        let mut tried: Vec<String> = Vec::new();
        let mut unpinned: Option<ElabError> = None;
        for (_, info) in &cands {
            let Some(ind) = self.lookup_inductive(&info.name).cloned() else {
                continue;
            };
            let targs = [(carrier.clone(), clvl.clone())];
            let vargs = match self.index_vargs(cx, info, &ind, &targs, &subject, span) {
                Ok(Some(v)) => v,
                Ok(None) => continue,
                Err(e) => {
                    unpinned.get_or_insert(e);
                    continue;
                }
            };
            let Ok((goal, glvl)) = self.lower_instance(cx, &ind, &targs, &vargs, span) else {
                continue;
            };
            let display = format!("{}<{subject}>", info.name);
            tried.push(display.clone());
            let mut tr = Vec::new();
            // Every candidate is tried even once one has succeeded: the
            // ambiguity is the point (§4 rule 3).
            let mut up = None;
            match self.resolve_goal_from(cx, &goal, &glvl, &display, None, span, &mut tr, &mut up) {
                Some(t) => hits.push((ind, goal, t, display, up)),
                None => trace.extend(tr),
            }
        }
        if hits.len() > 1 {
            let list = hits
                .iter()
                .map(|(_, _, _, d, _)| format!("`{d}`"))
                .collect::<Vec<_>>()
                .join(" and ");
            return err(
                format!(
                    "`{name}` at `{subject}` is declared by {list}, and each has an instance \
                     here — write the class you meant (`{subject}::⟨class⟩.{name}`) rather \
                     than letting the type choose"
                ),
                span,
            );
        }
        let Some((ind, goal, dict, display, up)) = hits.pop() else {
            if other.is_some() {
                return Ok(None);
            }
            if let Some(e) = unpinned {
                return Err(e);
            }
            return Err(ElabError::Resolution {
                goal: tried.join("` or `"),
                span,
                trace,
            });
        };
        // Receiver dispatch accepts a class member and a global that are one
        // term (issues/receiver-dispatch-coinciding-readings.md); a type
        // subject never can be. Here the subject is *not* an argument of the
        // projection, and the other reading exists only when it *is* one —
        // the callee's subject slot takes a type — so the two apply the same
        // global to different argument lists. The refusal stays unconditional.
        if let Some((desc, fix)) = other {
            return err(
                format!(
                    "`{name}` here is both a member of `{display}`, reached through the type \
                     `{subject}`, and {desc} — write one of them: \
                     `{subject}::{}.{name}` for the class member, or {fix} for the other",
                    ind.name
                ),
                span,
            );
        }
        // As in receiver dispatch: an upcast answer is read through
        // (docs/traits-named-upcast-design.md §2).
        let (ind, goal, dict) = self.through_upcast(ind, goal, dict, up, name);
        let Some(idx) = ind.field_index(name) else {
            return err(
                format!("internal: `{}` has no field `{name}` after all", ind.name),
                span,
            );
        };
        let skel = skel_of_ty(&ind.ctors[0].fields[idx].1);
        let (t, fty, flvl) = self.project_field(cx, &ind, &goal, Rc::new(dict), idx, span)?;
        Ok(Some(DotResolution::Project(t, fty, flvl, skel)))
    }

    /// What a `T.f(…)` would have meant if `T` were a value — the reading a
    /// successful type projection has to be named beside, and a failed one
    /// falls back to (docs/traits-type-projection-design.md §4).
    ///
    /// Two things make this narrower than receiver dispatch's `other`, and
    /// both are consequences of the subject being a **type**:
    ///
    /// - a **bare** `T.f` has no desugaring at all (a bare `p.f` is never a
    ///   method call), so it has no other reading, ever;
    /// - the desugaring puts the subject in the callee's *subject slot*, and a
    ///   type there is a reading only if that slot is **at a universe**. That
    ///   is read off the callee's own declared telescope — never by trying the
    ///   call — so this shrinks the candidate set the way owner-keying does
    ///   and is not a tiebreak. Undecidable (a builtin, a constructor, a
    ///   telescope that cannot be read) counts as a reading: the caution of
    ///   receiver-dispatch §7.2 belongs to exactly those.
    pub(crate) fn other_reading_of_a_type_subject(
        &self,
        cx: &Cx,
        ns: &Option<String>,
        name: &str,
        args: &Option<Vec<Expr>>,
        span: Span,
    ) -> Option<(String, String)> {
        args.as_ref()?;
        if let Some(t) = ns {
            let q = format!("{t}::{name}");
            if matches!(self.resolve_name(&q), NameRes::Found(_)) {
                return self.subject_slot_takes_a_type(cx, &q, span).then(|| {
                    (
                        format!("`{q}`, a member of `{t}`'s own namespace"),
                        format!("`{q}(…)`"),
                    )
                });
            }
        }
        if self.shadowed(cx, name) || self.ctor_of(name).is_some() {
            return self.subject_slot_takes_a_type(cx, name, span).then(|| {
                (
                    format!("`{name}`, a name in scope on its own"),
                    format!("the bare call `{name}(…)` with the type as an argument"),
                )
            });
        }
        BUILTIN_METHODS.contains(&name).then(|| {
            (
                format!("`{name}`, a built-in method"),
                format!("the bare call `{name}(…)`"),
            )
        })
    }

    /// Can `name` take a **type** where the method desugaring would put the
    /// receiver? A purely syntactic walk of the callee's own Π-telescope to
    /// its subject slot: no elaboration, no trial call, no context of its own.
    ///
    /// `true` when the answer cannot be read off a declaration, which is the
    /// conservative direction — it makes the desugaring count as a reading and
    /// so makes the diagnostic name both.
    pub(crate) fn subject_slot_takes_a_type(&self, cx: &Cx, name: &str, span: Span) -> bool {
        // This is a shape probe used only to decide whether two surface
        // readings are ambiguous. Its hypothetical callee is not a body edge.
        let dependency_mark = self.attempt.direct_dependencies.borrow().clone();
        let resolved = self.resolve_reading(cx, name, span);
        *self.attempt.direct_dependencies.borrow_mut() = dependency_mark;
        let Ok((_, ty, _)) = resolved else {
            return true;
        };
        let params = self.params_of(name);
        // Where the subject lands in *declaration* order. `subject_index`
        // counts explicit non-type parameters only, and the Π-telescope has
        // one domain per parameter in order, so this converts between the two.
        let mut pos = 0usize;
        if !params.is_empty() {
            let subj = self.subject_index(name);
            let mut seen = 0usize;
            let Some(i) = params.iter().position(|p| {
                if p.implicit || p.is_type {
                    return false;
                }
                let hit = seen == subj;
                seen += 1;
                hit
            }) else {
                // No such slot: the desugaring could not place the subject at
                // all, so it is not a reading.
                return false;
            };
            pos = i;
        }
        let mut cur = &ty;
        for _ in 0..pos {
            match cur {
                Type::Pi { cod, .. } => cur = cod,
                _ => return false,
            }
        }
        matches!(cur, Type::Pi { dom, .. } if matches!(**dom, Type::Ty(_)))
    }

    /// `G::AddCommMonoid` — the escape spelling: *the* `AddCommMonoid`
    /// dictionary at the type `G`, resolved rather than looked up
    /// (docs/traits-type-projection-design.md §5).
    ///
    /// Reached only from [`Self::resolve`]'s last stop, so it fires exactly
    /// where the answer would otherwise have been "unbound name". At a
    /// concrete carrier the qualified name is a registered global and never
    /// gets here, which is why `Nat::AddCommMonoid.plus` — the spelling the
    /// library already had — is untouched: this generalizes it to the carriers
    /// that have no global to name.
    /// `Nat::Monoid(add)` — the same spelling with the class's **index**
    /// (docs/operation-indexed-classes-design.md §5.1). An indexed class
    /// otherwise has no short dictionary spelling at a carrier with two
    /// structures, which is what discharges the projection round's
    /// "`T::C` takes no arguments" residue on `issues/traits.md`.
    pub(crate) fn class_at_type(
        &self,
        cx: &Cx,
        name: &str,
        index: &[Expr],
        span: Span,
    ) -> Option<R<(Term, Type, Level)>> {
        let (subject, class) = names::split_qual(name)?;
        let key = self.key_of(class)?;
        let info = Rc::clone(self.traits.class(&key)?);
        if info.params.len() != 1 || info.valparams.len() != index.len() {
            return None;
        }
        let ind = self.lookup_inductive(&info.name).cloned()?;
        let kind = if subject == "Nat" {
            TyKind::Nat
        } else {
            TyKind::Named {
                name: subject.into(),
                args: vec![],
            }
        };
        let (carrier, clvl) = self.elab_ty(cx, &Ty { kind, span }).ok()?;
        let targs = [(carrier, clvl)];
        // `Bool::Mon(+)` — the designation reference as a dictionary spelling
        // (docs/operation-indexed-classes-design.md §5.1, built in
        // docs/operators-onto-classes-design.md §4). This is the one argument
        // position where a bare symbol *does* have a carrier: the qualified
        // name wrote it. A symbol the table does not cover falls through to
        // the ordinary ladder, which reports it as written.
        let mut written: Vec<Expr> = Vec::with_capacity(index.len());
        // `subject` is a name the writer spelled in the qualified path, so it
        // resolves the way any written carrier does — `carrier_key`, in the
        // scope they wrote it — to the key the designation registered under.
        let subject_key = self.carrier_key(subject);
        for a in index {
            match &a.kind {
                ExprKind::OpSymbol { symbol: s, fixity } => {
                    match self.designated(s, *fixity, &subject_key) {
                        Some(op) => written.push(Expr {
                            kind: ExprKind::Var(op),
                            span: a.span,
                        }),
                        None => written.push(a.clone()),
                    }
                }
                _ => written.push(a.clone()),
            }
        }
        let vargs = match self.valparam_args(cx, &ind, &targs, &written, span) {
            Ok(v) => v,
            Err(e) => return Some(Err(e)),
        };
        let (goal, glvl) = self.lower_instance(cx, &ind, &targs, &vargs, span).ok()?;
        let display = format!(
            "{}<{subject}>{}",
            info.name,
            if index.is_empty() {
                String::new()
            } else {
                format!(
                    "({})",
                    index
                        .iter()
                        .map(traits::render_expr)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        );
        let mut tr = Vec::new();
        match self.resolve_goal(cx, &goal, &glvl, &display, None, span, &mut tr) {
            Some(t) => Some(Ok((t, goal, glvl))),
            None => Some(Err(ElabError::Resolution {
                goal: display,
                span,
                trace: tr,
            })),
        }
    }
}
