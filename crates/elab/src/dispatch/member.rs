//! Dot routing and precedence between surface member readings.
//!
//! This module owns record projection, nominal type-owned member selection,
//! method desugaring, and the ordering in which class-backed routes are asked.

use std::sync::Arc as Rc;

use heather_kernel::level::Level;
use heather_kernel::term::{
    CtxBase, GlobalBinding, LocalSubst, LocalVar, SubstTail, Term, Type,
};
use heather_syntax::{Expr, ExprKind, NamedArg, Span, Ty};

use crate::{
    BUILTIN_METHODS, Cx, DotResolution, ElabError, Elaborator, NameRes, R, err, skel_of_ty,
    application, vec,
};

use super::receiver::OtherReading;

/// Only disjoint outer carriers are used to discard imported candidates.
/// Type arguments and callbacks never break a tie; an unknown carrier keeps
/// the ambiguity, including a generic `self x: A`.
#[derive(PartialEq, Eq)]
enum ReceiverCarrier {
    Named(String),
    Vector,
}

/// The walk behind [`Elaborator::subject_excludes`]: the definitions whose
/// reducts are already being read, and a budget on the types it visits.
/// `recursive` holds the context positions bound to an eliminator's
/// recursive result while its step is read.
struct Reach {
    seen: Vec<usize>,
    recursive: Vec<usize>,
    fuel: u32,
}

impl Reach {
    const FUEL: u32 = 128;
}

impl Elaborator {
    // -- field access (docs/surface-records.md §4) ---------------------------

    /// Whether `recv` is a chain of bare projections rooted at an argument
    /// slot that the current ownership probe masks (a sibling, not its
    /// target).
    fn masked_slot_projection(&self, recv: &Expr) -> bool {
        match &recv.kind {
            ExprKind::ArgSlot(_) => self
                .attempt
                .slot_probe_target
                .get()
                .is_some_and(|target| target != recv.span),
            ExprKind::Dot {
                recv, args: None, ..
            } => self.masked_slot_projection(recv),
            _ => false,
        }
    }

    /// Resolve `p.f` / `p.f(a, …)` against the receiver's type (§4.2).
    ///
    /// The order matters and is the whole design. The **cheap negative test**
    /// comes first: if `f` is nobody's record field, this is the method
    /// desugaring and the receiver is never inferred here — which is every use
    /// that predates records (`p.sym()`, `p.inj(1)`, `xs.map(f)`), so their
    /// elaboration is bit-for-bit what it was when the parser did this.
    ///
    /// Only if `f` *is* some record's field does the receiver get inferred,
    /// and only if the receiver's own type is a record carrying `f` does this
    /// become a projection. So a field name that shadows a global costs the
    /// global nothing at any other receiver type.
    pub(crate) fn resolve_dot(
        &self,
        cx: &Cx,
        recv: &Expr,
        name: &str,
        tyargs: &[Ty],
        args: &Option<Vec<Expr>>,
        named: &[NamedArg],
        span: Span,
    ) -> R<DotResolution> {
        // A **type** subject, first: `A.unit`, `G.plus(x, y)`, `Nat.zero`
        // (docs/traits-type-projection-design.md). It is first because a type
        // is not a record and has no namespace member and is not a method
        // receiver, so nothing below could have read it — every reading it
        // takes was an error before this round, and every reading it declines
        // reaches its old handler untouched.
        // A **projection section** (`·.lines`, issues/field-projection-
        // sections.md) whose slot is a sibling masked by an ownership probe
        // (`elab_check_skel_slots`) stands for a disposable neutral, like the
        // masked slot itself (`expr.rs`): its receiver has no type to project
        // from yet, and the probe only asks which boundary owns the *other*
        // slot.
        if args.is_none() && self.masked_slot_projection(recv) {
            return Ok(DotResolution::Inferred(
                heather_kernel::term::Term::Var(heather_kernel::term::LocalVar(0)),
                Type::Nat,
                heather_kernel::level::Level::Zero,
            ));
        }
        if let Some(d) = self.type_projection(cx, recv, name, args, span)? {
            return Ok(d);
        }
        // The **index pseudo-projection** (`docs/operation-indexed-classes-
        // design.md` §5.2): `d.op` at `d: Monoid<A>(add)` is `add`, read off
        // the dictionary's type. Definitionally trivial, and it closes the
        // last "how do I refer to it" corner — anything that can name a
        // dictionary can name its index. Before the field path and harmless
        // there: a class cannot have a field named like its own index (the
        // record lowering refuses the collision), so the two never compete.
        if let ExprKind::Var(d) = &recv.kind
            && let Some(e) = self.index_of_dict(cx, d, name)
        {
            let (t, ty, lvl) = self.elab_infer(cx, &e)?;
            return Ok(DotResolution::Project(t, ty, lvl, None));
        }
        if self.types.has_record_field(name) {
            // Inference failure is not an error *here*: the fallback is what
            // handles a receiver whose type only the method call determines,
            // and reporting this failure would regress every such call.
            if let Ok((t, ty, lvl)) = self.elab_infer(cx, recv)
                && let Some(ind) = self.record_of_at(cx, &ty, span)
                && let Some(idx) = ind.field_index(name)
            {
                let (t, fty, flvl) = self.project_field(cx, &ind, &ty, Rc::new(t), idx, span)?;
                let _ = lvl;
                let skel = skel_of_ty(&ind.ctors[0].fields[idx].1);
                return Ok(DotResolution::Project(t, fty, flvl, skel));
            }
        }
        let Some(args) = args else {
            // A bare `p.f` is never a method call — a call needs parentheses —
            // so there is nothing to fall back to. Name the receiver's actual
            // type, since the usual mistake is a receiver that is not the
            // record the writer had in mind.
            let what = match self.elab_infer(cx, recv) {
                Ok((_, ty, _)) => match self.record_of_at(cx, &ty, span) {
                    Some(ind) => format!("`{}` has no field `{name}`", ind.name),
                    None => format!("this is not a record, so it has no field `{name}`"),
                },
                // A failed **resolution** in the receiver is a diagnosis of
                // its own — the search, as data — and is better than anything
                // this branch could say about a field. `G::AddCommMonoid.f` at
                // a carrier with no instance is the spelling that produces one
                // (docs/traits-type-projection-design.md §5).
                Err(e @ ElabError::Resolution { .. }) => return Err(e),
                // A slot receiver (`·.lines`) is a projection section: the
                // escape reaches the enclosing function-typed checking
                // position, which lowers it to `λ s => s.lines` and checks
                // the field against the binder's type
                // (issues/field-projection-sections.md).
                Err(e @ ElabError::ArgSlotEscape { .. }) => return Err(e),
                Err(_) => format!(
                    "no field `{name}` here (and the receiver's type \
                                   could not be inferred)"
                ),
            };
            return err(what, span);
        };
        // The method desugaring: the receiver fills the callee's `self`
        // parameter, which defaults to the first explicit one
        // (issues/method-receiver-position.md). Implicit endpoints are still
        // inferred from it — insertion is name-directed and indifferent to
        // explicit-argument order, which is why the old receiver-last rule
        // was never doing the work its comment claimed.
        // Which name the call is to: the bare one, or a member of the
        // receiver's own type (issues/type-owned-members-receiver-slice.md).
        // The `member_bases` test comes first for the same reason the record
        // one does — no receiver is inferred for a name nobody attaches.
        let head = self.member_head(cx, recv, name, !tyargs.is_empty(), span)?;
        let member_selected = head != name;
        let (head, vector_map) = if head == name && !self.shadowed(cx, name) {
            self.imported_receiver_head(cx, recv, name, span)?
        } else {
            (head, false)
        };
        // Receiver dispatch through an instance
        // (docs/traits-receiver-dispatch-design.md §3). Last, so nothing that
        // resolved before this round can be reinterpreted by it: a class
        // member is only reached when the receiver's own type has no such
        // field and its namespace has no such member.
        //
        // `other` is what a *successful* dispatch would be racing (§4 rule 2)
        // and what a *failed* one falls back to (rule 5). The builtin list is
        // there because `map`/`fold`/… are Rust rather than declarations, so
        // `shadowed` cannot see them.
        //
        // The first two kinds also carry the **callee** they desugar to: if it
        // resolves to a global, a dispatch whose field *is* that global is the
        // same reading rather than a rival
        // (issues/receiver-dispatch-coinciding-readings.md). A builtin never
        // carries one — it is Rust, not a declaration — and neither does a
        // call with written type arguments, which the class reading would
        // drop and the desugaring would apply.
        let callee = |c: &str| tyargs.is_empty().then(|| c.to_string());
        let other: Option<OtherReading> = if head != name {
            Some(OtherReading {
                desc: format!("`{head}`, selected using the receiver's type"),
                fix: format!("`{head}(…)`"),
                callee: callee(&head),
                ambient: None,
            })
        } else if self.shadowed(cx, name) || self.ctor_of(name).is_some() {
            Some(OtherReading {
                desc: format!("`{name}`, a name in scope on its own"),
                fix: format!("the bare call `{name}(…)` with the receiver as an argument"),
                callee: callee(name),
                // A constructor is the bare reading unless a local or alias
                // shadows it, and a constructor is never discarded.
                ambient: (cx.names.iter_inner().any(|n| n == name)
                    || cx.aliases.iter_inner().any(|a| a.name == *name)
                    || self.ctor_of(name).is_none())
                .then(|| name.to_string()),
            })
        } else if BUILTIN_METHODS.contains(&name) {
            Some(OtherReading {
                desc: format!("`{name}`, a built-in method"),
                fix: format!("the bare call `{name}(…)`"),
                callee: None,
                ambient: None,
            })
        } else {
            None
        };
        if let Some(d) = self.class_dispatch(cx, recv, name, other, args, span)? {
            return Ok(d);
        }
        if vector_map {
            application::refuse_named("vector map", "its arguments are positional", named)?;
            let [f] = args.as_slice() else {
                let mut supplied = vec![recv.clone()];
                supplied.extend(args.iter().cloned());
                return vec::method_arity_error(self, cx, &supplied, name, "`(f)`", span);
            };
            let (t, ty, lvl) = vec::elab_map(self, cx, f, recv, span)?;
            return Ok(DotResolution::Inferred(t, ty, lvl));
        }
        let name = &head;
        let mut args = args.clone();
        // The receiver is spliced into the positional list at its parameter's
        // index, which is how this desugaring has always worked. Named
        // arguments do not disturb that as long as every parameter *before*
        // the subject is still written positionally — and when one is not,
        // the receiver has no honest position to take, so it is refused here
        // rather than silently placed one slot early
        // (docs/named-arguments-design.md §5.4).
        let at = match cx.selfref.as_ref().filter(|self_ref| self_ref.matches(name)) {
            Some(self_ref) => self_ref.receiver_slot,
            None => {
                let params = self.params_of(name);
                // A member the receiver's type selected that marks no `self`:
                // remembered by the receiver's span, since a receiver meant
                // for a later parameter shows up only when the gate rejects
                // (`missing_self_message`). One push per such call; no probe.
                if member_selected && !params.iter().any(|p| p.is_self) {
                    self.attempt
                        .unmarked_receivers
                        .borrow_mut()
                        .push((recv.span, name.to_string()));
                }
                // Any member the receiver's type selected: the type picked
                // the namespace, not the instance, so a receiver at another
                // instance of it — `BitVec(16)` at a `BitVec(8)` member — is
                // also found only by the gate (`member_receiver_note`).
                if member_selected {
                    self.attempt
                        .member_receivers
                        .borrow_mut()
                        .push((recv.span, name.to_string()));
                }
                application::subject_index_in(&params)
            }
        };
        if !named.is_empty() && at > args.len() {
            return err(
                format!(
                    "`{name}`'s receiver is its parameter number {}, so a method call has to                      give the arguments before it positionally: `{}` names one of them and                      leaves the receiver nowhere to go. Write the plain call `{name}(…)`",
                    at + 1,
                    named[0].name
                ),
                named[0].name_span,
            );
        }
        self.refuse_unthreaded_mut_call(recv, name, span)?;
        let at = at.min(args.len());
        args.insert(at, recv.clone());
        let mut head = Expr {
            kind: ExprKind::Var(name.to_string()),
            span,
        };
        if !tyargs.is_empty() {
            head = Expr {
                kind: ExprKind::TyApp {
                    head: Box::new(head),
                    args: tyargs.to_vec(),
                },
                span,
            };
        }
        Ok(DotResolution::Method(Expr {
            kind: ExprKind::App {
                head: Box::new(head),
                args,
                named: named.to_vec(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        }))
    }

    /// A dot call `recv.m(a)` of a `mut self` method that no statement
    /// threads: anywhere but a marked call on a `let mut` local or `mut`
    /// parameter (docs/effects-capabilities-design.md §2.2), the call would
    /// give the `Mutated` record where its answer was meant, with the receiver
    /// unchanged, so it is refused here rather than where the record is
    /// used. The test reads the callee's written result head, so the hot
    /// dot-call path pays one surface lookup and no type is reduced.
    fn refuse_unthreaded_mut_call(&self, recv: &Expr, callee: &str, span: Span) -> R<()> {
        if self.scope.mut_call_site.get() == Some(span) {
            return Ok(());
        }
        let Some(abs) = self.lookup_global(callee).map(|g| g.abs) else { return Ok(()) };
        let Some((module, base)) = self.names.global_name_at(abs).and_then(|key| key.split_once("::")) else {
            return Ok(());
        };
        let Some(decl) = self.names.surface_decl_in(module, base) else { return Ok(()) };
        let mutated = matches!(&decl.result.kind,
            heather_syntax::TyKind::Named { name, .. } if name == heather_syntax::MUTATED_RECORD);
        if !mutated {
            return Ok(());
        }
        let method = callee.rsplit("::").next().unwrap_or(callee);
        let x = match &recv.kind {
            ExprKind::Var(x) => x.as_str(),
            _ => "x",
        };
        err(
            format!(
                "`{method}` is a `mut self` method, so it updates its receiver, and nothing here keeps the \
                 update: call it on a `let mut` local of this function's own blocks, as the statement \
                 `{x}.{method}(…);` or `let p = {x}.{method}(…);`, or call `{callee}(…)` by its qualified \
                 name for the `Mutated` record"
            ),
            span,
        )
    }

    /// The callee of a method call, given the receiver: `name` itself, or
    /// `D::name` when the receiver's type `D` has a member by that name
    /// (issues/type-owned-members-receiver-slice.md).
    ///
    /// Evidence **shrinks** the candidate set and never races candidates. If
    /// both readings exist — an ambient `name` *and* a `D::name` at this
    /// receiver — the answer is an ambiguity naming both, not a preference.
    /// Preferring the member would mean that adding `D::name` to a library
    /// silently reinterprets an existing `t.name(…)`, which is the one thing
    /// the growth invariant forbids (docs/modules-design.md §4).
    fn member_head(
        &self,
        cx: &Cx,
        recv: &Expr,
        name: &str,
        constructor_fallback: bool,
        span: Span,
    ) -> R<String> {
        if !self.names.has_member_base(name) {
            return Ok(name.to_string());
        }
        // A constructor identifies its nominal owner even when its result
        // parameters cannot yet be inferred. This matters for an explicitly
        // instantiated method call such as `Ok(x).fold<A, E, B>(...)`: `E`
        // is supplied by the method's type arguments, but choosing
        // `Result::fold` has to happen before those arguments are applied.
        let inferred = self
            .elab_infer(cx, recv)
            .ok()
            .and_then(|(_, rty, _)| self.receiver_owner(cx, &rty, span));
        let inferred = inferred.or_else(|| {
            constructor_fallback
                .then(|| self.constructor_receiver_owner(cx, recv))
                .flatten()
        });
        // A receiver whose type only the use site fixes — `BitVec::zero()`,
        // `R::mk()`, `Nil` — does not infer, yet its head already names its
        // owner. Asked only here, where the route above gave up, so nothing
        // that resolved before reaches it
        // (docs/receiver-member-resolution-design.md §1).
        let by_head = inferred.is_none();
        let Some((carrier, owner)) =
            inferred.or_else(|| self.receiver_owner_by_head(cx, recv, span))
        else {
            // A receiver at a type variable has no owner of its own, but a
            // class constraining the variable here is one
            // (issues/method-call-on-constrained-carrier.md).
            if let Some(qualified) = self.constrained_member(cx, recv, name, span)? {
                return Ok(qualified);
            }
            // `f.pos(…)` written for a function's member `f::pos`
            // (issues/function-owned-members.md): the receiver's type is a
            // function type, which owns no namespace, so the call falls back
            // to an ambient `pos`. Where there is none the fallback can only
            // fail, and saying which spelling reaches the member is strictly
            // better than "unbound" — a reading that resolved is never touched.
            if let ExprKind::Var(f) = &recv.kind
                && !cx.names.iter_inner().any(|n| n == f)
                && self.names_a_function(f)
                && matches!(self.resolve_name(name), NameRes::NotFound)
                && matches!(self.resolve_name(&format!("{f}::{name}")), NameRes::Found(_))
            {
                return err(
                    format!(
                        "`{f}.{name}` dispatches on the type of `{f}`, a function type, \
                         which owns no members — the member of the function `{f}` is \
                         `{f}::{name}(…)`"
                    ),
                    span,
                );
            }
            // Inference failure is not an error here, exactly as for a field:
            // the fallback is what handles a receiver whose type only the
            // call fixes.
            return Ok(name.to_string());
        };
        let qualified = format!("{owner}::{name}");
        match self.resolve_name(&qualified) {
            NameRes::Found(_) => {}
            // Two modules attaching the same member to the same type: the §4
            // regime's ambiguity, reported here rather than fallen back out
            // of — a receiver that *did* find candidates and cannot choose is
            // not a receiver that found none.
            NameRes::Ambiguous(_) => return Err(self.name_miss(&qualified, String::new(), span)),
            // A restricted name falls back exactly as a missing one does: the
            // receiver's namespace is not where a generated member is
            // reached, and the field route above already ran
            // (docs/repr-access-spellings-design.md §3.2).
            NameRes::NotFound | NameRes::NoSuchQualifier(_) | NameRes::Restricted(_) => {
                return Ok(name.to_string());
            }
        }
        if self.ambient_reading_survives(cx, name, &carrier, span) {
            // A receiver owned by its head reached this point only because
            // inference gave up, and before this route the call went to the
            // ambient reading from there. It still does: §0 keeps every
            // program that resolved resolving the same way, and the
            // desugared ambient call reports its own failure if it has one.
            if by_head {
                return Ok(name.to_string());
            }
            return err(
                format!(
                    "`{name}` here is both `{qualified}`, reached through the receiver's \
                     type, and a name in scope on its own — write one of them: \
                     `{qualified}(…)` for the member, or the bare call `{name}(…)` with \
                     the receiver as an argument"
                ),
                span,
            );
        }
        Ok(qualified)
    }

    /// The callee of `recv.name(…)` when the receiver's type is a type
    /// variable (or any type with no nominal carrier) that a class
    /// dictionary in scope constrains: `K::name` for the binder's class `K`
    /// or one of its parents at the same carrier, as Rust finds a trait's
    /// methods on a generic and Haskell a class's
    /// (issues/method-call-on-constrained-carrier.md).
    ///
    /// The candidates are read off `cx.dicts` — instance arguments
    /// `d: K<C> := infer` and section constraints, as written — and never off
    /// the instance registry: a variable has no instances, only constraints.
    /// So the route costs nothing in a declaration with no class binder,
    /// and a concrete receiver never reaches it (its owner answered first).
    ///
    /// Two constraining classes owning the member are an ambiguity naming
    /// both, and so is a member beside an ambient `name`: evidence shrinks
    /// the candidate set and never races candidates, as for a nominal owner.
    /// `None` leaves the call to the ambient reading, as before this route.
    fn constrained_member(&self, cx: &Cx, recv: &Expr, name: &str, span: Span) -> R<Option<String>> {
        if cx.dicts.is_empty() {
            return Ok(None);
        }
        let Ok((_, rty, rlvl)) = self.elab_infer(cx, recv) else {
            return Ok(None);
        };
        // The declaration under construction is reached by its written name:
        // a recursive `c.say(…)` inside `fn Log::say` is not yet a global.
        let selfref = cx.selfref.as_ref().map(|s| s.written_name.as_str());
        let mut found: Vec<(String, String)> = Vec::new();
        for d in cx.dicts.iter_inner() {
            let Some(dkey) = self.key_of(&d.class) else { continue };
            let Some(info) = self.traits.class(&dkey).cloned() else { continue };
            let Ok((dc, dlvl)) = self.elab_ty(cx, &d.carrier) else { continue };
            if dlvl != rlvl || !self.conv_types(cx, &dc, &rty, &rlvl) {
                continue;
            }
            // A parent is an owner only at the class's own carrier: a
            // multi-parameter class may extend a parent at another argument.
            let at_carrier = |args: &[Ty]| {
                matches!(args.first().map(|t| &t.kind),
                    Some(heather_syntax::TyKind::Named { name, args }) if args.is_empty()
                        && info.params.first() == Some(name))
            };
            let owners = std::iter::once(d.class.clone()).chain(
                info.ancestors
                    .iter()
                    .filter(|a| at_carrier(&a.args))
                    .map(|a| a.name.clone()),
            );
            for owner in owners {
                let qualified = format!("{owner}::{name}");
                let key = if selfref == Some(qualified.as_str()) {
                    qualified.clone()
                } else {
                    match self.resolve_name(&qualified) {
                        NameRes::Found(_) => {}
                        NameRes::Ambiguous(_) => return Err(self.name_miss(&qualified, String::new(), span)),
                        _ => continue,
                    }
                    let Some(key) = self.key_of(&qualified) else { continue };
                    key
                };
                if !found.iter().any(|(k, _)| *k == key) {
                    found.push((key, qualified));
                }
            }
        }
        match found.as_slice() {
            [] => Ok(None),
            [(_, qualified)] => {
                let ambient = cx.names.iter_inner().any(|n| n == name)
                    || cx.aliases.iter_inner().any(|a| a.name == *name)
                    || cx.selfref.as_ref().is_some_and(|s| s.matches(name) && s.written_name != *qualified)
                    || self.lookup_global(name).is_some();
                if ambient {
                    return err(
                        format!(
                            "`{name}` here is both `{qualified}`, reached through a class constraining \
                             the receiver's type, and a name in scope on its own — write one of them: \
                             `{qualified}(…)` for the member, or the bare call `{name}(…)` with the \
                             receiver as an argument"
                        ),
                        span,
                    );
                }
                Ok(Some(qualified.clone()))
            }
            many => {
                // Named in sorted order, never scope order.
                let mut many = many.to_vec();
                many.sort();
                let list = many.iter().map(|(_, q)| format!("`{q}`")).collect::<Vec<_>>().join(" and ");
                err(
                    format!(
                        "`{name}` at this receiver is {list}, each reached through a class \
                         constraining the receiver's type — write the one you meant by its \
                         qualified name"
                    ),
                    span,
                )
            }
        }
    }

    /// Does the bare `name` have a reading that could take a receiver of
    /// this carrier? Such a reading races `D::name`, and the answer is an
    /// ambiguity rather than a preference.
    ///
    /// A reading is **discarded** only when it provably cannot take the
    /// receiver (docs/receiver-member-resolution-design.md §2): a local or
    /// alias that is not a function at all, or a reading whose subject has a
    /// known outer carrier disjoint from the receiver's. That is the filter
    /// imported receiver dispatch already applies below, extended to every
    /// ambient kind. An unknown carrier on either side, a generic subject, or
    /// equal carriers keep the ambiguity — so adding `D::name` only ever
    /// reaches a receiver no ambient reading could have typechecked at.
    ///
    /// A local or alias is the whole bare reading when there is one: it
    /// shadows every declaration. Otherwise the declaration under
    /// construction (in scope under its base name so that it can recurse)
    /// and a committed global each count.
    fn ambient_reading_survives(
        &self,
        cx: &Cx,
        name: &str,
        carrier: &ReceiverCarrier,
        span: Span,
    ) -> bool {
        if let Some(takes) = self.local_reading_takes(cx, name, carrier, span) {
            return takes;
        }
        let selfref = cx.selfref.as_ref().is_some_and(|s| s.matches(name))
            && !self.selfref_subject_excludes(cx, name, carrier, span);
        let global = self.lookup_global(name).is_some()
            && !self.global_subject_excludes(name, carrier, span);
        selfref || global
    }

    /// [`Self::ambient_reading_survives`] for the class-dispatch race, where
    /// the receiver has already been inferred: is the bare reading one that
    /// cannot take a receiver of type `rty`? An unknown carrier answers no.
    pub(crate) fn ambient_cannot_take(&self, cx: &Cx, name: &str, rty: &Type, span: Span) -> bool {
        self.receiver_carrier(cx, rty, span)
            .is_some_and(|carrier| !self.ambient_reading_survives(cx, name, &carrier, span))
    }

    /// Whether the local or `let` alias `name` resolves to could take the
    /// receiver; `None` when no local or alias is in scope. The precedence
    /// is `resolve`'s: an alias bound at depth `d` shadows every binder at a
    /// position below `d`. Its subject is its first explicit parameter — a
    /// local has no `self` marker to consult.
    fn local_reading_takes(
        &self,
        cx: &Cx,
        name: &str,
        carrier: &ReceiverCarrier,
        span: Span,
    ) -> Option<bool> {
        let local_pos = cx.names.lookup(name);
        let alias = cx.aliases.iter_inner().find(|a| a.name == *name);
        let (mut ty, skel) = match (local_pos, alias) {
            (Some(pos), Some(a)) if a.depth <= pos => (self.local(cx, pos).1, cx.names.skel(pos).cloned()),
            (_, Some(a)) => (a.ty.shift_local((cx.names.len() - a.depth) as u32), a.skel.clone()),
            (Some(pos), None) => (self.local(cx, pos).1, cx.names.skel(pos).cloned()),
            (None, None) => return None,
        };
        let Some(subject) = skel.as_ref().map_or(Some(0), |s| {
            s.params.iter().position(|b| !b.implicit && !b.is_type)
        }) else {
            return Some(true);
        };
        let mut cx = cx.clone();
        for i in 0..=subject {
            match self.whnf(&cx, &ty, span) {
                Ok(Type::Pi { dom, dom_level, cod, .. }) => {
                    if i == subject {
                        return Some(!self.subject_excludes(&cx, &dom, carrier, span));
                    }
                    cx.push(format!("#{i}"), (*dom).clone(), dom_level);
                    ty = (*cod).clone();
                }
                // Not a Π at all, so not callable: `let len = xs.len()`
                // cannot be applied to anything. A level-polymorphic value,
                // a failed reduction, or a skeleton promising more binders
                // than the type has keeps the ambiguity.
                Ok(Type::UPi { .. }) | Err(_) => return Some(true),
                Ok(_) => return Some(i != 0),
            }
        }
        Some(true)
    }

    /// A constructor application's declaration, without elaborating its
    /// fields or solving its result parameters.
    fn constructor_receiver_owner(
        &self,
        cx: &Cx,
        recv: &Expr,
    ) -> Option<(ReceiverCarrier, String)> {
        let head = match &recv.kind {
            ExprKind::App { head, .. } => &head.kind,
            kind => kind,
        };
        let head = match head {
            ExprKind::TyApp { head, .. } => &head.kind,
            kind => kind,
        };
        let ExprKind::Var(name) = head else {
            return None;
        };
        let (ind, _) = self.ctor_here(cx, name)?;
        let key = crate::names::qkey(&ind.scope.module, &ind.name);
        Some((ReceiverCarrier::Named(key), ind.name.clone()))
    }

    /// Does the in-progress declaration's method subject provably reject a
    /// receiver of `carrier`? Its parameters are the outermost entries of
    /// `cx`; each stored type is scoped over the prefix before its binder,
    /// so inspect it in that prefix rather than in the (possibly much
    /// deeper) use-site context.
    fn selfref_subject_excludes(&self, cx: &Cx, name: &str, carrier: &ReceiverCarrier, span: Span) -> bool {
        let Some(self_ref) = cx.selfref.as_ref().filter(|s| s.matches(name)) else {
            return false;
        };
        let Some((subject, _)) = self_ref
            .params
            .iter()
            .enumerate()
            .skip(self_ref.n_tyvars)
            .filter(|(_, (_, implicit))| !implicit)
            .nth(self_ref.receiver_slot)
        else {
            return false;
        };
        let Some(entry) = cx.gamma.entries.get(subject) else {
            return false;
        };
        let ty = Rc::clone(&entry.ty);
        self.subject_excludes(&cx.prefix(subject), &ty, carrier, span)
    }

    fn receiver_carrier(&self, cx: &Cx, ty: &Type, span: Span) -> Option<ReceiverCarrier> {
        // Preserve Vec before normalization expands a concrete length into Σ.
        if matches!(&*crate::inductive::decoded(ty), Type::Vec { .. }) {
            return Some(ReceiverCarrier::Vector);
        }
        self.carrier_of_ty(cx, ty, span).map(|c| ReceiverCarrier::Named(c.key))
    }

    /// Can a value of `ty` provably never have the outer carrier `carrier`?
    /// [`Self::receiver_carrier`] answers for a type that reduces to a
    /// carrier. This also answers for a type family stuck on a neutral, the
    /// type of a proof parameter such as `h: x <= y` at `Rat`
    /// (issues/self-name-shadows-dot-call.md): it reads every type the
    /// family can reduce to, and answers yes only when each one has a known
    /// carrier other than `carrier`, or is a former no carrier converts to
    /// (a Π, a universe, an equation, `True`'s `Unit`). Anything it cannot
    /// read — a type variable, an opaque family, a stuck eliminator it does
    /// not walk, a spent budget — answers no, which keeps the ambiguity.
    fn subject_excludes(&self, cx: &Cx, ty: &Type, carrier: &ReceiverCarrier, span: Span) -> bool {
        let mut reach = Reach { seen: Vec::new(), recursive: Vec::new(), fuel: Reach::FUEL };
        self.reach_excludes(cx, ty, carrier, &mut reach, span)
    }

    fn reach_excludes(
        &self,
        cx: &Cx,
        ty: &Type,
        carrier: &ReceiverCarrier,
        reach: &mut Reach,
        span: Span,
    ) -> bool {
        if reach.fuel == 0 {
            return false;
        }
        reach.fuel -= 1;
        if let Some(c) = self.receiver_carrier(cx, ty, span) {
            return c != *carrier;
        }
        if let Type::El { level, tm } = ty
            && let Some(excludes) = self.family_excludes(level, tm, carrier, reach, span)
        {
            return excludes;
        }
        self.reduct_excludes(cx, ty, carrier, reach, span)
    }

    /// A definition applied to arguments, `El(F a₁ … aₖ)`: read `F` applied to
    /// its own parameters, so that every type it can reduce to, at these
    /// arguments or any others, is covered. A definition read once needs no
    /// second read (`Q::Le` reaching `Nat::Le` twice): any reduct that could
    /// take the receiver has already ended the walk. `None` when the head is
    /// not a closed definition.
    fn family_excludes(
        &self,
        level: &Level,
        tm: &Term,
        carrier: &ReceiverCarrier,
        reach: &mut Reach,
        span: Span,
    ) -> Option<bool> {
        let (head, args) = crate::spelling::app_spine(tm);
        let Term::GlobalTm { var, subst } = head else {
            return None;
        };
        if !subst.terms.is_empty() || !matches!(subst.tail, SubstTail::Empty) {
            return None;
        }
        let abs = self.global_abs_of(*var)?;
        let GlobalBinding::Tm { ctx, ty, body: Some(_), .. } = self.psi.bindings.get(abs)? else {
            return None;
        };
        if !matches!(ctx.base, CtxBase::Nil) || ctx.len() != 0 {
            return None;
        }
        if reach.seen.contains(&abs) {
            return Some(true);
        }
        reach.seen.push(abs);
        let growth = self.psi.bindings.len() as u32 - abs as u32
            + self.global_padding() + self.scope.meta_pushed.borrow().len() as u32;
        let mut ty = ty.shift_global(growth);
        let mut cx = Cx::empty();
        for i in 0..args.len() {
            let Ok(Type::Pi { dom, dom_level, cod, .. }) = self.whnf(&cx, &ty, span) else {
                return Some(false);
            };
            cx.push(format!("#{i}"), (*dom).clone(), dom_level);
            ty = (*cod).clone();
        }
        let k = args.len() as u32;
        // The generic application is read in a context of its own, where the
        // recursive results bound around this occurrence do not exist.
        let recursive = std::mem::take(&mut reach.recursive);
        let mut tm = Term::GlobalTm {
            var: *var,
            subst: LocalSubst {
                tail: SubstTail::Empty,
                terms: Vec::new(),
            },
        };
        for i in 0..k {
            tm = Term::AppAt { fun: Rc::new(tm), arg: Rc::new(Term::Var(LocalVar(k - 1 - i))) };
        }
        let generic = Type::El { level: level.clone(), tm: Rc::new(tm) };
        let excludes = self.reduct_excludes(&cx, &generic, carrier, reach, span);
        reach.recursive = recursive;
        Some(excludes)
    }

    /// What `ty` reduces to: a former no carrier converts to, or a code stuck
    /// on a neutral ([`Self::stuck_code_excludes`]).
    fn reduct_excludes(
        &self,
        cx: &Cx,
        ty: &Type,
        carrier: &ReceiverCarrier,
        reach: &mut Reach,
        span: Span,
    ) -> bool {
        match self.whnf(cx, ty, span) {
            Ok(
                Type::Pi { .. }
                | Type::UPi { .. }
                | Type::Ty(_)
                | Type::Id { .. }
                | Type::SEq { .. }
                | Type::SEmpty { .. }
                | Type::Squash { .. }
                | Type::Unit { .. }
                | Type::Empty { .. },
            ) => true,
            Ok(Type::El { level, tm }) => self.stuck_code_excludes(cx, &level, &tm, carrier, reach, span),
            _ => false,
        }
    }

    /// A code stuck on a neutral scrutinee, applied to arguments: read every
    /// branch, each a λ over those arguments read under its own binders, so
    /// that every argument is covered at once. Inside `elim_Nat`'s step the
    /// recursive result is a value of this same eliminator at a smaller
    /// scrutinee (`k.Le(l)` inside `Nat::Le`), so a reduct headed by it adds
    /// nothing the branches do not: the eliminator is well founded. A branch
    /// that does not take every argument as a λ is read at no arguments in
    /// particular, so it declines, as does any other eliminator.
    fn stuck_code_excludes(
        &self,
        cx: &Cx,
        level: &Level,
        tm: &Term,
        carrier: &ReceiverCarrier,
        reach: &mut Reach,
        span: Span,
    ) -> bool {
        let depth = cx.names.len();
        let (head, args) = crate::spelling::app_spine(tm);
        // (binders the branch sits under, whether the last is a recursive
        // result, the branch)
        let branches: Vec<(Vec<(Type, Level)>, bool, &Rc<Term>)> = match head {
            Term::Var(LocalVar(v)) => {
                return depth.checked_sub(*v as usize + 1).is_some_and(|at| reach.recursive.contains(&at));
            }
            Term::Case { lhs_level, rhs_level, lhs, rhs, case_l, case_r, .. } => vec![
                (vec![((**lhs).clone(), lhs_level.clone())], false, case_l),
                (vec![((**rhs).clone(), rhs_level.clone())], false, case_r),
            ],
            Term::ElimNat { level: motive_level, motive, base, step, .. } => vec![
                (Vec::new(), false, base),
                (
                    vec![(Type::Nat, Level::Zero), ((**motive).clone(), motive_level.clone())],
                    true,
                    step,
                ),
            ],
            _ => return false,
        };
        let marked = reach.recursive.len();
        let excludes = branches.into_iter().all(|(binders, recursive, branch)| {
            let mut cx = cx.clone();
            for (ty, lvl) in binders {
                cx.push("#branch".to_string(), ty, lvl);
            }
            if recursive {
                reach.recursive.push(cx.names.len() - 1);
            }
            let mut branch = Rc::clone(branch);
            let mut taken = 0;
            while taken < args.len() {
                let Term::Lam { dom, dom_level, body, .. } = &*branch else {
                    break;
                };
                cx.push("#arg".to_string(), (**dom).clone(), dom_level.clone());
                branch = Rc::clone(body);
                taken += 1;
            }
            if taken < args.len() {
                reach.recursive.truncate(marked);
                return false;
            }
            let branch = Type::El { level: level.clone(), tm: branch };
            let excludes = self.reach_excludes(&cx, &branch, carrier, reach, span);
            reach.recursive.truncate(marked);
            excludes
        });
        excludes
    }

    /// A desugared method call failed: say what the author can act on, when
    /// that is narrower than the failure itself. Only ever on the error path,
    /// so a call that elaborates pays nothing for it.
    pub(crate) fn method_call_failure(
        &self,
        cx: &Cx,
        recv: &Expr,
        call: &Expr,
        e: ElabError,
    ) -> ElabError {
        match self.missing_self_marker(cx, recv, call) {
            Some(msg) => {
                let span = match &e {
                    ElabError::Elab { span, .. } => *span,
                    _ => call.span,
                };
                ElabError::Elab { msg, span }
            }
            None => self.receiver_implicit_hint(recv, e),
        }
    }

    /// The failure path of a dot call to a member with no `self` marker:
    /// [`Self::missing_self_message`] at the receiver's carrier.
    fn missing_self_marker(&self, cx: &Cx, recv: &Expr, call: &Expr) -> Option<String> {
        let ExprKind::App { head, .. } = &call.kind else {
            return None;
        };
        let head = match &head.kind {
            ExprKind::TyApp { head, .. } => &head.kind,
            kind => kind,
        };
        let ExprKind::Var(member) = head else {
            return None;
        };
        // A member the receiver's type selected — recorded by `resolve_dot`
        // — and not the bare name or an imported candidate.
        if !self
            .attempt
            .unmarked_receivers
            .borrow()
            .iter()
            .any(|(at, m)| *at == recv.span && m == member)
        {
            return None;
        }
        let carrier = match self.elab_infer(cx, recv) {
            Ok((_, rty, _)) => self.receiver_carrier(cx, &rty, call.span),
            Err(_) => self.receiver_owner_by_head(cx, recv, call.span).map(|(c, _)| c),
        }?;
        self.missing_self_message(member, &carrier, call.span)
    }

    /// The gate's half of the same diagnostic: a recorded checking mismatch
    /// at the span of a receiver placed into an unmarked member. The receiver
    /// is what the note inferred, so its carrier comes for free.
    pub(crate) fn unmarked_receiver_note(&self, cx: &Cx, span: Span, got: &Type) -> Option<String> {
        let member = self
            .attempt
            .unmarked_receivers
            .borrow()
            .iter()
            .find(|(at, _)| *at == span)
            .map(|(_, m)| m.clone())?;
        let carrier = self.receiver_carrier(cx, got, span)?;
        self.missing_self_message(&member, &carrier, span)
    }

    /// The gate's note for a receiver its type selected a member for, at an
    /// instance the member does not take
    /// (issues/width-specific-method-on-other-width.md). Selection reads only
    /// the receiver's carrier — `BitVec`, whatever its width — so a member
    /// declared at one instance is reached from every other, and the
    /// mismatch is the kernel's to find; this names the member and both
    /// instances. Only when the two spell completely and differently: a pair
    /// that displays alike is left to the generic note, which says so.
    pub(crate) fn member_receiver_note(
        &self,
        cx: &Cx,
        span: Span,
        got: &Type,
        expected: &Type,
    ) -> Option<String> {
        let member = self
            .attempt
            .member_receivers
            .borrow()
            .iter()
            .find(|(at, _)| *at == span)
            .map(|(_, m)| m.clone())?;
        let got_s = self.display_type_clean(cx, got)?;
        let want_s = self.display_type_clean(cx, expected)?;
        (got_s != want_s).then(|| {
            format!(
                "`{member}` takes a receiver of type `{want_s}`, but this receiver has type \
                 `{got_s}`"
            )
        })
    }

    /// A type-owned member reached through a receiver, whose declaration
    /// forgot `self` on the parameter the receiver was meant for
    /// (issues/type-member-missing-self-diagnostic.md). Unmarked means the
    /// first explicit parameter is the subject, deliberately, so this claims
    /// the mistake only when the carriers say so: the first explicit
    /// parameter's carrier is known and differs from the receiver's, and
    /// exactly one later explicit parameter's is the receiver's. Anything
    /// less leaves the original error standing.
    fn missing_self_message(
        &self,
        member: &str,
        carrier: &ReceiverCarrier,
        span: Span,
    ) -> Option<String> {
        let params = self.params_of(member);
        if params.iter().any(|p| p.is_self) {
            return None;
        }
        let explicit: Vec<usize> = params
            .iter()
            .enumerate()
            .filter(|(_, p)| !p.implicit && !p.is_type)
            .map(|(i, _)| i)
            .collect();
        let (&first, later) = explicit.split_first()?;
        // Each explicit domain's carrier and spelling, read under the
        // binders before it. A signature is short and this is the error
        // path, so one telescope walk per parameter is fine.
        let domain = |i: usize| {
            self.read_signature(
                member,
                span,
                |_| Some(i),
                |scx, dom| {
                    Some((
                        self.receiver_carrier(scx, dom, span),
                        self.display_type_clean(scx, dom),
                    ))
                },
            )
        };
        let (first_carrier, _) = domain(first)?;
        if !first_carrier.is_some_and(|c| c != *carrier) {
            return None;
        }
        let mut matching = Vec::new();
        for &i in later {
            let (c, spelled) = domain(i)?;
            if c.as_ref() == Some(carrier) {
                matching.push((i, spelled));
            }
        }
        let [(at, spelled)] = matching.as_slice() else {
            return None;
        };
        let intended = &params[*at].name;
        let written = spelled.clone().unwrap_or_else(|| "…".to_string());
        Some(format!(
            "`{member}` treats its first explicit parameter `{}` as the receiver, because the \
             declaration marks no parameter `self`, but this receiver has the type `{intended}` \
             expects — did you mean to declare it `self {intended}: {written}`?",
            params[first].name
        ))
    }

    /// The named-argument spelling, added to an unsolved implicit of the
    /// *receiver's* callee: `R::mk().get()` in a position that pins nothing
    /// has no other fix, and `@` is the last rung of the ladder, not the
    /// first (docs/receiver-member-resolution-design.md §0, §1). Runs on the
    /// failure path of a method call only; every other error passes through.
    pub(crate) fn receiver_implicit_hint(&self, recv: &Expr, e: ElabError) -> ElabError {
        let ElabError::Elab { msg, span } = e else {
            return e;
        };
        let (head, has_args) = match &recv.kind {
            ExprKind::App { head, args, explicit: false, .. } => (&head.kind, !args.is_empty()),
            kind => (kind, false),
        };
        let head = match head {
            ExprKind::TyApp { head, .. } => &head.kind,
            kind => kind,
        };
        let param = match head {
            ExprKind::Var(g) => msg
                .strip_prefix("could not infer the implicit argument `")
                .and_then(|rest| rest.split_once('`'))
                .filter(|(_, rest)| rest.starts_with(&format!(" of `{g}`")))
                .map(|(p, _)| (g, p.to_string())),
            _ => None,
        };
        let Some((g, p)) = param else {
            return ElabError::Elab { msg, span };
        };
        let args = if has_args { "…, " } else { "" };
        ElabError::Elab {
            msg: format!(
                "{msg} — nothing here fixes the receiver's `{p}`; name it: `{g}({args}{p} := …)`"
            ),
            span,
        }
    }

    /// A type's carrier together with the namespace its members live in —
    /// the pair `member_head` selects `D::name` by.
    fn receiver_owner(&self, cx: &Cx, ty: &Type, span: Span) -> Option<(ReceiverCarrier, String)> {
        Some((self.receiver_carrier(cx, ty, span)?, self.type_namespace(cx, ty, span)?))
    }

    /// The owner of a receiver that does not infer on its own, read off its
    /// **head** without elaborating it
    /// (docs/receiver-member-resolution-design.md §1): a constructor names its
    /// inductive, a saturated call to a global names its declared result's
    /// carrier, and a method call names the result carrier of the member it
    /// resolves to. The owner only chooses the qualified name; whether the
    /// call typechecks is still the desugared application's to decide, with
    /// the expected type in hand. Anything else declines.
    fn receiver_owner_by_head(
        &self,
        cx: &Cx,
        recv: &Expr,
        span: Span,
    ) -> Option<(ReceiverCarrier, String)> {
        if let ExprKind::Dot { recv: inner, name, tyargs, args: Some(args), named } = &recv.kind {
            // Only a *member* reading: a bare `name` may still be a class
            // dispatch or an imported candidate, whose result this cannot
            // read without running those routes.
            let head = self.member_head(cx, inner, name, !tyargs.is_empty(), span).ok()?;
            if head == *name {
                return None;
            }
            return self.global_result_owner(&head, args.len() + 1, named, span);
        }
        if let Some(owner) = self.constructor_receiver_owner(cx, recv) {
            return Some(owner);
        }
        let (head, positional, named) = match &recv.kind {
            // `@g(…)` spells its implicits, so its arity is not the one below;
            // it also infers whenever it can be read at all.
            ExprKind::App { explicit: true, .. } => return None,
            ExprKind::App { head, args, named, .. } => (&head.kind, args.len(), named.as_slice()),
            kind => (kind, 0, &[][..]),
        };
        let head = match head {
            ExprKind::TyApp { head, .. } => &head.kind,
            kind => kind,
        };
        let ExprKind::Var(g) = head else {
            return None;
        };
        // The global must be what the name means here: a local, a `let`
        // alias or the declaration under construction shadows it, and its
        // type is not a committed signature.
        if cx.names.iter_inner().any(|n| n == g)
            || cx.aliases.iter_inner().any(|a| a.name == *g)
            || cx.selfref.as_ref().is_some_and(|s| s.matches(g))
        {
            return None;
        }
        self.global_result_owner(g, positional, named, span)
    }

    /// The owner of a saturated call's result: the carrier of the global's
    /// declared result type under its own telescope. A call that does not
    /// supply exactly the explicit parameters declines — an over-application
    /// applies the result further and a partial one is a function — and so
    /// does a result whose head depends on the arguments.
    fn global_result_owner(
        &self,
        name: &str,
        positional: usize,
        named: &[NamedArg],
        span: Span,
    ) -> Option<(ReceiverCarrier, String)> {
        self.read_signature(
            name,
            span,
            |params| {
                let explicit: Vec<&str> = params
                    .iter()
                    .filter(|p| !p.implicit && !p.is_type)
                    .map(|p| p.name.as_str())
                    .collect();
                let named_explicit =
                    named.iter().filter(|a| explicit.contains(&a.name.as_str())).count();
                (positional + named_explicit == explicit.len()).then_some(params.len())
            },
            |cx, result| self.receiver_owner(cx, result, span),
        )
    }

    /// Read the subject's outer carrier from a committed signature, under
    /// its own parameter telescope. No callback elaboration, speculative
    /// application, or scratch metavariable solutions escape this query.
    /// Any global, not only an imported candidate: the ambient reading a
    /// member races is filtered by the same read (§2 of
    /// docs/receiver-member-resolution-design.md).
    fn global_subject_carrier(&self, name: &str, span: Span) -> Option<ReceiverCarrier> {
        self.read_signature(
            name,
            span,
            |params| {
                params.iter().position(|p| p.is_self)
                    .or_else(|| params.iter().position(|p| !p.implicit && !p.is_type))
            },
            |cx, dom| self.receiver_carrier(cx, dom, span),
        )
    }

    /// [`Self::global_subject_carrier`]'s subject, asked whether it provably
    /// rejects a receiver of `carrier` ([`Self::subject_excludes`]).
    fn global_subject_excludes(&self, name: &str, carrier: &ReceiverCarrier, span: Span) -> bool {
        self.read_signature(
            name,
            span,
            |params| {
                params.iter().position(|p| p.is_self)
                    .or_else(|| params.iter().position(|p| !p.implicit && !p.is_type))
            },
            |cx, dom| Some(self.subject_excludes(cx, dom, carrier, span)),
        )
        .unwrap_or(false)
    }

    /// Walk a committed global's parameter telescope and `read` one type
    /// under it: parameter `at`'s domain, or the declared result when `at` is
    /// the parameter count. A signature under a section context, or one that
    /// stops being a Π early, answers `None`.
    fn read_signature<T>(
        &self,
        name: &str,
        span: Span,
        at: impl FnOnce(&[crate::application::ParamMeta]) -> Option<usize>,
        read: impl FnOnce(&Cx, &Type) -> Option<T>,
    ) -> Option<T> {
        let info = self.lookup_global(name)?;
        let GlobalBinding::Tm { ctx, ty, .. } = &self.psi.bindings[info.abs as usize] else {
            return None;
        };
        if !matches!(ctx.base, CtxBase::Nil) || ctx.len() != 0 { return None; }
        let growth = self.psi.bindings.len() as u32 - info.abs
            + self.global_padding() + self.scope.meta_pushed.borrow().len() as u32;
        let mut ty = ty.shift_global(growth);
        let mut cx = Cx::empty();
        let at = at(&info.params)?;
        for (i, p) in info.params.iter().enumerate() {
            let Type::Pi { dom, dom_level, cod, .. } = self.whnf(&cx, &ty, span).ok()? else {
                return None;
            };
            if i == at { return read(&cx, &dom); }
            cx.push(p.name.clone(), (*dom).clone(), dom_level);
            ty = (*cod).clone();
        }
        if at == info.params.len() { read(&cx, &ty) } else { None }
    }

    /// Only an ambiguous unqualified import set enters this route. Local
    /// bindings, selected imports, unique ambient names, record fields and
    /// nominal members keep their existing resolution rules.
    fn imported_receiver_head(&self, cx: &Cx, recv: &Expr, name: &str, span: Span)
        -> R<(String, bool)>
    {
        let NameRes::Ambiguous(origins) = self.resolve_name(name) else {
            return Ok((name.to_string(), false));
        };
        let (_, ty, _) = self.elab_infer(cx, recv)?;
        let Some(carrier) = self.receiver_carrier(cx, &ty, span) else {
            return Err(self.name_miss(name, String::new(), span));
        };
        let mut compatible = Vec::new();
        let mut unknown = false;
        for origin in &origins {
            let candidate = format!("{origin}::{name}");
            match self.global_subject_carrier(&candidate, span) {
                Some(c) if c == carrier => compatible.push(candidate),
                Some(_) => {}
                None => unknown = true,
            }
        }
        if !unknown {
            if let [candidate] = compatible.as_slice() {
                return Ok((candidate.clone(), false));
            }
            if compatible.is_empty() && name == "map" && carrier == ReceiverCarrier::Vector {
                return Ok((name.to_string(), true));
            }
        }
        // Never use declaration/import order, callback success, or a failed
        // carrier query as evidence for selecting a different operation.
        Err(self.name_miss(name, String::new(), span))
    }

}
