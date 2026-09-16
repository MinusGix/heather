//! Dot routing and precedence between surface member readings.
//!
//! This module owns record projection, nominal type-owned member selection,
//! method desugaring, and the ordering in which class-backed routes are asked.

use std::sync::Arc as Rc;

use heather_syntax::{Expr, ExprKind, NamedArg, Span};
use heather_kernel::term::{CtxBase, GlobalBinding, Type};

use crate::{
    BUILTIN_METHODS, Cx, DotResolution, ElabError, Elaborator, NameRes, R, err, skel_of_ty,
    application, vec,
};

/// Only disjoint outer carriers are used to discard imported candidates.
/// Type arguments and callbacks never break a tie; an unknown carrier keeps
/// the ambiguity, including a generic `self x: A`.
#[derive(PartialEq, Eq)]
enum ReceiverCarrier {
    Named(String),
    Vector,
}

impl Elaborator {
    // -- field access (docs/surface-records.md §4) ---------------------------

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
        let head = self.member_head(cx, recv, name, span)?;
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
        let other: Option<(String, String)> = if head != name {
            Some((
                format!("`{head}`, selected using the receiver's type"),
                format!("`{head}(…)`"),
            ))
        } else if self.shadowed(cx, name) || self.ctor_of(name).is_some() {
            Some((
                format!("`{name}`, a name in scope on its own"),
                format!("the bare call `{name}(…)` with the receiver as an argument"),
            ))
        } else if BUILTIN_METHODS.contains(&name) {
            Some((
                format!("`{name}`, a built-in method"),
                format!("the bare call `{name}(…)`"),
            ))
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
        let at = self.subject_index(name);
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
        let at = at.min(args.len());
        args.insert(at, recv.clone());
        let head = Expr {
            kind: ExprKind::Var(name.to_string()),
            span,
        };
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
    fn member_head(&self, cx: &Cx, recv: &Expr, name: &str, span: Span) -> R<String> {
        if !self.names.has_member_base(name) {
            return Ok(name.to_string());
        }
        // Inference failure is not an error here, exactly as for a field: the
        // fallback is what handles a receiver whose type only the call fixes.
        let Ok((_, rty, _)) = self.elab_infer(cx, recv) else {
            return Ok(name.to_string());
        };
        let Some(owner) = self.type_namespace(cx, &rty, span) else {
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
        if self.shadowed(cx, name) {
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

    fn receiver_carrier(&self, cx: &Cx, ty: &Type, span: Span) -> Option<ReceiverCarrier> {
        // Preserve Vec before normalization expands a concrete length into Σ.
        if matches!(&*crate::inductive::decoded(ty), Type::Vec { .. }) {
            return Some(ReceiverCarrier::Vector);
        }
        self.carrier_of_ty(cx, ty, span).map(|c| ReceiverCarrier::Named(c.key))
    }

    /// Read the subject's outer carrier from a committed signature, under
    /// its own parameter telescope. No callback elaboration, speculative
    /// application, or scratch metavariable solutions escape this query.
    fn imported_subject_carrier(&self, name: &str, span: Span) -> Option<ReceiverCarrier> {
        let info = self.lookup_global(name)?;
        let GlobalBinding::Tm { ctx, ty, .. } = &self.psi.bindings[info.abs as usize] else {
            return None;
        };
        if !matches!(ctx.base, CtxBase::Nil) || ctx.len() != 0 { return None; }
        let growth = self.psi.bindings.len() as u32 - info.abs
            + self.global_padding() + self.meta_pushed.borrow().len() as u32;
        let mut ty = ty.shift_global(growth);
        let mut cx = Cx::empty();
        let subject = info.params.iter().position(|p| p.is_self)
            .or_else(|| info.params.iter().position(|p| !p.implicit && !p.is_type))?;
        for (i, p) in info.params.iter().enumerate() {
            let Type::Pi { dom, dom_level, cod, .. } = self.whnf(&cx, &ty, span).ok()? else {
                return None;
            };
            if i == subject { return self.receiver_carrier(&cx, &dom, span); }
            cx.push(p.name.clone(), (*dom).clone(), dom_level);
            ty = (*cod).clone();
        }
        None
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
            match self.imported_subject_carrier(&candidate, span) {
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
