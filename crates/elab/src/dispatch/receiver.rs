//! Class-backed receiver dispatch.
//!
//! This resolves the declaring class at a receiver, reports competing
//! readings, and projects directly through upcast provenance.

use std::rc::Rc;

use heather_kernel::term::{Term, Type};
use heather_syntax::{Expr, Span};

use crate::inductive::Inductive;
use crate::{
    Cx, DotResolution, ElabError, Elaborator, R, Upcast, err, resolve, skel_of_ty, traits,
};

impl Elaborator {
    /// `x.op(y)` where `op` is a class member and `x`'s type is a carrier with
    /// an instance (docs/traits-receiver-dispatch-design.md).
    ///
    /// One route for every carrier, because dispatch *is* a resolution goal:
    /// the goal `C<typeof(x)>` is built in kernel form (§2.1) and handed to
    /// layer 2's `resolve_goal`, so a concrete carrier is answered by the
    /// registry, a generic one by the `requires` binder in scope, and a
    /// derivable one by backchaining — with layer 2's own scope-beats-registry
    /// order inherited rather than re-decided.
    ///
    /// `None` is "this is not a dispatch", and every `None` leaves the method
    /// desugaring to run exactly as it did (§4 rule 5).
    pub(crate) fn class_dispatch(
        &self,
        cx: &Cx,
        recv: &Expr,
        name: &str,
        other: Option<(String, String)>,
        args: &[Expr],
        span: Span,
    ) -> R<Option<DotResolution>> {
        // The cheap negative test, before anything is inferred or resolved.
        if !self.traits.has_member(name) {
            return Ok(None);
        }
        // Inference failure is not an error here, exactly as for a field and
        // for a member: the fallback is what handles a receiver whose type
        // only the call fixes.
        let Ok((_, rty, rlvl)) = self.elab_infer(cx, recv) else {
            return Ok(None);
        };
        // Candidates: every class **visible here** (the ordinary §4 regime,
        // asked by resolving the class's own name) that **declares** this
        // field, with exactly one type parameter (§2.1), in sorted
        // canonical-name order — never `HashMap` order, and never declaration
        // order.
        //
        // *Declares*, and not "has": a class that merely inherits `name` never
        // said anything about it, so it is not a candidate at all — before any
        // instance is consulted (docs/traits-owner-dispatch-design.md §2). That
        // is what makes an inherited member dispatchable without a tiebreak,
        // and it leaves two *unrelated* declaring classes ambiguous, which is
        // the case §4 rule 3 exists for.
        let with_field = self.declaring_classes(name);
        let cands: Vec<(String, Rc<traits::ClassInfo>)> = with_field
            .iter()
            .filter(|(_, i)| i.params.len() == 1)
            .cloned()
            .collect();
        if cands.is_empty() {
            // A multi-parameter class is refused *by name* rather than
            // mis-dispatched (§2.1): the receiver fixes the carrier and
            // nothing fixes the rest, and a goal with a meta in it is what
            // layer 2 §4 declines to resolve. Silent only when the call has
            // another reading to take (§4 rule 5).
            if let Some((_, info)) = with_field.first()
                && other.is_none()
            {
                return err(
                    format!(
                        "`{name}` is a member of `{}`, which takes {} type parameters: \
                         receiver dispatch builds its goal from the receiver alone, so it \
                         reaches a one-parameter class only — write the projection \
                         (`⟨instance⟩.{name}(…)`)",
                        info.name,
                        info.params.len()
                    ),
                    span,
                );
            }
            return Ok(None);
        }
        // What the trace calls the carrier. A display and never a key: an open
        // carrier has no nominal tag to name, and saying so beats rendering a
        // lowered type nothing can render totally (layer 2 §7).
        let carrier = self
            .type_namespace(cx, &rty, span)
            .unwrap_or_else(|| "the receiver's type".to_string());
        let mut trace: Vec<resolve::TraceLine> = Vec::new();
        let mut hits: Vec<(Rc<Inductive>, Type, Term, String, Upcast)> = Vec::new();
        let mut tried: Vec<String> = Vec::new();
        let mut unpinned: Option<ElabError> = None;
        for (_, info) in &cands {
            let Some(ind) = self.lookup_inductive(&info.name).cloned() else {
                continue;
            };
            let targs = [(rty.clone(), rlvl.clone())];
            // An indexed class's goal has a value slot, and the ladder's step 2
            // is what fills it here (§5.1): scope, then refuse by name.
            let vargs = match self.index_vargs(cx, info, &ind, &targs, &carrier, span) {
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
            let display = format!("{}<{carrier}>", info.name);
            tried.push(display.clone());
            let mut tr = Vec::new();
            // Every candidate is tried even once one has succeeded: the
            // ambiguity is the point, and a first hit would be a priority
            // (§4 rule 3).
            // `up` is the **upcast provenance** (`resolve_goal_from`): if this
            // goal is answered from a child dictionary, the child is what the
            // projection below reads from.
            let mut up = None;
            let found = self.resolve_goal_from(cx, &goal, &glvl, &display, span, &mut tr, &mut up);
            match found {
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
                    "`{name}` at this receiver is a member of {list}, and each has an \
                     instance here — write the projection you meant \
                     (`⟨instance⟩.{name}(…)`) rather than letting the receiver choose"
                ),
                span,
            );
        }
        let Some((ind, goal, dict, display, up)) = hits.pop() else {
            // No candidate resolved. If the call has another reading, that
            // reading runs and this search is forgotten; if it has none, the
            // search *is* the diagnosis and is reported instead of the
            // "unknown name" the method desugaring would have produced.
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
        if let Some((desc, fix)) = other {
            return err(
                format!(
                    "`{name}` here is both a member of `{display}`, reached through the \
                     receiver's type, and {desc} — write one of them: \
                     `⟨instance⟩.{name}(…)` for the class member, or {fix} for the other"
                ),
                span,
            );
        }
        // An answer that came by **upcast** is read *through*: the field is the
        // child's own (docs/traits-named-upcast-design.md §2).
        let (ind, goal, dict) = self.through_upcast(ind, goal, dict, up, name);
        // Reported rather than asserted, though the candidate filter is what
        // just found this field: a library must not panic to say two of its own
        // tables disagree.
        let Some(idx) = ind.field_index(name) else {
            return err(
                format!("internal: `{}` has no field `{name}` after all", ind.name),
                span,
            );
        };
        let (t, fty, flvl) = self.project_field(cx, &ind, &goal, Rc::new(dict), idx, span)?;
        let skel = skel_of_ty(&ind.ctors[0].fields[idx].1);
        // The receiver is the field's **first explicit argument**: a class
        // field is a function type, not a declaration, so it has no `self`
        // marker to consult and takes the position `subject_index` defaults to
        // (issues/method-receiver-position.md).
        let mut all = Vec::with_capacity(args.len() + 1);
        all.push(recv.clone());
        all.extend(args.iter().cloned());
        Ok(Some(DotResolution::Dispatch(t, fty, flvl, skel, all)))
    }

    /// A dispatched projection reads **through** an upcast
    /// (`docs/traits-named-upcast-design.md` §2).
    ///
    /// Owner-keyed dispatch builds its goal at the class that *declares* the
    /// field, so at a child dictionary the resolver answers by step 1b with an
    /// assembled ancestor record and the projection would be
    /// `⟨C { f: d.f, … }⟩.f`. But that slot **is** `d.f` — it is what the
    /// assembly is made of — and the child has `f` in its own flattened field
    /// list at its own index (layer 1 §3). So the projection is taken from the
    /// child dictionary directly, and the assembled ancestor never enters the
    /// term.
    ///
    /// This is not a change to the *value*: the two are equal by β and
    /// projection, and the proposal has already passed the resolver's kernel
    /// gate (layer 2 §4.4) before it gets here. What it changes is the
    /// spelling the field's type is handed downstream in — the child's own
    /// components, rather than projections of a record literal that every later
    /// conversion has to reduce again. That residue *was* the cost
    /// `issues/upcast-assembly-cost-at-open-carriers.md` measured.
    ///
    /// A `None` provenance (every answer that is not an upcast) is the
    /// identity, which is what keeps this off every dispatch in the corpus that
    /// resolves exactly.
    pub(crate) fn through_upcast(
        &self,
        ind: Rc<Inductive>,
        goal: Type,
        dict: Term,
        up: Upcast,
        name: &str,
    ) -> (Rc<Inductive>, Type, Term) {
        // Reported by returning the input, not asserted: a child whose
        // flattened list has lost the field would mean the flattening and the
        // resolver disagree, and the identity is the answer that still checks.
        let Some((child_dict, child_ty)) = up else {
            return (ind, goal, dict);
        };
        let Some(child) = self.tag_of(&child_ty) else {
            return (ind, goal, dict);
        };
        if child.field_index(name).is_none() {
            return (ind, goal, dict);
        }
        (child, child_ty, child_dict)
    }
}
