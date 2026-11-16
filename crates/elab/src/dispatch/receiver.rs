//! Class-backed receiver dispatch.
//!
//! This resolves the declaring class at a receiver, reports competing
//! readings, and projects directly through upcast provenance.

use heather_kernel::rc::Rc;

use heather_kernel::term::{CtxBase, GlobalBinding, LocalCtx, LocalVar, Term, Type};
use heather_syntax::{Expr, Span};

use crate::inductive::Inductive;
use crate::{
    Cx, DotResolution, ElabError, Elaborator, R, Upcast, err, resolve, skel_of_ty, traits,
};
use crate::dispatch::Members;
use crate::application::Callables;
use crate::dispatch::Carriers;
use crate::dispatch::Dictionaries;
use crate::dispatch::Projections;
use crate::resolve::Resolution;
use crate::name_lookup::NameLookup;

/// The reading a `.name(…)` call has besides the class member
/// (docs/language/classes/traits-receiver-dispatch-design.md §3, "another reading exists"):
/// what a successful dispatch races under §4 rule 2 and what a failed one
/// falls back to under rule 5.
pub(crate) struct OtherReading {
    /// The reading as the rule-2 diagnostic names it.
    pub(crate) desc: String,
    /// The spelling that selects it, for the same diagnostic.
    pub(crate) fix: String,
    /// The callee the desugared call is to — never for a builtin. Resolved
    /// only once a dispatch has succeeded beside it, to the committed global
    /// [`Receivers::field_is_global`] compares the dispatched field against
    /// (issues/receiver-dispatch-coinciding-readings.md). Resolving it only
    /// there keeps every other method call at its old price.
    pub(crate) callee: Option<String>,
    /// The bare name, when this reading is an ambient local, alias or
    /// declaration: one that is **discarded** once the receiver's type shows
    /// it cannot take the receiver (docs/language/classes/receiver-member-resolution-design.md
    /// §2). `None` for a member, a constructor or a builtin.
    pub(crate) ambient: Option<String>,
}

/// Receiver dispatch's part of the elaborator.
pub(crate) struct Receivers<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for Receivers<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Receivers<'_> {
    /// `x.op(y)` where `op` is a class member and `x`'s type is a carrier with
    /// an instance (docs/language/classes/traits-receiver-dispatch-design.md).
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
        other: Option<OtherReading>,
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
        // An ambient reading that provably cannot take this receiver is no
        // reading: it neither races a successful dispatch nor catches a
        // failed one. Read off the carrier just inferred, so it costs no
        // inference of its own.
        let other = other.filter(|o| {
            !o.ambient
                .as_ref()
                .is_some_and(|n| Members(self).ambient_cannot_take(cx, n, &rty, span))
        });
        // Candidates: every class **visible here** (the ordinary §4 regime,
        // asked by resolving the class's own name) that **declares** this
        // field, with exactly one type parameter (§2.1), in sorted
        // canonical-name order — never `HashMap` order, and never declaration
        // order.
        //
        // *Declares*, and not "has": a class that merely inherits `name` never
        // said anything about it, so it is not a candidate at all — before any
        // instance is consulted (docs/language/classes/traits-owner-dispatch-design.md §2). That
        // is what makes an inherited member dispatchable without a tiebreak,
        // and it leaves two *unrelated* declaring classes ambiguous, which is
        // the case §4 rule 3 exists for.
        let with_field = Projections(self).declaring_classes(name);
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
        let carrier = Carriers(self)
            .type_namespace(cx, &rty, span)
            .unwrap_or_else(|| "the receiver's type".to_string());
        let mut trace: Vec<resolve::TraceLine> = Vec::new();
        let mut hits: Vec<(Rc<Inductive>, Type, Term, String, Upcast)> = Vec::new();
        let mut tried: Vec<String> = Vec::new();
        let mut unpinned: Option<ElabError> = None;
        for (key, info) in &cands {
            let Some(ind) = self.types.inductive(key).cloned() else {
                continue;
            };
            let targs = [(rty.clone(), rlvl.clone())];
            // An indexed class's goal has a value slot, and the ladder's step 2
            // is what fills it here (§5.1): scope, then refuse by name.
            let (gargs, vargs) = match Dictionaries(self).index_vargs(cx, key, info, &ind, &targs, &carrier, span) {
                Ok(Some(v)) => v,
                Ok(None) => continue,
                Err(e) => {
                    unpinned.get_or_insert(e);
                    continue;
                }
            };
            let Ok((goal, glvl)) = self.lower_instance(cx, &ind, &gargs, &vargs, span) else {
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
            let found = Resolution(self).resolve_goal_from(cx, &goal, &glvl, &display, None, span, &mut tr, &mut up);
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
        // An answer that came by **upcast** is read *through*: the field is the
        // child's own (docs/language/classes/traits-named-upcast-design.md §2).
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
        if let Some(OtherReading { desc, fix, callee, .. }) = other {
            // The two readings **coincide** when the dictionary dispatch
            // actually resolved fills this field with the very global the
            // other reading calls: then there is one meaning, and the other
            // reading's path runs exactly as a failed dispatch's would, so the
            // emitted term is the direct global — what it is with no class in
            // scope at all. Read off the dictionary *after* the upcast, since
            // that is the one the projection would read. Anything else stays
            // the error: rule 2 is about readings that differ, and growth
            // still only ever adds errors, never reinterpretations
            // (issues/receiver-dispatch-coinciding-readings.md).
            if callee
                .and_then(|c| Callables(self).bare_global_abs(cx, &c))
                .is_some_and(|g| self.field_is_global(&dict, idx, g))
            {
                return Ok(None);
            }
            return err(
                format!(
                    "`{name}` here is both a member of `{display}`, reached through the \
                     receiver's type, and {desc} — write one of them: \
                     `⟨instance⟩.{name}(…)` for the class member, or {fix} for the other"
                ),
                span,
            );
        }
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
    /// (`docs/language/classes/traits-named-upcast-design.md` §2).
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

    /// Is field `idx` of the dispatched dictionary `dict` the global at
    /// absolute Ψ index `g`, called the way the method desugaring would call
    /// it? The coincidence test of §4 rule 2
    /// (issues/receiver-dispatch-coinciding-readings.md).
    ///
    /// **One local step, read syntactically — not conversion.** `dict` must be
    /// a global (the instance) applied to exactly as many arguments as its
    /// stored body has leading `λ`s; the body under them must be the record
    /// literal's `pair` spine; and the spine's entry `idx + 1` (entry 0 is the
    /// nominal tag) must be `g` itself, or `g` applied to precisely the
    /// instance's own binders in order. That is δ of the instance global, β
    /// of its parameters and ι of the projection, and nothing else: a local
    /// dictionary (rule 4's scope answer) is a variable and has no body to
    /// read, a field written as a λ or as another global's partial
    /// application is not a bare global, and a derivation whose body is not a
    /// literal spine is declined. Every decline keeps the rule-2 error, which
    /// is the conservative direction.
    ///
    /// **"Called the same way"** is read off `g`'s own parameter table. The
    /// class reading applies the field to the receiver and the arguments
    /// positionally, the receiver first; the desugaring puts the receiver at
    /// `g`'s subject slot and inserts `g`'s implicits. So the two are one call
    /// only when every parameter past the instantiated prefix is explicit,
    /// not a type, and the subject is the first of them.
    ///
    /// **A generic instance, and what "same type arguments" means there.**
    /// After instantiation the field is `g(σ⃗)`, σ⃗ the dictionary's type
    /// arguments, which the resolver found by matching the instance's head
    /// against the receiver's type. The other reading's arguments are only
    /// inferred later, by the application solving `g`'s subject domain
    /// against the same receiver type. Comparing the two answers would be
    /// elaborating both readings, so the rule is restricted to where they are
    /// answers to **one equation**: `g` takes the instance's binders all and
    /// in order as its leading implicits — a type binder as a type
    /// parameter, an index binder (`instance(n: Nat) DecEq<BitVec(n)>`) as
    /// an implicit `{n: Nat}` of the same domain that only unification fills
    /// — and `g`'s declared subject domain is *syntactically* the field's own
    /// carrier at those binders. Both solvers then match the same pattern
    /// against the same receiver type, and a pattern in distinct binders has
    /// one first-order answer (issues/deceq-instance-member-ambiguity.md).
    /// Excluded by this, and so still the error: an instance with
    /// `requires` (a dictionary binder handed to `g` would be one the
    /// desugaring resolves afresh, and `g`'s matching parameter has a
    /// solver), a universe-polymorphic `g` (`UApp`), and a subject domain
    /// spelled differently from the instance head (an alias, a respelling).
    ///
    /// A dictionary the resolver minted at closed arguments is a global
    /// whose body applies the instance to them; it is read through, so the
    /// test sees the instance's literal.
    ///
    /// Cost: this runs only where the rule-2 error was about to fire, which
    /// before this test was every such call — so no call that elaborated
    /// before pays anything.
    pub(crate) fn field_is_global(&self, dict: &Term, idx: usize, g: usize) -> bool {
        // The dictionary's spine: the instance global and its arguments.
        let (head, dargs) = crate::spelling::app_spine(dict);
        let Term::GlobalTm { var, .. } = head else {
            return false;
        };
        let Some(mut inst) = self.global_abs_of(*var) else {
            return false;
        };
        let mut n = dargs.len();
        // A dictionary the resolver minted at closed arguments
        // (`instance(n: Nat) DecEq<BitVec(n)>` at `BitVec(8)`) is a global
        // whose body is the instance applied to them: read through it, at
        // most a few times, to the instance whose body is the literal.
        let mut hops = 0;
        let (mut value, binder_doms) = loop {
            let Some(GlobalBinding::Tm {
                ctx,
                body: Some(body),
                ..
            }) = self.psi.bindings.get(inst)
            else {
                return false;
            };
            if !matches!(ctx.base, CtxBase::Nil) || ctx.len() != 0 {
                return false;
            }
            // β: exactly one `λ` per argument. A binder at a type is a type
            // parameter; any other is an index or a `requires` dictionary,
            // told apart below against `g`'s own parameter at the same
            // position.
            let mut value: &Term = body;
            let mut binder_doms: Vec<&Type> = Vec::with_capacity(n);
            for _ in 0..n {
                let Term::Lam { dom, body, .. } = value else {
                    return false;
                };
                binder_doms.push(dom);
                value = body;
            }
            if crate::spelling::pair_of(value).is_some() {
                break (value, binder_doms);
            }
            // The body is scoped over the Ψ prefix before its binding.
            let (inner, inner_args) = crate::spelling::app_spine(value);
            let Term::GlobalTm { var: inner, .. } = inner else {
                return false;
            };
            hops += 1;
            let Some(next) = inner.position(inst).filter(|_| hops <= 4) else {
                return false;
            };
            inst = next;
            n = inner_args.len();
        };
        // ι: entry `idx + 1` of the literal spine, in either pair spelling.
        for _ in 0..=idx {
            let Some((_, snd)) = crate::spelling::pair_of(value) else {
                return false;
            };
            value = snd;
        }
        let Some((field, _)) = crate::spelling::pair_of(value) else {
            return false;
        };
        // The field's carrier is written on the `pair` spelling; a `pair@`
        // layer is checked against its description and carries none
        // (docs/elaborator/intro-by-type-design.md), so there it is read off the
        // instance's declared type below.
        let field_ty = match value {
            Term::Pair { fst_ty, .. } => Some(fst_ty),
            _ => None,
        };
        // The field: `g`, applied to the instance's binders outermost first
        // (`x_{n-1} … x_0` in de Bruijn order), and to nothing else.
        let (fhead, fargs) = crate::spelling::app_spine(field);
        if fargs.len() != n {
            return false;
        }
        // Argument `k` from the end is binder `k`.
        if fargs
            .iter()
            .rev()
            .enumerate()
            .any(|(k, a)| !matches!(&***a, Term::Var(LocalVar(v)) if *v as usize == k))
        {
            return false;
        }
        let Term::GlobalTm { var: gv, .. } = fhead else {
            return false;
        };
        // The body is stored scoped over the Ψ prefix before its binding.
        if gv.position(inst) != Some(g) {
            return false;
        }
        // Called the same way: `n` leading implicit type parameters, then
        // explicit value parameters with the subject first.
        let params = NameLookup(self).params_at(g);
        if params.len() < n {
            return false;
        }
        let (lead, rest) = params.split_at(n);
        // A type binder is a leading `<A>`; an index binder is an implicit
        // `{n: T}` that nothing but unification fills — no default, no
        // solver, so never a `requires` dictionary the desugaring would
        // resolve afresh.
        let lead_fits = lead.iter().zip(&binder_doms).all(|(p, dom)| {
            p.implicit
                && if matches!(dom, Type::Ty(_)) {
                    p.is_type
                } else {
                    !p.is_type && p.solver.is_none() && p.default.is_none()
                }
        });
        if !lead_fits
            || rest.iter().any(|p| p.implicit || p.is_type)
            || rest.iter().position(|p| p.is_self).is_some_and(|i| i != 0)
        {
            return false;
        }
        if n == 0 {
            return true;
        }
        // One equation: `g`'s subject domain under its `n` type binders is
        // the field's carrier under the instance's `n` type binders. The
        // contexts line up binder for binder, and both name committed
        // definitions as constants, so the two compare as spelled.
        let Some(GlobalBinding::Tm { ty: gty, .. }) = self.psi.bindings.get(g) else {
            return false;
        };
        let mut gcur: &Type = gty;
        for idom in &binder_doms {
            let Type::Pi { dom, cod, .. } = gcur else {
                return false;
            };
            // Binder for binder the same domain: a universe for a type
            // binder, the index's own type for an index (`{n: Nat}` beside
            // `instance(n: Nat)`), so both solvers fill one telescope.
            let same = match (&**dom, *idom) {
                (Type::Ty(_), Type::Ty(_)) => true,
                (Type::Ty(_), _) | (_, Type::Ty(_)) => false,
                (gd, id) => *gd == *id,
            };
            if !same {
                return false;
            }
            gcur = cod;
        }
        let Type::Pi { dom: gdom, .. } = gcur else {
            return false;
        };
        match field_ty {
            Some(field_ty) => {
                let Type::Pi { dom: cdom, .. } = &**field_ty else {
                    return false;
                };
                **gdom == **cdom
            }
            None => self
                .declared_field_carrier(inst, n, idx)
                .is_some_and(|cdom| {
                    **gdom == cdom
                }),
        }
    }

    /// The subject domain of field `idx` as the instance's declared type
    /// states it — for a `pair@` dictionary, which writes none. Scoped at the
    /// current Ψ under the instance's `n` type binders: the declared type is
    /// unfolded to its record Σ, walked to entry `idx + 1` (strengthened past
    /// the entries before it, which a carrier that mentions them is not), and
    /// the field's Π read at its domain. `None` wherever a step does not
    /// land on that shape, which keeps the rule-2 error.
    fn declared_field_carrier(&self, inst: usize, n: usize, idx: usize) -> Option<Type> {
        let Some(GlobalBinding::Tm { ty, .. }) = self.psi.bindings.get(inst) else {
            return None;
        };
        let oracle = self.semantic_oracle();
        let mut cur = (**ty).clone();
        let mut gamma = LocalCtx::nil();
        for _ in 0..n {
            let Type::Pi { dom_level, dom, cod, .. } = cur else {
                return None;
            };
            gamma = gamma.extended(dom, dom_level);
            cur = (*cod).clone();
        }
        let outer = gamma.clone();
        for _ in 0..=idx {
            let Ok(Type::Sigma { fst_level, fst, snd, .. }) = oracle.whnf_type(&gamma, &cur) else {
                return None;
            };
            gamma = gamma.extended(fst, fst_level);
            cur = (*snd).clone();
        }
        let Ok(Type::Sigma { fst, .. }) = oracle.whnf_type(&gamma, &cur) else {
            return None;
        };
        let Ok(Type::Pi { dom, .. }) = oracle.whnf_type(&gamma, &fst) else {
            return None;
        };
        crate::unification::strengthen_ty(&outer, &dom, (idx + 1) as u32)
    }
}
