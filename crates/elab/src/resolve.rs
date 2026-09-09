//! Instance resolution and `:= infer` (`docs/traits-layer2-design.md`).
//!
//! One entry point — [`Elaborator::resolve_goal`], `(goal, scope) → term` —
//! consulted from `apply_implicit`'s retry loop for every **solver
//! parameter**. Three sources, in the record's ascending-scope order (§3):
//! the canonical derived table, the local scope innermost-first, then the
//! layer-1 instance registry by backchaining.
//!
//! One consumer reads an answer rather than taking it: a dispatched
//! projection, which asked for a dictionary only to take one field out of it.
//! [`Elaborator::resolve_goal_from`] tells it where an **upcast** answer came
//! from, and `docs/traits-named-upcast-design.md` is why that matters.
//!
//! Nothing here is trusted. Every proposal, from every source, is handed to
//! the kernel at the goal type before it is returned (§4.4) — which is what
//! makes selection-by-trial (§3.1) a *function* of the goal rather than a
//! guess, and what keeps a wrong candidate from surfacing pages later as a
//! declaration-gate rejection.

use std::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, GlobalVar, LocalCtx, LocalSubst, SubstTail, Term, Type};
use heather_kernel::typing;
use heather_syntax::{Expr, ExprKind, Span};

use crate::{Cx, ElabError, Elaborator, oracle, stats};

/// How deep backchaining may go before it refuses. Declaration-time
/// structural decrease (design §6) is what makes this unreachable; the cap is
/// the belt, not the braces — a registry assembled by a *failing* decrease
/// check (a class whose instances were declared before this round) must still
/// terminate.
const MAX_DEPTH: usize = 32;

/// The reduction allowance for a derived-table lookup
/// ([`Elaborator::derived_hit`]) and for the pending queue's duplicate check.
/// The table is keyed by conversion, and a conversion that has to reduce two
/// closed goals' operands to find them *unequal* can cost a proof's whole
/// budget (`issues/type-level-reduction-over-computed-operands.md`); the
/// table is an optimization, so its lookup is bounded and an inconclusive
/// comparison is a miss, which costs the registry route and a second mint,
/// never correctness.
const DERIVED_LOOKUP_FUEL: u64 = 1 << 12;

/// One record of a resolution search — the trace is a flat list of these, not
/// a prose paragraph (design §7, `issues/ai-facing-tooling.md` §7). `key` is
/// drawn from a closed vocabulary so a consumer can read the trace as data;
/// `depth` is the subgoal nesting.
#[derive(Clone, Debug)]
pub struct TraceLine {
    pub depth: usize,
    pub key: &'static str,
    pub value: String,
}

/// Two goals whose carrier heads are both known and differ are not compared
/// by conversion in the derived table (see [`DerivedInst::head`]).
fn heads_may_agree(a: Option<&str>, b: Option<&str>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a == b,
        _ => true,
    }
}

fn line(depth: usize, key: &'static str, value: impl Into<String>) -> TraceLine {
    TraceLine {
        depth,
        key,
        value: value.into(),
    }
}

/// Render a trace as one `key: value` line per record, indented by depth.
pub(crate) fn render_trace(trace: &[TraceLine]) -> String {
    trace
        .iter()
        .map(|l| format!("\n  {}{}: {}", "  ".repeat(l.depth), l.key, l.value))
        .collect()
}

/// A minted canonical derived instance (design §8): a real Ψ global standing
/// for one derivation, so the second use site references it instead of
/// deriving a second copy.
#[derive(Clone)]
pub(crate) struct DerivedInst {
    /// Machine name, unwritable by construction. Deterministic within one
    /// elaboration; see design §9.2 for what that is *not*.
    pub name: String,
    /// Absolute Ψ index, using the same convention as the name registry's
    /// global metadata.
    pub abs: u32,
    /// The goal this value was derived for — the table's key, compared up to
    /// conversion.
    pub ty: Type,
    pub level: Level,
    /// The Ψ length when the entry was minted. A stored type's `GlobalVar`s
    /// are relative to the Ψ that was, and Ψ only grows, so a lookup rebases
    /// by the difference (the same bookkeeping the pending queue does).
    pub at: u32,
    /// The goal carrier's head the search was ordered by, when it was read
    /// ([`Elaborator::solver_carrier_head`]). A lookup at a goal with a
    /// *different* known head skips the conversion: two goals at different
    /// heads can still convert, but deciding that means unfolding both, which
    /// over computed operands is the cost the head order exists to avoid
    /// (docs/reflection-through-decide-instances-design.md §3); a miss here
    /// costs the registry route, never correctness.
    pub head: Option<String>,
}

impl Elaborator {
    /// Resolve one goal, or explain in `tr` why not.
    ///
    /// `display` is what the diagnostic calls the goal (the parameter's
    /// written type). It is a display and never a key.
    ///
    /// `prefer` is the goal carrier's head key when the caller could read it
    /// off the solver parameter's written type ([`Elaborator::solver_carrier_head`]);
    /// it orders the registry's candidates and decides nothing.
    pub(crate) fn resolve_goal(
        &self,
        cx: &Cx,
        goal: &Type,
        lvl: &Level,
        display: &str,
        prefer: Option<&str>,
        span: Span,
        tr: &mut Vec<TraceLine>,
    ) -> Option<Term> {
        self.resolve_goal_from(cx, goal, lvl, display, prefer, span, tr, &mut None)
    }

    /// [`Self::resolve_goal`], reporting **where an upcast came from**.
    ///
    /// When step 1b answers, `up` receives the *child* dictionary and its class
    /// type — the two things a consumer needs to read the answer as a
    /// projection instead of as a value
    /// (`docs/traits-named-upcast-design.md` §2). Nothing else about the search
    /// changes, and the upcast proposal itself is still built and still gated:
    /// this reports a provenance, it does not open a second route.
    ///
    /// Only the two **dispatch** sites call this. Every other consumer wants a
    /// dictionary value and takes the plain entry point, whose `&mut None`
    /// makes the whole mechanism inert — including the recursive one, since
    /// backchaining recurses through `elab_check` into [`Self::resolve_goal`]
    /// and so can never leak a nested search's provenance into an outer one.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn resolve_goal_from(
        &self,
        cx: &Cx,
        goal: &Type,
        lvl: &Level,
        display: &str,
        prefer: Option<&str>,
        span: Span,
        tr: &mut Vec<TraceLine>,
        up: &mut Option<(Term, Type)>,
    ) -> Option<Term> {
        let depth = self.resolve_depth.get();
        tr.push(line(depth, "goal", display.to_string()));
        if depth >= MAX_DEPTH {
            tr.push(line(
                depth,
                "depth",
                format!("gave up at {MAX_DEPTH} nested subgoals"),
            ));
            return None;
        }

        // 0. The canonical table (design §8). Checked before the scope only
        //    because a hit is a *reference to the very value* the registry
        //    route would rebuild: it cannot shadow anything, since a local of
        //    the goal type would have been minted from nothing.
        if let Some(t) = self.derived_hit(cx, goal, prefer) {
            return Some(t);
        }

        // 1. Ascending scopes: locals innermost-first, then `let` aliases.
        //    "An explicit value in scope always wins over derivation" is this
        //    step returning before step 2 runs (design §3).
        for pos in (0..cx.names.len()).rev() {
            let (t, ty, l) = self.local(cx, pos);
            if self.conv_here(cx, &ty, goal, &l) {
                tr.push(line(depth, "local", cx.names[pos].clone()));
                return Some(t);
            }
        }
        for a in cx.aliases.iter().rev() {
            let by = (cx.names.len() - a.depth) as u32;
            let ty = a.ty.shift_local(by);
            if self.conv_here(cx, &ty, goal, &a.level) {
                tr.push(line(depth, "local", format!("{} (a `let`)", a.name)));
                return Some((*a.term).shift_local(by));
            }
        }
        // 1b. The same scope again, by **upcast**: a dictionary of a *child*
        //     class answers an ancestor's goal, through the canonical parent
        //     projection (docs/traits-owner-dispatch-design.md §3). After the
        //     exact pass, because an exactly-typed value in scope is the one
        //     the writer named; before the registry, because this is still a
        //     scope answer and not a derivation.
        if let Some((t, who, src)) = self.scope_upcast(cx, goal, lvl, span) {
            tr.push(line(depth, "local", who));
            *up = Some(src);
            return Some(t);
        }
        tr.push(line(
            depth,
            "scope",
            format!(
                "{} binder(s) consulted, none of the goal type",
                cx.names.len()
            ),
        ));

        // 2. The registry. Only a *class* has one: an `:= infer` goal at an
        //    ordinary type is a scope search and nothing else, and its trace
        //    says so rather than reporting an empty registry.
        let Some(ind) = self.tag_of(goal) else {
            tr.push(line(depth, "no-class", "the goal type is not a class"));
            return None;
        };
        // The goal has already exposed its nominal tag, so its owning
        // declaration is known. Re-resolving the bare class name here lets a
        // same-named local class redirect search away from the goal's actual
        // class; use the declaration identity carried by the tag instead.
        let ckey = crate::names::qkey(&ind.scope.module, &ind.name);
        if !self.traits.has_class(&ckey) {
            tr.push(line(
                depth,
                "no-class",
                format!(
                    "`{}` is a record, not a class, so it has no instances",
                    ind.name
                ),
            ));
            return None;
        }
        // Candidates in a *stated* order — sorted by canonical name, never
        // declaration order and never `HashMap` order (design §3.1) — with
        // the instances keyed at the goal carrier's own head first, when the
        // caller could name it.
        let cands = self.traits.candidates(&ckey, prefer);
        if let Some(head) = prefer {
            tr.push(line(depth, "head", head.to_string()));
        }
        if cands.is_empty() {
            tr.push(line(
                depth,
                "no-instance",
                format!("`{}` has no instances", ind.name),
            ));
            return None;
        }
        tr.push(line(
            depth,
            "class",
            format!("{} ({} instance(s))", ind.name, cands.len()),
        ));
        let class_has_value_indices = !self
            .traits
            .class(&ckey)
            .expect("class existence checked above")
            .valparams
            .is_empty();
        for (g, parameterized, index) in cands {
            // Candidate construction elaborates a real global reference, but
            // a rejected candidate is search state rather than part of the
            // winning term. Only the accepted branch may publish its edges.
            let dependency_mark = self.attempt.direct_dependencies.borrow().clone();
            // The index is part of the candidate line, not a separate one: at a
            // carrier with two structures the trace has to say *which* was
            // tried, and that is the whole observability the registry key buys
            // (docs/operation-indexed-classes-design.md §3.1, §11).
            tr.push(line(
                depth,
                "candidate",
                if index.is_empty() {
                    g.clone()
                } else {
                    format!("{g} (index `{index}`)")
                },
            ));
            self.resolve_depth.set(depth + 1);
            let built = self.build_candidate(cx, &g, goal, lvl, span);
            self.resolve_depth.set(depth);
            match built {
                Ok(t) if self.checks_at(cx, &t, goal, lvl) => {
                    // Only a *derivation* is canonicalized. A declared
                    // instance's value is already one global reached by name,
                    // and minting a second one for it would duplicate the very
                    // thing the table exists to keep single.
                    if parameterized && !class_has_value_indices {
                        // A closed value index can pass the mint's empty-context
                        // check, but each distinct index would then create a
                        // synonym for the same declared parameterized instance
                        // application. Indexed classes deliberately retain that
                        // application directly; open indices are unmintable in
                        // any case. This costs optional sharing, never
                        // correctness, and avoids one global per literal length.
                        self.record_derived(goal, lvl, prefer);
                    }
                    return Some(t);
                }
                Ok(_) => tr.push(line(
                    depth + 1,
                    "rejected",
                    "built, but not of the goal type".to_string(),
                )),
                Err(ElabError::Resolution { trace, .. }) => {
                    // A subgoal's own search, spliced in at one more level of
                    // nesting: the whole thing stays one flat list.
                    tr.extend(trace.iter().map(|l| TraceLine {
                        depth: l.depth + 1,
                        key: l.key,
                        value: l.value.clone(),
                    }));
                }
                Err(e) => tr.push(line(depth + 1, "rejected", e.message())),
            }
            *self.attempt.direct_dependencies.borrow_mut() = dependency_mark;
        }
        None
    }

    /// Build one candidate: the bare instance reference, elaborated in
    /// **checking** position against the goal (design §3.2). Implicit
    /// insertion supplies the instance's type arguments from the expected
    /// type, and its own `requires` binders recurse through this same
    /// function — which is the whole of backchaining.
    fn build_candidate(
        &self,
        cx: &Cx,
        global: &str,
        goal: &Type,
        lvl: &Level,
        span: Span,
    ) -> Result<Term, ElabError> {
        let e = Expr {
            kind: ExprKind::Var(global.to_string()),
            span,
        };
        self.elab_check(cx, &e, goal, lvl)
    }

    /// Step 1b: answer the goal from a *child* dictionary in scope
    /// (docs/traits-owner-dispatch-design.md §3).
    ///
    /// Owner-keyed dispatch builds its goal at the class that declared the
    /// member, so the dictionary the writer has in hand is routinely a
    /// descendant of the goal's class — `requires m: AddCommMonoid<G>` against
    /// a goal `AddSemigroup<G>`, at an **open** `G` where no registry entry and
    /// no synthesized parent global exist. Conversion cannot see through that:
    /// the two are different records.
    ///
    /// Returns the proposal, what the trace should call it, and the **child
    /// dictionary with its class type** — the provenance
    /// [`Self::resolve_goal_from`] hands a dispatched projection so that it can
    /// read the field out of the child instead of out of the assembled parent
    /// (`docs/traits-named-upcast-design.md` §2). `None` is "nothing in scope
    /// upcasts", which costs one `tag_of` when the goal is not a class at all.
    fn scope_upcast(
        &self,
        cx: &Cx,
        goal: &Type,
        lvl: &Level,
        span: Span,
    ) -> Option<(Term, String, (Term, Type))> {
        let cind = self.tag_of(goal)?;
        if !cind.is_record {
            return None;
        }
        let ckey = self.key_of(&cind.name)?;
        if !self.traits.has_class(&ckey) {
            return None;
        }
        // Innermost first, exactly as the exact pass: the two passes must not
        // disagree about which binder is nearer.
        for pos in (0..cx.names.len()).rev() {
            let (t, ty, l) = self.local(cx, pos);
            if let Some(u) = self.upcast_from(cx, &cind, &ckey, goal, lvl, &t, &ty, &l, span) {
                return Some((
                    u,
                    format!("{} (upcast to `{}`)", cx.names[pos], cind.name),
                    (t, ty),
                ));
            }
        }
        for a in cx.aliases.iter().rev() {
            let by = (cx.names.len() - a.depth) as u32;
            let ty = a.ty.shift_local(by);
            let t = (*a.term).shift_local(by);
            if let Some(u) = self.upcast_from(cx, &cind, &ckey, goal, lvl, &t, &ty, &a.level, span)
            {
                return Some((
                    u,
                    format!("{} (a `let`, upcast to `{}`)", a.name, cind.name),
                    (t, ty),
                ));
            }
        }
        None
    }

    /// One candidate for the upcast: is `dict_ty`'s class a descendant of the
    /// goal's, and if so does the canonical parent record built from it check?
    ///
    /// The record is assembled rather than projected, because at an open
    /// carrier there is nothing to project *from* — layer 1 §4.4 synthesizes a
    /// canonical parent per instance declaration, not per binder. So this is
    /// that same assembly (the parent record over the child's own components),
    /// with the dictionary bound as an unspellable `#` alias so the fields can
    /// be written as ordinary projections and go down the existing constructor
    /// path. Dependent law fields need no handling: `build_ctor` substitutes
    /// the earlier components into the later field types, and the components
    /// here are literally the dictionary's own.
    #[allow(clippy::too_many_arguments)]
    fn upcast_from(
        &self,
        cx: &Cx,
        cind: &crate::inductive::Inductive,
        ckey: &str,
        goal: &Type,
        lvl: &Level,
        dict: &Term,
        dict_ty: &Type,
        dict_lvl: &Level,
        span: Span,
    ) -> Option<Term> {
        let dind = self.tag_of(dict_ty)?;
        if dind.name == cind.name {
            return None; // the exact pass already had its chance
        }
        let dkey = self.key_of(&dind.name)?;
        let dinfo = self.traits.class(&dkey)?;
        let mut tcx = cx.clone();
        tcx.aliases.push(Rc::new(crate::Alias {
            name: "#dict".into(),
            depth: cx.names.len(),
            term: Rc::new(dict.clone()),
            ty: dict_ty.clone(),
            level: dict_lvl.clone(),
            skel: None,
        }));
        // A class may now contain the same ancestor at several tagged fibers.
        // Try each matching path; the expected goal (including its index)
        // remains the final authority over which one is the requested parent.
        for ancestor in dinfo
            .ancestors
            .iter()
            .filter(|r| self.key_of(&r.name).as_deref() == Some(ckey))
        {
            let mut source = Expr {
                kind: ExprKind::Var("#dict".into()),
                span,
            };
            for component in &ancestor.path {
                source = Expr {
                    kind: ExprKind::Dot {
                        recv: Box::new(source),
                        name: component.clone(),
                        args: None,
                        named: Vec::new(),
                    },
                    span,
                };
            }
            let mut args = Vec::with_capacity(cind.ctors[0].fields.len());
            for (n, _) in &cind.ctors[0].fields {
                args.push(Expr {
                    kind: ExprKind::Dot {
                        recv: Box::new(source.clone()),
                        name: n.clone()?,
                        args: None,
                        named: Vec::new(),
                    },
                    span,
                });
            }
            let Ok(t) = self.build_ctor(&tcx, cind, 0, &args, goal, lvl, span) else {
                continue;
            };
            // The gate every proposal passes (design §4.4). In particular it
            // distinguishes two paths to one operation-indexed class.
            if self.checks_at(cx, &t, goal, lvl) {
                return Some(t);
            }
        }
        None
    }

    /// [`Self::conv_here`] for consumers outside this module — the value-slot
    /// ladder's carrier test (`docs/operation-indexed-classes-design.md` §5).
    pub(crate) fn conv_types(&self, cx: &Cx, ty: &Type, goal: &Type, lvl: &Level) -> bool {
        self.conv_here(cx, ty, goal, lvl)
    }

    /// Is `ty` the goal type, here? Conversion, in the use site's context.
    fn conv_here(&self, cx: &Cx, ty: &Type, goal: &Type, lvl: &Level) -> bool {
        stats::time_kernel(|| {
            self.goal_oracle()
                .convert_type(&cx.gamma, Layer::Prog, ty, goal, lvl)
                .is_ok()
        })
    }

    /// The kernel, at the goal type (design §4.4). Selection by trial is only
    /// a function of the goal because this runs on every proposal.
    fn checks_at(&self, cx: &Cx, t: &Term, goal: &Type, lvl: &Level) -> bool {
        let psi = self.goal_psi();
        stats::time_kernel(|| {
            typing::check_term(&psi, 0, Layer::Code, &cx.gamma, t, goal, lvl, self.fuel).is_ok()
        })
    }

    // -- the canonical derived table (design §8) ----------------------------

    /// A reference to the already-minted derivation of this goal, if there is
    /// one. Keyed by conversion, which is the right notion of "the same goal"
    /// and needs no encoding of a kernel type (design §9.2).
    /// Conversion under [`DERIVED_LOOKUP_FUEL`]: the table's notion of "the
    /// same goal", with an inconclusive answer counted as "not".
    fn derived_conv(&self, cx: &Cx, ty: &Type, goal: &Type, lvl: &Level) -> bool {
        stats::time_kernel(|| {
            oracle::SemanticOracle::in_world(self.goal_psi(), self.fuel.min(DERIVED_LOOKUP_FUEL))
                .convert_type(&cx.gamma, Layer::Prog, ty, goal, lvl)
                .is_ok()
        })
    }

    fn derived_hit(&self, cx: &Cx, goal: &Type, prefer: Option<&str>) -> Option<Term> {
        let now = self.psi.bindings.len() as u32;
        let d = self
            .traits
            .derived()
            .iter()
            .filter(|d| heads_may_agree(d.head.as_deref(), prefer))
            .find(|d| self.derived_conv(cx, &d.ty.shift_global(now - d.at), goal, &d.level))?;
        Some(self.derived_ref(cx, d.abs))
    }

    /// `u^δ` for a minted global, the same construction [`Elaborator::resolve`]
    /// makes for a written name: the goals sit innermost, so a committed
    /// binding is that much further out, and a closed statement's delayed
    /// substitution is the empty map out of the current Γ.
    fn derived_ref(&self, cx: &Cx, abs: u32) -> Term {
        if let Some(key) = self.names.global_name_at(abs) {
            self.attempt
                .direct_dependencies
                .borrow_mut()
                .insert(key.to_string());
        }
        let len = self.psi.bindings.len() as u32;
        let var = GlobalVar(len - 1 - abs + self.attempt.goal_arena.base());
        Term::GlobalTm {
            var,
            subst: LocalSubst {
                tail: SubstTail::Empty {
                    len: cx.gamma.entries.len() as u32,
                    base: cx.gamma.base,
                },
                terms: vec![],
            },
        }
    }

    /// Record that this goal deserves a canonical global. Minting itself
    /// cannot happen here — Ψ must not grow while a declaration is being
    /// elaborated (design §8) — so the goal is queued and the *item* is
    /// re-elaborated once the queue is drained.
    ///
    /// Two narrowings, both stated in the design: only a goal reached through
    /// the registry (this is called from that branch alone), and only while no
    /// goals are in flight (`goal_base == 0`), which is what keeps the queued
    /// type in a world the mint can still read.
    ///
    /// `prefer` travels with the goal: the mint re-runs the search in the
    /// empty context, and the head that ordered the first search is what
    /// keeps the second from building the general candidates first.
    fn record_derived(&self, goal: &Type, lvl: &Level, prefer: Option<&str>) {
        if self.attempt.goal_arena.base() != 0 || !self.type_is_closed(goal, lvl) {
            return;
        }
        let mut pending = self.pending_derived.borrow_mut();
        if pending.iter().any(|(t, l, _, head)| {
            heads_may_agree(head.as_deref(), prefer)
                && self.derived_conv(&Cx::empty(), t, goal, l)
        }) {
            return;
        }
        // With the Ψ length at capture: the item that recorded this goal goes
        // on to push its own globals, and a stored type's `GlobalVar`s are
        // relative to the Ψ that was (see [`Self::mint_pending`]).
        pending.push((
            goal.clone(),
            lvl.clone(),
            self.psi.bindings.len() as u32,
            prefer.map(str::to_string),
        ));
    }

    /// Is this type closed? Asked of the kernel, in the empty context — the
    /// honest test, and the one the mint has to pass anyway.
    fn type_is_closed(&self, goal: &Type, lvl: &Level) -> bool {
        stats::time_kernel(|| {
            typing::check_type(
                &self.psi,
                0,
                Layer::Prog,
                &LocalCtx::nil(),
                goal,
                lvl,
                self.fuel,
            )
            .is_ok()
        })
    }

    /// Drain the pending queue, minting one Ψ global per derivation
    /// (design §8). Called **between items**, where Ψ may grow.
    ///
    /// Deliberately not a restart: the item that discovered a derivation has
    /// already inlined its copy, and re-elaborating it to make it reference
    /// the global instead would cost a whole second elaboration of every item
    /// that resolves anything new. So the *first* use site of a derivation
    /// inlines it and every later one references the mint — which is what the
    /// canonical table is for (one value, reached by name), one use site
    /// later than the record's wording suggests.
    ///
    /// Order is the order recorded, which is innermost-first (a subgoal's
    /// derivation completes inside its parent's), so a derived parent
    /// references its derived children instead of inlining them.
    pub(crate) fn mint_pending(&mut self) {
        // A mint resolves, and resolving can discover further derivations, so
        // the queue is drained to fixpoint rather than once. It is finite: a
        // mint either registers a table entry (and the goal that produced it
        // now hits) or fails and is dropped.
        for _ in 0..MAX_DEPTH {
            let pending: Vec<(Type, Level, u32, Option<String>)> =
                std::mem::take(&mut self.pending_derived.borrow_mut());
            if pending.is_empty() {
                return;
            }
            for (goal, lvl, at, prefer) in pending {
                // The item pushed its own globals after this goal was
                // captured, so every `GlobalVar` in it now points that much
                // further out.
                let grew = self.psi.bindings.len() as u32 - at;
                self.mint_one(&goal.shift_global(grew), &lvl, prefer.as_deref());
            }
        }
        self.pending_derived.borrow_mut().clear();
    }

    fn mint_one(&mut self, goal: &Type, lvl: &Level, prefer: Option<&str>) {
        let cx = Cx::empty();
        if self.derived_hit(&cx, goal, prefer).is_some() {
            return;
        }
        let mut tr = Vec::new();
        let span = Span { start: 0, end: 0 };
        let Some(term) =
            self.resolve_goal(&cx, goal, lvl, "a derived instance", prefer, span, &mut tr)
        else {
            return;
        };
        // A derivation that reached into a scope is not a global; a goal that
        // is not closed has no statement. Both are asked of the kernel rather
        // than tracked, and a failure costs sharing, never correctness.
        if !self.type_is_closed(goal, lvl) {
            return;
        }
        let ok = stats::time_kernel(|| {
            typing::check_term(
                &self.psi,
                0,
                Layer::Code,
                &LocalCtx::nil(),
                &term,
                goal,
                lvl,
                self.fuel,
            )
            .is_ok()
        });
        if !ok {
            return;
        }
        let name = format!("#derived{}", self.traits.derived().len());
        let abs = self.psi.bindings.len() as u32;
        self.psi.push(GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(goal.clone()),
            level: lvl.clone(),
            // A `fn`, not a `theorem`: the whole point of the canonical name
            // is that "which multiplication is this" is answered by unfolding
            // it (record §6.1).
            body: Some(Rc::new(term)),
        });
        let derived = DerivedInst {
            name,
            abs,
            ty: goal.clone(),
            level: lvl.clone(),
            // The Ψ length *before* the push above — the world the stored
            // type is scoped in.
            at: abs,
            head: prefer.map(str::to_string),
        };
        self.semantic_commit_derived(derived);
        self.refresh_delta_psi();
    }
}
