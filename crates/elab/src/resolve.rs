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

use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, GlobalVar, LocalCtx, LocalSubst, SubstTail, Term, Type};
use heather_kernel::typing;
use heather_syntax::{Expr, ExprKind, Span, TyKind};

use crate::oracle::Unfold;
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

/// The reduction allowance for the **computation** source at a proposition
/// goal (docs/positivity-evidence-design.md §6 A): `trivial` is proposed only
/// when the goal reduces to `True` within this much work. A goal whose
/// operands are large closed computations is not worth proving this way, and
/// an inconclusive check is a miss that falls through to the rules.
const COMPUTE_FUEL: u64 = 1 << 12;


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

/// The head an **open** derivation is filed under ([`Elaborator::record_open`]):
/// this prefix and the goal class's key. A lookup compares only the entries
/// of its own class, and the closed table's lookups none of them.
const OPEN_HEAD: &str = "#open:";

pub(crate) fn is_open_head(head: Option<&str>) -> bool {
    head.is_some_and(|h| h.starts_with(OPEN_HEAD))
}

/// `t`, read out of the goal world into the committed Ψ: its committed
/// globals renumbered down past the `pad` goals, or `None` if it mentions a
/// goal (the test [`Elaborator::record_joined`] makes of a type).
fn below_goals_ty(t: &Type, pad: u32) -> Option<Type> {
    if pad == 0 {
        return Some(t.clone());
    }
    let down = t.apply_global(&goal_markers(pad));
    (down.shift_global(pad) == *t).then_some(down)
}

/// [`below_goals_ty`] for a term.
fn below_goals_tm(t: &Term, pad: u32) -> Option<Term> {
    if pad == 0 {
        return Some(t.clone());
    }
    let down = t.apply_global(&goal_markers(pad));
    (down.shift_global(pad) == *t).then_some(down)
}

fn goal_markers(pad: u32) -> heather_kernel::subst::GlobalSubst {
    heather_kernel::subst::GlobalSubst {
        entries: (0..pad).map(|_| heather_kernel::subst::GlobalEntry::Tm(Rc::new(Term::Zero))).collect(),
    }
}

/// The binders an open derivation's type abstracts, outermost first, and
/// what is left under them.
fn open_telescope(ty: &Type) -> (Vec<&Rc<Type>>, &Type) {
    let mut doms = Vec::new();
    let mut cur = ty;
    while let Type::Pi { dom, cod, .. } = cur {
        doms.push(dom);
        cur = cod;
    }
    (doms, cur)
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

/// One `positivity` run's memory (docs/positivity-evidence-design.md §10):
/// the subgoals omega was already stuck on. Every subgoal of one run is
/// elaborated in the caller's context, since rules bind nothing, so a goal is
/// compared by syntax.
#[derive(Clone, Default)]
pub(crate) struct PositivityRun {
    stuck: Vec<Type>,
}

/// Everything a rejected proposition candidate may have left behind, so it
/// can be undone: its dependency edges, its checking notes, and (an `omega`
/// inside `positivity`) its named atom lists, warnings and Omega reports.
pub(crate) struct SearchMark {
    dependencies: usize,
    notes: usize,
    goals: usize,
    warnings: usize,
    omega_reports: usize,
    omega_failures: usize,
}

impl SearchMark {
    pub(crate) fn of(e: &Elaborator) -> Self {
        SearchMark {
            dependencies: e.attempt.direct_dependencies.borrow().mark(),
            notes: e.attempt.check_notes.borrow().len(),
            goals: e.attempt.goal_arena.mark(),
            warnings: e.pass.warnings.borrow().len(),
            omega_reports: e.pass.omega_reports.borrow().len(),
            omega_failures: e.pass.omega_failure_reports.borrow().len(),
        }
    }

    pub(crate) fn rollback(self, e: &Elaborator) {
        e.attempt.direct_dependencies.borrow_mut().rollback(self.dependencies);
        e.attempt.check_notes.borrow_mut().truncate(self.notes);
        e.attempt.goal_arena.rollback(self.goals);
        e.pass.warnings.borrow_mut().truncate(self.warnings);
        e.pass.omega_reports.borrow_mut().truncate(self.omega_reports);
        e.pass.omega_failure_reports.borrow_mut().truncate(self.omega_failures);
    }
}

impl Elaborator {
    /// The surface shape an `evidence theorem` must have before it is
    /// elaborated (docs/positivity-evidence-design.md §6 A). A rule is applied
    /// by search, so search has to be able to fill every parameter: a `{…}`
    /// value is solved by unifying the conclusion with the goal, and a
    /// premise is `:= infer`, resolved by the same search.
    pub(crate) fn evidence_shape(&self, decl: &heather_syntax::Decl) -> crate::R<()> {
        if decl.kind != heather_syntax::DeclKind::Theorem || decl.decreases.is_some() {
            return Err(ElabError::Elab {
                msg: "`evidence` marks a `theorem`: a rule is a proof `:= infer` applies, \
                      and only a theorem is one"
                    .into(),
                span: decl.span,
            });
        }
        if let Some(p) = decl.params.iter().find(|p| !p.implicit && p.solver.is_none()) {
            return Err(ElabError::Elab {
                msg: format!(
                    "`{}` is an explicit parameter, but an evidence rule is applied by \
                     search, which has no argument to give it: write it `{{{}: …}}` if \
                     the conclusion determines it, or `{}: … := infer` if it is a premise \
                     (docs/positivity-evidence-design.md §6 A)",
                    p.name, p.name, p.name
                ),
                span: p.span,
            });
        }
        Ok(())
    }

    /// Register a checked `evidence theorem`: key it by its conclusion's
    /// relation and check that backchaining through it terminates.
    ///
    /// Termination is Paterson's condition, the one instances obey
    /// (docs/traits-layer2-design.md §6), read on the checked statement: each
    /// `:= infer` premise is strictly smaller than the conclusion and mentions
    /// no binder more often. Every step of a search through rules then
    /// shrinks the goal, so no rule can loop, alone or with others.
    pub(crate) fn register_evidence(&mut self, decl: &heather_syntax::Decl) -> crate::R<()> {
        let refuse = |msg: String| Err(ElabError::Elab { msg, span: decl.span });
        let Some(key) = self.key_of(&decl.name) else {
            return refuse(format!("`{}` is not a declared global", decl.name));
        };
        let Some(info) = self.names.global(&key) else {
            return refuse(format!("`{}` is not a declared global", decl.name));
        };
        let abs = info.abs as usize;
        let params = Rc::clone(&info.params);
        let Some(GlobalBinding::Tm { ty, .. }) = self.psi.bindings.get(abs) else {
            return refuse(format!("`{}` is not a term declaration", decl.name));
        };
        let ty = Rc::clone(ty);
        // Peel the telescope, keeping each premise's domain and the number of
        // binders above it.
        let mut premises = Vec::new();
        let mut binders = 0u32;
        let mut cur: &Type = &ty;
        while let Type::Pi { dom, cod, .. } = cur {
            if params.get(binders as usize).is_some_and(|p| p.solver.is_some()) {
                premises.push((binders, Rc::clone(dom)));
            }
            binders += 1;
            cur = cod;
        }
        let conclusion = cur;
        let name_of = |v: GlobalVar| {
            abs.checked_sub(v.0 as usize + 1)
                .and_then(|g| self.names.global_name_at(g as u32).map(str::to_string))
        };
        let Some((relation, heads)) = proposition_key(conclusion, &name_of) else {
            return refuse(format!(
                "the conclusion of `{}` is not a relation applied to arguments \
                 (`0 < a * b`), so no goal could select it as an evidence rule",
                decl.name
            ));
        };
        let concl = Measure::of(conclusion, binders);
        for (at, dom) in &premises {
            // A dictionary premise (a rule stated in a section over a class,
            // `<A: OrderedField(…)>`) is a class goal: the instance registry
            // answers it, under the instances' own decrease check, and no
            // evidence rule is about a class, so it cannot lead back into
            // this rule set (docs/division-design.md §6).
            let written_class = params
                .get(*at as usize)
                .and_then(|p| p.solver.as_deref())
                .and_then(written_head)
                .is_some_and(|name| self.key_of(name).is_some_and(|k| self.traits.has_class(&k)));
            if written_class
                || self.tag_of(dom).is_some_and(|ind| {
                    self.traits.has_class(&crate::names::qkey(&ind.scope.module, &ind.name))
                })
            {
                continue;
            }
            let premise = Measure::of(dom, *at);
            if !premise.smaller_than(&concl) {
                let name = params.get(*at as usize).map_or("?", |p| p.name.as_str());
                return refuse(format!(
                    "the premise `{name}` of evidence rule `{}` is not smaller than its \
                     conclusion, so a search through it might not terminate: each premise \
                     must have fewer symbols than the conclusion and mention no variable \
                     more often (docs/traits-layer2-design.md §6)",
                    decl.name
                ));
            }
        }
        if self.traits.has_evidence(&key) {
            return refuse(format!("`{}` is already an evidence rule", decl.name));
        }
        self.semantic_commit_evidence(crate::traits::EvidenceRule { global: key, relation, heads });
        Ok(())
    }

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
        // Trait/instance resolution's own phase column
        // (`docs/instrumentation-design.md` §5). Backchaining recurses through
        // here; the registry's exclusive rule charges each nesting level only
        // its own share, so the column is search time and not search time
        // times depth.
        crate::stats::count(crate::stats::Counter::ResolveGoals);
        let _phase = crate::stats::guard(crate::stats::Timer::Resolve);
        // The goal in the **inline** spelling: it may arrive off a respelled
        // binder type or statement, where a parameterized class instantiation
        // is `El (app(C#tycode_fn^δ; ā))`, and every structural read below —
        // starting with the class lookup — is written against the lowering
        // (`docs/per-instantiation-type-codes-design.md` §4.2, amended
        // 2026-09-10; `docs/wf-shape-code-design.md` §4). One head unspell at
        // the entry, so the whole search sees one spelling.
        let spelled = goal;
        let inline = self.unspell_here(goal);
        let goal = inline.as_ref().unwrap_or(goal);
        let depth = self.scope.resolve_depth.get();
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
        // A merged class's assembly is minted at its applied spelling (step
        // 2b), which the inline lowering does not convert to within the
        // table's lookup fuel.
        if inline.is_some() && self.tag_of(goal).is_some_and(|i| i.name.contains('+')) {
            if let Some(t) = self.joined_hit(cx, spelled, prefer) {
                return Some(t);
            }
        }

        // 1. Ascending scopes: locals innermost-first, then `let` aliases.
        //    "An explicit value in scope always wins over derivation" is this
        //    step returning before step 2 runs (design §3).
        for pos in (0..cx.names.len()).rev() {
            let (t, ty, l) = self.local(cx, pos);
            if self.conv_here(cx, &ty, goal, &l) {
                tr.push(line(depth, "local", cx.names[pos].to_string()));
                return Some(t);
            }
        }
        for a in cx.aliases.iter_inner() {
            let by = (cx.names.len() - a.depth) as u32;
            let ty = a.ty.shift_local(by);
            if self.conv_here(cx, &ty, goal, &a.level) {
                tr.push(line(depth, "local", format!("{} (a `let`)", a.name)));
                // Read, not spliced (`Alias::splice`): a search's answer can
                // still be dropped by its caller, so a `let` found here is
                // left for its block to discard if nothing else uses it.
                return Some((*a.term).shift_local(by));
            }
        }
        // 1b. The same scope again, by **upcast**: a dictionary of a *child*
        //     class answers an ancestor's goal, through the canonical parent
        //     projection (docs/traits-owner-dispatch-design.md §3). After the
        //     exact pass, because an exactly-typed value in scope is the one
        //     the writer named; before the registry, because this is still a
        //     scope answer and not a derivation.
        // 1a. An open derivation minted by an earlier item: the same upcast
        //     or merged-class assembly at the same context prefix, reached
        //     as an application of its global (`Self::record_open`).
        if let Some((t, who, src)) = self.open_hit(cx, goal, lvl) {
            tr.push(line(depth, "local", who));
            if let Some(src) = src {
                *up = Some(src);
            }
            return Some(t);
        }
        if let Some((t, who, src)) = self.scope_upcast(cx, goal, lvl, span) {
            tr.push(line(depth, "local", who));
            self.record_open(cx, goal, lvl, &t);
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
            return self.resolve_proposition(cx, goal, lvl, span, depth, tr);
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
            if let Some(t) = self.join_parents(cx, &ind, &ckey, spelled, goal, lvl, prefer, span, depth, tr) {
                return Some(t);
            }
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
            let dependency_mark = self.attempt.direct_dependencies.borrow().mark();
            // Likewise its checking mismatches: a candidate built at the goal
            // records one wherever it is not of the goal type, and that is
            // the search answering "no", not a site the gate could later
            // blame — `Bool::Monoid` at `and` while `or` was asked
            // (issues/width-specific-method-on-other-width.md).
            let notes_mark = self.attempt.check_notes.borrow().len();
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
            // A conclusion that cannot meet the goal is dropped unbuilt.
            if self.conclusion_clashes(cx, &g, goal, span) {
                crate::stats::count(crate::stats::Counter::ConclusionClashes);
                tr.push(line(depth + 1, "rejected", "conclusion does not match".to_string()));
                continue;
            }
            self.scope.resolve_depth.set(depth + 1);
            let built = self.build_candidate(cx, &g, goal, lvl, span);
            self.scope.resolve_depth.set(depth);
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
            self.attempt.direct_dependencies.borrow_mut().rollback(dependency_mark);
            self.attempt.check_notes.borrow_mut().truncate(notes_mark);
        }
        self.join_parents(cx, &ind, &ckey, spelled, goal, lvl, prefer, span, depth, tr)
    }

    /// Step 2b: a **merged** class — the one a declaration's constraints
    /// sharing symbols at one carrier became (`merge_linked_constraints`,
    /// issues/constraints-sharing-indices.md) — has no instances of its own,
    /// and is assembled from its parents' at the goal: each parent's type is
    /// read off the goal's own arguments, resolved, and every field of the
    /// merged record is read off the first parent that has it.
    ///
    /// At a concrete carrier the parents' shared ancestor is one canonical
    /// instance reached by reference from both (traits-design §4), so the
    /// fields agree and the record checks; at an open carrier with no merged
    /// dictionary in scope they need not, and the kernel gate below says no.
    /// A closed answer is queued for the canonical table like any derivation,
    /// so a carrier pays for its assembly once.
    #[allow(clippy::too_many_arguments)]
    fn join_parents(
        &self,
        cx: &Cx,
        ind: &crate::inductive::Inductive,
        ckey: &str,
        spelled: &Type,
        goal: &Type,
        lvl: &Level,
        prefer: Option<&str>,
        span: Span,
        depth: usize,
        tr: &mut Vec<TraceLine>,
    ) -> Option<Term> {
        if !ind.name.contains('+') || !ind.is_record {
            return None;
        }
        let class = self.traits.class(ckey)?.clone();
        if class.is_kinded() {
            return None;
        }
        // The goal's arguments: off its applied spelling when it arrived
        // spelled (unsolved operations stay goals there, which the parents'
        // searches solve by unification as a registry candidate would), else
        // matched off the inline lowering.
        let read = match spelled {
            Type::El { tm, .. } => match self.gen_app_of(tm) {
                Some((crate::gendefs::GenDef::TyCodeFn(tag), args)) if tag == ind.tag => Some(args),
                _ => None,
            },
            _ => None,
        };
        let args = match read {
            Some(args) => args,
            None => self.instance_match(cx, ind, goal, 0, 0)?.1,
        };
        let np = class.params.len();
        if args.len() != np + class.valparams.len() {
            return None;
        }
        let parts: Vec<&str> = ind.name.split('+').collect();
        let mut tcx = cx.clone();
        let mut parents: Vec<(String, Rc<crate::inductive::Inductive>)> = Vec::new();
        // The parents are the ancestors the name lists; a transitive ancestor
        // need not even be nameable from here.
        let bare = |n: &str| n.rsplit("::").next().unwrap_or(n).to_string();
        for (k, a) in class
            .ancestors
            .iter()
            .filter(|a| a.path.is_empty() && parts.contains(&bare(&a.name).as_str()))
            .enumerate()
        {
            let akey = self.key_of(&a.name)?;
            let ainfo = self.traits.class(&akey)?;
            if !parts.contains(&ainfo.name.as_str()) {
                continue;
            }
            let aind = self.types.inductive(&akey)?.clone();
            // The parent's arguments are the merged class's own, by name: its
            // type arguments are the class's parameters and its index the
            // class's value parameters (`merge_linked_constraints` writes
            // nothing else).
            let mut aargs: Vec<Rc<Term>> = Vec::new();
            for t in &a.args {
                let TyKind::Named { name, args: targs } = &t.kind else { return None };
                if !targs.is_empty() {
                    return None;
                }
                aargs.push(Rc::clone(&args[class.params.iter().position(|p| p == name)?]));
            }
            for e in &a.index {
                let ExprKind::Var(name) = &e.kind else { return None };
                let at = class.valparams.iter().position(|v| v.name == *name)?;
                aargs.push(Rc::clone(&args[np + at]));
            }
            let (aty, alvl) = self.instance_type_at(cx, aind.tag, &aargs)?;
            tr.push(line(depth, "join", format!("`{}` from `{}`", ind.name, ainfo.name)));
            self.scope.resolve_depth.set(depth + 1);
            let shown = ainfo.name.clone();
            let got = self.resolve_goal(cx, &aty, &alvl, &shown, prefer, span, tr);
            self.scope.resolve_depth.set(depth);
            let got = got?;
            let alias = format!("#join{k}");
            tcx.aliases.push(Rc::new(crate::Alias {
                name: alias.clone(),
                depth: cx.names.len(),
                term: Rc::new(got),
                ty: aty,
                level: alvl,
                skel: None,
                spliced: None,
                shifted: Default::default(),
            }));
            parents.push((alias, aind));
        }
        let mut fields = Vec::with_capacity(ind.ctors[0].fields.len());
        for (n, _) in &ind.ctors[0].fields {
            let n = n.clone()?;
            let (alias, _) = parents
                .iter()
                .find(|(_, p)| p.ctors[0].fields.iter().any(|(m, _)| m.as_deref() == Some(n.as_str())))?;
            fields.push(Expr {
                kind: ExprKind::Dot {
                    recv: Box::new(Expr { kind: ExprKind::Var(alias.clone()), span }),
                    name: n,
                    tyargs: Vec::new(),
                    args: None,
                    named: Vec::new(),
                },
                span,
            });
        }
        let t = self.build_ctor(&tcx, ind, 0, &fields, goal, lvl, span).ok()?;
        if !self.checks_at(cx, &t, goal, lvl) {
            tr.push(line(depth, "rejected", "the parents' fields disagree here".to_string()));
            return None;
        }
        self.record_joined(cx, spelled, lvl, prefer);
        self.record_open(cx, goal, lvl, &t);
        Some(t)
    }

    /// Steps 3 to 5 at a goal that is not a class: **computation**, the
    /// **evidence rules** about the goal's relation
    /// (docs/positivity-evidence-design.md §6 A), and, only inside a
    /// `positivity` run, **omega** (§10). Locals and derivations have already
    /// had their turn, so an exact proof in scope still wins.
    fn resolve_proposition(
        &self,
        cx: &Cx,
        goal: &Type,
        lvl: &Level,
        span: Span,
        depth: usize,
        tr: &mut Vec<TraceLine>,
    ) -> Option<Term> {
        self.computed_or_ruled(cx, goal, lvl, span, depth, tr)
            .or_else(|| self.positivity_omega(cx, goal, lvl, span, depth, tr))
    }

    fn computed_or_ruled(
        &self,
        cx: &Cx,
        goal: &Type,
        lvl: &Level,
        span: Span,
        depth: usize,
        tr: &mut Vec<TraceLine>,
    ) -> Option<Term> {
        // 3. Computation. `0 < Succ(k)` and `0 < 5` reduce to `True`, whose η
        //    makes `trivial` its proof; the kernel at bounded fuel decides.
        let trivial = Term::Triv { level: lvl.clone() };
        let psi = self.goal_psi();
        let computes = stats::time_kernel(|| {
            typing::check_term(
                &psi, 0, Layer::Code, &cx.gamma, &trivial, goal, lvl,
                self.policy.fuel.min(COMPUTE_FUEL),
            )
            .is_ok()
        });
        if computes {
            tr.push(line(depth, "computed", "the goal reduces to `True`"));
            return Some(trivial);
        }
        // 4. The evidence rules, keyed by the goal's relation.
        let name_of = |v: GlobalVar| {
            self.global_abs_of(v)
                .and_then(|abs| self.names.global_name_at(abs as u32).map(str::to_string))
        };
        let Some((relation, mut heads)) = proposition_key(goal, &name_of) else {
            tr.push(line(depth, "no-rule", "the goal is not a relation applied to arguments"));
            return None;
        };
        // A goal argument headed by a local is neutral for good (a local has
        // no definition to unfold), so it can only meet a rule binder: a
        // rule whose argument has a head (`a * b`) is not worth a trial.
        // Only the goal side is read this way; a rule's binders stay
        // wildcards.
        for (head, arg) in heads.iter_mut().zip(proposition_args(goal)) {
            if head.is_none() && matches!(crate::spelling::app_spine(arg).0, Term::Var(_)) {
                *head = Some("#local".into());
            }
        }
        // A relation no rule is about at all may be a *computed* proposition
        // (`PowOk(x, n)`, a sign-dependent side condition): search what it
        // computes to, the first reduct whose head some rule is about.
        if self.traits.evidence_rules(&relation).is_empty()
            && let Some(unfolded) = self.unfolded_to_ruled(cx, goal, &relation)
        {
            tr.push(line(
                depth,
                "unfolded",
                format!(
                    "`{}` has no rules; searching what it computes to",
                    short_name(&relation)
                ),
            ));
            return self.computed_or_ruled(cx, &unfolded, lvl, span, depth + 1, tr);
        }
        let rules: Vec<_> = self
            .traits
            .evidence_rules(&relation)
            .iter()
            .filter(|rule| {
                rule.heads.len() == heads.len()
                    && rule.heads.iter().zip(&heads).all(|(r, g)| heads_may_agree(r.as_deref(), g.as_deref()))
            })
            .map(|rule| rule.global.clone())
            .filter(|g| !self.rule_clashes(g, goal))
            .collect();
        // A **search rule** (docs/facts-on-demand-design.md §3) is a rule
        // with a premise that runs a tactic, `h: P := omega`: a producer that
        // may cost a search. Every plain rule is tried first, in canonical
        // order, and the search rules after them, so a goal a cheap producer
        // answers never pays for a search.
        let (mut rules, search): (Vec<_>, Vec<_>) = rules.into_iter().partition(|g| !self.is_search_rule(g));
        // Rules stated over a class go weakest class first (a stable sort,
        // so canonical order within one class). The weakest statement of a
        // decomposition is the one with the plainest premises: at a sum,
        // `OrderedAddMonoid::positive_add` asks for two signs, the located
        // monoid's mixed rules ask for a nonnegative, which a search rule
        // answers by a `linarith` run, and canonical order alone would try
        // them first (docs/division-design.md §6).
        if rules.len() > 1 {
            rules.sort_by_cached_key(|g| self.rule_class_rank(g));
        }
        // Inside an arithmetic tactic's own run (`linarith`, `ring`,
        // `omega` reading and checking their certificates) no search rule
        // runs: its tactic would start another such run, whose reading can
        // meet the same goal again (a reciprocal's apartness, read while
        // `nlinarith` reads the context that mentions it), and the nesting
        // is bounded only by the depth cap, exponentially. Plain rules still
        // answer there (docs/division-design.md §3).
        if self.scope.ring_depth.get() == 0 && self.scope.omega_depth.get() == 0 {
            rules.extend(search);
        }
        if rules.is_empty() {
            tr.push(line(
                depth,
                "no-rule",
                format!("no evidence rule about `{}` fits", short_name(&relation)),
            ));
            return None;
        }
        tr.push(line(
            depth,
            "rules",
            format!("{} ({} rule(s))", short_name(&relation), rules.len()),
        ));
        for g in rules {
            // A rejected rule is search state, exactly as a rejected instance
            // is: neither its edges nor its checking notes survive it. Nor,
            // inside `positivity`, does an `omega` a premise of it ran: its
            // named atom list and its audit report go with it.
            let mark = SearchMark::of(self);
            tr.push(line(depth, "candidate", g.clone()));
            self.scope.resolve_depth.set(depth + 1);
            let built = self.scoped_cell(|s| &s.rule_citation, Some(g.clone()), || {
                self.build_candidate(cx, &g, goal, lvl, span)
            });
            self.scope.resolve_depth.set(depth);
            match built {
                Ok(t) if self.checks_at(cx, &t, goal, lvl) => return Some(t),
                Ok(_) => tr.push(line(
                    depth + 1,
                    "rejected",
                    "built, but not of the goal type".to_string(),
                )),
                Err(ElabError::Resolution { trace, .. }) => {
                    tr.extend(trace.iter().map(|l| TraceLine {
                        depth: l.depth + 1,
                        key: l.key,
                        value: l.value.clone(),
                    }));
                }
                Err(e) => tr.push(line(depth + 1, "rejected", e.message())),
            }
            mark.rollback(self);
        }
        None
    }

    /// The first reduct of `goal` headed by a relation other than `relation`
    /// that some evidence rule is about, within [`Unfold::RuleGoal`]. Stepping
    /// one reduct at a time rather than taking the weak head normal form is
    /// the point: the normal form of `PowOk(x, -1)` is `x.Apart(0)`'s own
    /// disjunction, which no rule is keyed by.
    fn unfolded_to_ruled(&self, cx: &Cx, goal: &Type, relation: &str) -> Option<Type> {
        let Type::El { level, tm } = goal else {
            return None;
        };
        let name_of = |v: GlobalVar| {
            self.global_abs_of(v)
                .and_then(|abs| self.names.global_name_at(abs as u32).map(str::to_string))
        };
        let oracle = self.goal_oracle();
        for reduct in oracle.unfold(&cx.gamma, tm, Unfold::RuleGoal) {
            let unfolded = Type::El { level: level.clone(), tm: Rc::new(reduct) };
            // The first relation the goal reaches decides: a rule about it,
            // or nothing. Stepping on through a rule-less relation would
            // unfold its arithmetic (`Rat::Lt` into `Int::Lt` into `Nat`'s
            // recursor) at every failing proposition goal, which on closed
            // operands is the whole cost of the search.
            if let Some((next, _)) = proposition_key(&unfolded, &name_of)
                && next != relation
            {
                return (!self.traits.evidence_rules(&next).is_empty()).then_some(unfolded);
            }
        }
        None
    }

    /// The `positivity` tactic (docs/positivity-evidence-design.md §10): the
    /// search `:= infer` runs at `goal`, with one more source at every
    /// proposition subgoal, `omega`, tried after the evidence rules. Cheap
    /// routes first: a local, computation and a rule are each one kernel
    /// trial, and omega runs only where they all failed, so `0 < a * b` with
    /// `3 <= a` and `0 < b` in scope costs one omega call, at `0 < a`.
    pub(crate) fn positivity(&self, cx: &Cx, goal: &Type, lvl: &Level, span: Span) -> crate::R<Term> {
        let spelled = self
            .spell_type_clean(cx, goal)
            .unwrap_or_else(|| "the goal".to_string());
        let mut tr = Vec::new();
        let found = self.scoped_cell(|s| &s.positivity, Some(PositivityRun::default()), || {
            self.resolve_goal(cx, goal, lvl, &spelled, None, span, &mut tr)
        });
        found.ok_or_else(|| ElabError::Elab {
            msg: format!("`positivity` could not prove `{spelled}` — the search:{}", render_trace(&tr)),
            span,
        })
    }

    /// The search a `:= infer` parameter runs at a proposition goal, as a
    /// term: what fills a `Pos<A>` record field's fact
    /// (`heather_syntax::POS_SEARCH`). Outside any `positivity` run, so omega
    /// is not a source, exactly as at a parameter.
    pub(crate) fn infer_proposition(&self, cx: &Cx, goal: &Type, lvl: &Level, span: Span) -> crate::R<Term> {
        let spelled = self
            .spell_type_clean(cx, goal)
            .unwrap_or_else(|| "the goal".to_string());
        let mut tr = Vec::new();
        let found = self.scoped_cell(|s| &s.positivity, None, || {
            self.resolve_goal(cx, goal, lvl, &spelled, None, span, &mut tr)
        });
        found.ok_or_else(|| ElabError::Elab {
            msg: format!("no evidence for `{spelled}` — the search:{}", render_trace(&tr)),
            span,
        })
    }

    /// Step 5, inside a `positivity` run only: hand the goal to `omega`. A
    /// goal omega was stuck on once in this run is not tried again, which
    /// bounds a failing run at one omega call per distinct subgoal.
    fn positivity_omega(
        &self,
        cx: &Cx,
        goal: &Type,
        lvl: &Level,
        span: Span,
        depth: usize,
        tr: &mut Vec<TraceLine>,
    ) -> Option<Term> {
        let stuck_before = match &*self.scope.positivity.borrow() {
            None => return None,
            Some(run) => run.stuck.iter().any(|g| g == goal),
        };
        if self.key_of("omega::nat_le_of_not_not_le").is_none() {
            tr.push(line(depth, "omega", "not imported, so not tried (`import omega;`)"));
            return None;
        }
        if self.shadowed(cx, "omega") {
            tr.push(line(depth, "omega", "a local named `omega` shadows the tactic"));
            return None;
        }
        if stuck_before {
            tr.push(line(depth, "omega", "already stuck on this goal"));
            return None;
        }
        // Omega's own certificate is elaborated with plain `infer`: a
        // positivity run does not reach into it.
        let mark = SearchMark::of(self);
        let e = Expr {
            kind: ExprKind::Var("omega".to_string()),
            span,
        };
        let proved = self.scoped_cell(|s| &s.positivity, None, || self.elab_check(cx, &e, goal, lvl));
        match proved {
            Ok(t) => {
                tr.push(line(depth, "omega", "proved"));
                Some(t)
            }
            Err(err) => {
                mark.rollback(self);
                // Omega's own report (atoms, residual, locals) is pages
                // long; the trace keeps its verdict, and `omega` written at
                // the goal still gives the whole report.
                let msg = err.message();
                let verdict = msg.lines().next().unwrap_or_default();
                let verdict = verdict.split(';').next().unwrap_or_default();
                tr.push(line(depth, "omega", verdict.to_string()));
                if let Some(run) = self.scope.positivity.borrow_mut().as_mut() {
                    run.stuck.push(goal.clone());
                }
                None
            }
        }
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
        let mut e = Expr {
            kind: ExprKind::Var(global.to_string()),
            span,
        };
        // A bare reference fills implicits and solver parameters but leaves
        // a defaulted parameter to a call (docs/named-arguments-design.md
        // §9.6), so a search rule is built as the call that names nothing:
        // its tactic premises run as their defaults, in the goal's context.
        if self.is_search_rule(global) {
            e = Expr {
                kind: ExprKind::App { head: Box::new(e), args: Vec::new(), named: Vec::new(), explicit: false, goal_oriented: false },
                span,
            };
        }
        self.elab_check(cx, &e, goal, lvl)
    }

    /// Can the rule's conclusion be told apart from the goal without trying
    /// it? Read as a first-order pattern, its binders matched against the
    /// goal's arguments along application spines: a binder the match would
    /// have to set to two different locals cannot fit, since two locals are
    /// never convertible. That is what tells a rule stated over a class,
    /// whose operations are its own binders, from a goal at another
    /// operation: `OrderedField::invertible_mul`'s conclusion
    /// `Invertible(…, *, …, x * y)` against `Invertible(…, *, …, c + d)`
    /// would set its `*` binder to the goal's `*` and its `+` both. An
    /// applied binder against a bare local cannot fit either (a first-order
    /// match has nothing to put there). Anything else (a global, a
    /// projection) says nothing, so a rule is skipped only when it fails.
    fn rule_clashes(&self, global: &str, goal: &Type) -> bool {
        let Some(info) = self.names.global(global) else {
            return false;
        };
        let Some(GlobalBinding::Tm { ty, .. }) = self.psi.bindings.get(info.abs as usize) else {
            return false;
        };
        let mut binders = 0u32;
        let mut cur: &Type = ty;
        while let Type::Pi { cod, .. } = cur {
            binders += 1;
            cur = cod;
        }
        let rule_args = proposition_args(cur);
        let goal_args = proposition_args(goal);
        if rule_args.len() != goal_args.len() {
            return false;
        }
        let mut assigned: Vec<(u32, u32)> = Vec::new();
        rule_args
            .iter()
            .zip(&goal_args)
            .any(|(r, g)| pattern_clashes(r, g, binders, &mut assigned))
    }

    /// How many ancestors the class a rule is stated over has (its section's
    /// dictionary premise), `0` for a rule over no class: the order
    /// [`Self::computed_or_ruled`] tries rules in. The class is read off the
    /// premise as written, in the rule's own module, which the caller may
    /// reach only through an import ([`crate::names::Names::reaches`]).
    fn rule_class_rank(&self, global: &str) -> usize {
        let Some(info) = self.names.global(global) else { return 0 };
        let Some((module, _)) = crate::names::split_qual(global) else { return 0 };
        let Some(scope) = self.names.module_scope(module) else { return 0 };
        for p in info.params.iter() {
            let Some(head) = p.solver.as_deref().and_then(written_head) else { continue };
            let found = self.names.resolve_kinds(Some(scope), head, crate::names::ANY_KIND, |_, _, _| false);
            let crate::names::NameRes::Found(origin) = found else { continue };
            let base = crate::names::split_qual(head).map_or(head, |(_, b)| b);
            if let Some(class) = self.traits.class(&crate::names::qkey(&origin, base)) {
                return class.ancestors.len();
            }
        }
        0
    }

    /// Does the global have a defaulted parameter: is it, as an evidence
    /// rule, a search rule (docs/facts-on-demand-design.md §3)? Read off the
    /// declaration's parameter table, so nothing new is stored in an image.
    pub(crate) fn is_search_rule(&self, global: &str) -> bool {
        self.names
            .global(global)
            .is_some_and(|info| info.params.iter().any(|p| p.default.is_some()))
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
        // By the tag's declaration, not the name: the goal's class may be a
        // parent the client never imported (`MonoidRel` under `Monoid`).
        let ckey = crate::names::qkey(&cind.scope.module, &cind.name);
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
                    format!("{} (upcast to `{}`)", &cx.names[pos], cind.name),
                    (t, ty),
                ));
            }
        }
        for a in cx.aliases.iter_inner() {
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
        let dkey = crate::names::qkey(&dind.scope.module, &dind.name);
        let dinfo = self.traits.class(&dkey)?;
        let mut tcx = cx.clone();
        tcx.aliases.push(Rc::new(crate::Alias {
            name: "#dict".into(),
            depth: cx.names.len(),
            term: Rc::new(dict.clone()),
            ty: dict_ty.clone(),
            level: dict_lvl.clone(),
            skel: None,
            spliced: None,
            shifted: Default::default(),
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
                        tyargs: Vec::new(),
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
                        tyargs: Vec::new(),
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
            typing::check_term(&psi, 0, Layer::Code, &cx.gamma, t, goal, lvl, self.policy.fuel).is_ok()
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
            oracle::SemanticOracle::in_world(self.goal_psi(), self.policy.fuel.min(DERIVED_LOOKUP_FUEL))
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
            .filter(|d| !is_open_head(d.head.as_deref()) && heads_may_agree(d.head.as_deref(), prefer))
            .find(|d| self.derived_conv(cx, &d.ty.shift_global(now - d.at), goal, &d.level))?;
        Some(self.derived_ref(d.abs))
    }

    /// [`Self::derived_hit`] for a merged class's assembly (step 2b), at the
    /// goal's applied spelling and in the goal world: a table entry's
    /// committed globals sit `global_padding` further out there. A
    /// tactic's certificate is elaborated with goals in flight, which is
    /// where nearly every such call is.
    fn joined_hit(&self, cx: &Cx, spelled: &Type, prefer: Option<&str>) -> Option<Term> {
        let now = self.psi.bindings.len() as u32;
        let pad = self.global_padding();
        let d = self
            .traits
            .derived()
            .iter()
            .filter(|d| !is_open_head(d.head.as_deref()) && heads_may_agree(d.head.as_deref(), prefer))
            .find(|d| {
                let ty = d.ty.shift_global(now - d.at);
                let ty = if pad == 0 { ty } else { weaken_global_below(&ty, pad) };
                self.derived_conv(cx, &ty, spelled, &d.level)
            })?;
        Some(self.derived_ref(d.abs))
    }

    /// Queue a merged class's assembly for the canonical table. Unlike
    /// [`Self::record_derived`] it accepts a goal met with goals in flight:
    /// the type is read out of the goal world (its committed globals
    /// renumbered down past the arena, refused if it mentions a goal) and
    /// out of the call's Γ (refused if it mentions a local), so the mint
    /// re-runs the search in the empty context of the committed Ψ.
    fn record_joined(&self, cx: &Cx, spelled: &Type, lvl: &Level, prefer: Option<&str>) {
        if !matches!(cx.gamma.base, heather_kernel::term::CtxBase::Nil) {
            return;
        }
        let n = cx.gamma.entries.len() as u32;
        let Some(local) = crate::unification::strengthen_ty(&LocalCtx::nil(), spelled, n) else {
            return;
        };
        let pad = self.global_padding();
        let closed = if pad == 0 {
            local
        } else {
            let down = local.apply_global(&heather_kernel::subst::GlobalSubst {
                entries: (0..pad).map(|_| heather_kernel::subst::GlobalEntry::Tm(Rc::new(Term::Zero))).collect(),
            });
            if weaken_global_below(&down, pad) != local {
                return;
            }
            down
        };
        if !self.type_is_closed(&closed, lvl) {
            return;
        }
        let mut pending = self.pass.pending_derived.borrow_mut();
        if pending.iter().any(|(t, l, _, head, open)| {
            open.is_none() && heads_may_agree(head.as_deref(), prefer) && self.derived_conv(&Cx::empty(), t, &closed, l)
        }) {
            return;
        }
        pending.push((closed, lvl.clone(), self.psi.bindings.len() as u32, prefer.map(str::to_string), None));
    }

    /// `f`'s answer at this scope and carrier, from [`Memos::scope_memo`]
    /// when the same scope asked before. For a tactic's reading of a class
    /// carrier that it elaborates from generated source; only an answer is
    /// kept, and the memo holds the last few scopes.
    ///
    /// [`Memos::scope_memo`]: crate::lifetimes::Memos::scope_memo
    pub(crate) fn scope_memo<T: Clone + Send + Sync + 'static>(
        &self,
        cx: &Cx,
        carrier: &Type,
        which: &'static str,
        f: impl FnOnce() -> Option<T>,
    ) -> Option<T> {
        const KEEP: usize = 8;
        let psi = self.psi.bindings.len() as u32;
        let pad = self.global_padding();
        let hit = self.memos.scope_memo.borrow().iter().find_map(|m| {
            (m.which == which
                && m.psi == psi
                && m.pad == pad
                && m.aliases.same(&cx.aliases)
                && m.dicts.same(&cx.dicts)
                && m.gamma == cx.gamma
                && m.carrier == *carrier)
                .then(|| m.value.downcast_ref::<T>().cloned())
                .flatten()
        });
        if hit.is_some() {
            return hit;
        }
        let value = f()?;
        let mut memo = self.memos.scope_memo.borrow_mut();
        if memo.len() >= KEEP {
            memo.remove(0);
        }
        memo.push(crate::lifetimes::ScopeMemo {
            which,
            psi,
            pad,
            gamma: cx.gamma.clone(),
            aliases: cx.aliases.clone(),
            dicts: cx.dicts.clone(),
            carrier: carrier.clone(),
            value: Rc::new(value.clone()),
        });
        Some(value)
    }

    /// Queue an **open** derivation: a class dictionary found at a class
    /// carrier, by upcast from a dictionary in scope (step 1b) or by a merged
    /// class's assembly (step 2b). Neither is closed, so the canonical table
    /// cannot take it; but both are built from the context's *prefix* alone
    /// (the section's carrier, its operations, its dictionary), and every
    /// item of that section repeats them. So the answer is abstracted over
    /// the shortest prefix of Γ that its goal and its value live in, and
    /// minted between items as one global of type `Π prefix. goal`; a later
    /// item with the same prefix reads it as that global applied to its own
    /// prefix variables ([`Self::open_hit`]). An assembled record is dozens of
    /// fields of projections, checked by the kernel at each use and carried
    /// in the proof term at each use; the application is a few nodes.
    ///
    /// The value is stored rather than re-searched, because a merged class's
    /// parents can come out of a `let` in scope (a tactic's certificate
    /// binds the integers it needs) that an empty context would not have.
    /// The mint checks it in the empty context; a failure costs sharing,
    /// never correctness.
    fn record_open(&self, cx: &Cx, goal: &Type, lvl: &Level, term: &Term) {
        if self.under_quotation() || !matches!(cx.gamma.base, heather_kernel::term::CtxBase::Nil) {
            return;
        }
        if matches!(goal, Type::Pi { .. }) {
            return; // the telescope must end at the goal (`open_telescope`)
        }
        let Some(ind) = self.tag_of(goal) else { return };
        let head = format!("{OPEN_HEAD}{}", crate::names::qkey(&ind.scope.module, &ind.name));
        let n = cx.gamma.entries.len() as u32;
        let prefix = |m: u32| {
            LocalCtx::from_vec(
                heather_kernel::term::CtxBase::Nil,
                (0..m as usize).map(|i| cx.gamma.entries[i].clone()).collect(),
            )
        };
        let fits = |m: u32| {
            let pre = prefix(m);
            let ty = crate::unification::strengthen_ty(&pre, goal, n - m)?;
            let tm = crate::unification::strengthen_tm(&pre, term, n - m)?;
            Some((ty, tm))
        };
        // The shortest prefix: strengthening is monotone in its length.
        let (mut lo, mut hi) = (0u32, n);
        while lo < hi {
            let mid = (lo + hi) / 2;
            if fits(mid).is_some() {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        let m = lo;
        if m == 0 {
            return; // closed: the canonical table's business
        }
        let Some((ty, tm)) = fits(m) else { return };
        let pad = self.global_padding();
        let (Some(ty), Some(tm)) = (below_goals_ty(&ty, pad), below_goals_tm(&tm, pad)) else {
            return;
        };
        let mut binders = Vec::with_capacity(m as usize);
        for i in 0..m as usize {
            let e = &cx.gamma.entries[i];
            let Some(t) = below_goals_ty(&e.ty, pad) else { return };
            binders.push((Rc::new(t), e.level.clone()));
        }
        let (mut ty, mut tm, mut level) = (ty, tm, lvl.clone());
        for (dom, dom_level) in binders.into_iter().rev() {
            tm = Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: level.clone(),
                dom: Rc::clone(&dom),
                body: Rc::new(tm),
            };
            ty = Type::Pi { dom_level: dom_level.clone(), cod_level: level.clone(), dom, cod: Rc::new(ty) };
            level = Level::join(dom_level, level);
        }
        let mut pending = self.pass.pending_derived.borrow_mut();
        if pending.iter().any(|(t, _, _, h, open)| open.is_some() && h.as_deref() == Some(head.as_str()) && *t == ty) {
            return;
        }
        pending.push((ty, level, self.psi.bindings.len() as u32, Some(head), Some(tm)));
    }

    /// Step 1a: a minted open derivation ([`Self::record_open`]) whose
    /// telescope is a prefix of Γ and whose goal, under it, is this one —
    /// the innermost such prefix, as step 1b takes the innermost dictionary.
    /// When the prefix ends in a dictionary of a descendant class, that is
    /// the answer's provenance, as step 1b reports it.
    fn open_hit(&self, cx: &Cx, goal: &Type, lvl: &Level) -> Option<(Term, String, Option<(Term, Type)>)> {
        if self.under_quotation() || !matches!(cx.gamma.base, heather_kernel::term::CtxBase::Nil) {
            return None;
        }
        let ind = self.tag_of(goal)?;
        if !ind.is_record {
            return None;
        }
        let ckey = crate::names::qkey(&ind.scope.module, &ind.name);
        let head = format!("{OPEN_HEAD}{ckey}");
        let n = cx.gamma.entries.len() as u32;
        let now = self.psi.bindings.len() as u32;
        let pad = self.global_padding();
        let mut best: Option<(u32, u32)> = None;
        for d in self.traits.derived().iter().filter(|d| d.head.as_deref() == Some(head.as_str())) {
            let ty = d.ty.shift_global(now - d.at);
            let ty = if pad == 0 { ty } else { weaken_global_below(&ty, pad) };
            let (doms, cod) = open_telescope(&ty);
            let m = doms.len() as u32;
            if m == 0 || m > n || best.is_some_and(|(_, b)| b >= m) {
                continue;
            }
            if !doms.iter().enumerate().all(|(i, dom)| *cx.gamma.entries[i].ty == ***dom) {
                continue;
            }
            if self.derived_conv(cx, &cod.shift_local(n - m), goal, lvl) {
                best = Some((d.abs, m));
            }
        }
        let (abs, m) = best?;
        let mut t = self.derived_ref(abs);
        for i in 0..m {
            t = Term::AppAt { fun: Rc::new(t), arg: Rc::new(Term::Var(heather_kernel::term::LocalVar(n - 1 - i))) };
        }
        let pos = (m - 1) as usize;
        let (dict, dict_ty, _) = self.local(cx, pos);
        let src = self
            .tag_of(&dict_ty)
            .filter(|dind| dind.name != ind.name)
            .and_then(|dind| self.traits.class(&crate::names::qkey(&dind.scope.module, &dind.name)))
            .filter(|dinfo| dinfo.ancestors.iter().any(|a| self.key_of(&a.name).as_deref() == Some(ckey.as_str())))
            .map(|_| (dict, dict_ty));
        let who = format!("{} (derived `{}` over the context's first {m})", &cx.names[pos], ind.name);
        Some((t, who, src))
    }

    /// Is `t` an open derivation applied to its prefix ([`Self::open_hit`]):
    /// a dictionary built from its arguments, which a structural matcher
    /// should compare by conversion rather than spine by spine?
    pub(crate) fn is_open_app(&self, t: &Term) -> bool {
        let Term::GlobalTm { var, .. } = crate::spelling::app_spine(t).0 else { return false };
        let Some(abs) = self.global_abs_of(*var) else { return false };
        self.traits.derived().iter().any(|d| d.abs as usize == abs && is_open_head(d.head.as_deref()))
    }

    /// `t` when it is an open derivation applied to its prefix
    /// ([`Self::open_hit`]): the minted body instantiated at the arguments,
    /// i.e. the record the derivation assembled, read where `t` stands. For a
    /// syntactic reader of dictionary fields (`ring`'s atoms), which a
    /// reference hides behind a δ step; `None` for anything else.
    pub(crate) fn unfold_open_app(&self, t: &Term) -> Option<Term> {
        let (head, args) = crate::spelling::app_spine(t);
        let Term::GlobalTm { var, .. } = head else { return None };
        let abs = self.global_abs_of(*var)? as u32;
        if !self.traits.derived().iter().any(|d| d.abs == abs && is_open_head(d.head.as_deref())) {
            return None;
        }
        let (_, body) = self.global_body_at(abs as usize)?;
        // Scoped in its prefix of Ψ; rescoped as `resolve` rescopes a
        // global's type, by the reference's own distance.
        let mut inner: Term = body.shift_global(var.0 + 1);
        let mut m = 0;
        while let Term::Lam { body, .. } = inner {
            inner = (*body).clone();
            m += 1;
        }
        if m != args.len() {
            return None;
        }
        let delta = LocalSubst {
            tail: SubstTail::Empty,
            terms: args.iter().map(|a| Rc::clone(a)).collect(),
        };
        Some(inner.apply_local(&delta))
    }

    /// Mint one open derivation ([`Self::record_open`]): `ty` is the closed
    /// `Π prefix. goal` and `body` the λ over the same binders.
    fn mint_open(&mut self, ty: &Type, lvl: &Level, body: &Term, head: Option<&str>) {
        let now = self.psi.bindings.len() as u32;
        if self
            .traits
            .derived()
            .iter()
            .any(|d| d.head.as_deref() == head && d.ty.shift_global(now - d.at) == *ty)
        {
            return;
        }
        if !self.type_is_closed(ty, lvl) {
            return;
        }
        let ok = stats::time_kernel(|| {
            typing::check_term(&self.psi, 0, Layer::Code, &LocalCtx::nil(), body, ty, lvl, self.policy.fuel).is_ok()
        });
        if !ok {
            return;
        }
        let abs = self.psi.bindings.len() as u32;
        self.psi.push(GlobalBinding::Tm {
            ctx: LocalCtx::nil(),
            layer: Layer::Code,
            ty: Rc::new(ty.clone()),
            level: lvl.clone(),
            // A `fn`, as a closed derivation is: a field is read off it by
            // unfolding.
            body: Some(Rc::new(body.clone())),
        });
        let derived = DerivedInst {
            name: format!("#open{}", self.traits.derived().len()),
            abs,
            ty: ty.clone(),
            level: lvl.clone(),
            at: abs,
            head: head.map(str::to_string),
        };
        self.semantic_commit_derived(derived);
        self.refresh_delta_psi();
    }

    /// `u^δ` for a minted global, the same construction [`Elaborator::resolve`]
    /// makes for a written name: the goals sit innermost, so a committed
    /// binding is that much further out, and a closed statement's delayed
    /// substitution is the empty map out of the current Γ.
    fn derived_ref(&self, abs: u32) -> Term {
        if let Some(key) = self.names.global_name_at(abs) {
            self.attempt
                .direct_dependencies
                .borrow_mut()
                .insert(key.to_string());
        }
        let len = self.psi.bindings.len() as u32;
        let var = GlobalVar(len - 1 - abs + self.global_padding());
        Term::GlobalTm {
            var,
            subst: LocalSubst {
                tail: SubstTail::Empty,
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
        if self.global_padding() != 0 || !self.type_is_closed(goal, lvl) {
            return;
        }
        let mut pending = self.pass.pending_derived.borrow_mut();
        if pending.iter().any(|(t, l, _, head, open)| {
            open.is_none()
                && heads_may_agree(head.as_deref(), prefer)
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
            None,
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
                self.policy.fuel,
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
            let pending: Vec<crate::lifetimes::PendingDerived> =
                std::mem::take(&mut self.pass.pending_derived.borrow_mut());
            if pending.is_empty() {
                return;
            }
            for (goal, lvl, at, prefer, open) in pending {
                // The item pushed its own globals after this goal was
                // captured, so every `GlobalVar` in it now points that much
                // further out.
                let grew = self.psi.bindings.len() as u32 - at;
                match open {
                    None => self.mint_one(&goal.shift_global(grew), &lvl, prefer.as_deref()),
                    Some(body) => self.mint_open(&goal.shift_global(grew), &lvl, &body.shift_global(grew), prefer.as_deref()),
                }
            }
        }
        self.pass.pending_derived.borrow_mut().clear();
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
                self.policy.fuel,
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

/// The name a written solver type is headed by: `OrderedField` in a
/// section's constraint binder `OrderedField(A)(≈, <, …)`.
fn written_head(ty: &heather_syntax::Ty) -> Option<&str> {
    fn expr_head(e: &Expr) -> Option<&str> {
        match &e.kind {
            ExprKind::Var(name) => Some(name),
            ExprKind::App { head, .. } | ExprKind::TyApp { head, .. } => expr_head(head),
            _ => None,
        }
    }
    match &ty.kind {
        TyKind::Named { name, .. } => Some(name),
        TyKind::OfExpr(e) => expr_head(e),
        _ => None,
    }
}

/// [`Elaborator::rule_clashes`]'s match of one rule argument against one
/// goal argument. `assigned` holds the binders already set to a goal local,
/// as (binder, local index).
fn pattern_clashes(rule: &Term, goal: &Term, binders: u32, assigned: &mut Vec<(u32, u32)>) -> bool {
    let (rh, rargs) = crate::spelling::app_spine(rule);
    let Term::Var(rv) = rh else {
        return false;
    };
    if rv.0 >= binders {
        return false;
    }
    let (gh, gargs) = crate::spelling::app_spine(goal);
    // An applied binder (a class operation, `x + y`) against a bare local:
    // only a higher-order solution would fit, and the rule's operation is
    // pinned by its dictionary.
    if !rargs.is_empty() && gargs.is_empty() && matches!(gh, Term::Var(_)) {
        return true;
    }
    if !rargs.is_empty() && rargs.len() != gargs.len() {
        return false;
    }
    let target = if rargs.is_empty() { goal } else { gh };
    if let Term::Var(gv) = target {
        match assigned.iter().find(|(b, _)| *b == rv.0) {
            Some((_, prev)) if *prev != gv.0 => return true,
            Some(_) => {}
            None => assigned.push((rv.0, gv.0)),
        }
    } else if !rargs.is_empty() {
        return false;
    }
    rargs.iter().zip(&gargs).any(|(r, g)| pattern_clashes(r, g, binders, assigned))
}

/// A qualified key without its module, for a trace line: `Nat::Lt`.
fn short_name(key: &str) -> &str {
    key.split_once("::").map_or(key, |(_, rest)| rest)
}

/// The head of an evidence rule's or a goal's argument: the global it is an
/// application of, or the Nat, pair or sum constructor it is, `None` where it
/// is a variable or anything else. Only a prefilter reads it.
fn argument_head(t: &Term, name_of: &dyn Fn(GlobalVar) -> Option<String>) -> Option<String> {
    let (head, _) = crate::spelling::app_spine(t);
    match head {
        Term::GlobalTm { var, .. } => name_of(*var),
        Term::Zero => Some("#zero".into()),
        Term::Succ(_) => Some("#succ".into()),
        Term::NatLit(n) => Some(if n.is_zero() { "#zero" } else { "#succ" }.into()),
        // A record or sum value written out: no rule about an application
        // of a global fits it without unfolding that global, which the
        // prefilter does not do (a literal `Rat(2, 1)` would otherwise try
        // every rule about products, powers and inverses).
        Term::Pair { .. } | Term::PairAt { .. } => Some("#pair".into()),
        Term::Inl { .. } | Term::InlAt { .. } => Some("#inl".into()),
        Term::Inr { .. } | Term::InrAt { .. } => Some("#inr".into()),
        _ => None,
    }
}

/// The arguments of a relation application, in [`proposition_key`]'s order.
fn proposition_args(ty: &Type) -> Vec<&Rc<Term>> {
    match ty {
        Type::El { tm, .. } => crate::spelling::app_spine(tm).1,
        _ => Vec::new(),
    }
}

/// A proposition as an evidence-rule key: the qualified name of its relation
/// (the head global of `El(R a₁ … aₙ)`) and the head of each argument.
pub(crate) fn proposition_key(
    ty: &Type,
    name_of: &dyn Fn(GlobalVar) -> Option<String>,
) -> Option<(String, Vec<Option<String>>)> {
    let Type::El { tm, .. } = ty else {
        return None;
    };
    let (head, args) = crate::spelling::app_spine(tm);
    let Term::GlobalTm { var, .. } = head else {
        return None;
    };
    let relation = name_of(*var)?;
    let heads = args.iter().map(|a| argument_head(a, name_of)).collect();
    Some((relation, heads))
}

/// Symbol count and per-binder variable occurrences of a premise or
/// conclusion, for an evidence rule's termination check. Binders are numbered
/// from the outside of the rule's telescope, so a premise and the conclusion,
/// which sit under different numbers of them, compare.
struct Measure {
    size: usize,
    occurrences: std::collections::BTreeMap<u32, usize>,
}

impl Measure {
    fn of(ty: &Type, under: u32) -> Measure {
        let mut m = Measure { size: 0, occurrences: Default::default() };
        match ty {
            Type::El { tm, .. } => m.term(tm, under),
            _ => m.size = usize::MAX / 2,
        }
        m
    }

    fn term(&mut self, t: &Term, under: u32) {
        self.size += 1;
        match t {
            Term::Var(v) => {
                if let Some(b) = under.checked_sub(v.0 + 1) {
                    *self.occurrences.entry(b).or_default() += 1;
                }
            }
            Term::Succ(x) => self.term(x, under),
            _ => {
                let (head, args) = crate::spelling::app_spine(t);
                if !args.is_empty() {
                    // The head already counted as this node.
                    if let Term::Var(_) = head {
                        self.term(head, under);
                        self.size -= 1;
                    }
                    for a in args {
                        self.term(a, under);
                    }
                }
            }
        }
    }

    fn smaller_than(&self, other: &Measure) -> bool {
        self.size < other.size
            && self
                .occurrences
                .iter()
                .all(|(b, n)| other.occurrences.get(b).is_some_and(|m| n <= m))
    }
}

/// A committed-world type read into a goal world `pad` arena entries deep:
/// every global moves `pad` further out, since the arena sits innermost.
fn weaken_global_below(t: &Type, pad: u32) -> Type {
    t.shift_global(pad)
}
