//! Instance resolution and `:= infer` (`docs/traits-layer2-design.md`).
//!
//! One entry point — [`Elaborator::resolve_goal`], `(goal, scope) → term` —
//! consulted from `apply_implicit`'s retry loop for every **solver
//! parameter**. Three sources, in the record's ascending-scope order (§3):
//! the canonical derived table, the local scope innermost-first, then the
//! layer-1 instance registry by backchaining.
//!
//! Nothing here is trusted. Every proposal, from every source, is handed to
//! the kernel at the goal type before it is returned (§4.4) — which is what
//! makes selection-by-trial (§3.1) a *function* of the goal rather than a
//! guess, and what keeps a wrong candidate from surfacing pages later as a
//! declaration-gate rejection.

use std::rc::Rc;

use heather_kernel::conv::conv_type;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    GlobalBinding, GlobalVar, LocalCtx, LocalSubst, SubstTail, Term, Type,
};
use heather_kernel::typing;
use heather_syntax::{Expr, ExprKind, Span};

use crate::{stats, Cx, ElabError, Elaborator};

/// How deep backchaining may go before it refuses. Declaration-time
/// structural decrease (design §6) is what makes this unreachable; the cap is
/// the belt, not the braces — a registry assembled by a *failing* decrease
/// check (a class whose instances were declared before this round) must still
/// terminate.
const MAX_DEPTH: usize = 32;

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

fn line(depth: usize, key: &'static str, value: impl Into<String>) -> TraceLine {
    TraceLine { depth, key, value: value.into() }
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
    /// Absolute Ψ index, exactly as [`crate::GlobalInfo`]'s.
    pub abs: u32,
    /// The goal this value was derived for — the table's key, compared up to
    /// conversion.
    pub ty: Type,
    pub level: Level,
    /// The Ψ length when the entry was minted. A stored type's `GlobalVar`s
    /// are relative to the Ψ that was, and Ψ only grows, so a lookup rebases
    /// by the difference (the same bookkeeping the pending queue does).
    pub at: u32,
}

impl Elaborator {
    /// Resolve one goal, or explain in `tr` why not.
    ///
    /// `display` is what the diagnostic calls the goal (the parameter's
    /// written type). It is a display and never a key.
    pub(crate) fn resolve_goal(
        &self,
        cx: &Cx,
        goal: &Type,
        lvl: &Level,
        display: &str,
        span: Span,
        tr: &mut Vec<TraceLine>,
    ) -> Option<Term> {
        let depth = self.resolve_depth.get();
        tr.push(line(depth, "goal", display.to_string()));
        if depth >= MAX_DEPTH {
            tr.push(line(depth, "depth", format!("gave up at {MAX_DEPTH} nested subgoals")));
            return None;
        }

        // 0. The canonical table (design §8). Checked before the scope only
        //    because a hit is a *reference to the very value* the registry
        //    route would rebuild: it cannot shadow anything, since a local of
        //    the goal type would have been minted from nothing.
        if let Some(t) = self.derived_hit(cx, goal) {
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
        tr.push(line(
            depth,
            "scope",
            format!("{} binder(s) consulted, none of the goal type", cx.names.len()),
        ));

        // 2. The registry. Only a *class* has one: an `:= infer` goal at an
        //    ordinary type is a scope search and nothing else, and its trace
        //    says so rather than reporting an empty registry.
        let Some(ind) = self.tag_of(goal) else {
            tr.push(line(depth, "no-class", "the goal type is not a class"));
            return None;
        };
        let Some(ckey) = self.key_of(&ind.name) else {
            tr.push(line(depth, "no-class", format!("`{}` does not resolve here", ind.name)));
            return None;
        };
        if !self.classes.contains_key(&ckey) {
            tr.push(line(
                depth,
                "no-class",
                format!("`{}` is a record, not a class, so it has no instances", ind.name),
            ));
            return None;
        }
        // Candidates in a *stated* order — sorted by canonical name, never
        // declaration order and never `HashMap` order (design §3.1).
        let mut cands: Vec<(String, bool)> = self
            .instances
            .iter()
            .filter(|((c, _), _)| *c == ckey)
            .map(|(_, i)| (i.global.clone(), i.parameterized))
            .collect();
        cands.sort();
        if cands.is_empty() {
            tr.push(line(depth, "no-instance", format!("`{}` has no instances", ind.name)));
            return None;
        }
        tr.push(line(depth, "class", format!("{} ({} instance(s))", ind.name, cands.len())));
        for (g, parameterized) in cands {
            tr.push(line(depth, "candidate", g.clone()));
            self.resolve_depth.set(depth + 1);
            let built = self.build_candidate(cx, &g, goal, lvl, span);
            self.resolve_depth.set(depth);
            match built {
                Ok(t) if self.checks_at(cx, &t, goal, lvl) => {
                    // Only a *derivation* is canonicalized. A declared
                    // instance's value is already one global reached by name,
                    // and minting a second one for it would duplicate the very
                    // thing the table exists to keep single.
                    if parameterized {
                        self.record_derived(goal, lvl);
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
        let e = Expr { kind: ExprKind::Var(global.to_string()), span };
        self.elab_check(cx, &e, goal, lvl)
    }

    /// Is `ty` the goal type, here? Conversion, in the use site's context.
    fn conv_here(&self, cx: &Cx, ty: &Type, goal: &Type, lvl: &Level) -> bool {
        let psi = self.goal_psi();
        stats::time_kernel(|| {
            conv_type(&psi, &cx.gamma, Layer::Prog, ty, goal, lvl, self.fuel).is_ok()
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
    fn derived_hit(&self, cx: &Cx, goal: &Type) -> Option<Term> {
        let now = self.psi.bindings.len() as u32;
        let d = self
            .derived
            .iter()
            .find(|d| self.conv_here(cx, &d.ty.shift_global(now - d.at), goal, &d.level))?;
        Some(self.derived_ref(cx, d.abs))
    }

    /// `u^δ` for a minted global, the same construction [`Elaborator::resolve`]
    /// makes for a written name: the goals sit innermost, so a committed
    /// binding is that much further out, and a closed statement's delayed
    /// substitution is the empty map out of the current Γ.
    fn derived_ref(&self, cx: &Cx, abs: u32) -> Term {
        let len = self.psi.bindings.len() as u32;
        let var = GlobalVar(len - 1 - abs + self.goal_base);
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
    fn record_derived(&self, goal: &Type, lvl: &Level) {
        if self.goal_base != 0 || !self.type_is_closed(goal, lvl) {
            return;
        }
        let mut pending = self.pending_derived.borrow_mut();
        if pending.iter().any(|(t, l, _)| {
            let psi = self.goal_psi();
            conv_type(&psi, &LocalCtx::nil(), Layer::Prog, t, goal, l, self.fuel).is_ok()
        }) {
            return;
        }
        // With the Ψ length at capture: the item that recorded this goal goes
        // on to push its own globals, and a stored type's `GlobalVar`s are
        // relative to the Ψ that was (see [`Self::mint_pending`]).
        pending.push((goal.clone(), lvl.clone(), self.psi.bindings.len() as u32));
    }

    /// Is this type closed? Asked of the kernel, in the empty context — the
    /// honest test, and the one the mint has to pass anyway.
    fn type_is_closed(&self, goal: &Type, lvl: &Level) -> bool {
        stats::time_kernel(|| {
            typing::check_type(&self.psi, 0, Layer::Prog, &LocalCtx::nil(), goal, lvl, self.fuel)
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
            let pending: Vec<(Type, Level, u32)> =
                std::mem::take(&mut self.pending_derived.borrow_mut());
            if pending.is_empty() {
                return;
            }
            for (goal, lvl, at) in pending {
                // The item pushed its own globals after this goal was
                // captured, so every `GlobalVar` in it now points that much
                // further out.
                let grew = self.psi.bindings.len() as u32 - at;
                self.mint_one(&goal.shift_global(grew), &lvl);
            }
        }
        self.pending_derived.borrow_mut().clear();
    }

    fn mint_one(&mut self, goal: &Type, lvl: &Level) {
        let cx = Cx::empty();
        if self.derived_hit(&cx, goal).is_some() {
            return;
        }
        let mut tr = Vec::new();
        let span = Span { start: 0, end: 0 };
        let Some(term) = self.resolve_goal(&cx, goal, lvl, "a derived instance", span, &mut tr)
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
        let name = format!("#derived{}", self.derived.len());
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
        self.derived.push(DerivedInst {
            name,
            abs,
            ty: goal.clone(),
            level: lvl.clone(),
            // The Ψ length *before* the push above — the world the stored
            // type is scoped in.
            at: abs,
        });
        self.refresh_delta_psi();
    }
}
