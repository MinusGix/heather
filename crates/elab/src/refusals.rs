//! Kernel refusals' part of the elaborator: turning a refused judgment into a located error.

use heather_kernel::typing;
use heather_kernel::conv::ConvError;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalCtx, LocalCtx, Term, Type};
use heather_kernel::typing::TypeError;

use heather_syntax::{Expr, ExprKind, Span};

use crate::{Elaborator, MismatchNote, R, RecordedSite, attempt, diagnostics, err, inductive, names, oracle};
use crate::context::Cx;
use crate::diagnostics::{ElabError, KernelSite};
use crate::mismatch_notes::MismatchNotes;
use crate::partial::Partial;

/// Kernel refusals' part of the elaborator: turning a refused judgment into a located error.
pub(crate) struct Refusals<'e>(pub(crate) &'e Elaborator);

/// How many times the gate's budget a declaration refused out of fuel is
/// checked again with, to say whether its claim is false or its proof only
/// costly (issues/false-closed-claim-out-of-fuel.md). The false SHA-256
/// claim that met it is decided at about three and a half times the budget.
const REFUSAL_FUEL_FACTOR: u64 = 8;

impl std::ops::Deref for Refusals<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl Refusals<'_> {
    fn operator_fallback_note(&self) -> Option<String> {
        let notes = self.attempt.op_fallback_notes.borrow();
        (!notes.is_empty()).then(|| notes.join("; "))
    }

    /// The gate's rejection, said as well as it can be said
    /// (`issues/check-fallback-discards-expected-type.md`). A bare
    /// `NotConvertible` at the declaration is what this exists to avoid: when
    /// checking noticed *which* expression disagreed and could state both
    /// types, that report replaces the kernel one — same rejection, at a span,
    /// with the types. Any other `TypeError` keeps the kernel's own report,
    /// because this slot has no claim about it.
    ///
    /// The operator note travels either way: it explains a designation that was
    /// resolved by fallback, which is as relevant to the precise message as to
    /// the bare one.
    ///
    /// Both notes are *probed* here rather than read: the conversion that
    /// decides whether either has anything to say runs at this verdict, not at
    /// the site it was recorded at (`issues/elab-diagnostic-probe-cost.md`).
    /// This is the only place a rejection is reported from — the parallel
    /// gate's join reports no note, discards its pass and replays it serially
    /// (`docs/kernel/parallel-kernel-gate-design.md` §5.1) — so the candidates are
    /// always in hand, at every width.
    ///
    /// A written `refl`'s note ([`MismatchNotes::note_refl_mismatch`]) travels a third
    /// way: it neither replaces the report nor merely annotates the
    /// declaration. The verdict stays the kernel's, and the *span* becomes the
    /// `refl` that stands for it — the one expression in the body that claimed
    /// the conversion the gate refused. A checking mismatch whose types do not
    /// both spell travels the same way ([`MismatchNote::Located`]), when no
    /// `refl` note has more to say.
    pub(crate) fn kernel_error(&self, decl: &str, span: Span, e: TypeError) -> ElabError {
        // A head of the wrong former is the same disagreement met one step
        // later: a proof of `same(x, y)` filled into a goal whose statement
        // unfolds to a Π is refused where the goal is *applied*, as
        // `HeadMismatch`, and the site that explains it is the checking note
        // at the `on` (issues/elab-accepts-conjunction-for-equation.md).
        // So is a level that disagrees: an argument whose type lives at
        // another level than its domain (a section's `f<A>` placed before its
        // dictionary was filled) is refused for the levels before any
        // conversion is asked, and the note recorded at the argument says why
        // (issues/applied-field-source-spelling-level-mismatch.md).
        // Out of fuel is no verdict on the claim, but where the claim is
        // likely false is still worth saying, at the site.
        if matches!(e, TypeError::OutOfFuel)
            && let Some((note, at)) = MismatchNotes(self).fuel_note(span)
        {
            return ElabError::Kernel {
                decl: decl.to_string(),
                span: at,
                err: e,
                note: Some(note),
                site: KernelSite::Recorded,
            };
        }
        let conversion = matches!(e, TypeError::NotConvertible | TypeError::HeadMismatch | TypeError::LevelMismatch);
        if conversion
            && let Some((note, at)) = self.refused_decide().or_else(|| self.refused_trivial())
        {
            return ElabError::Kernel {
                decl: decl.to_string(),
                span: at,
                err: e,
                note: Some(note),
                site: KernelSite::Recorded,
            };
        }
        let mismatch = conversion
            .then(|| MismatchNotes(self).pending_mismatch())
            .flatten();
        let located = match mismatch {
            Some((MismatchNote::Spelled(msg), at)) => {
                let msg = match self.operator_fallback_note() {
                    Some(note) => format!("{msg} (note: {note})"),
                    None => msg,
                };
                return ElabError::Elab { msg, span: at };
            }
            Some((MismatchNote::Located(msg), at)) => Some((msg, at)),
            None => None,
        };
        let refl = conversion
            .then(|| MismatchNotes(self).pending_refl_note())
            .flatten()
            .or(located);
        let (span, refl_note) = match refl {
            Some((msg, at)) => (at, Some(msg)),
            None => (span, None),
        };
        // A term the kernel cannot infer is the elaborator's too: every form
        // it emits is meant to infer or to sit where it is checked, so a
        // `NotInferable` names a route that placed a checked spelling in an
        // inference position, and the locator below says which term
        // (issues/kernel-refuses-inj-through-corecursive-reduct.md).
        let site = if refl_note.is_some() {
            KernelSite::Recorded
        } else if conversion || matches!(e, TypeError::NotInferable) {
            KernelSite::Unrecorded
        } else {
            KernelSite::Other
        };
        let note = match (refl_note, self.operator_fallback_note()) {
            (Some(refl), Some(op)) => Some(format!("{refl} (note: {op})")),
            (Some(refl), None) => Some(refl),
            (None, op) => op,
        };
        ElabError::Kernel {
            decl: decl.to_string(),
            span,
            err: e,
            note,
            site,
        }
    }

    /// [`Self::kernel_error`] for a refusal of `body` at `ty` (or of `ty`
    /// itself, with no body) in `psi`; Γ: when no recorded site's probe
    /// decides it, ask the kernel where it failed
    /// (`issues/elab-accepts-conjunction-for-equation.md`).
    ///
    /// **Why the kernel, and why only here.** Every recorded site is a place
    /// the elaborator *knew* it was trusting the gate. An unrecorded refusal
    /// is one where it did not know — a route that placed a term without
    /// comparing or recording — and no list of routes kept by hand closes
    /// that class: the inferred-argument route (#168), the β-redex spelling
    /// (#184) and the check fallback were each found by a bisection after a
    /// bare `NotConvertible`. The kernel is the one place every placement
    /// passes through, so it is the one that can always say where. It costs
    /// one more check of the refused declaration, and runs on no other path.
    ///
    /// The located term is then looked for among the recorded sites, by
    /// syntax: a site whose probe was only *inconclusive* (a `refl` whose
    /// sides outran the note's small budget) is still the site, and the
    /// kernel has now decided it, so the report moves there as if the probe
    /// had. Only a refusal that matches no recorded site stays
    /// [`KernelSite::Unrecorded`], at the declaration, naming the refused
    /// term and its two types where they spell.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn kernel_refusal(
        &self,
        decl: &str,
        span: Span,
        e: TypeError,
        psi: &GlobalCtx,
        layer: Layer,
        gamma: &LocalCtx,
        body: Option<&Term>,
        ty: &Type,
        level: &Level,
    ) -> ElabError {
        let error = self.kernel_refusal_at_budget(decl, span, e, psi, layer, gamma, body, ty, level);
        if !matches!(e, TypeError::OutOfFuel) {
            return error;
        }
        // Out of fuel is no verdict on the claim. Checked again with more
        // fuel, the refused declaration may get one: a false claim whose two
        // sides only differ once both are computed (`digest(abc) =
        // digest(abd)`), or a right proof that only costs more than a
        // conversion is allowed. The verdict stays the gate's; only what the
        // refusal says changes, and only on this path.
        let budget = self.policy.fuel.saturating_mul(REFUSAL_FUEL_FACTOR);
        let retried = match body {
            Some(body) => typing::check_term(psi, 0, layer, gamma, body, ty, level, budget),
            None => typing::check_type(psi, 0, layer, gamma, ty, level, budget),
        };
        let said = match retried {
            Err(TypeError::NotConvertible | TypeError::HeadMismatch) => format!(
                "with {REFUSAL_FUEL_FACTOR} times the budget the kernel computes both sides and finds \
                 them different: the claim is false"
            ),
            Ok(()) => format!(
                "the proof is right, but checks only with up to {REFUSAL_FUEL_FACTOR} times the budget: \
                 split the computation into stage theorems (docs/proof-patterns.md)"
            ),
            Err(_) => return error,
        };
        match error {
            ElabError::Kernel { decl, span, err, note, site } => ElabError::Kernel {
                decl,
                span,
                err,
                note: Some(match note {
                    Some(note) => format!("{}; {said}", note.replace(": the claim is likely false", "")),
                    None => said,
                }),
                site,
            },
            other => other,
        }
    }

    /// [`Self::kernel_refusal`] at the gate's own budget: the site, and the
    /// note that says why.
    #[allow(clippy::too_many_arguments)]
    fn kernel_refusal_at_budget(
        &self,
        decl: &str,
        span: Span,
        e: TypeError,
        psi: &GlobalCtx,
        layer: Layer,
        gamma: &LocalCtx,
        body: Option<&Term>,
        ty: &Type,
        level: &Level,
    ) -> ElabError {
        let error = self.kernel_error(decl, span, e);
        let ElabError::Kernel { site: KernelSite::Unrecorded, note: op_note, .. } = &error else {
            return error;
        };
        let with_op = |said: String| match op_note {
            Some(op) => format!("{said} (note: {op})"),
            None => said,
        };
        let found = match body {
            Some(body) => typing::locate_refusal(psi, 0, layer, gamma, body, ty, level, self.policy.fuel),
            None => typing::locate_type_refusal(psi, 0, layer, gamma, ty, level, self.policy.fuel),
        };
        let said = match &found {
            Some(found) if found.psi_len == psi.bindings.len() => {
                if let Some(at) = self.recorded_site_of(psi, found) {
                    return at.into_error(decl, e, with_op);
                }
                self.refused_site_note(found)
            }
            Some(_) => "no checking site recorded this refusal; the kernel refused a term \
                        under a binder of the global context, which has no surface spelling"
                .to_string(),
            None => "no checking site recorded this refusal, and the kernel refused no \
                     term check in it"
                .to_string(),
        };
        ElabError::Kernel {
            decl: decl.to_string(),
            span,
            err: e,
            note: Some(with_op(said)),
            site: KernelSite::Unrecorded,
        }
    }

    /// The recorded site a located refusal is, if any: a written `refl` at
    /// the same depth whose side converts with the refused `Refl`'s, or a
    /// checking site at the same depth whose two types convert with the
    /// refused check's. **By conversion, not syntax**: the kernel holds the
    /// emitted spelling (the statement and every slot are respelled on their
    /// way through the emission chokepoint), the note the elaborator's, and
    /// the two differ in exactly the way conversion forgives. Budgeted like
    /// the `refl` note; out of budget is no match. Only in a world with no
    /// goal slots, where the two sides' global indices agree.
    fn recorded_site_of(&self, psi: &GlobalCtx, found: &typing::RefusedSite) -> Option<RecordedSite> {
        let world = self.goal_psi();
        if world.bindings.len() != psi.bindings.len() {
            return None;
        }
        let oracle = oracle::SemanticOracle::in_world(world, self.policy.fuel.min(diagnostics::REFL_NOTE_FUEL));
        let gamma = &found.gamma;
        let same_depth = |c: &Cx| c.gamma.base == gamma.base && c.gamma.entries.len() == gamma.entries.len();
        if let Term::Refl { tm, .. } = &found.term {
            let refls = self.attempt.refl_notes.borrow();
            let site = refls.iter().find(|n| {
                same_depth(&n.cx)
                    && (n.lhs == **tm || oracle.convert_term(gamma, Layer::Prog, &n.lhs, tm, &n.ty, &n.level).is_ok())
            });
            if let Some(n) = site {
                let sides = self.spell_term_clean(&n.cx, &n.lhs).zip(self.spell_term_clean(&n.cx, &n.rhs));
                return Some(RecordedSite::Refl { span: n.span, sides });
            }
        }
        let (Some(expected), Some(inferred)) = (&found.expected, &found.inferred) else {
            return None;
        };
        let converts = |a: &Type, b: &Type, level: &Level| {
            a == b || oracle.convert_type(gamma, Layer::Prog, a, b, level).is_ok()
        };
        let checks = self.attempt.check_notes.borrow();
        let n = checks.iter().find(|n| {
            same_depth(&n.cx) && converts(&n.expected, expected, &n.level) && converts(&n.got, inferred, &n.level)
        })?;
        if let Some(msg) = n.partial.as_ref().and_then(|f| Partial(self).partial_use_note(&n.cx, f, &n.got, &n.expected)) {
            return Some(RecordedSite::Named { span: n.span, msg });
        }
        let got = self.display_type_clean(&n.cx, &n.got);
        let want = self.display_type_clean(&n.cx, &n.expected);
        Some(RecordedSite::Check { span: n.span, types: got.zip(want).filter(|(g, w)| g != w) })
    }

    /// The located refusal, said: the term and the two types, each where it
    /// spells in full ([`Elaborator::spell_term_clean`], [`Elaborator::display_type_clean`]:
    /// a claim about a type the reader cannot check is worse than none).
    fn refused_site_note(&self, found: &typing::RefusedSite) -> String {
        let cx = self.refused_site_cx(found);
        let term = cx.as_ref().and_then(|cx| self.spell_term_clean(cx, &found.term));
        let spell = |ty: &Option<Type>| match (&cx, ty) {
            (Some(cx), Some(ty)) => self.display_type_clean(cx, ty),
            _ => None,
        };
        let (got, want) = (spell(&found.inferred), spell(&found.expected));
        let what = match term {
            Some(t) => format!("`{t}`"),
            None => "a term with no surface spelling".to_string(),
        };
        let types = match (got, want) {
            (Some(g), Some(w)) if g != w => format!(", which has type `{g}`, where `{w}` is expected"),
            (Some(g), Some(_)) => format!(
                ", which has type `{g}` where a type that displays the same is expected"
            ),
            (None, Some(w)) => format!(" where `{w}` is expected"),
            (Some(g), None) => format!(", which has type `{g}`"),
            (None, None) => String::new(),
        };
        format!(
            "no checking site recorded this refusal: the kernel refused {what}{types} \
             (an elaborator gap: issues/elab-accepts-conjunction-for-equation.md)"
        )
    }

    /// Names for a located refusal's Γ, binder by binder: the name a
    /// recorded site's context gave it, where that context shares Γ up to
    /// it (those are the binders the source wrote, under the names it
    /// wrote); else the declaration's parameter name at that position (the
    /// kernel's outermost binders are the telescope, whose types the
    /// statement respells, so they are matched by position); else a fresh
    /// name, as the display names a binder the kernel does not name.
    fn refused_site_cx(&self, found: &typing::RefusedSite) -> Option<Cx> {
        let gamma = &found.gamma;
        if !matches!(gamma.base, heather_kernel::term::CtxBase::Nil) {
            return None;
        }
        let shared = |c: &Cx| -> usize {
            if c.gamma.base != gamma.base {
                return 0;
            }
            (0..c.gamma.entries.len().min(gamma.entries.len()))
                .take_while(|&i| c.gamma.entries.get(i) == gamma.entries.get(i))
                .count()
        };
        let checks = self.attempt.check_notes.borrow();
        let refls = self.attempt.refl_notes.borrow();
        let none = crate::spine::Binders::default();
        let (k, written) = checks.iter().map(|n| &n.cx).chain(refls.iter().map(|n| &n.cx))
            .map(|c| (shared(c), &c.names))
            .max_by_key(|(k, _)| *k)
            .unwrap_or((0, &none));
        let telescope = self.attempt.telescope.borrow();
        let mut cx = Cx::empty();
        for i in 0..gamma.entries.len() {
            let entry = gamma.entries.get(i)?;
            let name = match (i < k).then(|| written.get(i)).flatten().or_else(|| telescope.get(i)) {
                Some(name) => name.to_string(),
                None => ["x", "y", "z", "a", "b", "c"]
                    .iter()
                    .map(|n| n.to_string())
                    .chain((i..).map(|n| format!("x{n}")))
                    .find(|n| !cx.names.contains(n))?,
            };
            cx.push(name, (*entry.ty).clone(), entry.level.clone());
        }
        Some(cx)
    }

    /// Is a bare `decide` something the writer bound, rather than the goal
    /// combinator? The library's own `bool::decide` is the one global that
    /// does not count (see the checking arm).
    pub(crate) fn decide_shadowed(&self, cx: &Cx) -> bool {
        cx.names.iter_inner().any(|n| n == "decide")
            || cx.aliases.iter_inner().any(|a| a.name == "decide")
            || cx.selfref.as_ref().is_some_and(|s| s.matches("decide"))
            || self
                .key_of("decide")
                .is_some_and(|key| key != names::qkey("bool", "decide"))
    }

    /// The `decide` goal combinator: elaborate `bool::decide_yes(refl)` at
    /// the goal and remember what it resolved to, so a gate refusal can be
    /// reported at this `decide` with the instance named.
    pub(crate) fn elab_decide(&self, cx: &Cx, expected: &Type, lvl: &Level, span: Span) -> R<Term> {
        let Some(yes) = self.key_of("bool::decide_yes") else {
            return err(
                "`decide` proves a closed goal by running its `Decide` instance, and needs \
                 the class in scope: add `import bool;`",
                span,
            );
        };
        let e = Expr {
            kind: ExprKind::App {
                head: Box::new(Expr {
                    kind: ExprKind::Var(yes),
                    span,
                }),
                args: vec![Expr {
                    kind: ExprKind::Refl,
                    span,
                }],
                named: Vec::new(),
                explicit: false,
                goal_oriented: false,
            },
            span,
        };
        let t = self.elab_check(cx, &e, expected, lvl)?;
        // `decide_yes(P, inst, refl)`, outermost argument first: the `refl`,
        // whose left side is `or_index(inst.dec)`, then the dictionary.
        let mut args = Vec::new();
        let mut head = &t;
        while let Some((fun, arg)) = crate::spelling::app_of(head) {
            args.push(&**arg);
            head = fun;
        }
        if let [Term::Refl { tm, .. }, inst, ..] = args.as_slice() {
            // The instance as the registry names it — module-qualified, the
            // way a resolution trace names a candidate — when the dictionary
            // is a declared instance's global; a minted derivation is spelled.
            let mut head = *inst;
            while let Some((fun, _)) = crate::spelling::app_of(head) {
                head = fun;
            }
            let instance = match head {
                Term::GlobalTm { var, .. } => self
                    .global_abs_of(*var)
                    .and_then(|abs| self.names.global_name_at(abs as u32))
                    .map(str::to_string),
                _ => None,
            }
            .or_else(|| self.spell_term_clean(cx, inst))
            .unwrap_or_else(|| "its `Decide` instance".to_string());
            self.attempt.decide_uses.borrow_mut().push(attempt::DecideUse {
                span,
                gamma: cx.gamma.clone(),
                index: (**tm).clone(),
                goal: self.display_type(cx, expected),
                instance,
            });
        }
        Ok(t)
    }

    /// After a `NotConvertible` at the gate: the first written `decide` whose
    /// decision reduces to the wrong side, with the note that names it. The
    /// re-reduction runs only on the failure path and under the gate's own
    /// budget; an inconclusive one stays silent, like a `refl`'s note.
    fn refused_decide(&self) -> Option<(String, Span)> {
        let uses = self.attempt.decide_uses.borrow();
        if uses.is_empty() {
            return None;
        }
        let oracle = oracle::SemanticOracle::in_world(self.goal_psi(), self.policy.fuel);
        let zero = inductive::nat_lit(0);
        uses.iter().find_map(|u| {
            (oracle.convert_term(&u.gamma, Layer::Prog, &u.index, &zero, &Type::Nat, &Level::Zero)
                == Err(ConvError::NotConvertible))
            .then(|| {
                (
                    format!(
                        "`decide` resolved `Decide<{}>` to `{}`, whose decision here is not \
                         `Inl`: the goal is false, or not closed enough to decide",
                        u.goal, u.instance
                    ),
                    u.span,
                )
            })
        })
    }

    /// After a `NotConvertible` at the gate: the first `trivial` left unread
    /// ([`expr::UnitCheckingElab`](crate::expr::UnitCheckingElab)) whose expected type, reduced now under
    /// the gate's own budget, is not `True`. [`Self::refused_decide`]'s
    /// counterpart: the reduction runs only on the failure path, and an
    /// inconclusive one stays silent.
    fn refused_trivial(&self) -> Option<(String, Span)> {
        let uses = self.attempt.trivial_uses.borrow();
        if uses.is_empty() {
            return None;
        }
        let oracle = oracle::SemanticOracle::in_world(self.goal_psi(), self.policy.fuel);
        uses.iter().find_map(|u| {
            let head = oracle.whnf_type(&u.cx.gamma, &u.expected).ok()?;
            if matches!(head, Type::Unit { .. }) {
                return None;
            }
            let goal = self.display_type(&u.cx, &u.expected);
            let reduct = match self.display_type_clean(&u.cx, &head) {
                Some(r) if r != goal => format!(", which reduces to `{r}`"),
                _ => String::new(),
            };
            Some((
                format!(
                    "`trivial` proves `True`, but `{goal}` is expected here{reduct}: \
                     the verdict is false, or not closed enough to compute"
                ),
                u.span,
            ))
        })
    }
}
