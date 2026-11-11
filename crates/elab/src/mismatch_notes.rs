//! The notes a refused check carries: what the two sides were and where they part.

use heather_kernel::conv::ConvError;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::rc::Rc;
use heather_kernel::term::{GlobalBinding, LocalVar, Term, Type};

use heather_syntax::{Expr, ExprKind, Span};

use crate::{Elaborator, MismatchNote, application, diagnostics, oracle, stats};
use crate::attempt::{CheckNote, ReflNote};
use crate::context::Cx;
use crate::diagnostics::ElabError;
use crate::dispatch::{Casts, Members};
use crate::name_lookup::NameLookup;
use crate::partial::Partial;

/// The notes a refused check carries: what the two sides were and where they part.
pub(crate) struct MismatchNotes<'e>(pub(crate) &'e Elaborator);

impl std::ops::Deref for MismatchNotes<'_> {
    type Target = Elaborator;
    fn deref(&self) -> &Elaborator {
        self.0
    }
}

impl MismatchNotes<'_> {
    /// Notice what the kernel is going to reject, and where
    /// (`issues/check-fallback-discards-expected-type.md`). Checking that ends
    /// in inference holds an inferred type and used to drop it, so the simplest
    /// type error in the language — a literal at the wrong type — was
    /// discovered by the decl-final gate: at the declaration, with no span and
    /// no types, as a bare `NotConvertible`.
    ///
    /// The kernel stays the judge, and this method does not even raise an error:
    /// it records a candidate in [`DeclAttempt::check_notes`](crate::attempt::DeclAttempt::check_notes), which only the
    /// gate reads and only when the gate itself rejects. `Layer::Prog` against
    /// [`Elaborator::goal_psi`] is [[auto-refl-empty-block]]'s gate, for its reason
    /// (a type mentioning an outstanding goal must still be well-scoped).
    ///
    /// **One outcome is silence rather than an error**, and it is the
    /// difference between reporting and judging: out of fuel is *inconclusive*
    /// — the gate has a fresh budget and may well succeed, and a message about
    /// two types that might yet convert is worse than no message. Only
    /// `NotConvertible`, which is the decided answer, is reported.
    pub(crate) fn note_check_mismatch(&self, cx: &Cx, got: &Type, expected: &Type, lvl: &Level, span: Span) {
        self.note_check_clash(cx, got, expected, lvl, span, None)
    }

    /// [`Self::note_check_mismatch`] for an argument whose type disagreed
    /// with an implicit already solved: the clash is said beside the
    /// mismatch if the gate refuses (issues/unifier-checked-assignment.md).
    pub(crate) fn note_check_clash(&self, cx: &Cx, got: &Type, expected: &Type, lvl: &Level, span: Span, clash: Option<application::SlotClash>) {
        self.note_check_candidate(cx, got, expected, lvl, span, clash, None)
    }

    /// [`Self::note_check_mismatch`] for a written expression `e`. A call's
    /// head is kept, and read only if the gate refuses: a call to a `partial
    /// fn` is then refused naming the function rather than only the two
    /// types (issues/partial-fn-use-site-refusal.md).
    pub(crate) fn note_check_expr(&self, cx: &Cx, e: &Expr, got: &Type, expected: &Type, lvl: &Level) {
        let head = match &e.kind {
            ExprKind::App { head, .. } => match &head.kind {
                ExprKind::Var(name) => Some(name),
                _ => None,
            },
            _ => None,
        };
        self.note_check_candidate(cx, got, expected, lvl, e.span, None, head.filter(|_| got != expected).cloned())
    }

    /// The candidate itself, with the two optional additions to its message.
    #[allow(clippy::too_many_arguments)]
    fn note_check_candidate(
        &self,
        cx: &Cx,
        got: &Type,
        expected: &Type,
        lvl: &Level,
        span: Span,
        clash: Option<application::SlotClash>,
        partial: Option<String>,
    ) {
        // **Recording is not probing** (`issues/elab-diagnostic-probe-cost.md`).
        // The conversion below used to run here, on every checking site of
        // every declaration, to find out whether there was anything to say —
        // and on a run where nothing fails, every one of those answers was
        // discarded. What is kept here is the *candidate*: the two types, the
        // context they were compared in, and the span. The probe runs in
        // [`Self::probed_check_note`], only when the gate has actually
        // rejected the declaration.
        //
        // The one filter cheap enough to apply at record time is syntactic
        // equality, which is a decision — identical types convert — and not a
        // probe, so it costs nothing and shortens the list.
        if got == expected {
            return;
        }
        stats::count(stats::Counter::DiagCandidates);
        self.attempt.check_notes.borrow_mut().push(CheckNote {
            span,
            cx: Rc::new(cx.clone()),
            got: got.clone(),
            expected: expected.clone(),
            level: lvl.clone(),
            clash,
            partial,
        });
    }

    /// The deferred half of [`Self::note_check_mismatch`]: run one recorded
    /// candidate's conversion and spelling, and return the message if it has
    /// one.
    ///
    /// A diagnostic probe is elaborator-side conversion run for the *message*,
    /// not for the judgement. That is what makes it its own column
    /// (`docs/instrumentation-design.md` §5) rather than a share of the body
    /// walk that contains the site — and now that the probe runs only on
    /// rejection, the column reads as what it always meant: on a successful
    /// module it is zero.
    fn probed_check_note(&self, note: &CheckNote) -> Option<(MismatchNote, Span)> {
        stats::count(stats::Counter::DiagNotes);
        let _phase = stats::guard(stats::Timer::DiagNote);
        let CheckNote {
            span,
            cx,
            got,
            expected,
            level,
            clash,
            partial,
        } = note;
        if self
            .goal_oracle()
            .convert_type(&cx.gamma, Layer::Prog, got, expected, level)
            != Err(ConvError::NotConvertible)
        {
            return None;
        }
        // **Readable, or located.** This message makes a claim about two
        // types, and a claim the reader cannot check is worse than no claim:
        // so the claim is made only when both types spell *entirely* in
        // surface — no raw node anywhere — and do not spell **alike**. The
        // look-alike case is real and is where the display's own limit shows:
        // `And<…>` against `And<…>`, whose type arguments are the whole
        // difference ([[display-inductive-type-arguments]]).
        //
        // Below that bar the conversion was still *decided* here, so the site
        // is known, and it used to be dropped with the claim: a stuck `match`
        // in an inferred type (a commuting conversion the kernel does not
        // have) came back as a bare `NotConvertible` at the declaration and
        // was found by bisecting a generated proof by hand
        // (issues/elab-accepts-projection-through-opaque-theorem.md). So the
        // gate's verdict stays, as [`Self::note_refl_mismatch`]'s does, the
        // span moves to the site, and the note says only what it can show.
        //
        // A receiver placed into a type-owned member's unmarked first
        // parameter says more than the two types do: the declaration forgot
        // `self` (issues/type-member-missing-self-diagnostic.md).
        if let Some(msg) = Members(self).unmarked_receiver_note(cx, *span, got) {
            return Some((MismatchNote::Spelled(msg), *span));
        }
        // Likewise a receiver at another instance of the member's type: the
        // member is what the reader wrote the call to, so it is named
        // (issues/width-specific-method-on-other-width.md).
        if let Some(msg) = Members(self).member_receiver_note(cx, *span, got, expected) {
            return Some((MismatchNote::Spelled(msg), *span));
        }
        // A `partial fn`'s call where its result is expected: the function
        // is named, with the ways out (docs/partial-functions-design.md §4.2).
        if let Some(msg) = partial.as_ref().and_then(|f| Partial(self).partial_use_note(cx, f, got, expected)) {
            return Some((MismatchNote::Spelled(msg), *span));
        }
        let got_s = self.display_type_clean(cx, got);
        let want_s = self.display_type_clean(cx, expected);
        let note = match (got_s, want_s) {
            (Some(g), Some(w)) if g != w => MismatchNote::Spelled(format!(
                "this has type `{g}`, but `{w}` is expected here{}{}{}",
                clash.as_ref().map(|c| self.slot_clash_note(cx, c)).unwrap_or_default(),
                self.opaque_equation_note(cx, got, expected),
                Casts(self).cast_help(cx, got, expected, *span),
            )),
            (Some(g), Some(_)) => MismatchNote::Located(format!(
                "this has type `{g}` where a type that displays the same is expected; \
                 they differ in something the display does not show"
            )),
            (None, Some(w)) => MismatchNote::Located(format!(
                "the type of this expression does not convert to `{w}` \
                 (its own type has no surface spelling)"
            )),
            (Some(g), None) => MismatchNote::Located(format!(
                "this has type `{g}`, which does not convert to the type expected here \
                 (that type has no surface spelling)"
            )),
            (None, None) => MismatchNote::Located(
                "the type of this expression does not convert to the type expected here \
                 (neither has a surface spelling)"
                    .to_string(),
            ),
        };
        Some((note, *span))
    }

    /// What an argument's [`application::SlotClash`] adds to its mismatch:
    /// the implicit, what an earlier argument solved it to, and what this
    /// one's type says. Each value is spelled as the type it decodes to when
    /// the slot is a type, as a term otherwise; one that does not spell
    /// leaves the clause out rather than show a raw node.
    fn slot_clash_note(&self, cx: &Cx, clash: &application::SlotClash) -> String {
        let show = |t: &Rc<Term>| match &clash.dom {
            Some(Type::Ty(level)) => {
                self.display_type_clean(cx, &Type::El { level: level.clone(), tm: Rc::clone(t) })
            }
            _ => self.spell_term_clean(cx, t),
        };
        let name = &clash.name;
        let first = show(&clash.first);
        if clash.guessed {
            // A guess is the head with its leading arguments, the last one
            // abstracted ([`unification::Guesses`]); the reader who meant
            // another argument writes the λ.
            let guess = first.or_else(|| self.spell_type_constructor(cx, clash)).map(|f| format!(" as `{f}`")).unwrap_or_default();
            let later = match clash.later.as_ref().and_then(show) {
                Some(later) => format!(", and this argument's type would make it `{later}`"),
                None => String::new(),
            };
            return format!(
                "; `{name}` was guessed{guess}{later}: no argument fixes it, so it took the type's \
                 constructor with every argument but the last, and abstracted the last. If \
                 another argument is the one that varies, give `{name}` as a λ \
                 (`{name} := λ A => …`)"
            );
        }
        match (first, clash.later.as_ref().and_then(show)) {
            (Some(first), Some(later)) if first != later => format!(
                "; `{name}` was inferred as `{first}` from an earlier argument, \
                 and this argument's type would make it `{later}`"
            ),
            _ => format!("; `{name}` was inferred from an earlier argument, and this argument's type disagrees"),
        }
    }

    /// A solution at a type-constructor slot (`M: Type → Type`), spelled
    /// applied to a hole: `Pair2<Nat>` as `Pair2<Nat, ·>`, the argument it
    /// abstracted shown where it goes. `None` for any other slot type, or a
    /// solution that does not spell.
    fn spell_type_constructor(&self, cx: &Cx, clash: &application::SlotClash) -> Option<String> {
        let Some(Type::Pi { dom_level, cod_level, dom, cod }) = &clash.dom else { return None };
        let (Type::Ty(_), Type::Ty(level)) = (&**dom, &**cod) else { return None };
        let mut hole = cx.clone();
        hole.push("·".to_string(), (**dom).clone(), dom_level.clone());
        let tm = Term::App {
            fun: Rc::new(clash.first.shift_local(1)),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(dom.shift_local(1)),
            cod: Rc::new(cod.shift_local_above(1, 1)),
            arg: Rc::new(Term::Var(LocalVar(0))),
        };
        self.display_type_clean(&hole, &Type::El { level: level.clone(), tm: Rc::new(tm) })
    }

    /// The first recorded checking mismatch that has something to say, probed
    /// in the order the sites were met: the first *spelled* one, else the
    /// first one that is only located.
    ///
    /// Recording order plus "stop at the first" is exactly the eager version's
    /// "the first note to fill the slot wins": the same candidates are tried in
    /// the same order and the same one answers. What changed is that the ones
    /// after it are never run — and that on a declaration the gate accepts,
    /// none of them is. A located note does not stop the search: it used to be
    /// silence, and a later site that names both types (or a `refl` note,
    /// which [`Refusals::kernel_error`](crate::refusals::Refusals::kernel_error) tries before it) says more.
    pub(crate) fn pending_mismatch(&self) -> Option<(MismatchNote, Span)> {
        let notes = self.attempt.check_notes.borrow();
        let mut located = None;
        for note in notes.iter() {
            match self.probed_check_note(note) {
                Some((MismatchNote::Spelled(msg), at)) => {
                    return Some((MismatchNote::Spelled(msg), at));
                }
                Some(found) => {
                    located.get_or_insert(found);
                }
                None => {}
            }
        }
        located
    }

    /// The first checking mismatch recorded since note `from` that the probe
    /// decides, as an error: for a construction the declaration gate never
    /// sees, such as an `IWf`-route family's signature built at its
    /// declaration (`inductive.rs`), where nothing else would refuse it.
    pub(crate) fn mismatch_since(&self, from: usize) -> Option<ElabError> {
        let notes = self.attempt.check_notes.borrow();
        notes.iter().skip(from).find_map(|note| {
            self.probed_check_note(note).map(|(m, span)| {
                let (MismatchNote::Spelled(msg) | MismatchNote::Located(msg)) = m;
                ElabError::Elab { msg, span }
            })
        })
    }

    /// [`Self::note_check_mismatch`] at the one checking form that compares
    /// nothing (`issues/elab-refl-accepts-match-eta-kernel-rejects.md`).
    ///
    /// A written `refl` emits `Refl(lhs)` against the goal's `lhs = rhs` and
    /// leaves the equation to the kernel — deliberately, and still. The cost
    /// was the message: a false equation came back as `NotConvertible` at the
    /// whole declaration, naming neither side, which is how three library
    /// proofs about `int::Int::add` were debugged the hard way. The note is filled
    /// here and read only by the gate, only when the gate rejects, so nothing
    /// is reported that the kernel did not refuse.
    ///
    /// **It adds to the gate's report; it does not replace it**, which is
    /// where this parts company with [`Self::note_check_mismatch`]. A refusal
    /// spelled `NotConvertible` at a named declaration is what the certifying
    /// pipeline's mutation controls read — a corrupted ELF header must be
    /// refused *by conversion*, not by a parse slip — and those refusals are
    /// `refl` pins whose sides are far too large to spell. So the verdict and
    /// its class stay, the span moves to the `refl`, and the two sides are
    /// appended when they can be shown.
    ///
    /// **Budgeted, and silent when the budget runs out.** Unlike the checking
    /// note, this conversion is work the kernel is about to do again, and the
    /// sides of an expensive `refl` — a certificate pinned against its
    /// transcription — are exactly where repeating it would be felt. A small
    /// budget keeps the cost of the note proportional to what it can say: a
    /// disagreement between a stuck `match` and its scrutinee is decided in a
    /// handful of steps, and anything that outruns the budget is inconclusive
    /// (`OutOfFuel`, never a wrong `NotConvertible`) and says nothing. Two
    /// syntactically identical sides skip even the world the oracle needs.
    pub(crate) fn note_refl_mismatch(
        &self,
        cx: &Cx,
        lhs: &Term,
        rhs: &Term,
        ty: &Type,
        level: &Level,
        span: Span,
    ) {
        if lhs == rhs {
            return;
        }
        // Recorded, not probed — [`Self::note_check_mismatch`]'s reason, and
        // the expensive half of it: the certificate is thousands of `refl`
        // pins whose two sides are large, and a budgeted conversion on every
        // one of them was 18% of a successful build
        // (`issues/elab-diagnostic-probe-cost.md`).
        stats::count(stats::Counter::DiagCandidates);
        self.attempt.refl_notes.borrow_mut().push(ReflNote {
            span,
            cx: Rc::new(cx.clone()),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            ty: ty.clone(),
            level: level.clone(),
        });
    }

    /// The deferred half of [`Self::note_refl_mismatch`]
    /// ([`Self::probed_check_note`]'s counterpart at the `refl` form).
    fn probed_refl_note(&self, note: &ReflNote) -> Option<(String, Span)> {
        // [`Self::probed_check_note`]'s column, for the same reason: the
        // conversion below is the note's, not the gate's.
        stats::count(stats::Counter::DiagNotes);
        let _phase = stats::guard(stats::Timer::DiagNote);
        let ReflNote {
            span,
            cx,
            lhs,
            rhs,
            ty,
            level,
        } = note;
        let oracle = oracle::SemanticOracle::in_world(
            self.goal_psi(),
            self.policy.fuel.min(diagnostics::REFL_NOTE_FUEL),
        );
        if oracle.convert_term(&cx.gamma, Layer::Prog, lhs, rhs, ty, level)
            != Err(ConvError::NotConvertible)
        {
            return None;
        }
        // Readable or silent, for [`Self::note_check_mismatch`]'s reason: two
        // sides the reader cannot check, or that spell alike, are worse than
        // the gate's honest `NotConvertible`.
        let (Some(lhs_s), Some(rhs_s)) = (
            self.spell_term_clean(cx, lhs),
            self.spell_term_clean(cx, rhs),
        ) else {
            return None;
        };
        if lhs_s == rhs_s {
            return None;
        }
        let opaque = self
            .opaque_stuck_note(&oracle, cx, &[lhs, rhs])
            .map_or_else(String::new, |why| format!("; {why}"));
        Some((
            format!(
                "`refl` needs both sides to be definitionally equal, \
                 but `{lhs_s}` and `{rhs_s}` are not{opaque}"
            ),
            *span,
        ))
    }

    /// [`Self::opaque_stuck_note`] for a checking note between two
    /// equations, read at their endpoints, as a suffix for the message. Only
    /// for two types that both spell — the probe has shown they are small
    /// enough to read — and only for an equation as written: a type is not
    /// reduced to find one, since a certificate's pinned equations are where
    /// reducing again costs what the gate's own check does.
    fn opaque_equation_note(&self, cx: &Cx, got: &Type, expected: &Type) -> String {
        let oracle = oracle::SemanticOracle::in_world(
            self.goal_psi(),
            self.policy.fuel.min(diagnostics::REFL_NOTE_FUEL),
        );
        let ends: Vec<&Term> = [got, expected]
            .into_iter()
            .filter_map(|ty| match ty {
                Type::Id { lhs, rhs, .. } => Some([&**lhs, &**rhs]),
                _ => None,
            })
            .flatten()
            .collect();
        self.opaque_stuck_note(&oracle, cx, &ends)
            .map_or_else(String::new, |why| format!("; {why}"))
    }

    /// Why a side of a refused conversion will never compute, when the
    /// reason is a global that does not unfold
    /// (`issues/stuck-on-opaque-theorem-diagnostic.md`). "`ex().witness` and
    /// `3` are not" reads as "the number is wrong" to a writer used to `fn`s;
    /// what is wrong is that nothing ever computes `ex().witness`.
    ///
    /// A side qualifies when its whnf is stuck eliminating
    /// ([`oracle::SemanticOracle::eliminated_global`]) a named, body-less
    /// global with no sealed proof: an `axiom`, or a `theorem` whose
    /// statement [`sealing::carries_data`](crate::sealing::carries_data) did not accept. A theorem whose
    /// statement carries data is opened by the elimination, so meeting one
    /// here means the budget ran out first, and nothing is claimed. Only on a
    /// refusal the probe already decided, so it costs an evaluation of each
    /// side under the same small budget, on the error path.
    fn opaque_stuck_note(
        &self,
        oracle: &oracle::SemanticOracle,
        cx: &Cx,
        sides: &[&Term],
    ) -> Option<String> {
        sides.iter().find_map(|side| {
            let abs = self.global_abs_of(oracle.eliminated_global(&cx.gamma, side)?)?;
            let Some(GlobalBinding::Tm { body: None, .. }) = self.psi.bindings.get(abs) else {
                return None;
            };
            if self.psi.sealed.get(abs).is_some() {
                return None;
            }
            let report = self.provenance.report(&NameLookup(self).global_qualified_name_at(abs)?)?;
            let name = NameLookup(self).global_declared_name_at(abs)?;
            Some(if report.is_axiom {
                format!(
                    "`{name}` is an axiom, so it has no proof to unfold \
                     and what is stuck on it never computes"
                )
            } else {
                format!(
                    "`{name}` is a theorem whose statement was not judged to carry data, \
                     so its proof is not kept and never unfolds; \
                     to compute with what it builds, declare it as a `fn`"
                )
            })
        })
    }

    /// The first recorded `refl` that has something to say, in the order the
    /// `refl`s were met — [`Self::pending_mismatch`]'s counterpart, preserving
    /// the same first-wins order for the same reason.
    pub(crate) fn pending_refl_note(&self) -> Option<(String, Span)> {
        let notes = self.attempt.refl_notes.borrow();
        notes.iter().find_map(|n| self.probed_refl_note(n))
    }
}
