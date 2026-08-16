---
title: Diagnostics inside a desugared or generated match name the wrong form and site
status: closed
labels: [frontend,diagnostics]
created: 2026-08-05
updated: 2026-08-16
---



Two rounds have now shipped a desugaring whose diagnostics name the form the
*elaborator* sees rather than the one the user wrote. Neither is misleading —
the constructor names and the arm in question are always correct — but both
point somewhere the user did not type.

1. **`split` says `match`** (`docs/match-equation-split-design.md` §6). Five
   message sites in `inductive.rs` / `elab_match_nat` say "`match` is missing
   an arm for `C`" at a block whose text says `split`/`on`.
   **FIXED** — the eliminations 2026-08-16, reprgen and the pattern compiler
   the same day (see the log; it was never five sites, nor seven). Every
   message that names a form now asks the node's `MatchForm`.
2. **A non-exhaustive *inner* column of a deep pattern reports at the outer
   `match`** (`docs/nested-match-patterns-design.md` §3.4). The generated
   inner `match` carries the whole match's span, because there is no source
   text for the level it is reporting about — the user wrote a *pattern*, and
   the missing constructor belongs to a column, not to an arm. Pinned by
   `a_deep_match_with_no_fallthrough_is_not_exhaustive` in
   `crates/elab/tests/nested_match_patterns.rs`, so an improvement has to
   change a test deliberately.
   **PROMOTED** to [[inner-column-diagnostic-span]] (2026-08-16), which is why
   this issue closes: the form half is done everywhere, and the span half is a
   different question with its own owner.

The shape of a fix is the same for both: thread a *site* — a form name and a
span — into the five message sites, set by whoever built the arms. It was
declined twice for the same reason (five messages and their tests for a
cosmetic gain), which is the argument for giving it one owner rather than
re-deciding it every round.

*Corrected 2026-08-16*: the two halves are **separable**, and only the form
half was one fix. The form travels on the node (`MatchForm`), so it reaches a
generated level by inheritance; the span cannot, because a generated level
stands for a *column* and has no source text. Item 2 is therefore not residue
of this fix but a question of its own, and it left with
[[inner-column-diagnostic-span]] when this issue closed.

## What it assumes from elsewhere

- **[[match-with-equation]]** / **[[split-on-arms]]** and
  **[[nested-match-patterns]]** own their desugarings. Assumed here: only that both build
  `ExprKind::Match` nodes the elaborator cannot distinguish from written ones,
  which is the property that makes the messages wrong and is also the property
  that made both rounds cheap.

## Log

- 2026-08-09: Partial payment from the operators round: operator applications now render as written (a + b, not add(a)(b)) via render_expr's re-sugaring.
- 2026-08-16: ITEM 1 FIXED (2026-08-16); item 2 untouched and this issue stays open for it. A `form: MatchForm` field on ExprKind::Match carries the spelling that built the node, and every message that names a form asks it instead of saying `match`. THREE CORRECTIONS to the issue and to the design paragraph it quotes, all found by doing it rather than by reading. (a) IT IS SEVEN NAMING SITES, NOT FIVE, and not the five the split design listed: three of those (unknown constructor, duplicate arm, wrong arity) never named a form at all and needed nothing, while four the list missed did — the `Fin` two-arm check, the `Fin` open-length refusal, the empty types "takes no arms", and the missing-motive refusal. The three "`match` is missing an arm" copies (inductive.rs, indexed.rs, forded.rs) are one message at three sites. (b) IT WAS NOT PURELY COSMETIC, which is the argument that had declined it twice: the missing-motive message suggested `match e as λ z => T { … }`, a spelling a writer who typed `split` CANNOT PASTE. It now suggests `split e as λ z => T;`, and a test checks that the suggestion checks — advice that does not parse is a worse defect than a wrong noun, and nothing in the two declines had noticed it. (c) The threading is NOT the "site (form name + span)" the issue specified, because the span half turned out to be already correct: `split`s desugaring spans start.join(end) over the written `split … on …` text, so the reported span was pointing exactly where the user typed all along. Only the noun was wrong. Mechanics: the parser sets Match/Split at its two construction sites; elab_match and elab_convoy take the form and pass it to the five lowerings (data/indexed/forded/nat/fin); the pattern compiler carries it in `Compile` so a GENERATED inner level inherits the written form rather than hardcoding one. That last is honest-but-unobservable today and is recorded as such: a generated inner level is reachable only from deep patterns, and a `split` arms binders are plain names, so no `split` can reach one — the field is there because a generated node must carry SOME form and inheriting is the only answer that cannot become a lie later. The tautology the split design bought is intact and is why the field is safe: both spellings still build one elimination, from scrut/eqbind/motive/arms, and nothing that computes a term may read `form` — it carries a keyword, not a variant of behaviour. WHAT ITEM 2 STILL WANTS, now sharper: the form half and the span half are SEPARABLE, not one fix as this issue assumed. An inner column of a split now says `split`; what it still cannot do is point AT the column, because a generated level has no source text — which is item 2s own observation, and a_deep_match_with_no_fallthrough_is_not_exhaustive still pins the outer span, unchanged and still green. FOUND IN PASSING, not fixed, deliberately: reprgens fragment-decline messages (crates/elab/src/reprgen.rs ~690-706, "`{op}`s body is not a bare `match`", "`{op}`s match has N arms for M constructors") are a THIRD instance of this wart in a subsystem neither of the two rounds touched — a datarepr transfer body written as a `split` is accepted and then described as a `match`. Left alone because those messages describe a documented fragment SHAPE rather than diagnosing the users spelling, and fixing them means threading the form into the generator; if it bites, it is a small follow-up on this same field. Tests +3 in crates/elab/tests/match_equation_split.rs: a_splits_diagnostics_name_split (all seven, one assertion each, plus the pasteable-spelling assertion), a_matchs_diagnostics_still_name_match (the control at all seven — without it, hardcoding `split` would pass), and the_suggested_split_motive_spelling_checks (the advice, elaborated). Two existing assertions were checked rather than re-baselined: a_splits_arms_are_checked_like_a_matchs matches on `Succ` and `duplicate arm`, a_split_needs_an_inductive on `declared inductive`, and all three substrings survive the rewording. Docs: match-equation-split-design.md §6s cost paragraph marked paid with corrections (a) and (b); nested-match-patterns-design.mds inner-column bullet amended to say the form half is paid and the span half is not. Suite 1652 -> 1655, full run on the final tree; scripts/bench --check: 18 comparisons within thresholds.
- 2026-08-16: ITEM 1 IS NOW COMPLETE ACROSS THE CODEBASE, not just at the elimination messages; item 2 (the inner-column SPAN) is untouched and this issue stays open for it alone. Last round's own "found in passing, not fixed" — reprgen's fragment declines — is discharged, and a survey for further instances found a fourth site the seven-site count had also missed. THE COUNT WAS NEVER SEVEN: it was seven ELIMINATION messages, and two other subsystems name a form, both reachable from a written `split`. (a) reprgen (crates/elab/src/reprgen.rs): a datarepr transfer body is read as `ExprKind::Match`, so a body spelled `split` is ADMITTED — which is the split design's §6 working exactly as designed — and was then described back to its author as a `match`. Three messages now read the form off the body they are describing ("body is not a bare `split`", "does not split on its `S` parameter", "`f`'s split has N arms for M constructors"). The fourth, "not a structural `match`", is deliberately NOT threaded and the reasoning is the receiver-method round's: it fires when the body is no case analysis at all, so there is no spelling to name and its `match` is the shape the fragment REQUIRES rather than a claim about what was written. (b) the pattern compiler (crates/elab/src/patterns.rs), which is item 2's own subsystem and was missed anyway: the §6 deep-pattern refusal ("a deep pattern is not available in this `match`") and the arity-disagreement message ("`C` binds N field(s) in an earlier pattern of this `match`"). Both had `form` in hand already — the first through prepare_arms, the second through `Compile`, the field last round added — so both are one-line fixes. Their ADVICE stays `match` on purpose: "a nested `match` inside the arm" names a fresh elimination in the arm body, which either spelling can hold, so it is pasteable as-is (the (b)-class check from last round, applied and passed rather than assumed).

CORRECTION TO LAST ROUND'S OWN NOTE, and the round's one real finding. The `Compile.form` field was recorded as "honest but unobservable today", on the ground that "a `split` arm's binders are plain names, so no `split` can reach a generated inner level". THAT PREMISE IS FALSE. An `on` arm's binders are parsed by `pat_args` — the very same function a `match` arm's go through (crates/syntax/src/parser.rs) — so a deep pattern is writable in a `split` arm, and `split r; on Stuck := d; on OutOfFuel := d; on Out(Out(v)) := v;` reports `` `split` is missing an arm for `Stuck`, `OutOfFuel` `` from the GENERATED inner level. The inheritance is observable, was right all along, and is now pinned rather than asserted. Verified through the CLI under the standing ulimit before writing the test.

NOT FIXED, and not the same problem: certgen.rs's three "a nested `match` is outside the fragment" (~2240-2260) and "a tier-1 `match` in a fn with no tier-1 parameter" (~2345). That pass walks KERNEL TERMS (Term::Case, Term::ElimWf, Term::ElimNat), where the surface form is long gone. Naming the written spelling there means carrying it through elaboration into the kernel, which is a categorically larger question than reading a field off a surface node — so it is recorded here as a known non-instance rather than as residue of this fix.

Tests +4: crates/elab/tests/reprgen.rs gains a_split_bodied_transfer_is_admitted_and_declined_in_its_own_words (the POSITIVE half first — a split-bodied `slength` transfers and installs its `Impl`, which nothing had pinned — then the three declines, each also asserting the message does not contain "match") and a_match_bodied_transfers_declines_still_name_match (the control at the same three shapes; without it, hardcoding `split` passes). crates/elab/tests/match_equation_split.rs gains a_splits_deep_patterns_name_split (the generated inner level, asserted at BOTH missing constructors so it cannot drift onto the outer column's message; the §6 refusal, with its advice asserted to stay `match`; the arity disagreement) and a_matchs_deep_patterns_still_name_match. Docs: match-equation-split-design.md §6 gains a "Completed 2026-08-16" paragraph listing both subsystems, the one deliberately-unthreaded message and the certgen non-instance; nested-match-patterns-design.md §11's inner-column bullet is amended a second time to retract the unobservability claim. Suite 1655 -> 1659, full run on the final tree; scripts/bench --check: 18 comparisons within thresholds.
