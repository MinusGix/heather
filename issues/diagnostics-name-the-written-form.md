---
title: Diagnostics inside a desugared or generated match name the wrong form and site
status: open
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
2. **A non-exhaustive *inner* column of a deep pattern reports at the outer
   `match`** (`docs/nested-match-patterns-design.md` §3.4). The generated
   inner `match` carries the whole match's span, because there is no source
   text for the level it is reporting about — the user wrote a *pattern*, and
   the missing constructor belongs to a column, not to an arm. Pinned by
   `a_deep_match_with_no_fallthrough_is_not_exhaustive` in
   `crates/elab/tests/nested_match_patterns.rs`, so an improvement has to
   change a test deliberately.

The shape of a fix is the same for both: thread a *site* — a form name and a
span — into the five message sites, set by whoever built the arms. It was
declined twice for the same reason (five messages and their tests for a
cosmetic gain), which is the argument for giving it one owner rather than
re-deciding it every round.

## What it assumes from elsewhere

- **[[match-with-equation]]** / **[[split-on-arms]]** and
  **[[nested-match-patterns]]** own their desugarings. Assumed here: only that both build
  `ExprKind::Match` nodes the elaborator cannot distinguish from written ones,
  which is the property that makes the messages wrong and is also the property
  that made both rounds cheap.

## Log

- 2026-08-09: Partial payment from the operators round: operator applications now render as written (a + b, not add(a)(b)) via render_expr's re-sugaring.
- 2026-08-16: ITEM 1 FIXED (2026-08-16); item 2 untouched and this issue stays open for it. A `form: MatchForm` field on ExprKind::Match carries the spelling that built the node, and every message that names a form asks it instead of saying `match`. THREE CORRECTIONS to the issue and to the design paragraph it quotes, all found by doing it rather than by reading. (a) IT IS SEVEN NAMING SITES, NOT FIVE, and not the five the split design listed: three of those (unknown constructor, duplicate arm, wrong arity) never named a form at all and needed nothing, while four the list missed did — the `Fin` two-arm check, the `Fin` open-length refusal, the empty types "takes no arms", and the missing-motive refusal. The three "`match` is missing an arm" copies (inductive.rs, indexed.rs, forded.rs) are one message at three sites. (b) IT WAS NOT PURELY COSMETIC, which is the argument that had declined it twice: the missing-motive message suggested `match e as λ z => T { … }`, a spelling a writer who typed `split` CANNOT PASTE. It now suggests `split e as λ z => T;`, and a test checks that the suggestion checks — advice that does not parse is a worse defect than a wrong noun, and nothing in the two declines had noticed it. (c) The threading is NOT the "site (form name + span)" the issue specified, because the span half turned out to be already correct: `split`s desugaring spans start.join(end) over the written `split … on …` text, so the reported span was pointing exactly where the user typed all along. Only the noun was wrong. Mechanics: the parser sets Match/Split at its two construction sites; elab_match and elab_convoy take the form and pass it to the five lowerings (data/indexed/forded/nat/fin); the pattern compiler carries it in `Compile` so a GENERATED inner level inherits the written form rather than hardcoding one. That last is honest-but-unobservable today and is recorded as such: a generated inner level is reachable only from deep patterns, and a `split` arms binders are plain names, so no `split` can reach one — the field is there because a generated node must carry SOME form and inheriting is the only answer that cannot become a lie later. The tautology the split design bought is intact and is why the field is safe: both spellings still build one elimination, from scrut/eqbind/motive/arms, and nothing that computes a term may read `form` — it carries a keyword, not a variant of behaviour. WHAT ITEM 2 STILL WANTS, now sharper: the form half and the span half are SEPARABLE, not one fix as this issue assumed. An inner column of a split now says `split`; what it still cannot do is point AT the column, because a generated level has no source text — which is item 2s own observation, and a_deep_match_with_no_fallthrough_is_not_exhaustive still pins the outer span, unchanged and still green. FOUND IN PASSING, not fixed, deliberately: reprgens fragment-decline messages (crates/elab/src/reprgen.rs ~690-706, "`{op}`s body is not a bare `match`", "`{op}`s match has N arms for M constructors") are a THIRD instance of this wart in a subsystem neither of the two rounds touched — a datarepr transfer body written as a `split` is accepted and then described as a `match`. Left alone because those messages describe a documented fragment SHAPE rather than diagnosing the users spelling, and fixing them means threading the form into the generator; if it bites, it is a small follow-up on this same field. Tests +3 in crates/elab/tests/match_equation_split.rs: a_splits_diagnostics_name_split (all seven, one assertion each, plus the pasteable-spelling assertion), a_matchs_diagnostics_still_name_match (the control at all seven — without it, hardcoding `split` would pass), and the_suggested_split_motive_spelling_checks (the advice, elaborated). Two existing assertions were checked rather than re-baselined: a_splits_arms_are_checked_like_a_matchs matches on `Succ` and `duplicate arm`, a_split_needs_an_inductive on `declared inductive`, and all three substrings survive the rewording. Docs: match-equation-split-design.md §6s cost paragraph marked paid with corrections (a) and (b); nested-match-patterns-design.mds inner-column bullet amended to say the form half is paid and the span half is not. Suite 1652 -> 1655, full run on the final tree; scripts/bench --check: 18 comparisons within thresholds.
