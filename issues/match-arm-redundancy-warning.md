---
title: Report unreachable match rows and redundant `_` arms
status: closed
labels: [frontend,elaboration,diagnostics]
created: 2026-08-05
updated: 2026-08-16
---



The pattern compiler ([[nested-match-patterns]],
`docs/nested-match-patterns-design.md` §3.4) computes neither redundancy nor
reachability, and both silences are deliberate rather than forgotten:

- a row shadowed by an earlier one never reaches a leaf, so its body is never
  elaborated — harmless (the hole pre-count is documented as an upper bound)
  and invisible;
- a `_` arm with nothing left to expand to is **dropped**, because the
  compiler emits redundant `_` arms itself (a `Nat` column already covered by
  `Zero` and `Succ`), so refusing one would have meant marking generated arms
  and the pass remembering which spelling produced it.

Both want the same thing, and it is the thing that does not exist: a
**warning** channel. `check_source` returns `Vec<ElabError>` and every
diagnostic is fatal, so "this is dead code" has nowhere to be said. Making
redundancy an *error* is the wrong trade — it turns a refactor that adds a
constructor arm into a build break at every `_` that used to cover it.

## What it assumes from elsewhere

- **[[nested-match-patterns]]** owns the pattern compiler. Assumed here: only
  that a generated `_` arm is indistinguishable from a written one, which is
  what makes "refuse a redundant `_`" unavailable without new bookkeeping.

## Log

- 2026-08-16: LANDED 2026-08-16, both halves, with the warning channel this issue was parked on (docs/diagnostic-warnings-design.md — new, §7 is this customer). Unreachable rows and redundant `_` arms are now REPORTED, as warnings, on a file that still checks.

THE ANALYSIS WAS ALREADY THERE, which is why one round paid for both halves this issue lists. `Compile.uses[i]` — the leaf census §5 of the nested-match design computes to decide between SHARING an arm's body and copying it — is exactly "how many leaves arm i's body reached", so reachability is not a new pass: it is that number being zero, at a branch `settle` already had (`0 => {}`, where an unelaborated body gets dropped). One `self.warn` there covers both a shadowed deep row and a `_` that stands for nothing.

THE STATED BLOCKER WAS REAL, and is paid rather than dodged. This issue said refusing a redundant `_` "would have meant marking generated arms", because the compiler emits `_` arms of its own and re-runs the pass over them. Marking them is what landed: a `generated: bool` on ExprKind::Match, set by the pattern compiler's emit site and nobody else, read by diagnostics only — the same discipline as, and the field beside, the `form: MatchForm` the diagnostics round added. It suppresses nothing of the user's: one compilation's census spans every level it emits, so reachability for the WRITTEN arms is complete at the outermost pass and the flag only silences a report about our own arms. LOAD-BEARING, verified by removing it rather than by argument: without the guard, `match p { Mk(TA, TA) => 0, Mk(TB, TA) => 1, Mk(x, y) => 2 }` — every written arm reachable — reports a `_` arm that does not occur in the source, pointed at the whole match. That falsification is now the control test.

The issue's second half of the same sentence, "and the pass remembering which spelling produced it", turned out to be free: the form field landed earlier the same day, so the message names `match` or `split` by asking it.

CORRECTION to this issue's own framing of the first bullet: a shadowed row was described as "harmless and invisible". Harmless is right about the emitted term and wrong about what the writer gets — an arm that reaches no leaf is never elaborated, so its body is also NEVER TYPE-CHECKED. The silence hid a body nobody had checked, which is the half that makes this worth a diagnostic rather than a tidiness note, and the message says so.

Deliberately NOT done, unchanged from this issue's own judgment: redundancy as an ERROR. It would turn a refactor that adds a constructor into a build break at every `_` that used to cover it.

Tests: crates/elab/tests/warnings.rs (new, 11), split channel/customer. Customer half: both reported shapes with their messages, both silent controls (a `_` that stands for a real constructor; a match with no `_`, which never enters the pass), the generated-level control above, and the `split` spelling. Checked against the library too, before writing any test: lib/certgen/ir_v1.hthr, list_algos.hthr and vec_code.hthr check with ZERO warnings, so this is not a storm on existing code. Suite 1659 -> 1671, full run on the final tree; scripts/bench --check: 18 comparisons within thresholds.
