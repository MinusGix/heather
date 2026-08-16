---
title: Allow per-name modifiers inside a shared-annotation run: `g as ∙, h: T` and `self x, y: T`
status: closed
labels: [frontend,ergonomics,parser]
created: 2026-08-11
updated: 2026-08-16
---

**Decided on user review (2026-08-11): allow.** Not urgent; filed so the two
refusals are lifted together when someone is in the parser anyway.

The multi-binder round refused a modifier anywhere in a shared run — `self x,
y: A` and, following its precedent, the op-as round refused `g as ∙, h: A ->
A -> A` — under the sentence "a modifier prefixes exactly one name." The user
review read that sentence the other way, and the other way is right: the
modifier *does* prefix exactly one name — the one it is written on — and the
annotation is the only thing the run shares. `g as ∙, h: A -> A -> A` is
unambiguously "`g` carries `∙`; `g` and `h` are both `A -> A -> A`", and
`fn List::concat<A>(self x, y: List<A>)` is structurally sensible the same
way. Nothing downstream cares: the symbol's scope already starts at its own
binder, `check_symbol_free` runs per spelling not per group, and `self` is a
per-parameter flag.

What lifting costs: the two parser refusal sites (both in the fn/theorem
parameter loop; the `as` one also guards nothing else), reading the modifier
per-name inside the run instead of erroring at the comma, and rewording the
design-doc sentence to what it now means — a modifier attaches to the name it
prefixes, per-name, not per-group. Tests: the two refusal tests become
positive pins (symbol on the first name of a run, `self` likewise), plus a
control that the *second* name of a run may carry its own `as` and that two
symbols in one run still hit the uniqueness rule.

## What it assumes from elsewhere

- **[[binder-symbol-as-notation]]** (closed) owns the as-device. Assumed here:
  only that a binder's symbol scope starts at the binder itself.
- **[[multi-binder-function-types]]** (closed) owns the shared run. Assumed
  here: only that the run desugars to the curried chain per-name, so a
  per-name flag has an obvious binder to land on.

## Log

- 2026-08-16: LANDED. A modifier is now read per NAME inside a shared-annotation run: 'fn f(self x, y: A)' marks x and leaves y an ordinary parameter of the same type, and 'fn f(g as ∙, h: A -> A -> A)' gives the symbol to g alone. Both refusals are gone.

Mechanics: the fn/theorem parameter loop (crates/syntax/src/parser.rs) parses a group as a loop over ENTRIES — 'self? name (as ∙)?' — with the shared ': T' read once at the end, and carries (name, span, is_self, symbol) per entry into the push. Nothing downstream moved, as the issue predicted: check_symbol_free already ran per spelling, and elab's symbol-installation loop already walked params one at a time.

The one rule that did NOT relax: at most one self per declaration. Its scan had to grow — it looked only at 'params', and a run's names are not pushed there until the annotation is read, so 'self x, self y: Nat' would have slipped through. It now scans the run it is standing in as well, and names the earlier binder the same way. The solver check ('self' cannot take ':= infer') moved from the group flag to 'any name in this run is the receiver'.

Tests +3, suite 1643 -> 1646 (full run, this tree). The two refusal tests became positive pins: parser.rs's a_modifier_prefixes_a_single_name now asserts 'self x: Nat, y: Nat' and 'self x, y: Nat' are the SAME two parameters (plus a later-name case 'x, self y'), and as_marks_a_single_parameter became as_marks_the_name_it_is_written_on_inside_a_run (symbol on the first name, None on the rest; 'g as ∙, h as +' gives each its own). New: two_selfs_in_one_run_are_still_refused; binder_symbol_notation's a_symbol_in_a_shared_run_reaches_only_its_own_name (checking position — a theorem statement — at an open carrier, with a negative control); method_receiver's a_marked_subject_may_be_a_name_inside_a_shared_run (receiver position pinned through n.pick(1,3) = pick(1,n,3)). The uniqueness control the issue asked for is in a_declaration_installs_each_spelling_once: two 'as ∙' in one run hit the same collision with the same message, two different symbols in one run both install.

Docs: dated amendments rather than rewritten history, at docs/surface-function-types.md §1.1's superseded note and docs/operators-onto-classes-design.md's modifier bullet. The sentence needed no replacing — 'a modifier prefixes exactly one name' was always true, and the name it prefixes is the one it is WRITTEN on; the amendment says the reading is per-name, not per-group.

Checked and deliberately out: valparam_list (class heads, record value parameters) has no shared-annotation run at all — every value parameter is 'name: T' — so there was nothing to lift there. The record 'as' refusal stands: it is about what a binder is, not where its modifier sits.
- 2026-08-16: Verification on the final tree: full scripts/test 1646 passed, 0 failed; scripts/bench --check 18 comparisons within thresholds.
