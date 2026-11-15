---
title: Export the Nat, Bool, logic and List library and record every stop
status: closed
labels: [translation,export]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-20
updated: 2026-10-21
---

The `export-fragment` milestone is done when a closed, layer-free fragment of
the library (Nat and List lemmas) is translated and rechecked in Lean
(`docs/roadmap.md`). The prototype covers a test source only. This round runs
the exporter over the real modules, `lib/std/num/nat.hthr`, `bool.hthr`,
`logic.hthr` and `list.hthr`, through the CLI's loader, and records by cause
every declaration that is:

- refused by the exporter (the cause is the `Refusal` text);
- rejected by Lean or Rocq (the cause is the first failing conversion,
  classified against `docs/library/export-fragment-design.md` §6's list);
- too slow in the target (§5.4).

The table of causes is the deliverable, more than the pass count. It is the
list a trusted-fragment theorem would have to cover
([[export-checks-theorem]]). It also tests the conjecture of §5.1: that the
elaborator's generated code never uses `elim_Wf`'s β at an open tag. That
needs [[export-wf-native-inductives]] for `List`, and the sweep can land Nat,
Bool and logic before it. Decided 2026-10-21 (design §11.3): violations
are counted here, syntactic open-tag redexes are pre-reduced by the
exporter, and only conversion-created ones would motivate a Heather-side
change.

Rechecking stays opt-in (`scripts/export-recheck`): the suite does not
assume Lean or Rocq is installed.

## Log

- 2026-10-21 (PR #87): first sweep, over the closure of `lib/std/data/list.hthr`
  (`crates/export/tests/library_sweep.rs`, which pins the refusal causes).
  387 bindings, 293 exported; every refusal is `Wf` (90) or mentions one
  (4), so Nat, Bool, logic, option and pair export whole and `List` waits
  on [[export-wf-native-inductives]]. Lean accepts all of them: 292 through
  the kernel route in about two seconds (`bool::is_true_dec_yes` keeps a
  hole, [[export-typed-translation]]) and all 293 as source text, slowly
  (design §7). No target rejection is left to classify yet; the open-tag β
  count waits for the `Wf` realisation.
- 2026-10-21, later: with [[export-wf-native-inductives]] all 387 bindings
  export, and Lean's kernel accepts all but the two bodies that keep holes
  (`bool::is_true_dec_yes`, `List::filter_map`;
  [[export-typed-translation]]). No target rejection is left to classify.
  The open-tag β count is zero, because Lean would reject any declaration
  that needed it, and a negative control shows it does. That meets the
  milestone's "done when" for this closure, so this issue closes. A sweep
  over more of `lib/std` (rationals, reals, the native modules) is the next
  milestone-sized step, and belongs to the owner issue.
