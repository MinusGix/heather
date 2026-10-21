---
title: Export the Nat, Bool, logic and List library and record every stop
status: open
labels: [translation,export]
area: heather-in-lean-coq
milestone: [export-fragment]
created: 2026-10-20
updated: 2026-10-20
---

The `export-fragment` milestone is done when a closed, layer-free fragment of
the library (Nat and List lemmas) is translated and rechecked in Lean
(`docs/roadmap.md`). The prototype covers a test source only. This round runs
the exporter over the real modules, `lib/std/nat.hthr`, `bool.hthr`,
`logic.hthr` and `list.hthr`, through the CLI's loader, and records by cause
every declaration that is:

- refused by the exporter (the cause is the `Refusal` text);
- rejected by Lean or Rocq (the cause is the first failing conversion,
  classified against `docs/export-fragment-design.md` §6's list);
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
