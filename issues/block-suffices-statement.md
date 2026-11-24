---
title: Block-level suffices statement for forward-readable backward reasoning
status: closed
labels: [frontend,syntax,proofs,ergonomics]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-24
updated: 2026-11-24
closed: 2026-11-24
---

Block-level `suffices [h:] P by justify; <rest>` for forward-readable backward
reasoning: state the intermediate goal `P` and the short justification `justify`
from `P` to the current goal upfront, then prove `P` across the remainder of
the block without nesting braces.

## Resolution

- **Parser (`crates/syntax/src/parser.rs`):** contextual Rule-1 keyword
  `suffices` (`at_suffices` scans at bracket depth 0 for `by` before `;`/`}`),
  keeping locals named `suffices` valid everywhere.
  - Named `suffices h: P by justify; <rest>` lowers to `{ have h: P = <rest>; justify }`.
  - Anonymous `suffices P by justify; <rest>` lowers to `\0suffices(TyLit(P), justify, <rest>)`.
- **Elaborator (`crates/elab/src/binding.rs`, `checking.rs`, `inference.rs`):**
  `Bindings::elab_suffices` checks `<rest>` at `P` and tries `justify` both at
  `expected` with an opaque local `__suffices : P` in scope (for tactics like
  `omega`/`linarith`) and as a function `P → expected` applied to `<rest>`.
- **Tests:** `lib/_tests/std/core/destructure_suffices_tests.hthr` and
  `crates/syntax/src/parser.rs`.



