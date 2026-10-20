---
title: Deep conjunction facts are read by counting .right; name them
status: open
labels: [surface,proofs,ergonomics]
area: language
created: 2026-10-04
updated: 2026-10-04
---

Raised by Minus (2026-10-04) over
`crates/elab/tests/fixtures/open_read_close.hthr:183`:

```heather
let second = argv.right.proof.right.right.right.right;
```

A fact deep in a right-nested conjunction is reached by counting `.right`s,
and the count is the only thing naming it. The library has 55 lines with
chains of four or more (`grep -c '\.right\.right\.right\.right'` over
`lib/*.hthr`). The *cost* of such chains is fixed
([[conjunction-projection-chain-cost]]); this issue is about reading and
writing them.

How it goes wrong: in `lib/elf64_stat_width.hthr`, R15's fact sits at
`regs.right.right` (the kept registers) then nine more `.right`s. Two
places wrote eight. The elaborator accepted the result (a conjunction passed
for an equation, [[elab-accepts-conjunction-for-equation]]) and the kernel
refused the whole declaration with no span; finding it took a bisection.

## Two directions, not exclusive

**Language.** The conjunction's components already have names in the
places that matter most: a `fn … → Type` whose body is `A ∧ (B ∧ …)` is
read by position only, while a `record` gets fields. Options:

- A destructuring `let`: `let ⟨rbx, ⟨r12, kept⟩⟩ = regs;`. Patterns already
  accept `⟨…⟩` (`docs/logic-connectives-design.md` §4.1), but only in
  `match`, so today this is a `match` with one arm and a motive.
- Flat patterns for right nesting: `⟨a, b, c⟩` against `A ∧ (B ∧ C)`
  (today `⟨a, ⟨b, c⟩⟩`), which is most of what makes the chains long.
- Indexing by position: `facts.3` for the fourth conjunct (still a count,
  but one number instead of a run).

**Library.** Where a conjunction is a register file's worth of facts
(`CursorKept`, `FmtKept`, `StatKept`, `ScanKept`, `WriteKept`,
`ArgvPointers`'s per-argument facts), make it a `record` with a field per
register, as `ReadPrintFormat` and `GroupFacts` already are. `ArgvFrom` /
`ArgvPointers` would carry a record per argument (`pointer`, `positive`,
`bound`, `string`, `rest`). The `Kept` families also have hand-written
`_refl` / `_trans` lemmas whose bodies are the same chains; a record would
not shorten those, but a derived `trans` for "every field is an equation"
could.

The library direction is available today and local; the language direction
removes the count everywhere. The destructuring `let` looks cheapest and
helps with both: it names each fact once, at the point it is taken apart.
