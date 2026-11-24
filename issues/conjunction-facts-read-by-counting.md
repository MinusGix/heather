---
title: Deep conjunction facts are read by counting .right; name them
status: closed
labels: [surface,proofs,ergonomics]
area: language
created: 2026-10-04
updated: 2026-11-24
closed: 2026-11-24
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
  accept `⟨…⟩` (`docs/library/logic-connectives-design.md` §4.1), but only in
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

## Log

- 2026-10-21: The code cited above (crates/elab/tests/fixtures/open_read_close.hthr, examples/x86-native/wc.hthr) was burned in B1 ([[native-burn-process-stack]]; last at 189659d, tag native-v0); the language ask stands on its own.
- 2026-11-08: Stdlib awkwardness survey (docs/surveys/stdlib-math-awkwardness-survey.md §7): probed 2026-11-08, `let ⟨n, a, b⟩ = h;` is still a parse error (`expected let binding name, found LAngle`), while `match h { ⟨n, ⟨a, b⟩⟩ => … }` works. Math libraries: 59 chains of three or more `.left`/`.right`, 60 nested `Exists(…) => match` arms (36 in creal.hthr), 904 `.witness`/`.proof` reads.
- 2026-11-24: Implemented positional destructuring `let ⟨p1, p2, …⟩ = e;` and `let ⟨p1, p2, …⟩ <- e;` (`crates/syntax/src/parser.rs`, `crates/elab/src/statements.rs`, `tree-sitter-heather/grammar.js`), supporting single-constructor records (`And`, `Exists`, `Pair`, `Iff`, user records), nested `⟨…⟩` (also inside `let { f := ⟨…⟩ } = e;`), wildcards `_`, 0-field `let ⟨⟩ = e;`, and flat right-nesting (`let ⟨a, b, c⟩ = e;` against `A ∧ B ∧ C` or `∃ x, P(x) ∧ Q(x)`). Verified in `lib/_tests/std/core/destructure_suffices_tests.hthr`.
