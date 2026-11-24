# Docs

Design docs, guides and surveys, one folder per area of `roadmap.md`. A doc
sits where the code it describes lives, not where its round was filed.

## Read first

CLAUDE.md says when each one applies.

- `roadmap.md`: the areas, their priority, the milestones.
- `compilation-vision.md`: the settled principles of native compilation.
- `proof-patterns.md`: how to write proofs that check cheaply.
- `library/program-and-proof-style.md`: how definitions, data and proofs about programs should read.
- `testing-generated-terms.md`: the axes a test of generated terms varies.
- `test-value-audit.md`: when a claim is a Rust test and when a theorem.
- `agent-policy.md`: what a thread may decide and what it asks.

## Folders

| Folder | What it holds |
| --- | --- |
| `kernel/` | Formers (sprop, `Wf`, `IWf`, `M`, coinduction), conversion and NbE, metatheory passes, the gate, kernel cost records |
| `inductives/` | How an inductive or codata declaration becomes kernel terms: the tier 0/1/2 and indexed lowerings, codata, mutual families, type codes |
| `elaborator/` | Elaborator internals: unifier, intros and applications typed by their head, instance identity, the attribution records behind its costs |
| `language/` | Surface features: records, function types, universes, `let` and blocks, named arguments, sections, effects, sequencing, loops (`loop-combinator-design.md`), numerals, `When` |
| `language/classes/` | Traits and instances, operator designations, dispatch, `Decide` |
| `language/matching/` | The dependent match compiler, nested patterns, equation binding, `if let` |
| `language/recursion/` | `decreases`, course-of-values, mutual recursion, recursion at the top |
| `metaprogramming/` | Reflection, meta defs, generators, the host elaboration interface, registered values |
| `tactics/` | `rewrite`, `simp`, `grind`, `omega`, `linarith`, `ring`, `calc`, `norm_num`, `mono`, `induct`, `bv_decide` |
| `native/` | The compiler: program logic, FunctionIR, one compiler, procedures, exports, layout, `runtime fn` setups, datarepr, the emitted code's benchmarks |
| `itrees/` | Interaction trees and coinductive itrees |
| `library/` | Library design: algebra, the separation algebra (`separation-algebra-design.md`), orders, division, reals (`creal.md`), float, strings, the parser, lib layout and style |
| `showcase/` | Checked example programs (`showcases.tsv` lists them) and the prose around them: subtypes, setoids, relational contexts, the calculator |
| `infrastructure/` | Testing architecture, caches and module images, module DAG builds, `--only`, instrumentation, benchmarking |
| `surveys/` | Paper and outside-system surveys, and whole-library assessments |
| `delam/` | The type theory (`delam/README.md` says which chapters matter) |
| `papers/` | The papers the docs and issues read, with an index |
| `archive/` | Docs whose code is gone but whose sections live code still cites |

## Where a doc goes, and when it leaves

A new design doc is named for its subject (`<subject>-design.md`) and goes in
its area's folder. When the code a doc describes is deleted or replaced, the
doc goes in the same change: deleted if nothing live cites it (mentions become
`docs/<name>.md@<rev>`, readable with `git show <rev>:docs/<name>.md`), moved
to `archive/` if code still cites its sections. A later round of the same
subject extends its doc instead of starting a new one.
