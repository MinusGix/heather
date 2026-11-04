---
title: A wide inductive's constructor k sits k injections deep; balance the sum
status: closed
labels: [elaboration,kernel,inductives,performance]
area: language
milestone: [hih-passes]
created: 2026-10-27
updated: 2026-10-27
---

Left over from [[wide-inductive-constructor-mention-cost]]: a declaration's
constructors lower to a **right-nested** sum `P₀ + (P₁ + (… + P_{n-1}))`, so
constructor `k` is `k` injections deep, a `match` arm `k` sits under `k`
`Case` layers, and everything that walks a value or an arm (the gate's
injection chains, the identity theorem of `inductive/isa-roundtrip`, the
spine-code guards, displays) pays depth `Θ(k)` per use where a balanced tree
pays `Θ(log n)`. The next-steps note of that round
(https://claude.ai/artifact/S6iJmkV173vKLfTghQfaAX) staged the change:

1. **One place decides the shape.** `crates/elab/src/sum_layout.rs`: a
   `Layout` per constructor count (preorder `+` nodes, each covering a
   constructor range), with `path`, `index_of` and `fold`. `Spine` keeps
   `nodes` (one per `+`, preorder, `nodes[0]` the whole) in place of the
   right-nested `tails`; `SpineCodes` likewise, and `D#suffixₖ` names node
   `k + 1`.
2. **Every reader and writer asks it.** The lowerings
   (`inductive::sum_of_payloads`, tier 0, codata, indexed branch classes),
   the injections (`inject_at`), every case tree (`case_tree`,
   `const_case_tree`, `wf_case_tree`, `w_case_tree`, the indexed walks'
   shared `case_split`), the spine codes and their guard
   (`register_spine_codes`, `spine_agreement`), the injection-path decoders
   (`spelling::inj_path`: display, omega's recursive-field candidates,
   no-confusion, `read_ctor`), and the Lean/Rocq export's `supf` chain,
   which reads the tree off the evaluated shape rather than assuming a right
   spine. With `split = lo + 1` this step changes no term.
3. **Halve the wide ones.** `split` halves a range once the declaration has
   eight or more constructors; below that the right-nested shape stays, so
   `Bool`, `Option`, `List` and every hand-written test term keep their
   spelling and the depth saved is at most a few layers anyway.

## Acceptance

- Step 2 changes no term: `heather check --timings` count columns over the
  library identical before and after.
- Step 3: the whole-library gate and `scripts/test` (exact lane: the image
  format changed) pass; `inductive/*` bench bands re-recorded, the
  roundtrip slope well below its 1.96.

## Result (2026-10-27)

Done in two commits: the tree with the old shape, then the policy.

- Step 2 changed no term: over `lib/std`, every kernel counter of every item
  (`decls_gated`, `gendefs_pushed`, `conv_*`, `eval_*`) is identical to
  master's. Only elaborator-side substitution counts moved, from motives no
  longer built for a payload and the last payload's reference computed once.
- Step 3: `scripts/test` (exact lane) green. `inductive/*` bands
  re-recorded over three cloud runs: `isa-opcode-match` 1.34 → 0.94,
  `isa-roundtrip` 1.96 → 1.13, `enum-equality` 2.51 → 1.96,
  `mutual-declaration` 1.49 → 1.15; the rest inside their bands. By hand,
  release, width one: the roundtrip at 512 forms 21.9 s → 0.43 s, at 1024
  1.1 s.
- **IWf families take it too.** A mutual group's generated member sum and
  every family's constructor sum go through the same lowering, so the comb
  [[iwf-shape-spine-comb-depth]] describes is balanced from eight members:
  the `mutual_group` ring with its structural recursion at 32 members
  5.8 s → 1.7 s, at 64 members 46 s → 8.0 s (exponent 32 → 64 about 3.0 →
  2.2). What is left there is that issue's other half (the named signature,
  PR #213), measured on master's side of it.

