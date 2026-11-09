---
title: The empty substitution tail records nothing: closed syntax is context-independent
status: closed
labels: [kernel,performance,representation]
area: kernel
created: 2026-11-09
updated: 2026-11-09
---

The paper's empty local substitution is `·^k_{g?}`: it records the length
`k` and the base `g?` of the context it is *read in*. The kernel kept both
(`SubstTail::Empty { len, base }`). Every reference to a closed global,
`u^{·}`, carried one, so every reference to a library definition, a
constructor code or a theorem was a node whose spelling depended on how many
binders stood above it.

Nothing computed with that decoration. It was only ever copied and adjusted:

- substitution composition reads δ̂ off a **weakening** (`wk^k_g ∘ δ` is
  scoped only when δ's tail is `wk_g`); from an empty tail it took a length
  it then wrote back onto another empty tail;
- typing pinned both fields to the ambient context (`Γ ⊢ ·^k_{g?} : ·`
  demanded `k = |Γ|` and Γ's base), so on well-typed terms the erasure is
  injective: the decoration is recoverable from where the term stands;
- the value domain had dropped it since the NbE round (`VTail`), because an
  environment machine never renormalizes it;
- every traversal (`shift_local`, `subst_local`, `inst_top`) had to *visit*
  each closed reference to bump its `k`, which is what made a term with no
  free variable still "mention the context" for the bounds memo
  (`LocalUse::has_tail`), for the typing memo's strengthening and for the
  elaborator's closed-copy registry.

## What landed (2026-11-09)

`SubstTail::Empty` is a unit. `Γ ⊢ · : ·` holds in every Γ. A weakening
`wk^k_g` keeps its length, which composition does read.

The consequence that pays: **a subtree with no free local variable and no
`wk` is closed syntax, identical in every context and under any binders**.

- Kernel: `shift_local`/`subst_local`/`inst_top` skip such a subtree at its
  root (`bounds.rs`: skip iff `bound <= d && !has_wk`); before, any global
  reference inside it forced the walk and a rebuild of the spine above it.
  The closed-conversion memo keys on the type itself instead of a
  tail-erased `ClosedSide` copy. `VTail::of` no longer normalizes anything.
  `LocalSubst::source_len`/`source_base` are gone.
- Elaborator: the "frame" bookkeeping that re-tailed closed registry copies
  into each reader's context is deleted (`weakened`, `weaken`, `frame_tail`,
  `spine_frame`, `gen_ref_deeper`, the frame components of the guard and
  spine-code memo keys, the hole matcher's `strict` tail mode, and the
  context parameters that existed only to compute a tail).
- Formats: the module image, the interface image and all five Merkle domains
  moved (the tail's encoding is one tag now). The verdict store is sectioned
  by kernel fingerprint, so its own format number did not need to.
- Export refuses only a `wk` tail now.

The diff removes more lines than it adds.

## Two elaborator behaviours that changed, both for the better

Both were found by asking why `decls_gated` fell by a third (it counts every
elaborator call into the kernel, probes included) before believing the
timing.

1. **Closed instance goals under binders reach the canonical derived
   table.** `record_derived` asks the kernel whether the goal type checks in
   the *empty* context. A goal resolved inside a function body mentioned
   globals at `·^k`, `k > 0`, which the empty context refused, so the goal
   was never minted and every later occurrence re-ran the registry search
   (unifier, solution checks, the kernel's check of each proposal). Now a
   goal with no free local is closed wherever it was met, is minted once,
   and later occurrences are `derived_hit`s. In `grind`'s `read_diseq`
   alone: 12 failed closedness probes, 14 proposal checks and 28 solution
   checks became 0, 2 and 4.
2. **More instantiations are named through their code function.**
   `instance_match`'s identity step compared the template at the recovered
   arguments with the subject *including tails*, and declined where the two
   had been spelled at different depths. There is no tail to disagree on, so
   `H5(S5(FA, 1))` is `El(app(H5#tycode_fn; …))` where it was the inline Σ
   (`wf.rs`, `a_projection_off_an_unnamed_spine_takes_the_chokepoints_spelling`).

## A trap the old representation was hiding

Several elaborator sites used `t.shift_local(1) == t` as "this term is
closed and mentions no global". The second half was an accident of the
tail: a global reference changed under a local shift only because its `·^k`
did. With the tail gone the test means what it says (no free *local*), and
`named_type_memo` then cached global-mentioning lowerings without the goal
padding in its key: `len_nil` in `lib/std/text/string.hthr` was refused
with a level mismatch off a stale global index. The sites now ask both
questions (`shift_local(1) == t && shift_global(1) == t`;
`iwf_family.rs`'s `literal_closed`, `inductive.rs`'s memo guard).

## What is deliberately left

- `wk^k_g` keeps `k`. Dropping it needs composition to find δ̂ elsewhere
  (the checker's context), which is a real change to `subst.rs`'s interface,
  and weakenings are rare outside contextual types.
- `Ambient::gamma_base` stays in the typing memo keys: a term can still
  mention the base through a `wk`.

## Log

- 2026-11-09: Measured with `scripts/perf ab`, cloud box, cold width-one `heather check docs/showcase/calc_parser.hthr`, three interleaved samples, master 8a593b6 against this change alone (no allocator change): wall 95.8/102.1/100.5 s to 39.3/39.5/37.6 s (-61%, separate), kernel gate 33.8/35.8/34.9 s to 12.2/12.5/11.6 s (-65%), max RSS 948 MB to 570 MB (-40%). Counters: `local_subst_nodes` 175.1 M to 16.7 M, `shift_global_nodes` 56.5 M to 38.2 M, `syntax_eq_nodes` 30.6 M to 17.7 M, `syntax_eq_memo_hits` 3.96 M to 0.86 M, `eval_steps` 10.5 M to 7.49 M, `conv_misses` 116,754 to 104,055, `conv_shortcut_hits` 2.82 M to 1.94 M, `typing_memo_hits` 961,673 to 673,377, `global_ref_rescopes` 500,902 to 322,029. The elaborator-side counters moved with the two behaviour changes in the body: `decls_gated` 45,006 to 31,691, `check_terms` 4,882 to 3,904, `solution_checks` 6,248 to 4,292, `unify_calls` 12,277 to 10,321; `resolve_goals`, `gendefs_pushed`, `instance_match_calls` and the projection counters are unchanged. Together with [[global-allocator]] on a quiet box: wall 93.5/99.2/83.4 s to 32.8/30.7/28.3 s (-67%), gate 32.9/36.1/29.2 s to 10.6/9.8/9.2 s (-70%), max RSS 949 MB to 635 MB. After the change, stack samples of the same run put substitution at about 28% of busy time, of which the global namespace (`shift_global`, `apply_global`) is the larger part: [[psi-references-by-level]], [[zonk-reads-in-one-pass]].
- 2026-11-09: Rest of the quick corpus, `scripts/perf ab --base origin/master` (b1ba860 against the branch with [[global-allocator]]), cold, width one, two interleaved samples; the box was not quiet (load 2.6 after the builds), so read the seconds as sizes, the counters as exact. `compile-x86 examples/x86-native/levels.hthr program`: wall 250.6/260.0 s to 115.8/111.9 s (-55%), kernel gate 108.8/112.0 s to 52.0/49.7 s (-54%), max RSS 3,102 MB to 1,558 MB (-49%); `local_subst_nodes` 405.6 M to 55.4 M, `shift_global_nodes` 221.7 M to 183.6 M, `syntax_eq_nodes` 99.4 M to 67.1 M, `eval_steps` 67.9 M to 50.1 M, `conv_misses` 1,168,348 to 788,106, `decls_gated` 122,567 to 106,157. `lib/std/tactic/omega.hthr`: wall 5.00/4.82 s to 3.98/3.90 s (-20%), `local_subst_nodes` 6.06 M to 4.78 M. `lib/std/num/nat.hthr`: wall 0.75/0.78 s to 0.66/0.60 s. The small files move mostly by the allocator: their terms have few closed references under binders.
