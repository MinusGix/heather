---
title: The empty substitution tail records nothing: closed syntax is context-independent
status: open
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
