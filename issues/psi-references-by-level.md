---
title: Refer to Ψ by level: a term closed in Ψ should not change when Ψ grows
status: open
labels: [kernel,performance,representation,design]
area: kernel
created: 2026-11-09
updated: 2026-11-09
---

Evaluate referring to Ψ's bindings by **level** (position from the start of
Ψ) instead of by de Bruijn **index** (distance from its end), so that a term
which is closed in Ψ is one spelling in every extension of Ψ.

## Why now

[[empty-substitution-tail-decoration]] removed the last thing that made a
closed reference depend on its *local* context, and local shifts and
substitutions stopped visiting closed syntax. What is left of substitution
cost on a cold check is the *global* namespace, and it has the same shape
the tail had: a decoration nothing computes with, adjusted by every
traversal.

`GlobalVar(i)` counts from the end of Ψ. So:

- **Every push renumbers everything.** A binding's type and body are stored
  in the prefix they were checked in; every later reader rescopes them by
  its distance (`shift_global(v + 1)` in the `u^δ` rules, `resolve_at`,
  `body_of`, `ty_code_fn_at`, `guard_read`, `derived_hit`'s
  `d.ty.shift_global(now - d.at)`, the image loader's relocation). Each is a
  full walk and a full copy: under indices *every* node that mentions a
  library definition changes, so no bound can prune the walk the way
  `bounds.rs` prunes local ones.
- **The copies are fresh allocations**, so everything keyed by node identity
  (the bounds memo, the typing memos, the conversion shortcut) starts cold
  on each of them.
- **The caches this forces are soundness-relevant.** `reduce::GlobalCache`
  holds rescoped signatures and bodies and "is sound for one Ψ only"
  ([[kernel-psi-bound-cache]]); the elaborator keeps `guard_reads`,
  `guard_spine_reads` and `ty_code_fn_at` for the same reason
  ([[type-code-fn-template-stale]], [[codes-registered-in-a-stale-scope]]
  were both this defect class).
- **The scratch world pays twice.** An implicit application puts `n` metas
  at indices `0..n`, which shifts every committed global by `n` on the way
  in (`shift_global(n)` of every domain) and substitutes them away on the
  way out (`zonked`: two `apply_global` walks and a structural comparison,
  [[zonk-reads-in-one-pass]]). Under levels the metas are the `n` levels
  *after* Ψ's last: entering changes nothing, and leaving touches only the
  subtrees that mention a meta, which a "largest level mentioned" bound
  (the global twin of `LocalUse::bound`) prunes at the root.

## The idea

- `GlobalVar(p)` is the binding's position from the start of the ambient Ψ.
  A term checked in Ψ is well scoped, unchanged, in Ψ, Ψ'.
- Term formers that **bind** a global (`letbox`, the code recursors'
  branches, context abstraction, a contextual type's telescope) bind level
  `|Ψ| + depth`. Moving such a term into a longer Ψ renumbers its *bound*
  globals only. That walk is prunable ("contains a global binder" is a
  per-subtree fact) and those formers are confined to meta-level code.
- `GlobalSubst` in instantiation form substitutes the top `n` levels and
  leaves the rest alone, instead of renumbering the rest down.
- `reduce::GlobalCache`'s rescoped signatures and the elaborator's
  rescope-on-read memos have nothing left to hold for a binder-free binding.

The alternative with the same payoff is the split most kernels make:
top-level **constants** by absolute id and bound global **variables** by
index. Levels keep one namespace and one substitution algebra, which is the
smaller change to `docs/delam/04–06`'s correspondence; the constant split
is the fallback if bound-global renumbering turns out not to be rare.

## What has to be evaluated before committing

1. **How much is at stake now.** Stack samples on a cold width-one
   `calc_parser` after the tail change put global-namespace traversals at
   about a fifth of wall time (Log). Re-measure on the x86 certificates,
   where generated definitions are many and shallow.
2. **Where bound globals occur.** Count `letbox`/recursor/`Λ(g)` nodes in
   the library's committed bodies; the design needs them rare or the
   renumbering walk needs its own bound.
3. **The adequacy paragraph**, for `crates/kernel/DESIGN.md`, before code:
   the paper's Ψ is index-based, and levels are its standard
   order-reversing presentation; say what `Ψ ⊢ σ : Ψ'` and the letbox β-rule
   become.
4. **The elaborator boundary.** Every `GlobalVar(len - 1 - abs + padding)`
   becomes `GlobalVar(abs)`; goal-arena and `meta fn` padding
   (`global_padding`, `meta_offset`, `gen_ref_len`) stop entering reference
   construction. This is most of the diff and all of it is deletion or
   simplification, but it is ~everywhere.
5. **Images.** A module image stores terms relative to its import closure;
   relocation ([[relocatable-semantic-module-images]])
   today shifts by index. Under levels a module's own bindings sit at
   `base + k`; relocation is an offset on levels `>= base` of the *old*
   closure, which is the same walk with a different predicate. Format bump.
6. **Staging.** The kernel half can land behind the existing API if
   `GlobalVar` construction goes through one function first; do that
   refactor as its own round so the flip is a one-file change to audit.

## Log

- 2026-11-09: Sizing, on the tree that has [[empty-substitution-tail-decoration]] and [[global-allocator]]: 614 stack samples (gdb, 50 ms) of a cold width-one `heather check docs/showcase/calc_parser.hthr`. 27.7% of busy samples are inside `subst.rs`. Of the ones whose operation is on the visible stack: `apply_global` 6.0%, `shift_global` 6.0%, `apply_local` 2.3%, `shift_local` 2.1%, `reindex_global` 0.5%; another 10.7% are traversals deeper than the 50 frames sampled, and deep traversals are the whole-term global walks more often than the pruned local ones. So the global namespace is somewhere between an eighth and a fifth of wall time. Callers of `shift_global`, by sample count: the kernel's signature rescope in `tm_infer_inner` 9, the elaborator's `resolve_at` 8, `guard_ty` 4, `body_of` 3, `apply_implicit_planned` 3, `ty_code_fn_at` 3, `lower_named_type` 3. Callers of `apply_global`: `zonked_tm` 21, `zonked` 7, `check_decl` 4, `apply_implicit_planned` 4. Counters for the same run: `shift_global_nodes` 38.2 M against `local_subst_nodes` 15.1 M; before the tail change they were 56.5 M against 175 M.
- 2026-11-09: Size of the flip, by grep on 2266a35: `shift_global` is called at 70 sites in the kernel and 172 in the elaborator; `GlobalVar(` is constructed at 75 and 60; the elaborator's padding helpers (`global_padding`, `meta_offset`, `gen_ref_len`) appear 39 times. Term formers that bind a global are the `dep(0, 1, 0)` rows of `subst.rs`'s dep table (box types, letbox, the code recursors' branches). So step 6 (one construction function, then the flip) is a round of its own before any behaviour changes.
