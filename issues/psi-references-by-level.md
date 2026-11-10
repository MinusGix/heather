---
title: Refer to Ψ by level: a term closed in Ψ should not change when Ψ grows
status: closed
labels: [kernel,performance,representation,design]
area: kernel
created: 2026-11-09
updated: 2026-11-10
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
- 2026-11-09: Evaluation items 1 and 2, first numbers. (1) On the x86 certificate (`compile-x86 examples/x86-native/levels.hthr program`, cold, width one, the branch with [[empty-substitution-tail-decoration]]) the global namespace is the larger walk by more than on the showcase: `shift_global_nodes` 183.6 M against `local_subst_nodes` 55.4 M, where the showcase has 38.2 M against 15.1 M. (2) A source-level proxy for where bound globals can occur: the kernel formers that bind a global are `CtxPi`, `TyPi`, `CtxLam`, `TyLam`, `LetBoxTy`, `LetBoxTm` and the code recursors' branches (`subst.rs`'s `dep(0, k, _)` rows), and 27 of the library's 396 `.hthr` files mention `letbox`, `meta fn` or `.code` (tactic, lang, native generators, a few text modules). A count over committed bodies still needs a walker.
- 2026-11-10: Decided for the split this issue named as the fallback, and built it: Ψ is read as `Σ; Ψ′`, a signature of **constants** named by position from the start, then **variables** named by index as before (`crates/kernel/DESIGN.md`, "Constants are addressed from the start of Ψ"). Levels for every binding lost on three counts once the elaborator's worlds were read closely. (a) A bound global would have to be renumbered whenever its term moves under a longer Ψ, and every weakening would need the length of the Ψ its argument was scoped in, which no call site has. (b) The elaborator commits helper definitions (`#open`, `#derived`, generated codes, lifted proofs) to Ψ *while a declaration's goals are in scope*: goals after Ψ by level would be renumbered at each such commit, where under the split the commit is syntactically invisible to every term in flight. (c) Evaluation item 2 does not need answering: binders push variables, and nothing a term binds is ever a constant, so how common bound globals are stops mattering. What the split costs is a second spelling, and the reference rule makes each binding have exactly one (a constant must be below `|Σ|`, an index must not reach into Σ; `TypeError::MisspelledGlobal`), so `==` on references is still binding identity and conversion resolves nothing.
- 2026-11-10: What changed, in the order it was staged. Kernel: `GlobalVar` is opaque with the two spellings (`index`, `constant`), `GlobalCtx` records `consts` and grows Σ only through `commit`, which asserts there is no variable; weakening and `apply_global` leave constants alone; a constant's statement and body are read as stored, so `reduce::GlobalCache` holds variables' rescopes only, and a value environment made for a constant's body carries the constant where a variable's carries its offset (`Env::of_binding`, which is what the refold readback of [[wf-ih-rebuilt-per-node]] reads the definition from). With `consts == 0` all of this is the previous kernel, so the kernel half landed under the whole existing suite before anything committed a constant. Outside the kernel: every decoder of a reference goes through `GlobalVar::position`, then the eight commit sites and the committed-reference constructors (`resolve`, `gen_ref`, `derived_ref`, the tactic protocol heads, lifted proofs) flipped together. None of the `shift_global(now - at)` call sites had to change: they are the identity on what they are applied to now.
- 2026-11-10: Two things fell out. (1) The stale-scope defect class ([[type-code-fn-template-stale]], [[codes-registered-in-a-stale-scope]]) cannot be spelled any more: its negative controls had built the stale lowering with `shift_global(1)`, which is now the identity, and write the wrong reference out instead. (2) The verdict keys had a gap the split closes. `merkle.rs` resolved every index against the prefix without counting the global binders it had crossed, so a `letbox`-bound global was hashed as whichever committed binding sat that far from the end of Ψ: a key that moved with an unrelated binding, and one hash for two bound globals whose stand-ins had the same interface. A constant is now hashed as its referent and a variable, which in a gated term is always bound, as its index; a Ψ with variables in it has no keys at all (`heather-cache`'s `is_signature`). Hash domains and both image magics bumped.
- 2026-11-10: Measured against master 3d26280 with `scripts/perf ab --base origin/master` (cloud box, cold, width one, three interleaved samples). Showcase `calc_parser`: wall 27.5/29.7/29.5 → 15.7/15.6/15.1 s (median −47%; the box was still settling from the two builds), and on a quiet rerun of the same two binaries 28.9/29.5/32.5 → 15.7/18.7/18.5 s (−37%); kernel gate −41% and −31%, max RSS 636 → 471 MB; every seconds metric separates in both runs. Counters: `shift_global_nodes` 38.2 M → 0.5 M, `global_sig_rescopes` 53,004 → 0, `delta_body_rescopes` 15,153 → 0, `subst_memo_hits` 24.8 M → 4.2 M, `local_subst_nodes` 15.0 M → 10.8 M, `syntax_eq_nodes` 17.7 M → 7.1 M, conversion queries 2.37 M → 1.59 M, `typing_memo_hits` 673 k → 233 k, `eval_steps` 7.49 M → 7.09 M; 28 columns identical, `check_terms` and every elaborator count among them. x86 certificate (`compile-x86 examples/x86-native/levels.hthr program`, one cold run per binary): wall 117.0 → 57.2 s, kernel gate 51.7 → 25.2 s, peak growth 1,477 → 824 MB, `shift_global_nodes` 183.3 M → 1.5 M, `local_subst_nodes` 55.0 M → 37.4 M, `eval_steps` 50.1 M → 31.2 M, `conv_misses` 787 k → 363 k, `syntax_eq_nodes` 67.0 M → 24.0 M, Merkle walk 3.35 → 1.80 s; the assembly and the certificate are byte-identical. The seconds moved by more than the walks' sampled share (about an eighth of busy samples) because a rescope was also a fresh copy: every Ψ length had its own copy of each library statement it read, so the memos keyed by a node's identity (typing, conversion, values) missed on it and `==` walked it. One stored statement is one node at every use. That reading fits the counters and was not isolated further. The global bound alone, on the debug CLI: `shift_global_nodes` 8.0 M → 0.41 M after the flip had already taken it from 38.2 M.
- 2026-11-10: Two elaborator counters moved on the x86 certificate, both explained. (1) `unify_calls` 28,996 → 27,745 and `instance_match_calls` 28,264 → 27,300, all in the native modules, three per declaration that names `Prog`. `named_type` keeps a finished module's bare lowering only when `shift_global(1)` leaves it alone, which used to mean "mentions no global" and now means "mentions no global variable": a lowering whose fields name another declaration's code is kept across items, where master lowered it again (and matched its instantiations again) at every mention. A three-declaration probe over replayed images shows it: master pays 3/3/3, this tree 3/0/0. The entry is dropped by every rollback that moves Ψ back (`clear_positional`, `restore_from_clone`). (2) `decls_gated` 106,157 → 106,151, six fewer in one `by sets()` proof (`Tm::disjoint_tail`): six obligations are admitted by the verdict store instead of gated again. That is what the key fix predicts for a body with a bound global, whose key no longer moves with Ψ's length; the six were not traced individually.
- 2026-11-10: `scripts/bench --check`, twice: the known `wf/check-tree` band ([[cloud-bench-bands-out-of-range]]) and the `level/` family (equiv-shared 2 → 3 ns, join:4 69 → 91 ns), which this change does not touch and which master built on the same box reads the same (3 ns, 96 ns). Two point flags in the first run (`nat/step-once:128`, `wf/check-tree:303`) did not reproduce in the second or in isolation (252 ns and 42 µs, at or under baseline). 42 lines improved; the baseline was recorded at 709e71c, before [[empty-substitution-tail-decoration]], and was not re-recorded here. Exact suite `scripts/test`: 3844 passed, 0 failed, 2 ignored. Closing: what is left is deletion, filed as [[identity-rescopes-after-constants]].
