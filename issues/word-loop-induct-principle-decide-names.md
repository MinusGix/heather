---
title: A loop over words gets no induction principle: `decide_true` unresolved
status: open
labels: [elab,loops,function-induction]
area: language
created: 2026-11-18
updated: 2026-11-18
---

Found while fixing [[word-loop-body-exponential]]. A method's `for` over words, `fn R::f(mut self r: R) -> u64 { for i in 0..8 { r.a := r.a + i; } r.a }` in a file importing `logic`, `bitvec` and `bitvec_omega` (not `bool`), checks, but its induction principle `R::f_loop#induct` is refused, silently: the principle is attempted and dropped like any companion.

The refusals, read with a temporary trace around `elab_decl_one` on master f4a3b865:

- `R::f_loop#induct#obl_1`: "`decide_true` takes no type arguments (only a `fn` or `theorem` declared `decide_true<A, …>` does)".
- `R::f_loop#induct#body`: the same for `decide_false`.

`function_induction::tree` spells each test's evidence as `decide_true<P>(e)` / `decide_false<P>(e)` by bare name (`crates/elab/src/function_induction.rs`, the `side` in `tree`). Both live in `lib/std/core/bool.hthr`, which the file reaches only through `bitvec_omega`'s imports, so the bare name probably resolves to nothing the way the principle needs. Not checked: whether `import bool;` in the user's file makes the principle check.

Until this is fixed, a proof by functional induction over such a loop has no principle to cite. The fix is likely the principle naming the two by their module (as the loop lowering names `bitvec_omega::found_fact`) and a probe in `lib/_tests` that cites `#induct` of a word loop without importing `bool`.
