---
title: A written decreasing proof still pays an omega run: the lifted obligation closes with omega on top of the clean statement
status: closed
labels: [elaboration,termination,omega,performance]
created: 2026-09-22
updated: 2026-09-23
---

`docs/showcase/calc_parser.hthr`'s heaviest declaration after the app@ round
is `checked_expr` (780 ms cold in the 2026-09-23 snapshot), a three-line
well-founded recursion whose one self-call is discharged by the writer:

```text
fn checked_expr(source: List<PTok>, begin: Cursor<PTok>(source)) -> Checked(0,source,begin)
    decreases list_len(rest(source,begin)) {
    expr_body(source,begin,checked_factor(source,begin),
        λ (next: …) (smaller: nat::Lt(list_len(rest(source,next)),list_len(rest(source,begin))))
            => checked_expr(source,next) decreasing tail)
    on decreasing tail := smaller;
}
```

**Attribution** (`--cache --only checked_expr --timings`, release, width one,
2026-09-22): item total 335 ms, of which **`omega_check` 224 ms**; the
kernel gate is 0.3 ms, the body 18 ms, unification 22 ms. The file never
calls `omega`.

**Mechanism.** `measure.rs`'s `obligation` lifts each self-call's
obligation into `f#obl_N`. When the site has a *clean* statement (the
`Clean` of `docs/mutual-recursion-design.md` §4), the lifted body is always

```text
let __dec_clean : nat::Lt(args, raw) := <closer: the `on` proof, or omega>;
omega
```

— `omega` runs **on top of** the writer's proof to derive the refined
obligation `at_args < refined` from the clean statement. That is §4's
arithmetic for a group (scaled measures) or a refined scrutinee, but for a
single self-recursive function with no enclosing refinement the clean
statement *is* the goal, and omega certifies `h : a < b ⊢ a < b` — at
224 ms here, because the atoms are `list_len(rest(source, …))` terms. The
three sibling functions (`checked_factor`, `checked_atom`) pay it too.

**Levers** (not chosen):
- When the clean statement is syntactically the obligation (strictness, args
  and measure equal after refinement), close with `__dec_clean` itself and
  write no `omega`.
- Separately: omega's certificate check for a one-hypothesis identity goal
  over two opaque atoms should not cost 224 ms; that half is
  [[omega-performance-telemetry]]'s question, and this is a clean probe of it.

Value: this is ordinary well-founded code, the shape every `decreases`
function with a written proof has, so the constant lands across the library.

## Log

- 2026-09-23: FIXED, and the premise above was wrong: checked_expr and its two siblings are a mutual group, and a group's clean statement is never the goal. The obligation is the scaled `args*3 + r_to < raw*3 + r_from` (docs/mutual-recursion-design.md §4), so omega was doing real arithmetic and could not be skipped by an equality test. Nor was the cost the list_len atoms: the same goals over two plain variables cost 200-500 ms per omega item (a ~5 KB certificate elaborated, then gated). A first try — two omega-proved lemmas per group, cited at every site — cut elaboration but raised kernel work (four-variable certificates), and was dropped. FIX: lib/std/nat.hthr gains add_mono_r, add_mono_l, mul_mono_l, scaled_lt and scaled_le (structural, ~1 ms each); a group site's body is `let __dec_clean := <closer>; nat::scaled_lt/le(args, raw, r_to, r_from, N, __dec_clean, trivial)`; a rank-lowering site at an unchanged argument (`x <= x`) closes by nat::le_refl unasked; and a group no longer requires `import omega`/`import int` (omega is only the default closer of an undischarged site, as in Part A). Measured with scripts/perf ab --base a484f811, 5 interleaved cold samples, calc_parser (imports held fixed): checked_expr 436 -> 38 ms median, samples disjoint; its omega check 179 -> 0 ms and gate 173 -> 9 ms. File-wide counters: conv_misses -7.6%, unify_calls -20%, shift_global_nodes -9.9%. File wall time is inside the spread, because the file's cold time is dominated by checking the omega module, which it still imports transitively. calc_parser dropped its now-unused `import int; import omega;`, and a --source-patch A/B confirms that moves nothing. Tests: mutual_recursion gains a group that checks without omega or int (open-argument reflexive site, literal computation), and the closer-less negative control now imports pair, so it reaches the unsolved-goal path it claims to test (it had been failing on the missing pair import). Full suite 2871 passed.
- 2026-09-23: Merged with master's receiver-style stdlib: the lemmas are `Nat::scaled_lt` / `Nat::scaled_le` (self a, …), placed after `Nat::mul_le_mono` and proved from master's `add_le_mono_l`/`add_le_mono_r`/`mul_le_mono_r` kit. The three helper lemmas this round had written (add_mono_r, add_mono_l, mul_mono_l) duplicated that kit and were dropped. The lowering cites `nat::Nat::scaled_lt`/`scaled_le`/`le_refl`.
