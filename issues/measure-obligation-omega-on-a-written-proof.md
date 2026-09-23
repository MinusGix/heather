---
title: A written decreasing proof still pays an omega run: the lifted obligation closes with omega on top of the clean statement
status: open
labels: [elaboration,termination,omega,performance]
created: 2026-09-22
updated: 2026-09-22
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
