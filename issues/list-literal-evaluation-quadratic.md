---
title: A [...] list literal costs evaluation steps quadratic in its length
status: open
labels: [kernel,elaboration,performance]
area: language
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Found by [[reflected-languages-typed-by-construction]] (2026-11-25). A closed list written as a `[…]` literal costs the kernel's evaluator a number of steps quadratic in its length the first time something reads it; the same list spelled `Cons(…, Cons(…, Nil))` is linear.

The measurement: `Steps::apart(m_xs(), m_ys()) = Some(Nil)` by `refl`, with `m_xs` and `m_ys` two `List<Step>` of length `n` declared as `fn`s (`lib/lang/ownership/steps.hthr`), `heather check --timings`, release, width one. The `steps` column of the theorem's row:

| n | `[…]` | `Cons` spine |
|---|---|---|
| 32 | 11,302 | 2,048 |
| 64 | 40,774 | 3,840 |

The `[…]` column grows about fourfold per doubling and the `Cons` column twofold; `m_get` (a read through `Val::place` of the same list) shows the same split. The literal goes through `CollectionLiteral<List<A>>`'s `fromLiteral`, a `fold` over the vector (`lib/std/data/list.hthr`), whose fold is the container schema on the vector's length (`crates/elab/src/vec.rs`); which part is quadratic is not attributed. The absolute cost is small at the lengths the library writes, but every reflected program the checker evaluates is a literal of this kind once a reflector emits one.

## Done when

A literal of length `n` costs evaluation steps linear in `n`, measured as above at doubling lengths, or the quadratic part is attributed and a decision recorded.

## What it assumes from elsewhere

- **[[collection-literal-resolution-per-literal]]** owns the literal's elaboration cost (resolution per literal); this issue is about evaluating the elaborated term.
