---
title: The binding-statement lowering copied each node once per ancestor
status: closed
labels: [syntax,performance]
area: language
created: 2026-11-11
updated: 2026-11-11
---

The parser lowers `e?`, `(<- e)` and `let x <- e;` by a continuation-passing walk (`crates/syntax/src/try_lower.rs`), and puts an expression into a continuation's slot with `plug`. `plug` rebuilt each child from a **copy** of the child:

```rust
children(&mut e, &mut |x| *x = plug(x.clone(), slot, value));
```

`x.clone()` is a deep copy of the subtree, taken at every level on the way down, so a node at depth d was copied d times (and dropped as often). And a block's continuation is plugged once per statement, with the rest of the block already inside it.

## What that cost

Checking `examples/x86-native/levels.hthr` cold at width one, under callgrind: 1,460 calls of `plug` from `Lower::cps`, 3,432 M instructions inclusive (3.1% of the run, 2.35 M per call), nearly all of it `ExprKind::clone` and the matching drops. The files that pay are the ones written with binding statements in long blocks (`lib/native`); the showcase has almost none and paid 0.1 M.

In seconds it is less than the instruction share suggests (copies run at a high instruction rate): the run's `parse_ns` fell from about 0.31 s to 0.14 s of about 21 s.

## What is built

`plug` walks in place (`plug_in`) and copies only the value, where the slot is. The result is the same tree: the old code also returned the value's copy at the slot without walking into it, and rebuilt every other node from its plugged children.

The counters of the certificate run are identical before and after, in every count column of all 5,198 rows.

## Left as it is

A block of n statements still plugs a continuation that holds the rest of the block n times, so the walk is quadratic in the block's size, now at a few instructions a node and no allocation. A slot is written once per continuation, so a walk that stopped at the slot would be linear; that is a claim about every continuation `cps` builds and is not made here.
