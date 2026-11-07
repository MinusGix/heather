---
title: Comparing two long vectors or lists by value meets the conversion's depth budget
status: closed
labels: [kernel, conversion, literals]
area: kernel
created: 2026-11-07
updated: 2026-11-07
---

Since [[long-string-literal-stack-overflow]] a literal of any length checks,
because its term is shallow (`Term::VecItems`, a bounded list spine). Its
*value* is not: when the kernel has to compare two long vectors or lists that
are not the same term, conversion walks them component by component, and the
Σ rule (`Conv::tm_nf_sigma` in `crates/kernel/src/conv.rs`) compares the tail
with a native call after the head. A `List`'s constructor values go the same
way through their children. Past [[kernel-native-depth-budget]]'s bound
(about a thousand levels) the comparison is refused `OutOfFuel`.

## Reproduction

```heather
import logic; import nat; import list; import char; import string;
fn s() → String { "aaaa…" }                       // 3,000 copies of `a`
theorem q(): s() = "aaaa…" { refl }               // OutOfFuel
theorem r(): "aaaa…" ++ "b" = "aaaa…b" { refl }   // OutOfFuel
```

At 900 characters both check. A kernel-level twin: `conv_term` of two equal
5,000-element `VecItems` nodes built separately is `OutOfFuel`, at 500 it is
accepted (`a_node_longer_than_any_chain_the_stack_holds_checks` pins 500).

## Why it matters

A self-hosted lexer evaluated by the kernel ([[self-hosted-lexer]]) proves
facts like `lex(src) = tokens` whose sides are lists as long as a file; so
does any test that compares a computed list against a literal one.

## Direction

The comparison is a right-nested walk whose last premise is the tail, so it
can be a loop rather than a recursion: `TmProgress` already carries one tail
continuation (`Nat`, the residual comparison after cancelling a successor
prefix). A `Sigma` tail (and the last child of a `Wf` constructor value)
would be the same shape: no binder, context or type change beyond the
instantiated `snd` type, and no sibling comparison left. Two items nodes
with the same array could also compare item by item before evaluating, as a
congruence. Measure with `scripts/perf ab`: this is the conversion's hottest
path.

## Log

- 2026-11-07: fixed by conversion's deferral of comparisons met deep
  (docs/deep-term-walks-design.md §3.4) rather than a Σ-tail continuation:
  the reproduction's two theorems check at 3,000 characters, and the
  kernel twin compares two 20,000-element nodes
  (`a_node_longer_than_any_chain_the_stack_holds_checks`). What is left is
  time, not depth: [[vec-items-window-bounds]].
