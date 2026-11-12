---
title: An argument typed by one type function passes the elaborator where another is expected; only the kernel refuses, without spelling it
status: closed
labels: [frontend,diagnostics,bug]
area: language
created: 2026-11-11
updated: 2026-11-12
---

An argument whose type is one zero-argument type function, passed where
another is expected, is accepted by the elaborator when the two differ by
a leading argument, and refused only by the kernel, with a note that
cannot spell the argument's own type.

```
import nat;
import list;

fn Inner() → Type { Nat → List<Nat> → Nat }
fn Outer() → Type { List<Nat> → Inner() }

fn takes(f: Outer()) → Nat { f([], 0, []) }
fn inner() → Inner() { λ n ws => n }

// An `Inner()` where an `Outer()` is expected.
fn wrong() → Nat { takes(inner()) }
```

```
error: the kernel rejected `wrong`: NotConvertible. the type of this expression does not convert to `List<Nat> -> Inner` (its own type has no surface spelling)
```

Found 2026-11-11 while threading `Readers()` (`Buffers() → Answers()`)
through the native compiler in place of `Answers()`
(`lib/native/function_ir/function_ir_state.hthr`): two probes of the `rt`
IO layer kept passing an `Answers()` and each failed this way, at the
argument but with no word about what was passed.

Two things are wrong, and the second is the one a user meets.

- The elaborator's check of the argument against the parameter's type
  passes. `Inner()` against `Outer()` should fail there, with the two
  types spelled, as it does when the types are written out
  (`Nat → List<Nat> → Nat` against `List<Nat> → Nat → List<Nat> → Nat`).
  The two are function types of different domains once unfolded, so this
  is not a disagreement the kernel alone can see.
- The kernel's note says the argument's type "has no surface spelling".
  It is `Inner()`, or its unfolding, both of which have one.

## Done when

- The example is refused by the elaborator with both types named, as an
  `// expect-error` probe under `lib/_tests`.
- If a kernel refusal can still reach this site, its note spells the
  argument's type.
