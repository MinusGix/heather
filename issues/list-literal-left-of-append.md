---
title: A list literal left of ++ has no carrier in an expression
status: open
labels: [frontend,elaborator,ergonomics]
created: 2026-10-04
updated: 2026-10-04
---

In an expression, `[x] ++ y` is refused: "`++` has no meaning here: no
constraint binder named it …, `++` designates something at `List`
(`list::List::append`)". The left operand alone decides the carrier, and a
list literal has none until it is checked against a type. Every other
spelling of the same append elaborates:

- `y ++ [x]` (the literal on the right);
- `Cons(x, Nil) ++ y`, or `let l: List<Nat> = [x]; l ++ y`;
- `List::append([x], y)`.

Found writing `lib/elf64_command_output.hthr`, where an emitted row is
`… ++ Cons(newline(), later)`: `[newline()] ++ later` was the natural form.
Probe (expression position, `import list; import nat;`):

```
fn front(x: Nat, y: List<Nat>) → List<Nat> { [x] ++ y }        // refused
fn front3(x: Nat, y: List<Nat>) → List<Nat> { [x, x] ++ y }    // refused
fn front8(x: Nat, y: List<Nat>) → List<Nat> { y ++ [x] }       // ok
```

Two directions: when the left operand is a literal with no carrier, take
the carrier from the right operand (or the expected type) before giving up;
or let the expected type `List<Nat>` seed the operator's carrier. Either
needs a negative control: a literal on both sides with no expected type
stays refused with the same diagnostic.

In a type position `[x] ++ y = …` is a parse error instead (a vector type
`[T; n]` is expected), which is a separate question for
[[list-literal-syntax]].
