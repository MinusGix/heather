---
title: A list literal left of ++ has no carrier in an expression
status: open
labels: [frontend,elaborator,ergonomics]
area: language
created: 2026-10-04
updated: 2026-10-26
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

## Log

- 2026-10-20: Same refusal with a generic call on the left: `MonoidRel::fold(Nat::add, xs) + MonoidRel::fold(Nat::add, ys)` is refused ("`+` has no meaning here"), because the call's carrier is still a metavariable when `+` is resolved; `Nat::add(…, …)` or a `fn sum(xs: List<Nat>) → Nat` wrapper elaborates. Found writing docs/showcase/semiring_client.hthr.
- 2026-10-21: A method call on a list literal has the same missing carrier: `[x, x].len()` is refused with "unbound name `len`", found writing the float-error tests (`[d1, d2, d3].prod_one_add()`; they spell `List::prod_one_add([…])`). A fix that gives a carrier-less literal its carrier from the method's owner, or from the expected type, should cover both.
- 2026-10-26: A related masking, found 2026-10-26: when the left operand is an unbound name, the operator's refusal is reported instead of the unbound name. `fn Box::twice(self b: Box) → Nat { get(b) + get(b) }` (with `get` unbound) says "`+` has no meaning here: … `+` designates something at `Nat`"; `{ get(b) }` alone says "unbound name `get`". A fix that resolves the operator's carrier from the operand should surface the operand's own error first.
