# Declarations and modules

## Functions, theorems, and axioms

```heather
fn id<A>(x: A) -> A { x }

theorem id_is_id<A>(x: A): id(x) = x { refl }

axiom excluded_middle(P: Type): Or<P, Not<P>>;
```

| Form | Body | After checking |
|---|---|---|
| `fn` | required | transparent and computational |
| `theorem` | required | opaque; later conversion never unfolds the proof |
| `axiom` | `;`, no body | admitted assumption tracked by provenance tools |

`fn` writes its result after `->`; `theorem` and `axiom` use `:`.

Type parameters precede value parameters. `<A>` means
`<A: Type<0>>`; higher universes may be explicit. Value parameters sharing a
type may share an annotation:

```heather
fn choose<A: Type<1>>(x, y: A) -> A { x }
```

Braces inside the value-parameter list mark an implicit parameter. The
elaborator normally infers it; `@` makes all value arguments positional and
explicit.

```heather
fn keep_length({n: Nat}, xs: [Nat; n]) -> [Nat; n] { xs }
fn use(xs: [Nat; 2]) -> [Nat; 2] { keep_length(xs) }
fn explicit(xs: [Nat; 2]) -> [Nat; 2] { @keep_length(2, xs) }
```

Any other expression after `:=` is a **default**. A defaulted parameter has
no positional slot: a call that leaves it out gets the default, and a named
argument overrides it. The default is checked at the call, against the
parameter's type with the call's arguments filled in. Its names mean what they
mean at the declaration, and a tactic default such as `omega` or `positivity`
can use the caller's hypotheses.

```text
fn second(a: Nat, b: Nat := 0) -> Nat { b }
theorem pos(n: Nat, h: 0 < n := omega): 0 < n { h }

second(1)            // second(1, b := 0)
second(1, b := 2)
pos(k)               // omega proves 0 < k from the caller's facts
```

A default may mention the parameters before it, and reads the call's
arguments for them. It may not mention its own parameter, a later one, or a
type parameter.

```text
fn window(start: Nat, len: Nat := 8, end: Nat := start + len) -> Nat { end }

window(2)            // window(2, len := 8, end := 2 + 8)
window(2, len := 1)  // end := 2 + 1
```

A parameter defaulted with `:= infer` is filled by instance resolution. A
class constraint can also be written with `requires` or inline on a type
parameter:

```text
fn f<A: Monoid>(x: A) -> A { ... }
fn g<A>(x: A) -> A requires m: Monoid<A> { ... }
```

## Values

`def` names a value. It takes no parameter list and is used without `()`;
its type may be written or inferred from the value.

```heather
def five: Nat = 5;
def six = Succ(five);                    // six : Nat, inferred
def empty<A>: List<A> = Nil;             // type parameters are implicit
def add_five: Nat -> Nat = λ x => x + five;
def five_is: (five = 5) = refl;          // an equation type is parenthesised

theorem six_is(): six = 6 {}
```

A value unfolds as a `fn` does, so closed facts about it hold by computation.
`five()` is refused (a value is not a function), and a value cannot refer to
itself.

## Declaration prefixes

A name before `fn`, `theorem` or `def` is a **generator** that runs over the
declaration: an ordinary library function returning
`tactic::Tac<List<tactic::Decl>>`, like the one `generate g(args);` runs. It is
called with the declaration's name (and, for a `def`, its value) before any
arguments written after the prefix.

```text
at_zero fn double(n: Nat) -> Nat { n + n }   // at_zero("double"): publishes double::at_zero
regex def is_hex = "[0-9a-f]+";              // regex("is_hex", "[0-9a-f]+")
runtime(owned) fn f(…) -> T { … }            // runtime("f", owned)
```

A prefixed `fn` or `theorem` is published as written and then read by its
generator. A prefixed `def` is handed to its generator instead, which must
declare the name: `regex` parses the string and declares `is_hex` as the
expression's meaning and `is_hex::term` as the expression. Either way the
generator's declarations are published with it, or the whole item is refused.

## Termination

Structural recursion is inferred from a recursive `match`. When that is not
enough, attach a natural-valued measure:

```text
fn loop(args...) -> T decreases measure {
    ...
}
```

Each recursive call must prove that the instantiated measure decreases. The
elaborator raises named decrease goals when local evidence or arithmetic
automation does not settle them; use the goal mechanisms described later.

## Assumption groups

`assuming` supplies solver parameters to several declarations without making
them global axioms:

```text
assuming h: P {
    theorem first(...): Q { ... }
    theorem second(...): R { ... }
}
```

It is parser sugar for ordinary implicit evidence parameters on each enclosed
declaration.

## Sections

A `section` writes a declaration head once for a run of declarations. Its
type parameters and parameters are put in front of each enclosed `fn` and
`theorem`'s own, in order, exactly as if they were written there:

```text
section<A: StrictOrder(≈, <, <=)> {
    theorem StrictOrder::le_refl(x: A): x <= x { ... }
    theorem StrictOrder::le_of_lt(x, y: A, h: x < y): x <= y { ... }
}
```

means `theorem StrictOrder::le_refl<A: StrictOrder(≈, <, <=)>(x: A): ...`
and so on. Callers, inside the section and outside, pass the same arguments
they would to the written-out declaration. Sections nest, outermost head
first. Every member gets every binder, so a member cannot rebind a section's
name, and a section type parameter or `{}` implicit that a member's head does
not mention is refused at that member (no call could infer it). Only `fn`,
`theorem` and nested sections may be inside. Members are conventionally not
indented. See `docs/sections-design.md`.

## Modules and names

```heather
import list;
import option::{Option, map};
export relation::{Relation};
```

Imports and exports come first. Use `module::name` for qualification. A file
may also define names in a type or class namespace, such as `List::map`.
Imports are elaborated once per root's dependency graph; cycles are rejected.

## Other top-level items

Heather also has these declaration families:

- `inductive` and `record` define data types.
- `class`, `instance`, and `designation` define interfaces,
  implementations, and operator meanings.
- `meta fn` defines a layer-m program over quoted syntax.
- `datarepr` and `impl` connect specifications to certified runtime
  representations.
