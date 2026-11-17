# Expressions and functions

## Values and calls

Heather has decimal, hexadecimal, octal, and binary `u64` numerals, character
and string literals, variables, and constructor values:

```heather
42
0xff
0o755
0b1010_0011
'λ'
"hello\n"
Succ(0)
```

Calls accept positional arguments followed by named arguments. Named
arguments are reordered to declaration order and may fill implicit slots.

```heather
f(a, b)
f(a, limit := 10)
@f(A, a, b)
f<Nat>(a)
```

`f<T>` supplies type arguments. `@f(...)` disables implicit value-argument
insertion; type arguments and `@` are independent.

Function values and repeated application are ordinary expressions:

```heather
(λ (x: Nat) => x)(3)
make_adder(2)(4)
```

## Lambdas, sequents, and argument slots

```heather
λ (x: Nat) y => x
fun x => x
x y ⊢ x
x y |- x
add(·, 1)
pair(·₁, ·₀)
```

`fun` is the ASCII lambda spelling. An unannotated lambda binder gets its type
from the expected function type.

A sequent is checking-position sugar for a lambda. The turnstile may also head
a longer block, so its binders scope over the remaining statements.

Argument slots build a lambda section at the nearest checking boundary. Bare
slots are numbered left-to-right; subscripted slots are explicitly zero-based.

## Goal-oriented application

```heather
apply trans;
give first_proof;
second_proof
```

This is the same n-ary call as `trans(first_proof, second_proof)`, with
arguments written in goal order. Every non-final argument is introduced by
`give`; the final expression is bare.

## Blocks and local bindings

```heather
{
    let x = compute();
    let p: x = x = refl;
    p
}
```

A block contains zero or more semicolon-terminated statements and a final
result expression. `let x: T = e;` checks `e` against `T`; without the
annotation, `e` must infer a type. Prefix braces are a block expression.

Record destructuring binds selected projections:

```heather
let { witness := x, proof := hx } = package;
```

Use `_` to ignore a selected field, and shorthand `field` when the new binder
has the same name.

## Projection, methods, and indexing

```heather
point.x
xs.map(f)
xs[i]
```

Dot resolution is type-directed. A record field projects a value; a method
call dispatches using its designated `self` parameter or class instance; the
legacy global-call fallback remains available. Vector indexing requires a
`Fin` index, though a numeral is converted when the bound is known.

## Operators

The lexer recognizes prefix `-` and infix `*`, `/`, `%`, `+`, `-`, `++`, `∙`,
`⊔`, `⊓`, `<<`, `>>`, `&`, `|`, `&&`, `||`, `<`, `<=`, and `≈`. At the
integer types `/`, `%`, the shifts and the bitwise operators read as Rust's
(`>>` is arithmetic at a signed word); a right shift needs a space before it,
since a tight `>>` closes two type-argument lists. At `Rat` and `CReal`, `/`
is field division and asks for the divisor's apartness from zero, searched
at the call as `x⁻¹`'s is (a hypothesis, a sign, a closed divisor, or
`nlinarith` over the context), so `a / 0` is refused rather than given a
value. Their meaning is resolved from a local binder
symbol, a carrier-specific `designation`, or a built-in fallback where one
exists.
An infix operator alone in parentheses, `(<=)`, is the operation itself as a
value, resolved the same way at the carrier its position asks for
([Operator designations](classes-and-operators.md#operator-designations)).

## Conditional expressions

```heather
if P { yes_case } else { no_case }

if let Some(x) = value {
    use(x)
} else {
    fallback
}
```

`if P` uses a `Decide<P>` instance and branches on its result. `if let` is a
one-pattern match plus a default branch. Both elaborate through ordinary
inductive elimination.
