# Types and universes

## Built-in and named types

```heather
Nat
Type
Type<1>
List<Nat>
[Nat; 4]
Fin(4)
∥P∥
Squash<P>
```

`Type` abbreviates `Type<0>`. A type in `Type<n>` itself lives one universe
higher. Type parameters default to level zero, while `<A: Type<1>>` ranges
over types one level higher.

Named types use angle brackets for type arguments. Ordinary parentheses
supply value indices, so `Vec<A>(n)` and `Fin(n)` visibly distinguish type and
value arguments.

`[A; n]` is the primitive fixed-length vector type and `Fin(n)` its primitive
index type. `∥P∥` and `Squash<P>` are equivalent spellings of propositional
truncation.

## Function types

```heather
Nat -> Nat
(x: Nat) -> Vec<Nat>(x)
(x, y: Nat) -> Nat
{A: Type} -> A -> A
```

Arrows associate to the right. Parenthesized binders make dependency
explicit; braces mark an implicit binder. Shared annotations use commas.

Types are also expressions. A function may return a type, a record projection
whose value is a type can be used in type position, and motives may be
ordinary lambdas returning `Type`.

Vector types can be returned directly, including at an unknown length:

```heather
fn V<A>(n: Nat) -> Type { [A; n] }
fn pass<A>(n: Nat, xs: V<A>(n)) -> [A; n] { xs }
fn one<A>(x: A) -> V<A>(1) { [x] }
```

The semicolon distinguishes a vector type `[A; n]` from a collection literal
such as `[x, y]`.

## Equality and propositions

```heather
x = y
x ≠ y
P ∧ Q
P ∨ Q
¬P
P ↔ Q
P <-> Q
∀ x, y: A, P(x, y)
∃ x: A, P(x)
```

These forms elaborate to ordinary library types (`And`, `Or`, `Not`, `Iff`,
and `Exists`) except equality, which is a core type. `∀` is a dependent
function type. The connectives require the appropriate standard-library
declarations, normally through `import logic;`.

From tightest to loosest, the logical portion of precedence is comparison,
`¬`, `∧`, `∨`, `->`, `↔`. `∧` and `∨` associate right; comparisons and `↔`
do not chain. Parenthesize the intended nesting.

## Modal types

The metaprogramming layer adds:

```heather
Ctx
TyCode(g)
Code(g |- T)
```

`Ctx` is a code context, `TyCode(g)` is quoted type syntax in `g`, and
`Code(g |- T)` is quoted term syntax of type `T` in `g`. These belong in
`meta fn` signatures; ordinary definitions generally work with values rather
than syntax.
