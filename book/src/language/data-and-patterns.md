# Data, records, and patterns

## Inductive types

```heather
inductive Option<A> {
    None,
    Some(value: A),
}

inductive Vec<A> : (n: Nat) -> Type {
    Nil : Vec<A>(0),
    Cons(n: Nat, head: A, tail: Vec<A>(n)) : Vec<A>(Succ(n)),
}
```

Constructor fields may be named and may depend on earlier fields. An indexed
family declares its index telescope after `:` and each constructor states its
result index. Recursive branching families are supported through Heather's
`Wf`-based lowering; consult the design notes when defining advanced indexed
families.

## Records

```heather
record Point { x: Nat, y: Nat }

fn origin() -> Point {
    Point { y: 0, x: 0 }
}
```

A record is a one-constructor inductive with named fields. Literal fields may
appear in any order. Projection uses `p.x`; a record type with value
parameters can act as a predicate:

```heather
record IsSuccess(code: Nat) { proof: code = 0 }
```

## Collection and anonymous constructor literals

```heather
[1, 2, 3]
⟨left, right⟩
⟨value |⟩
⟨| error⟩
```

Collection literals are expected-type directed. Primitive vectors and types
implementing the standard collection-literal protocol may accept them.

`⟨...⟩` selects the sole constructor of the expected type. The bar spellings
select the first or second constructor of a type with exactly two
constructors. The same notation works in patterns.

## Matching

```heather
match value {
    None => fallback,
    Some(x) => use(x),
}
```

Patterns may nest, use `_` as a wildcard, and select constructor fields by
name:

```heather
match tree {
    Node(left := Leaf(x), right := r) => combine(x, r),
    _ => fallback,
}
```

An optional motive makes dependency explicit:

```text
match value as λ z => ResultType(z) { ... }
```

An equation binder records how the scrutinee equals the arm pattern:

```text
match h : value { Constructor(x) => ... }
```

The equation direction is `value = pattern`. This convoy form is unavailable
for indexed families where the equation would need to be heterogeneous.

On `Nat`, `match` is also structural induction. A `Succ(k)` arm receives an
automatically synthesized induction hypothesis when recursive calls require
one; `Succ(k, ih)` is the explicit low-level spelling.

## Primitive vectors and `Fin`

`FZ` and `FS(j)` construct finite indices in checking position. Numerals are
accepted at a known `Fin(n)` type. Match on `Fin` is supported, and `xs[i]`
indexes a primitive vector.
