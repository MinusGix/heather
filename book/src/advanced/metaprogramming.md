# Metaprogramming and representations

These features are implemented but specialized. Read the design documents
linked from the source when extending them; this chapter records their public
surface so they are not mistaken for missing syntax.

## Layer-m functions and quotation

```text
meta fn transform(g: Ctx, a: TyCode(g), body: Code(g |- $a))
    for family.slot -> Code(g |- $a) {
    let code saved = body;
    code { ${saved} }
}
```

`meta fn` declares a program over syntax. An optional `for family.slot`
registers it as the elaborator for that slot. Its modal parameter types are
`Ctx`, `TyCode(g)`, and `Code(g |- T)`.

`code { e }` quotes a term and is checking-only: the expected `Code` type
supplies its context and object type. `$x` or `${expression}` splices code
inside a quote. In a meta block, `let code x = e;` binds code so a later splice
can hoist the appropriate let-box.

`match code e as T { ... }` performs intensional analysis with the kernel's
code recursor. Its arms use the fixed kernel branch names, bind recursive
results positionally, and require a `_` arm for unlisted syntax forms. Unlike
an ordinary dependent match, its motive is the constant type `T`.

## Certified data representations

A `datarepr` relates an inductive specification to a runtime representation:

```text
datarepr VecList for List<Token> {
    R := VecToken,
    mk Nil := empty,
    mk Cons := prepend,
}
```

It may instead be minted by a supported generator route:

```text
datarepr VecList for List<Token> := repr::naive();
```

An `impl` supplies one operation at a representation, including its refinement
certificate:

```text
impl length for VecList {
    body := vec_length,
    refines := vec_length_refines,
}
```

Like `datarepr`, an `impl` may use `:= route();` where a registered generator
supports it. Clause names and required certificates depend on the represented
specification and operation; use existing library examples as the practical
reference.

These generators and lowerings are not trusted. Their emitted declarations
and certificates go through the same elaborator and kernel gate as handwritten
Heather.
