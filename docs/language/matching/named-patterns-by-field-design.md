# Named pattern fields

Implementation record for `issues/named-patterns-by-field.md`.

## 1. Surface rule

`field := pattern` selects a declared field and fills it with a pattern:

```heather
let { witness := x, proof := hx } = h;

match xs {
    Cons(tail := t, head := h) => ..., 
    Nil => ...,
}
```

The shorthand `let { witness, proof } = h;` remains
`witness := witness, proof := proof`. The `:=` token has the same structural
reading as a named call: fill this named slot. It does not claim that calls
and patterns move values in the same direction.

Named fields are order-free and may be omitted. Omission means `_`, not a
default value. A pattern list is wholly positional or wholly named; mixing
the two is refused because the position at which names begin would otherwise
affect which fields an omitted name denotes.

## 2. Record `let`

A record `let` remains projection sugar. The elaborator infers the receiver's
record, validates unknown and duplicate fields, restores declaration order,
then aliases each right-hand binder to the corresponding projection. Restoring
order matters for a dependent record: `proof := hx` may have a type mentioning
the earlier `witness := x`, even when `proof` is written first.

The right side is a binder or `_`. A constructor subpattern is refutable and a
plain `let` has no failure continuation, so it is rejected with advice to use
`match` or `if let`. This is a control-flow boundary, not a parser limitation.

## 3. Constructor patterns

The AST temporarily retains `field := pattern` wrappers. Before the existing
pattern-matrix pass runs, the elaborator resolves the constructor, validates
its declared field names, permutes the supplied patterns into declaration
order, and inserts `_` at omitted fields. Nested constructors run the same
normalizer recursively. The matrix and every inductive lowering therefore
continue to receive exactly their old positional `Vec<Pat>` shape.

Constructors whose fields were declared only by type have no field names to
select. Built-in `Nat`/`Fin` constructors likewise remain positional. Both
cases produce a targeted positional-only diagnostic. Unknown fields,
duplicates, and positional/named mixing are rejected before matrix lowering.

## 4. Composition and invariants

Explicit `match`, `split`, and positional `if let` share the same arm AST, so
the normalization composes with all three. A pattern without a named field
takes the old fast path unchanged. Record destructuring still emits only
projections and aliases; constructor matching still emits only the ordinary
pattern-matrix decision tree. No kernel form or trusted rule changes.

Tests in `crates/elab/tests/named_patterns.rs` cover an open dependent record,
reverse written order, shorthand equivalence, partial and ignored fields,
nested constructor patterns, `if let`, computation in both branches, and each
diagnostic boundary above.
