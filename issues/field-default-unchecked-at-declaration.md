---
title: Check a record field's default at the record, not only at a construction
status: closed
labels: [frontend,elaboration,defaults]
area: language
code: crates/elab/src/inductive.rs
created: 2026-10-23
updated: 2026-10-24
---

A record field's default (`name: T := e`, docs/named-arguments-design.md
§9.5) is elaborated only at a construction that leaves it out
(`Elaborator::elab_field_default`), so a default no construction uses is
checked by nobody — the field-side twin of
[[parameter-default-unchecked-at-declaration]], which closed for parameters.

```heather
record P { a: Nat, h: a = 3 }
record Q { x: Nat, y: Nat := P(2, refl).a }   // accepted
```

## Direction

The parameter rule carries over unchanged (§9.7): a discharge (`omega`,
`positivity`, `refl`, …) is the construction's; a value is elaborated in the
record's field telescope (its parameters and the fields before it) and
kernel-checked there, at the field's type or at its own when a construction
could still change the fit. The work is finding that telescope: fields are
lowered in `inductive.rs` far from where a `Cx` with the earlier fields as
binders exists, and the hidden `Pos<A>` search default
(`is_pos_search`) is a discharge.

## Resolution (2026-10-24)

docs/named-arguments-design.md §9.7, "Record fields".
`Elaborator::check_field_defaults_at_declaration` builds the record's field
telescope at its own parameters (type parameters as binders at `Type`,
value parameters as binders of their declared types, then the tag and the
earlier fields) and runs `check_default_at_declaration` on each default in
it, made hygienic: a construction cannot name an earlier field either, so a
default that does (`y: Nat := x`) is refused at the record.

Tests: `crates/elab/tests/named_arguments.rs`
(`a_field_default_no_construction_uses_is_still_checked`,
`a_field_default_under_parameters`,
`a_field_default_cannot_name_an_earlier_field`).
