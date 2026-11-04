---
title: String literal without bool imported says to import char
status: closed
labels: [diagnostics,elaboration]
area: language
created: 2026-10-28
updated: 2026-10-28
---

A string literal in a module that imports `char` and `string` but not
`bool` is refused with "a literal at `char::Char` needs the type in scope:
add `import char;`" (crates/elab/src/literals.rs, `literal_needs_module`),
naming a module that is already imported. The literal's lowering apparently needs
something from `bool` (a `Char`'s scalar witness is `IsTrue`), and the
message names the type's own module instead of the missing piece. Found
writing crates/elab/tests/tactic_generate.rs, whose prelude lacked `bool`.

## Acceptance

- The message names the module actually missing (`bool`), or the refusal
  goes away because the literal no longer needs a name the client did not
  import.
- A Rust refusal test (`support::assert_refused`) pins the corrected text
  with `char` and `string` imported and `bool` not.

## Resolution

The refusal goes away. A literal's generated call is the term of the
module declaring its spec type, so it now elaborates with names resolved as
that module reads them (`read_in_module` in crates/elab/src/literals.rs, the
stored-scope push a parameter default already uses): `char::ofNat`'s witness
finds `bool::decide_yes` through `char`'s imports, and a string's
characters build through `string`'s, so `import string;` alone suffices for
`"hi"`. The client's own scope still decides whether the type is in reach,
so a literal with neither module imported keeps naming the import it lacks
(`a_literal_without_its_module_says_which_import_is_missing`).
`a_literal_needs_only_its_own_types_module` in
crates/elab/tests/char_string_literals.rs pins it in checking, inference and
collection positions, with a kernel-refused wrong string as the negative
control.
