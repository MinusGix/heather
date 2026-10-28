---
title: String literal without bool imported says to import char
status: open
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
