---
title: Byte literals need algebra, char and byte imported
status: open
labels: [elaboration,surface-syntax,ergonomics]
created: 2026-10-02
updated: 2026-10-02
---

To write `10` or `'\n'` at a byte, a program needs `import algebra; import
char; import byte;` (2026-10-02, S3 of
docs/native-programs-read-like-programs-design.md):

- `Numeral` is consulted only when the program's own scope can see the class
  (`elab_overloaded_num_check`: "the class is optional at the language level").
  `bitvec` imports `algebra` and declares `Numeral<BitVec(n)>`, but a program
  that imports only `bitvec` gets "this has type `Nat`, but `BitVec` is
  expected".
- A character literal needs `char` in scope even at a byte, because its intro
  is built as a `Char` first ("a literal at `char::Char` needs the type in
  scope").
- `CharLiteral<BitVec(8)>` lives in `byte`, so that `bitvec` does not import
  `char` and break test harnesses that list their modules.

Wanted: a literal at a carrier resolves its class whenever an instance for that
carrier exists in the session, whether or not the class name is in scope, and
a character literal's intro does not need `Char` in the importer's scope. Then
a program writes `import bitvec;` and nothing else for byte literals.
