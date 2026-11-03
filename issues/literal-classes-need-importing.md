---
title: Byte literals need algebra, char and byte imported
status: open
labels: [elaboration,surface-syntax,ergonomics]
area: language
created: 2026-10-02
updated: 2026-11-03
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

## Log

- 2026-10-20: `rat` and `creal` now `export algebra::{Numeral}` so their clients write `0` without `import algebra` ([[rat-numerals-and-semigroup-clash]]): a per-carrier workaround; `bitvec` could do the same until this lands.
- 2026-10-21: (tac-host-interface round 2) a string literal needs `import list; import bool; import char;` besides `string` (the collection literal, `bool::decide_yes` in each character's intro, and `char::ofNat`), and when `bool` is the one missing the error still says `add import char;` (`literals.rs`: `char_intro` returns None for either key). A tactic argument naming a hypothesis by string (`resolve("p")`) is the newest client to hit it.
- 2026-10-28: (native-compile-other-calls) hit again writing `cat FILE…`'s messages in `lib/native/native_tools.hthr` with `utf8::encode("…")`: `import char` was there, `bool` was the missing one, and the error still said `add import char;`. A one-character string elaborates without `bool`, which makes the message harder to read. Naming the missing key's module in `literal_needs_module` would be the cheap half of the fix.
- 2026-10-29: (proof-patterns audit, [[proof-patterns-audit-2026-10]]) Re-probed on master 4f0ac27. **String half fixed**: since [[literal-needs-module-names-wrong-module]] (PR #250) a string literal needs only `import string;` (`fn hi() → string::String { "hi" }` checks with nothing else). **Byte half still open**: with `import bitvec; import byte;`, `'a'` at `BitVec(8)` says "a literal at `char::Char` needs the type in scope: add `import char;`", and `10` at `BitVec(8)` says "this has type `Nat`, but `BitVec(8)` is expected here" (with `import bitvec;` alone too) until `import algebra;` is added. The 2026-10-21 and 2026-10-28 entries above describe the string case as it was before #250.
- 2026-11-03: Byte half fixed by [[numerals-without-algebra-import]]: with `import bitvec; import byte;` both `10` and `'\n'` at `BitVec(8)` elaborate (a char literal's `char::Char`/`char::ofNat` are read in `char`'s scope when it is in the closure). Remaining: with `byte` not imported, `'a'` at a byte still says `add import char;` where `import byte;` is the fix.
