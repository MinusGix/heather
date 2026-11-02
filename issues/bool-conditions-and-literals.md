---
title: A Bool as an if condition, and False/True without a type
status: open
labels: [language,frontend,surface-syntax]
area: language
milestone: [lang-sequencing]
created: 2026-11-02
updated: 2026-11-02
---

A `Bool` cannot be an `if` condition, and `False`/`True` need a type to resolve. Minus raised this reviewing PR #394 (2026-11-02). Probed on master that day:

- `if ok { … }` and `if !ok { … }` on `ok: Bool` fail: the condition is read as a type ("unknown type `ok`", "this is not a type"). Code writes `if ok = False { … }`, which works because `ok = False` is a decided proposition.
- `False` and `True` are ambiguous between `logic` and `bool` when both are imported, so `let mut failed = False;` is refused. In a checking position at `Bool` they resolve (`let mut failed: Bool = False;`, `fn f() → Bool { False }`, `if ok = False`). That is why code writes `Bool::False` when no type is written.

Both make native and effectful code read worse than it should (`lib/native/runtime/line_tools.hthr`, `lib/std/os/linux/linux_world.hthr`), and that is the code being written now.

## Scope

- `if c { … }` with `c: Bool` (and `!c`, `a && b` over Bools) branches on the Bool, as `match c { True => …, False => … }`. A condition that is a proposition keeps today's decided meaning. Which reading applies is decided by the condition's type, and one that is neither is refused, naming both readings.
- `False`/`True` with no expected type: prefer the `Bool` constructor in a term position whose type is not a universe, or refuse with a note that names the annotation. The decision, and what `logic::False` costs in a term position, is the issue's to make (see [[bool-from-decidable-prop]] for the other direction, and the closed [[false-collides-with-bools-constructor]]).
- The native frontends and `rt`'s reflector see the same `match` on a Bool, so nothing downstream changes.

## Done when

`line_tools` is written with `if !ok` and with untyped `let mut failed = False`, and the literal probes still pass. A probe in `lib/_tests/std/core/imperative_statements_tests.hthr` covers `if b`, `if !b` and `if a && b`, each at a neutral and a literal Bool.
