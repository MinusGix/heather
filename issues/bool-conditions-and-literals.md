---
title: A Bool as an if condition, and False/True without a type
status: closed
labels: [language,frontend,surface-syntax]
area: language
milestone: [lang-sequencing]
created: 2026-11-02
updated: 2026-11-03
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

## Log

- 2026-11-03: DONE. Both halves built in the elaborator; the parser is unchanged.

  **Bool conditions.** The parser still lowers every `if c` to `decide_bit<c>()` (`decide<c>()` with an evidence binder), since it cannot know `c`'s type. `Elaborator::elab_condition` (crates/elab/src/lib.rs) picks the reading by type: the proposition reading first, so every condition that worked before takes exactly the old path at no extra cost; only when it fails is `c` elaborated as a term (under a rollback), and at `Bool` the scrutinee is that term itself. That is definitionally what `decide_bit<c.IsTrue()>()` is (the `IsTrue` instance's `bit := c`), and it means the frontends and `rt` see the plain `match c`, `match not(c)`, `match and(a, b)` they already read. `if h: b` is `decide<b.IsTrue()>()`, so `h: b.IsTrue()`. A condition that is neither is refused: "a condition is a proposition, decided by its `Decide` instance, or a `Bool`; this is a value of `Nat`". Only the parser's lowered call takes the Bool reading (`surface::bool_condition`: its head carries the condition's span), so a written `decide_bit<b>()` still says `b` is not a type. `while c` goes through the same call and gets it too, but see [[while-bool-condition-measure]]. A mixed `b && n = 0` is refused ([[mixed-bool-prop-condition]]).

  **`False`/`True` with no type.** Decided: a bare name that is exactly one constructor and otherwise only type names (`False` with `logic` and `bool`) is the constructor in inference (`Elaborator::ctor_over_types`, read by `resolve`). A choice, not a shrink like the two of [[false-collides-with-bools-constructor]], licensed because every position that wants the type takes it before a constructor route runs: type position filters to `Inductive`, and checking at a universe reads the expression as a type ahead of the constructor arms. So `let p: Type = False` is still `logic::False`. A function or value of the same name, or two constructors, keep the ambiguity. Wired into `resolve` only, not `ctor_here`: in `ctor_here` it also fired in checking routes ahead of the universe reading (`fn no_callees() → Callees() { λ _ _ _ => False }` in function_ir broke). The pinned `a_bare_false_at_an_unsolved_carrier_is_ambiguous` (crates/elab/tests/nat_order.rs) flips to `..._is_the_constructor`, with a universe control.

  Rewritten: `lib/native/runtime/line_tools.hthr` (`if !ok`, `if c.eq_bit(…)`, `if later && better`, untyped `let mut failed = False`), `Io::write_all` in linux_world, `count_words`/`branch_tick` in the probes. New probes at the end of `lib/_tests/std/core/imperative_statements_tests.hthr`: `if b`, `if !b`, `if a && b`, `if a || b` at literal and neutral Bools and an open result type, a checking position, the evidence form, untyped `let mut found = False`, `False` at a universe, and the negative control. Design note: docs/language/decidable-if-expression-design.md.
