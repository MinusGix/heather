---
title: A generator's instance at a named type carrier is refused
status: open
labels: [elaborator, classes, generators]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

A generator registers an instance by `Decl(AsInstance(class, args, index), …)` (`lib/std/tactic/tactic.hthr`). `publish_instance_member` (`crates/elab/src/host.rs`) spells each type argument as a host leaf, and an arrow as an arrow between two leaves, "because an instance's key reads the carrier's head off its spelling". A leaf has no head, so an instance at a named type is refused:

```
`generate laid_copy(…)`: the generated `Header::copy` was refused: ` host-leaf-0` is not a type or a type former in scope, so ` host-leaf-0::Copy` attaches to nothing
```

Only `runtime::Compile` and `runtime_file::CompileSpan`, whose carriers are function types, have been generated so far. Found by `ownership-copy-clone`, whose `laid_copy` generator wanted to register `Copy<T>(T::rep)` and `ExactClone<T>` for a laid record; it publishes the values instead and the record's module registers them by hand (`lib/lang/facts/copy.hthr`, the end).

## Scope

Spell a type argument whose whnf is a global type applied to arguments as that global's name over leaves for its arguments, as the arrow case already spells its two sides, so the carrier's head is read off the name. A type with no head stays refused with today's message.

## Done when

`laid_copy` registers both instances itself, and `lib/_tests/lang/facts/copy_tests.hthr` drops its two `instance` lines; a negative control (a generated instance at a bare type variable) is still refused by name.
