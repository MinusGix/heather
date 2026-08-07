---
title: Scoped instance installation: use instance at module/block scope
status: open
labels: [frontend,elaboration,traits,ergonomics]
created: 2026-08-07
updated: 2026-08-07
---

Decided wanted (user, 2026-08-07), regardless of how [[operation-indexed-classes]] resolves: a scoped form that installs a NAMED instance value as the resolution answer within a scope — `use instance nat_mul_monoid;` at module scope (this file works multiplicatively) and the `let instance` form at block scope (traits layer-2 slice §10 already notes the plain `let` HAS the behavior; this issue owns the keyword form and the module-level variant). Semantics already fixed by the record: scope beats registry, shadows the canonical table, never mutates it. The design questions are only: surface form; whether module-level installation is import-transitive (probably not — a file's context is its own); and the diagnostic when an installed value and a registry instance would disagree (none needed — shadowing is the point — but the trace should SHOW the installation as the winning scope entry).

Small; wants nothing; natural rider on whichever traits round next touches the resolver.
