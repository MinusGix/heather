---
title: Name the kernel checker's modes (Gate/Oracle/Spell/Locate) with an enum
status: closed
labels: [kernel,refactor,state-machine]
area: kernel
created: 2026-11-02
updated: 2026-11-09
---

Name the kernel checker's four modes with an enum instead of four independent fields.

## Problem

`typing::Tc` (`crates/kernel/src/typing.rs` ~1080) carries `materialize_eagerly: bool`, `spellings: Option<…>`, `spell_all: bool` and `refused: Option<…>`: sixteen combinations, four built. Gate (`Tc::new`), Oracle (`Tc::eager`), Spell (`Tc::eager` then two field writes, ~723 and ~797) and Locate (`Tc::new` then a field write, ~564 and ~587). `spell_all` is unread outside Spell. "Spell implies eager" holds because both spell paths start from `Tc::eager`. Arms test the combination directly (`!self.materialize_eagerly && self.spellings.is_none()` ~3342; the memo is skipped when `spellings` is `Some` ~2661). Survey: `docs/implicit-state-machines-survey.md` §6.

## Proposal

`enum TcMode { Gate, Oracle, Spell { all, record }, Locate { slot } }` with predicates such as `eager()` and `memo_allowed()`, so arms ask a named question and the impossible combinations cannot be built. `tests/typing_differential.rs` already covers the behaviour. Low urgency: do it in a kernel round that touches `Tc` anyway, with `scripts/bench --check` (the mode tests sit on the checker's hot path).

## Related

Filed together from the implicit-state-machines survey (`docs/implicit-state-machines-survey.md`, 2026-11-02, ranked there): [[elab-field-lifetimes-explicit]], [[module-pass-state-machine]], [[kernel-psi-bound-cache]], [[decl-attempt-lifecycle]], [[goal-slot-state-enum]].

## Log

- 2026-11-08: 2026-11-08: still accurate in the kernel second pass (`docs/kernel-implicit-state-review.md` §5); line numbers moved (`Tc` ~1080, mode tests ~2146–3446). A Locate checker bypasses the typing memo via `tm_check_noting`, so `mode.memo_allowed()` should cover it, and it can share the [[kernel-premise-queue-type]] queue without the memo take-back question.
- 2026-11-09: done. `TcMode { Gate, Oracle, Spell { all, record }, Locate { slot } }` with `eager()`, `spellings()`, `spell_all()`, `refused_slot()`; the spelling and locating checkers are built with their mode by `Tc::with_mode`.
