---
title: User-defined effects as interfaces over a mut-self carrier, handled by instance
status: open
labels: [language,effects,design]
area: language
milestone: [nh-effects]
created: 2026-11-08
updated: 2026-11-08
---

User-defined effects have no surface of their own: `Io` is the one
capability, hard-wired to Linux's calls, and a function's type cannot say
which effects it uses (`docs/effects-locality-design.md` §3, N1–N3). The
design note's recommendation (§5.2) is capability passing resolved
statically: an effect is a class whose members update a carrier
(`class Log<C> { log: C → Bytes → Mutated<C, True> }`), an operation is a
`mut self` method generic in the carrier, a function generic in the carrier
states its effects as constraints, and a handler is an instance (pure, at
`Io`, or a wrapper such as `Buffered<C>`). The note's appendix probe shows
the pure, `Io` and buffered handlers working today by `refl`.

## Scope

- A library home for effect interfaces (`lib/std/effect/` or beside
  `linux_world`), with two or three real ones (a logger, a byte sink with a
  restricted `Stdout` instance at `Io`, a seeded random source), each with
  a pure instance and an `Io`-backed one.
- Wrapper carriers that handle one interface and delegate the rest to
  `inner`, and a generator that writes the delegation (`delegate Log to
  inner`) instead of hand-written instances.
- Callbacks that take the carrier (`for_each<C>` with a step
  `C → A → Mutated<C, B>`), the replacement for the refused λ capturing an
  outer world (note §5.4 item 3).
- Probes in `lib/_tests` at a pure carrier and at `Io`, including a
  negative control (a function generic in `Stdout<C>` cannot call `open`).

## What it assumes from elsewhere

- **[[method-call-on-constrained-carrier]]** owns dot calls on a carrier
  variable. Assumed here: only that `c.say(m)` will thread `c` once it
  lands; until then the probes write `c := Log::say(c, m).after`.
- **[[reflect-world-in-carrier-record]]** owns compiling these at an
  `Io`-backed carrier. Assumed here: nothing; this issue is the surface.
