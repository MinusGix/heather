---
title: Ownership body meaning: a long-lived local sinks one deeper per binding
status: open
labels: [ownership,library,performance]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The body's environment (`lib/lang/ownership/body.hthr`, `Env`) holds the arguments by position and the locals newest-first (`Var { Arg(i), Loc(j) }`). A variable bound early and used late sinks one deeper with each binding after it, so the kernel's `Env::get` of it walks a list that grows with the body. An argument is reached in place; a local is not. This is filed, not fixed: the coordinating session decided not to build an indexed environment in the interfaces package (`docs/language/ownership-design.md` §22.2, "Variables are `Arg(i)` or `Loc(j)`").

## The measured shape

Kernel steps at width one, fresh cache, `refl` pins of `Func::denote` against the source, read with `scripts/timings` (bench generator kept out of the repo; the shapes are what matters):

| Body of N statements | N = 32 | 64 | 128 | 256 | shape |
|---|---|---|---|---|---|
| N word additions reading one argument | 8.0k | 15.5k | 30.8k | 61.6k | linear |
| N list reads, the list an argument | 18.7k | 36.8k | 73.4k | 146k | linear |
| the same, the list first taken into a local | 23k | 52k | 133k | 379k | superlinear |
| §21.5 probe 2, a `[u64; 16]` local among the words (one environment) | 128k | 280k | 660k | 2.76M, out of fuel | superlinear |
| the same with objects in an environment of their own | 117k | 236k | 485k | 1.02M | linear |

The third row is the long-lived local alone: the object is read once per statement and each statement binds a word above it, so read k walks k deep, which makes the whole body quadratic.

## What would fix it

A long-lived local wants to be reached in constant depth. Possible routes, none taken:

- an environment indexed by a variable's binding position (a map from slot to `Dyn`), with `get`/`push` laws of the same names, so no theorem changes (every theorem reaches the environment only through push, get and the laws);
- objects apart from words (the fifth row), which §21.5 probe 2 measured and which the uniform `Dyn` environment chose against.

The condition the decision set holds in the meantime: no theorem may reach the environment except through `Env::push`, `Env::get` and their laws, so the representation can change underneath.

## Log

- 2026-11-25: filed from the ownership interfaces package with the measurements above.
