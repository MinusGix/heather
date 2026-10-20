---
title: Make equality orientation matter only at explicit elimination boundaries
status: open
labels: [frontend,proofs,elaboration,ergonomics,research,design]
area: language
created: 2026-08-19
updated: 2026-08-19
---

Equality is symmetric as a proposition, but proof APIs often make the writer
care whether the available term has type `a = b` or `b = a`. This is sometimes
essential at `j`/transport, yet it can become incidental friction in rewriting,
constructor equations, and goal-directed proof steps. Lean exhibits this bite
occasionally even though choosing the direction is rarely the mathematical
point.

Research how Heather can keep orientation explicit at genuine elimination
boundaries while making routine consumers symmetric. This is not a proposal to
change the kernel's oriented `Id`: `j` still transports from a fixed endpoint.
Candidate surface/elaboration approaches include:

- a goal-directed rewrite that selects the direction from occurrences in the
  goal and reports ambiguity rather than guessing through both;
- theorem/application elaboration that may insert `sym` when exactly one
  orientation satisfies an expected equality argument;
- symmetric interfaces for common equality combinators, while retaining
  explicitly directed variants for predictable proof terms;
- a uniform convention for generated constructor equations, with cheap
  adapters at their consumers.

The design must study ambiguity, rewrite loops/term growth, inference stability,
diagnostics, and whether automatic symmetry obscures a genuinely intended
direction. Positional `if let` keeps the established `scrutinee = pattern`
convention in the meantime ([[let-else-sugar]]).

## Acceptance

- Collect several real sites where a bare `sym` is merely orientation tax and
  several where direction carries information.
- Prototype at least goal-directed rewriting and expected-argument symmetry;
  compare predictability and generated terms.
- State exactly which operations may try the reverse direction and how
  ambiguity is diagnosed.
- Preserve an explicit, stable route to oriented `j`/transport.

