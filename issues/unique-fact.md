---
title: "Unique: the second fact on demand, with in-place update as its consumer"
status: open
labels: [compiler, ownership, design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-01
updated: 2026-11-01
---

`Unique(p, k)`: the buffer the `k`th update of `p` consumes is not read
again, neither by that name nor by any name sharing its storage. Consumer:
compile that update in place instead of copying. Producers, cheapest first
(`docs/native/facts-on-demand-design.md` §7):

- the ownership setup's judgment, as a plain evidence rule
  `Unique::of_owned({p}, {k}, o: Owned(p) := infer)`, `Owned(p)` a linearity
  check that evaluates to `True`;
- a per-site liveness check, verified once and answered by evaluation, as
  the compiler's budgeted fallback.

The mechanism (search rules, `Synth`, `request`, proof-carrying sites) is
[[facts-on-demand]]'s and carries over unchanged. What `Unique` adds is a
semantics where aliasing is observable: the compiler's theorem is a
simulation against a store of slots with a name→slot map, whose invariant is
that every live name reads its slot. That store is `rt`'s memory and the
ownership setup's, so this is built over them rather than over a toy store
that would be discarded.

## Acceptance

- A program with a linear update compiles it in place, the fact from the
  ownership judgment; a non-linear program whose consumed buffer is dead
  anyway gets it from the liveness fallback; one that reads the old buffer
  after the update keeps the copy.
- The compiler's theorem is proved once, for any facts.

## What it assumes from elsewhere

- **[[facts-on-demand]]** owns the request and the order of producers.
- **[[ownership-discipline-over-code]]** owns the ownership judgment.
  Assumed: it is a decidable judgment over reflected code with one
  soundness theorem.
- **[[runtime-fn-reflected-language]]** owns `rt` and its memory.

## Log

- 2026-11-01: Filed from the facts-on-demand prototype, which built
  `InBounds` end to end and designed this one (design §7).
- 2026-11-01: The fact and its producers built over `rt` (design §7,
  rewritten). `rt` has a byte read and a byte write (`Op::Get`, `Op::Set`:
  `List::byte_at`, `List::with_byte`), reflected and pinned by `refl`.
  `lib/lang/facts/unique.hthr` states `Unique(p, f, k)` as a verdict:
  liveness over ANF with storage identities through lets, records, fields,
  branches, calls and folds. Parameters are owned, so calls and fold starts
  are moves. The ownership judgment `Owned(p)` is published once and read
  by the plain rule `Unique::of_owned`, proved once. The per-site check
  `Unique::by_check` is the planner's fallback.
  `lib/lang/facts/write_facts.hthr` publishes a `WritePlan` of proof-carrying
  sites. All three routes are probed in
  `lib/_tests/lang/facts/write_facts_tests.hthr`.

## What is left

- **The in-place lowering and its theorem**, with the plan's proofs as
  hypotheses at the `InPlace` sites. This is the runtime setup's: it lowers
  `Bytes` to a buffer plus a length
  ([[runtime-default-setup-soundness]]), and its store is where "every live
  name reads its slot" is stated. That is acceptance item 2.
- **The calling convention's half.** A callee may write its parameter in
  place only because callers move. The lowering has to pass the buffer
  itself (no copy) at a call whose `Pass` verdict holds, and copy at one
  whose verdict fails.
- **A setup publishing `Owned` itself.** Today a test declares the verdict.
  A runtime setup would publish it beside `judge(p) = Ok`.
