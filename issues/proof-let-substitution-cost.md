---
title: A proof let is substituted at every use: a let chain checks as one term the size of every copy
status: open
labels: [elaboration,kernel,performance,proofs]
created: 2026-09-25
updated: 2026-09-25
---

A `let` in a proof body is an alias. `statements::elaborate_let` extends the
context with the bound term, and every use of the name is that term. So a
proof written as a chain of `let`s, each using the ones before, reaches the
kernel as one term that holds every copy. The kernel checks each copy where
it occurs, since it has no `let` former.

The certified `wc -l` print profile hit this on 2026-09-25.
`elf64_read_print::read_print_after_read`, written as one body of about
twenty `let`s over the run's intermediate states, took **216 s** to check.
The round split it into three lemmas: `print_formats`, `print_sends` and
`print_writes`. Each is small and the chain is carried by their statements.
The module then checked in about 1.3 s, with no change to what is proved.
Splitting is a fine library style, but a person should not have to find it by
bisection. The next large program will have longer chains.

## Questions

- Where exactly is the copy paid: elaboration (each use re-inferred), the
  kernel gate (each occurrence re-checked), or conversion (a type mentioning
  a bound name compared after it is unfolded)? `--timings` gives the
  frontend/gate split per item. The 216 s item has not been attributed yet.
- What shares the check? Options, cheapest first:
  - elaborate `let x = v; b` as the redex `(λ (x: T) => b)(v)`. The kernel
    checks `v` once, but conversion may still substitute it;
  - lift a large proof `let` to a generated private lemma, which is what the
    round did by hand;
  - a kernel `let` former. That is a kernel design change, and
    `crates/kernel/DESIGN.md` and the DeLaM chapters decide it, not a
    performance issue.
  The first two stay outside the kernel.
- Does the same copy explain [[frontend-large-proof-composition-cost]]'s
  staging gap? If it does, that issue gains its mechanism.

## Acceptance

- The 216 s shape as a regression test or a bench family: a chain of `k`
  `let`s, each using the previous, at growing `k`. Its cost is linear in `k`
  under the chosen fix and is recorded before and after.
- `read_print_after_read` written back as one body checks within a small
  factor of the split form, or this issue records why the split is the
  intended style and the diagnostics say so.

## What it assumes from elsewhere

- **[[proof-scale-abbreviations]]** owns surface syntax for sharing across
  declarations. This issue is about the cost of the `let` that already
  exists.
- **[[conjunction-projection-chain-cost]]** is the same round's other shape.
  It may share a cause.
