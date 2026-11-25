---
title: A decider for a holding's validity over its spans' endpoints, not every address
status: open
labels: [algebra,ownership]
area: mathematics
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`Held::valid` (`lib/std/data/set/held.hthr`) decides a holding's validity by checking every address below the last end of its spans (`Held::bound`): sound and complete, but its cost is linear in the largest address, not in the number of spans. Holdings over a 16-word arena or a record's bytes are cheap; holdings at real addresses (a buffer at `0x1000`) are not (residue of [[ownership-library-join]]).

## Scope

- A decider that checks only the spans' bases: the sum of shares at an address is at most the sum at the largest base at or below it among the spans that hold it, so validity at every base is validity everywhere. Sound (that domination argument) and complete (it checks real addresses), stated beside `Held::valid` with the same `valid_sound`/`valid_complete` shape.

## Done when

A closed holding at large addresses (a span at `2^20`) is decided by evaluation at a cost in its number of spans, with a negative control (three overlapping halves refused).

## What it assumes from elsewhere

- **[[separation-algebra-paths-instance]]** owns the `Held` carrier and its instance. Assumed here: only `Held::share_at` and `Held::Valid`.
