---
title: "A module whose image is refused as over budget is silently un-probeable, and --only's advice is wrong"
status: open
labels: [tooling, cli, cache, diagnostics]
created: 2026-09-18
updated: 2026-09-18
---

`docs/showcase/calc_text.hthr`'s semantic image does not fit the store:

```text
cache: could not store module `calc_text` (semantic image has 483322044 syntax
nodes, past the decode budget of 256000000; not stored, so a warm run
re-elaborates this module)
```

Two consequences, one per half of this issue.

**The cost.** Because the image is never stored, every warm run re-elaborates
the module. Measured on the 529ab47 tree, unloaded: a **theorem-only** edit
costs **95 s** to recheck and a grammar-level edit **96 s** — the edit's size
does not matter, because nothing about the module is ever cached. For
comparison `docs/showcase/calc_parser.hthr`, the same grammar over tokens,
stores without a notice and probes with `--only` in **5 s**.

**The diagnostic.** `check --cache --only <item>` on such a module says:

```text
error: --only: no stored image of module `calc_text` over these dependencies to
replay the prefix from; run `heather check --cache` on the file once first
```

The advice cannot work and the message does not say why: the `--cache` run *did*
happen, and the store refused its image. `--only` should distinguish "never
checked" from "checked, and the image was refused as over budget", and say the
latter with the node count — otherwise a user follows the instruction in a loop.
The publish notice is printed on the seeding run, but a reader looking at the
`--only` failure has no reason to re-read an earlier run's output.

The budget itself is probably not the thing to raise. 483 M syntax nodes for a
500-line file is the symptom of
[[elaborator-canonical-type-spelling]]'s record-spelling defect written into
every annotation — the same root cause as that file's 27× conversion misses and
its >8 GiB peak ([[sequence-parser-source]]). Fix the spelling and the image
should fall under the budget on its own; then this issue is only the diagnostic.

## Log

- 2026-09-18: Filed the same day as a claimed `--only` regression ("refuses on
  every module"), which was **wrong** and is corrected here. `--only` works:
  5 s on `calc_parser`, 1 s on `lib/std/string.hthr`. Two different failures had
  been conflated — a transient one where a `.latest` pointer named an older
  dependency world right after `lib/std/list.hthr` changed, and this permanent
  one, which is over-budget publication. The transient case repairs itself on
  the next full check; only the over-budget case is a standing defect.
- 2026-09-18: The diagnostic half landed: `NoPreviousImage` now names both ways to reach it —
  "not checked with `--cache` over these dependencies yet" *and* "its image was
  refused as too large to store, which that run reports as `cache: could not store
  module …`; a module whose image does not fit cannot be probed with --only at
  all". Pinned by two assertions in
  `crates/cli/tests/check.rs::only_elaborates_the_named_declarations_over_a_replayed_prefix`,
  so it cannot regress to the advice alone.

  Deliberately *not* done: a refusal marker beside the `.latest` pointer, which
  would let the message quote the node count at the `--only` run instead of asking
  the reader to remember an earlier run's notice. That adds a file kind to the
  cache's on-disk contract, which is load-bearing for image and verdict identity,
  and it deserves its own decision rather than riding along with a message fix.
  Worth doing if anyone loops on this again.

  The cost half stays open and is not this issue's: it is the record axis on
  [[elab-emits-normal-form-of-matched-type-argument]], whose family the user
  paused on 2026-09-16.
