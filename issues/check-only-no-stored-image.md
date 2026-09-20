---
title: "A module whose image is refused as over budget is silently un-probeable, and --only's advice is wrong"
status: open
labels: [tooling, cli, cache, diagnostics]
created: 2026-09-18
updated: 2026-09-20
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
- 2026-09-20: Implementer, **day one — `check-only-no-stored-image`**: the refusal marker
  the 2026-09-18 entry deliberately left out is in, so `--only` now *tells the
  two cases apart* instead of naming both, and quotes the size.

  `crates/cache/src/module_image.rs` (+112): `ImageRefusal` (`Nodes { nodes,
  limit }` / `Bytes { bytes, limit }`, one line of ASCII, `v1`-tagged so an
  unknown future variant parses back as `None` rather than as a wrong number);
  `ModuleImageCache::{refusal, note_refusal, refusal_path, world_key}`.
  `latest_path` and `refusal_path` are now the same `world_key` with different
  extensions, so the marker is per (module, dependency world) exactly as the
  pointer is. `publish_as` writes it on both size refusals (the node budget and
  the byte limit — the node one is the issue's case, the byte one is the same
  user-visible situation on a different rail and must not be reported with a
  node count it does not have) and **clears it after a successful publish**, so
  a world that now has a pointer can never report a stale refusal.

  On the on-disk-contract reservation the 09-18 entry raised, which is why this
  was deferred: the marker is outside the contract by construction and the doc
  comment says so — `load`, `load_previous`, `publish`'s identity and the
  verdict store never read it, `sweep` already ignores every extension but
  `.latest` and `.hmi`, and every write and read is swallowed on error. A lost,
  truncated or corrupt marker costs one less helpful sentence and nothing else.
  One wrinkle found in testing: the budget check precedes `publish_as`'s
  `create_dir_all`, so `note_refusal` creates the store directory itself — a
  store that has never published anything writes the marker as its first file.

  `crates/cli/src/semantic.rs` (+22/−9): `NoPreviousImage` gains
  `refusal: Option<ImageRefusal>`, filled from the store at both `--only`
  failure sites. With a marker the message is *"the store refused it: its image
  has N syntax nodes, past the decode budget of M. It was checked; re-running
  `heather check --cache` will not help, because the refusal is the image's size
  and not a missing run."* Without one the 09-18 two-way message is unchanged,
  which is still right: no marker means "no marker", never "the image fits"
  (a store pruned or predating this change).

  *Tests run* (only what could break, per the round's scope):
  `heather-cache` `module_images` 9 passed, `end_to_end` 17 passed,
  `heather-cli` `check` 28 passed — including
  `only_elaborates_the_named_declarations_over_a_replayed_prefix`, whose two
  assertions on the old message still hold because the no-marker branch is
  unchanged. `an_image_past_the_node_budget_is_refused_at_publication_not_at_every_load`
  extended with the two assertions that matter: the refused publish records
  `Nodes { nodes > 1, limit: 1 }`, and the subsequent publish under the default
  budget clears it.

  Not done here: exercising it on `calc_text` itself (~6 min, 9.8 GiB); the
  mechanism is unit-tested and `calc_text` is stage 2's subject anyway.
  The issue's *cost* half stays open and is this round's stages 1–2.
