---
title: The image seed is a night behind master and ten times its live images
status: open
labels: [performance,testing,cache]
area: infrastructure
created: 2026-11-13
updated: 2026-11-13
---

A fresh container's library gate costs what master changed since the seed was published, and every thread's container pays it again. The seed is published once a night, by a green sentinel run, as an archive ten times the size of the images in use.

Found after [[kernel-self-check-cost-on-skipped-terms]] took the gate's cold build step from fourteen minutes to under five and Minus asked for less (2026-11-13).

## Measured

Four-core cloud box, the test profile's `heather` with the self-checks off, master a39d194, the seed of c4ae57c (published 09:15 UTC, 53 commits behind by the afternoon).

- `heather check --unbuilt lib` over the seed: 540 of 543 modules have no image under master's keys.
- The gate's build step over that seed: 284 s wall, 1125 s of child time over 535 modules.
  - About half is each child replaying its imports: a warm check of every module sums to 560 s (the median module 0.85 s; [[build-children-replay-their-imports]]). A third of a replay is moving each import's image into the child's world, which the DAG keying requires of every (module, import) pair.
  - The other half is elaboration: 105 modules cost more than a second over their replay (462 s). Most were not edited: a registry change upstream (`tactic`, `function_ir`'s new constructor) keeps every importer from being moved.
- The whole gate (`library.rs`) over a store that matches master: 19 s. Without the verdict file, 52 s.

So the five minutes are the distance between the seed and master, not the gate.

The seed itself: 517 MB compressed, 5173 images in the CLI store for 543 modules. A store keeps every image of earlier trees until its 4 GiB budget is spent (`ModuleImageCache::sweep`), and the sentinel seeds from its own last publication before it runs, so the archive carried images back to 2026-10-25. The images the last run read or wrote (their modification time, which a read renews) are 810 over the three stores: 79 MB compressed, built in 9 s, unpacked in 2 s. `--unbuilt lib` lists the same 540 modules over either seed, and a check of `trig_law` over either reports the same counts.

## What landed

- `scripts/sentinel run` publishes only the files live since the run began (`live_files`): images by modification time, the `.latest` and `.src` pointers that name one of them, no lock files. The manifest records `since`, `images_commit` and `images_date`.
- `scripts/sentinel refresh [--force] [--dry-run]`: publishes this checkout's stores under the last green run's manifest when its tree is master's and the published images are over three hours old. It runs nothing. It keeps what the last publication held as live plus what this checkout read or built since, because a `--pr` lane renews only the images of the tests its diff could affect. `run` still bisects and compares from the manifest's `commit`, which a refresh does not touch.

Checked without pushing: the archive built from the published seed and from a store built on master (`--dry-run`: 1352 images, 70 MB), the refusal off master's tree, and that the small seed plans and replays as the full one does. The push is `publish`'s, unchanged.

## For Minus to decide

1. **Who runs `refresh`.** It needs a session whose stores are of master. Two candidates: a round that has merged (its branch is master's tree, and it has just run `--pr` over it), as a line in the merge instructions; or a scheduled session every few hours that checks out master, runs `scripts/test --pr` with `HEATHER_PR_AFFECTED=all`, and refreshes. The first costs nothing and follows master exactly; the second does not depend on rounds remembering. Until one is chosen the nightly run is the only publisher, now of a smaller archive.
2. **A red master stops the seed.** `run` publishes only when green. A `refresh` does not ask, since a seeded image can only be a miss; with rounds refreshing, the seed keeps following master through a red night.
3. **The seed carries verdicts.** `cli-check-images/entries-v1.tsv` and `native-test-images/entries-v1.tsv` are the CLI's verdict stores, and they sit inside the directories the seed archives, so they have been published all along, against "images only, never verdicts" (docs/testing-architecture-design.md §3.1.2). A fresh box whose kernel source matches the seed's takes those verdicts and skips the kernel for them. Left as it was here, because removing them makes every native certificate check cold on a fresh box ([[native-tool-test-cold-certificate-rail]]) and that is a choice about the lanes, not a cleanup. The library gate alone would cost half a minute more.

## Done when

A fresh container started a few hours after a merge finds images for all but the modules its own round changes.
