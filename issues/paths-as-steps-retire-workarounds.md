---
title: Retire KeyIn and Footprint, and narrow PathSame, now that places are steps
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

With places as steps (lib/lang/ownership/steps.hthr), three things the path libraries built to work around incomparable paths have a successor:

- **`PathSame`** (lib/std/machine/path.hthr): two spellings of one path. Between places it is replaced by comparing steps (`Step::same`, decided by evaluation). What remains is the regrouping of a denotation (`Path::then_assoc`, a trailing `Path::id`), which stays as a lemma about `Steps::denote` (for instance `denote(xs ++ ys)` the same as `denote(xs).then(denote(ys))`). Keep it; stop using it as the carrier of "this path is that shape".
- **`KeyIn`** (lib/std/data/store_path.hthr) records that a path is a key's then an inner path, through a `PathSame` field. A place whose steps start with `SKey` says that syntactically, and `KeyIn::apart` is the decider's key case. Its clients (`arena_handle_paths.hthr`) move to steps, then `KeyIn` goes.
- **`Footprint`** (lib/std/data/set/footprint.hthr): the design review calls it redundant beside `Held`. Which parts a live place holds is now its steps and the checker's place states; the separation algebra that remains is level 3's (`Held`, `placement_sound`). Port `footprint_frame.hthr` and `access_frame.hthr` to `Held`, then delete `Footprint`, its tests and its `pcm` instance.

Do this once package 3's checker reads places as steps, so the ports land against their real client.

## What it assumes from elsewhere

- **[[ownership-steps]]** built steps and the decider.
