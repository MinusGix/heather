---
title: A byte-level model of steps: fields as Part::path, for placement
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Steps (lib/lang/ownership/steps.hthr) are denoted through a `StepModel<S>`, and the decider is sound in any model with `StepModelLaws`. The one model built is the value universe of level 2 (lib/lang/ownership/value_steps.hthr). Level 3 needs a second: steps over the bytes of a laid value, where a field step is `Part::path` (lib/std/machine/part_path.hthr) at an offset from a layout table, an element of a fixed vector is `Path::entry` (vector_path.hthr) or a window of the element's size, and two fields are apart by `Part::paths_apart` on their offsets. Its `apart` law is the byte-span verdict, so the model's `Sel::apart` for fields there is the layout's spans, not the field indexes; whether one `Sel::apart` serves both models or the model supplies its own verdict is the first decision.

This is what `placement_sound` (package 6) reads to take a level-2 reference with steps to a byte span; it is not needed before then.

## What it assumes from elsewhere

- **[[ownership-steps]]** owns the model interface and the value model.
