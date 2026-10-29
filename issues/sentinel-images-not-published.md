---
title: Publish the sentinel's image stores again (archive over GitHub's file limit)
status: open
labels: [testing,sentinel,caching]
area: infrastructure
created: 2026-10-29
updated: 2026-10-29
---

The nightly sentinel is running and green (2026-10-29: `3608 passed, 0
failed` in 1341 s at 4f0ac27), but its report says "Green, but publishing
the image stores failed". `claude/sentinel-images` still holds the
2026-10-26 07:58 run at 657094c, so every fresh container seeds images
fifty-odd merges old and its first suite elaborates most of what changed
since, in the warmups and the tests.

Likely cause (the run's push output was not kept): the stores go up as one
`images.tgz`, which was already 89.6 MB on 2026-10-26, and GitHub refuses a
pushed file over 100 MB. The library and the DAG images have grown since.

## Fix (2026-10-29)

`scripts/sentinel` publishes the archive in parts of 90 MB
(`images.tgz.000`, …) and `seed` joins them, still reading a single
`images.tgz` from older publishes. Round trip checked against a scratch
repository with a 1000-byte part size; seeding from the current branch
checked too.

## Done when

The next green sentinel's report says "Image stores published". If it still
fails, the session log has the push's error.
