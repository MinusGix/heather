---
title: Make a red sentinel say whether the PR lane's selection would have run the failure
status: open
labels: [testing]
area: infrastructure
created: 2026-10-30
updated: 2026-10-30
---

`scripts/test --pr` now runs only the test files a diff can affect
([[pr-lane-affected-selection]]). The sentinel's full nightly run is what
catches a miss, but it does not say whether one happened: when it bisects a
failing target to a merge, it should also run `scripts/affected-targets.mjs
--paths` over that merge's diff and say whether the failing file was
selected. A "not selected" is a selector bug to fix (an input the selector
does not see), and the count of them over time is the data §2.3 of
docs/testing-architecture-design.md asked for before trusting the lane.
