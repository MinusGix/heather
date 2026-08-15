---
title: Projecting a theorem-valued record field exhausts memory
status: open
labels: [elaborator,defect]
created: 2026-08-15
updated: 2026-08-15
---

Found in the datarepr v1 round (2026-08-15, docs/datarepr-design.md §1.4 as-landed note 7): projecting a theorem-valued field off an assembled record VALUE (e.g. `ListTok().Cons_abs`) exhausts memory and dies on the ulimit — a user-reachable SIGABRT, not a slow check. The datarepr elaboration works around it by reaching through the generated namespace (`Repr_N::Cons_abs()`), which is why nothing in the landed tests hits it. Repro shape: any record with a proof-valued field, assemble a value, project the proof field. Likely a conversion/unfolding blowup where the projection forces the whole record value; worth a minimized repro before any fix. Related: [[datarepr-separation]].
