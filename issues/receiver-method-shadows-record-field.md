---
title: Builtin receiver methods claim names before the receiver's type is consulted
status: open
labels: [elaborator,defect]
created: 2026-08-15
updated: 2026-08-15
---

Found in the datarepr v1 round (2026-08-15, docs/datarepr-design.md §1.4 as-landed note 7): `value.fold` on a record value is claimed by the builtin vector receiver method before the receiver's type is consulted, so a record field named `fold` is unreachable by projection. Resolution order should consult the receiver's type first (or at least prefer a field when the receiver is a record). Workaround in the datarepr elaboration: reach through the generated namespace instead of projecting. Related: [[datarepr-separation]], [[theorem-field-projection-oom]].
