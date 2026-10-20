---
title: Recover inline record projections in diagnostics
status: open
labels: [frontend,diagnostics,records]
area: language
created: 2026-09-05
updated: 2026-09-05
---

A hole at x.value = y.value for record Plain { value: Nat } still prints inline fst/snd kernel terms. [[positive-subtype-manual-round]] adds nominal recognition for registered RecProj definitions, which covers unparameterized dependent records such as PositiveNat. Nondependent records and parameterized records keep inline projections and need a separate bounded inverse. Recover field and receiver names from trusted record metadata and the actual projection shape; cover nested fields, dependent contexts, and generic records. Decline when identity or scope is uncertain, preserve the printers node/depth budget, and do not unfold arbitrary terms or confuse a structural pair projection with a record accessor.
