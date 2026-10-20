---
title: A wrong dictionary field is refused at the checking position naming a generated projection reference, not the offending declaration
status: open
labels: [frontend,diagnostics,traits,ergonomics]
area: language
created: 2026-09-15
updated: 2026-09-15
---

Since the telescoped-dependent projection device (docs/telescoped-record-projections-design.md, 2026-09-15) a class dictionary's field read such as `A.unit` is a named projection `CommMonoid#projⱼ^δ ā v` rather than an inline `fst(sndʲ v)`, so a wrong unit is caught in the checking position and the message reads `this has type or(x, (CommMonoid#bool#or).unit) = x, but or(x, True) = x is expected here` — it names the two types and a generated instance name where it used to name the declaration that supplied the wrong field (`lib_algebra::one_law_three_structures`, `operation_indexed_classes::slow_acceptance_the_wrong_unit_is_refused`; both controls now assert the substance). The refusal is correct; the rendering is the regression. Fix shape: `display.rs` already resugars `RecProj` references as `.field`; the note should additionally name the declaration/instance the receiver came from, or the diagnostic site should keep pointing at the field's declaration. Triggered by [[diagnostic-operator-resugaring]]'s next round or the next user report of an opaque `#` name in a message.
