---
title: Decide what MustRefines should mean—or whether to keep the name
status: open
labels: [stdlib,logic,semantics,design]
area: heather-in-heather
created: 2026-08-26
updated: 2026-08-26
---

`std/relation` currently defines `MustRefines(implementation, specification)`
as reverse relation inclusion: the implementation supplies every outcome the
specification requires.  That is a useful finite terminating order, but
“must refinement” can mean something richer once divergence, refusal, or
interaction is observable.

Before the name gains customers, decide whether to keep it with its restricted
meaning, rename it to something literal such as `IncludesRequired`, or defer a
must-style judgment until the semantic model has enough structure.  “Keep it
unchanged” is a valid outcome if the boundary can be stated without ambiguity.

## What it assumes from elsewhere

- **[[relational-semantics-refinement-kit]]** owns the current definition.
- **[[effects-direction]]** owns the richer observations that may eventually
  make reverse inclusion insufficient.
