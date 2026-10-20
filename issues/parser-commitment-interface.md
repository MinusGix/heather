---
title: Clarify scoped parser commitment and backtracking
status: open
labels: [stdlib,parsing,proofs]
area: heather-in-heather
created: 2026-09-15
updated: 2026-09-15
---

## Problem

commit marks failures as committed, while an enclosing attempt makes those failures retryable. Successful commit does not establish a persistent cut. The name can suggest a stronger effect than the implementation provides.

## Scope and acceptance

Decide names and documentation using nested choice, attempt, optional and lookahead examples. Keep diagnostic position distinct from retry policy. Decide separately whether a persistent cut is useful enough to add; do not silently change existing behavior.

Acceptance: a concise behavior table, nested checked examples, and an explicit compatibility decision for any rename or new operator.

## What it assumes from elsewhere

[[parser-combinator-library]] supplies the current checked failure semantics.
