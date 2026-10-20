---
title: Design compositional parser diagnostic labels and context
status: open
labels: [stdlib,parsing,proofs]
area: heather-in-heather
created: 2026-09-15
updated: 2026-09-15
---

## Problem

Numeric expected-token IDs support stable merging but provide little help with nested formats or user-facing messages.

## Scope and acceptance

Design typed labels and explicit context attachment while preserving farthest-error selection, tie merging and independent retry policy. Specify how context behaves through attempt, choice and lookahead, and how callers render diagnostics. Use malformed calculator and length-prefixed inputs as examples.

Acceptance: compositional API, useful rendered examples, and laws/tests pinning context retention and expectation ordering. Keep source positions available independently of display strings.

## What it assumes from elsewhere

[[parser-combinator-library]] supplies ErrorView and current error merging; [[parser-dependent-format-client]] supplies a structured-format client.
