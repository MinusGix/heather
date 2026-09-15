---
title: Improve parser certificate composition and inference
status: open
labels: [stdlib,parsing,proofs]
created: 2026-09-15
updated: 2026-09-15
---

## Problem

The checked parser API exposes explicit operation-indexed Consumes and Sound arguments. Nested combinators repeat parser expressions, token/result types and source-indexed callback annotations.

## Scope and acceptance

Use calculator grammar soundness and a value-dependent format as clients. Add reusable postcondition weakening/composition where demanded; investigate predictable certificate inference without broad search over arbitrary parser functions. Keep manual certificates available and retain their exact operation indices.

Acceptance: shorter checked clients, rejection of certificates borrowed from a different parser, and diagnostics that identify the missing law. Do not equate proof-carrying outputs by assuming proof irrelevance.

## What it assumes from elsewhere

[[parser-grammar-soundness]] supplies the first substantial semantic-proof client; [[parser-dependent-format-client]] supplies dependent output constraints.

## Log

- 2026-09-15: The grammar client motivated flattened Certified fields, certified recognition and generic Result folding. [[parser-certified-composition-cost]] owns the substantial checking cost exposed by this client; ergonomics changes must be evaluated against it.
