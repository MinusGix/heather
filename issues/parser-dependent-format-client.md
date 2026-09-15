---
title: Exercise dependent parsing with a length-prefixed format
status: open
labels: [stdlib,parsing,proofs]
created: 2026-09-15
updated: 2026-09-15
---

## Problem

Dependent bind is checked, but the library needs a substantive client where a parsed header determines the payload type.

## Scope and acceptance

Implement a small length-prefixed token format using bindD and Counted. Cover zero length, truncated payloads, trailing data, nested records, and malformed headers. Prove the header/payload length relation on open inputs. Assess how much cursor and certificate plumbing escapes into user code.

Acceptance: executable format, open dependent guarantee, negative controls for fabricated lengths, and documented API friction.

## What it assumes from elsewhere

[[parser-combinator-library]] supplies dependent bind and finite repetition. [[parser-certificate-ergonomics]] owns generic API improvements revealed by the client.
