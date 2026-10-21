---
title: Expose a scoped host elaboration interface usable from Heather
status: open
labels: [metaprogramming,elaboration,design]
area: tactics
milestone: [tac-host-interface, hih-passes]
created: 2026-09-07
updated: 2026-10-21
---

Own the public interface between user metafunctions and the active compiler:
scoped name resolution, checking syntax against expected types, diagnostics,
instance lookup, and checked declaration publication. Initially implemented by
Rust, the interface must admit an ordinary Heather implementation later.

An import of elaborator definitions names a module implementation; it does not
implicitly replace the elaborator currently executing the build. Access to the
current environment is an explicit host context/capability. Pin the active
implementation for a build. Future self-hosting may build a selected toolchain
and hand off at a stage boundary; mid-module self-replacement is not required.
Artifact identity must account for dependencies/configuration, not just a version
string. Identity and correctness are separate claims.

## Acceptance

- Specify a bounded context interface and its effects, including instance lookup,
  expected-type checking, diagnostics, and publication after kernel checking.
- Keep structured syntax, source provenance, hygienic names, and typed references
  across calls; avoid requiring string round trips after resolution.
- Separate imported elaborator definitions from current host services explicitly.
- Document which parts are host primitives and how Heather implementations could
  replace them without changing generator clients.
- Distinguish well-typed emitted terms from preservation of surface semantics;
  moving elaboration into Heather enables proofs but does not itself prove either.

## What it assumes from elsewhere

- [[generators-in-the-language]] owns moving generators into Heather.
- [[scoped-declaration-generators]] owns invocation and module expansion.

## Log

- 2026-09-08: [[heather-checked-construction-api]] owns the first bounded Heather-side construction customer; this issue retains the host capability boundary.
- 2026-10-21: Design proposal: docs/host-elaboration-interface-design.md. Tactics are ordinary Heather values of a request tree `Tac<A>` (an interaction tree over a `Req`/`Resp` container) that the elaborator runs like an in-language analyzer, seeing terms through a lazy surface-level view with host-issued handles; layer-m Code stays the home of typed generators (design §2 says why tactics are the opposite case). Four decisions for Minus in §0; rounds R1–R4 in §10. The probe (crates/elab/tests/tactic_request_tree.rs) checks the protocol, `bind` and a Heather handler compute in today's surface.
