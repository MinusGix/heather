---
title: Resolve Result map receivers with overlapping imported map names
status: closed
labels: [frontend,elaboration,modules,ergonomics]
created: 2026-09-14
updated: 2026-09-14
---

## Reproduction and scope

During the calculator round, `calculate(ts).map(λ (n: Nat) => Some([n]))`
reported that `map`'s receiver has to be a vector. The receiver is
`Result<Nat, ParseError>`; the client imports several libraries exposing map
operations. `docs/showcase/calc_parser.hthr` uses qualified `result::map`
as the workaround. Minimize this against the actual combined imports and
separate method selection from callback inference before choosing a fix.

There is a name-based vector-map path in application elaboration, but that
observation alone does not establish which resolution step should change.
Preserve existing field, local-shadowing, explicit-qualification, and
nominal-member rules while diagnosing the fallback. Compatible receiver
types should guide selection; genuine ambiguity should be reported rather
than resolved by arbitrary import order.

## Acceptance

- A Result receiver reaches its map operation under the calculator imports,
  first with a callback whose type is explicit so inference is independent.
- Result, List, and primitive-vector clients coexist; unrelated imported
  map names do not divert the call to an incompatible vector primitive.
- Preserve callable record fields named `map`, local shadowing, and explicit
  qualification. Multiple genuinely compatible candidates have an actionable
  ambiguity diagnostic under the documented resolution policy.
- Wrong callback types are reported as errors for the selected operation;
  failed receiver inference is not replaced by a misleading vector error.
- Include neutral receivers, polymorphic payloads, and refusal controls.

## What it assumes from elsewhere

- **[[receiver-method-shadows-record-field]]** owns an earlier, CLOSED arity
  diagnostic fix; assumed here: its field/receiver regression cases stay
  valid. This issue does not reopen or restate that old defect.
- **[[type-owned-members-receiver-slice]]** owns existing nominal dispatch;
  assumed here: its visibility and shadowing policy is preserved.
- **[[callback-expected-type-propagation]]** owns callback type inference;
  this issue isolates selecting the correct map operation.
- **[[parser-combinator-library]]** is the downstream library customer.

## Log

- 2026-09-14: Implemented ambiguous-import receiver selection
  (`docs/language/classes/imported-receiver-dispatch-design.md`). Candidates are filtered only
  by known distinct outer carriers, with canonical declaration identity;
  same-carrier and unknown/generic candidates retain ambiguity. Existing
  field/local/selected-import/nominal-member routes retain precedence. Bare
  ambiguous `map(...)` now reports module ambiguity. The calculator uses
  `.map` with an explicitly typed callback, isolating the inference follow-on.
  Focused dispatch and calculator acceptance: 7 passed; existing field,
  receiver-position, nominal-member and class-dispatch targets also passed.
  Full `scripts/test`: **2647 passed, 0 failed, 5 ignored**. The isolated
  benchmark gate reports six Nat timing flags, recorded with the existing
  [[kernel-benchmark-nat-baseline-drift]]; baseline unchanged. Issue-link and
  diff checks pass. This dispatch scope is complete; callback inference
  remains with its existing owner.
