---
title: A relation-indexed algebra proof over Ir exhausts kernel conversion fuel
status: closed
labels: [ir,proofs,performance,kernel,algebras]
created: 2026-08-18
updated: 2026-08-18
---

Filed by the first certified-pass algebra probe
(`docs/metaprogramming/certified-pass-algebra-probe.md`). The intended architecture is one
`IrAlgLaws(R, alg)` field per constructor and one generic theorem

```heather
ir_fold_sound(R, alg, laws, ir): R(ir, ir_fold(alg, ir))
```

whose recursive calls supply each field's local hypotheses. The nondependent
`IrAlg`/fold checks. The dependent theorem is kernel-refused with `OutOfFuel`.

This is not evidence against the algebra interface alone: the identical
relation-polymorphic construction checks for branching `Tree`, including a
non-identity mirror pass, two-IH Node law and a rejected bad clause. It is a
scale boundary at the actual IR's eight constructors and branching recursive
fields.

## Narrowings already tried

All were written and kernel-checked against the real `Ir`, then withdrawn:

1. arbitrary `R : Ir -> Ir -> Type` with a dependent law record;
2. the induction family named as a definition, so recursive calls compare a
   stable head rather than spelling `R(ir, ir_fold(alg, ir))` repeatedly;
3. `R` specialized entirely away to equality (`ir = ir_fold(alg, ir)`);
4. `fn` changed to `theorem`.

Every dependent form failed at the generic induction with `OutOfFuel`. The
algebra, fold and law-record declarations before it checked. The concrete pass
was a tag normalization `n` to `add(0,n)`, chosen because it is not
definitionally identity at open `n` but has the local law
`sym(add_left_zero(n))`; semantic refinement would then follow from global
equality.

## Acceptance

A relation-polymorphic `Ir` algebra induction checks under the ordinary kernel
budget and supports the tag-normalization control. The wrong mutation
`n -> Succ(n)` must be refused at the LetCon law. Do not accept a global fuel
increase: identify and control the generated term/conversion shape, following
the named-definition and generated-term-def cuts elsewhere in the frontend.

After that mechanical acceptance, the real architectural customer is a pass
whose output is not propositionally equal to its input and whose `R` is an
execution refinement. That semantic round belongs back on
[[case-algebra-definitions]], not here.

## What it assumes from elsewhere

- **[[case-algebra-definitions]]** owns the pass architecture. This issue owns
  only the checker refusal encountered before its IR semantics could be
  tested.
- **[[datatype-container-algebras]]** owns the explicit algebra exploration;
  its Tree pass is the positive control.

## Log

- 2026-08-18: Filed from the certified-pass probe after all four narrowings
  above produced the same kernel `OutOfFuel`; Tree's general relation-indexed
  version and engaged mutation control are green.
- 2026-08-18: Kernel-boundary probe isolated the refusal to one type
  conversion while checking the equality-specialized theorem body (local
  context length 9); the theorem statement itself checks at `DEFAULT_FUEL`.
  The value-domain converter fails at 2^20 and first succeeds in the sampled
  sweep at 2^21. The pair is the same large `Ir`/`Wf` encoding in two
  spellings: one side is already unfolded to the inline `Sigma`/`Wf` tree,
  while the other still contains the generated `El (D#tycode)` and Wf-slot
  references. The syntax-domain differential oracle accepts the exact pair
  at 2^18 (fails at 2^16) in roughly 84--94 ms, so this is a value-domain
  sharing/accounting gap rather than difficult conversion or divergence.

  The missed value shortcut is also concrete. Millions of comparisons reach
  alpha-equal syntactic type-closure bodies under distinct captured
  environments; a representative pair is the four-entry identity environment
  versus a one-entry substitution environment, so the existing
  same-environment reflexivity rule correctly declines. Allowing equal
  *locally closed* bodies to ignore their environments is sound and makes the
  theorem fit 2^20, but the isolated check still takes about 22 s: it replaces
  structural conversion with repeated deep `Type::eq` and is therefore not an
  accepted performance fix. About 0.65 M of 2.1 M observed closed-body pairs
  repeated, insufficient to make a pair cache the whole answer.

  The narrow next lever is spelling provenance at the elaborator boundary:
  find where match/constructor checking keeps the inline type returned by
  `whnf` while emitted `Supf`/motive/application annotations use the registered
  references, and preserve one spelling across that seam. Do not route the
  production checker through the syntax oracle (it is deliberately only the
  differential specification), and do not land the closed-body shortcut as a
  fuel-only win without a wall-time reduction.
- 2026-08-18: **FIXED at the spelling seam, with no kernel change.** The
  exhausted conversion was the theorem's `laws` local (variable 7 in a
  nine-entry branch context). Its Γ entry had the component-respelled record
  type produced when the theorem's binders were closed, while
  `project_field`'s fallback Σ walk emitted `Fst`/`Snd` annotations from the
  inline structural copy. `IrEqLaws(alg)` is value-parameterized, so it is
  deliberately outside the named-projection-definition boundary; that is why
  the otherwise related `RecProj` path was not involved.

  `project_field` now follows the existing structural/emission split used by
  constructors and match lowering: it keeps the inline Σ tail for structural
  reads and substitutions, but component-respells the `fst` and binder-scoped
  `snd` annotations it emits. The resulting projection synthesizes the same
  spelling Γ stores, so the expensive inline-vs-code conversion disappears.
  The arbitrary-relation `IrPassLaws`/`ir_fold_sound` checks at ordinary
  `DEFAULT_FUEL`; a concrete pass rewrites `LetCon` tags to `add(0, tag)` and
  is certified by the constructor-local laws; attempting to reuse those laws
  for `Succ(tag)` is refused as `NotConvertible`.

  Verification: projection-focused suites 122 passed; full `scripts/test`
  1926 passed, 0 failed; `scripts/bench --check` 106 comparisons within
  thresholds. `scripts/bench-frontend --check --no-heavy` was run twice but
  is not claimed green: at system load 4.5--5.6 it flagged 12 then 10 broad
  time regressions, including parser-only and prelude-clone rows unreachable
  from this change; no noisy baseline was saved. The issue's mechanical
  acceptance is met. A genuinely
  semantics-changing IR refinement remains the architectural next step owned
  by [[case-algebra-definitions]].
