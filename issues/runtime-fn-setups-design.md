---
title: Design runtime fn setups: fragment, judgment, soundness once, lowering
status: open
labels: [design,native,metaprogramming,compiler]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-10-31
---

Round R4 of `docs/compiler-milestones-proposal.md` (§4, §7): the design round for `hih-native-heather`.
Minus's note (2026-10-31): not every function is compiled, as Lean does.
A `runtime fn` is opted in under a setup that boxes the function and
pokes at it intensionally. There is a default setup, and users can build
others, such as a borrow-checked one that gives the compiler extra proofs.

## Scope

- The setup record (proposal §4.1): a fragment read through the pull API, a decidable judgment, one soundness theorem per setup, and a lowering to `Source`. Settle how the compiler consumes a setup's evidence.
- The `runtime fn` marker as a Heather declaration generator ([[runtime-compile-opt-in]], [[scoped-declaration-generators]]) on the host interface. Settle what remains of [[compile-typeclass-design]]'s class layer.
- Reflecting a body beyond the Nat fragment of `Elaborator::fn_body_code` ([[elabcode-abstraction-layer]], [[code-variable-analysis-api]]).
- The default setup's pure fragment: widths, `Bool`, flat records and enums laid out in words, `Nat` narrowing (`docs/datarepr-design.md` §2.4), loops, and byte arrays.
- How the `_agrees` certificate scales. Price route 2 of [[in-language-certificate-emission]] (agreement proved once over the fragment) as the fallback.
- How the builder (`lib/native/native_build.hthr`) stops being how people write programs.

## Done when

Minus has decided the note, and [[runtime-fn-default-setup]] states its scope against it. [[native-build-loop-regions]] and [[native-build-reflected-helpers]] are folded in or closed.

## Log

- 2026-10-31: [[native-build-loop-regions]] and [[native-build-reflected-helpers]] closed (2026-10-31): the builder's `Calc` regions, `heather reflect`, and calls to reflected programs.
