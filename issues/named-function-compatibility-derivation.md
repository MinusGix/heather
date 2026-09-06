---
title: Derive reusable compatibility proofs for named functions
status: closed
labels: [frontend,proofs,setoids,automation]
created: 2026-09-05
updated: 2026-09-05
---

Explicit proof-position rel_derive requests should unfold transparent named definitions compositionally, reuse existing certificates, handle local bindings, and produce an ordinary named theorem. Missing compatibility and branch-choice evidence must remain scoped resumable obligations. Exercise the same proof on list and tree backends; preserve rel_cong behavior and user-name shadowing. Bounded homogeneous Type<0> fragment, with branch support through the checked relation_function::choose combinator. Customer: docs/showcase/derive_set_functions.hthr. Related: [[setoid-auto-lifting]], [[certified-parametricity]], [[finite-set-client-design]].

## Log

- 2026-09-05: Implemented bare rel_derive preservation requests and pointwise rel_derive(h), bounded transparent reduction with certificate reuse, fixed-argument family laws, and checked Boolean choice composition. Missing operation/branch evidence is resumable; separate source requests keep independent goals. Five regressions cover author/client files, both backends, wrong/missing evidence, shadowing, and independent obligations. Full plain Furnace suite: 2,418 passed, 0 failed, 5 ignored.
