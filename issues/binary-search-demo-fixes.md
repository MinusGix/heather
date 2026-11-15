---
title: A `runtime fn` with an `on` block over a nested test, and a conjunction in `bv_omega`'s scope, were refused
status: closed
labels: [native,tactics]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-15
updated: 2026-11-15
---

Found writing the binary search example (`examples/binary-search/search.hthr`),
two refusals of correct programs and proofs:

1. **"rt: a `match`: it is not a `match`".** A measured `runtime fn` whose
   `on ?decN := { … }` discharges a call under a test nested in `if h:` has
   its inner `match` under the obligation's binding, applied: a β-redex.
   `View` contracts a head β-redex (it showed `HMatch`), but `Arms` read the
   raw term, found a `λ` at the head and refused. `Arms` now contracts head
   β-redexes as `View` does (`host.rs`, `arms_request`).
2. **"`bv_omega` wrote a proof that does not parse".** A conjunction in
   scope is read side by side as `m.left` and `m.right`
   (`omega_cert::push_conjuncts`); a side restated over a word the walk takes
   apart was rebound under its own name, and `(m.left: …) →` is no binder.
   It is now bound fresh (`__bv_factK`), and the root `m` is hidden as `True`
   once every side read from it is restated, as rebinding hides a plain name.

Probes: `count_down_odd` in `lib/_tests/native/runtime/runtime_loop_tests.hthr`
and `conjunct_fact_restated` in `lib/_tests/std/tactic/bitvec_omega_tests.hthr`;
both refused before.

Left open from the same rounds: [[bv-omega-word-comparison-goal-composite]]
(binary search), [[runtime-mut-self-let-read-walk]] and
`theorem-branch-on-measured-fn-goal` (sort; filed and fixed in its own PR).
