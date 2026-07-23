---
title: Implement the three substitution operations (ch. 05)
status: open
labels: [kernel, delam]
blocked-by: [kernel-v0-scope]
created: 2026-07-22
updated: 2026-07-22
---

The mechanical bulk of the kernel, and where de Bruijn bookkeeping bugs
breed. Implement per the ch. 05 operation tables, over the full syntax
including motives/branches:

- **Universe substitution `φ`** (`Vec<Level>` per level.rs): propagates
  everywhere; extends under `UPi`/`ULam` binders and per-branch universe
  telescopes. Composition and identity.
- **Local substitution `δ`**: application to types/terms, lookup, the
  query ops δ̂/δ̌ (done in term.rs), composition (`wk`/`empty` tail cases),
  identity as `wk^0_Γ`. Note boxed code is *opaque* to δ (`box T [δ] =
  box T`) — code lives in its own Δ.
- **Global substitution `σ`**: the subtle one — substituting a context `Γ`
  for a context variable `g` rewrites substitution *tails* (`wk^k_g`,
  `·^k_g`) by re-expanding against Γ, and global-variable lookup composes
  `σ(u)[δ[σ]]`. Extends under every global binder (branches bind up to 5).
- Plus de Bruijn shifting for all three namespaces (the weakenings the
  paper takes for granted).

Verification: property-test the ch. 05 algebraic laws (identity,
associativity/composition, commutation between the three kinds) on
generated well-scoped terms. These tests are the main defense for
everything downstream.
