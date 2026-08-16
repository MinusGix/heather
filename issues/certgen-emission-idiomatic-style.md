---
title: certgen's emissions keep the curried/annotated style the datarepr generators dropped
status: open
labels: [ergonomics,testing]
created: 2026-08-16
updated: 2026-08-16
---

Spun off [[idiomatic-spelling-pass]] (2026-08-16), which flipped the **datarepr/reprgen** family's emission style to the idiomatic surface — one n-ary argument list spilled across the curried Π spine, one unannotated multi-binder λ — and deliberately stopped at the charter's boundary.

certgen emits surface source too, and three of its sites still write the older style:

- `cert_app` (crates/elab/src/certgen.rs) renders a member's invariant theorem as `{name}({rec_arg})({others})` — the declaration is 1-ary returning a Π, exactly the shape `Repr_N::fold()(B)(…)` was before the flip;
- the fuel wrappers write `eval({fuel}, {f}_gen_prog())({env}, {f}_gen_body())`;
- `emit_instance` writes an annotated λ chain, `λ (p: T) => …`, for the instance's `cert` field.

Everything else certgen emits is already n-ary.

Why it was not done in that round, recorded so it is a decision and not an oversight: the charter names datarepr/reprgen, the certgen emissions are pinned by the two **whole-library acceptance tests** that dominate suite wall time ([[suite-wall-time-two-tests]], [[certgen-harness-cost]]), and certgen's workloads are the ones where a conversion surprise is expensive. A style pass that has to iterate against those is a different-sized round.

What it would take, if run: the three sites above, plus a re-baseline of the emission-text assertions in `crates/elab/tests/certgen_t0param.rs` and `certgen_tier1.rs` (`gate_gen_conv_in_route(f)(n, VNil)`, `esum_gen_conv(gf0)(VNil)`, `tsel_gen_conv(gf1)(f, VNil)`), and the same guard the datarepr round added to its mutation controls — a perturbed emission must be refused by the kernel, never by the parser, or the control passes on a re-cut pattern rather than on the mutation.

## What it assumes from elsewhere
- **[[idiomatic-spelling-pass]]** owns the style decision itself. Assumed here: only that the idiomatic spelling is the one the surface wants, which that issue settled with the user.
