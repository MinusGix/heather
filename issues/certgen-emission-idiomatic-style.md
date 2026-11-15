---
title: certgen's emissions keep the curried/annotated style the datarepr generators dropped
status: closed
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

## As landed (2026-08-16)

Done as scoped, plus a **fourth site the survey above missed**, and the miss
is the round's one finding worth keeping.

The three named sites went as described: `cert_app` renders one n-ary list
(`{name}(rec, others…, VNil)`), the two fuel wrappers write
`eval(fuel, f_gen_prog(), env, f_gen_body())` — `eval` is declared 2-ary
returning `Val -> Ir -> Res`, so one list reaches the whole spine — and
`emit_instance` writes `λ p q => …`, which let its `pts` parameter go: the
instance emitter no longer needs to know its parameters' *types* at all,
because the `cert` field is in checking position and the record's field type
already says them.

**The fourth site: the tier-1 induction hypothesis** (`render_cert`'s
self-call branch), which spelled `{f}_gen_conv({child})({others})`. It was not
in the survey because the survey read the *emitters*, and this one is inside
the certificate renderer. What makes it worth recording rather than just
fixing: `docs/certgen-tier1-source-types-design.md@4acf2fe` §§1, 5 had been describing
the idiomatic form since the tier-1 round — `tsum_gen_conv(gf1, VNil)`,
`f_gen_conv(gf0, VNil)` — while the emitter wrote `tsum_gen_conv(gf1)(VNil)`.
The doc was simply wrong about the text, and nothing could catch it: the tests
pin the emission against its own literal (`esum_gen_conv(gf0)(VNil)`, green),
never against the doc. The same terms, two spellings, and the *documented* one
was the one that did not exist. It exists now, and §5 carries a note saying so.

Premise verified before any edit, the way the datarepr round verified its own:
a CLI probe that an n-ary list spills past a `fn`'s declared arity into an
arrow-typed result, and past a `theorem`'s declared binder into its Π result.
Both check. No elaborator feature grew.

The mutation-control guard is `support::refuted_by_the_kernel`, and it is
**shared** rather than copied — the six `certgen_*` binaries had byte-identical
private `refuted`s, which is exactly the shape where a guard gets added to one
copy and not the other five. A `ParseError` now fails the control instead of
passing it: `assert_ne!` catches a pattern that matched nothing, this catches a
pattern that matched and cut.

Emission-text assertions re-baselined: the three the issue named, plus
`gate_gen_conv_in_wsum`. Doc examples flipped at
`certgen-tier0-params-design.md` and `certgen-cert-expression-design.md`.
`lib/certgen/ir_v1.hthr`'s own curried `cert: λ (a: Nat) => …` is untouched — hand-written
library, not generator-copied text, the same boundary [[idiomatic-spelling-pass]]
drew.

## What it assumes from elsewhere
- **[[idiomatic-spelling-pass]]** owns the style decision itself. Assumed here: only that the idiomatic spelling is the one the surface wants, which that issue settled with the user.
