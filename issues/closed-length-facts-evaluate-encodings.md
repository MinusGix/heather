---
title: Closed facts about a generated program's length evaluate its encodings
status: closed
labels: [elaboration, performance, native]
code: crates/cli/src/native/read_loop.rs @ 357c0afa
created: 2026-09-29
updated: 2026-09-29
---

A certificate's size facts over the 15 KB `wc` program ran past every CPU
rail, although the code equality they build on (`_code_written`) checks in
milliseconds:

- `_code_fits`, `Nat::leb_sound(232 + (spelled).len(), 65536, trivial)` over
  the code spelled with the formatter's `_lit()` trees: over 300 CPU-s for one
  declaration (20+ CPU-minutes for the image facts together).
- A generated chain of `List::len_append` steps over the same closed pieces,
  each `trans(len_append(p, rest), cong_fn(λ n => p.len() + n, …))`: over
  120 CPU-s, where the terms line up syntactically.

Unattributed. The hypothesis is that unification or a whnf probe
([[elaborator-whnf-probes-on-computing-types]]) meets a closed Nat sum and
evaluates it, which unfolds `structured_bytes` and runs the encoder on the
formatter's three copies ([[conversion-cost-at-large-values]] is the closest
closed relative).

Worked around (docs/native-wc-design.md §6.1): `read_fields_code_len` proves
the length once over open parts in the library, and the certificate
instantiates it with the formatter's `_byte_length` lemmas.
`image_facts`'s other path, reading the length off the spelled code, is
still what `--read-loop` and `--print` use: cheap at their sizes, and the
same trap once their tails grow. [[structured-lowering-code-size]] would
shrink the evaluation, not remove it.

Next: `--timings` on a cut certificate with only `_code_split` restored, and
the value-machine counters, to find which step evaluates.

## Log

- 2026-09-29: The attribution tooling this needed has landed ([[native-build-no-partial-diagnostics]]): a build killed at the rail now leaves its `--timings` rows, `<stem>.open.tsv` naming the declaration that was running, and the certificate as `<out>.certificate.unchecked.hthr`, so the bisection by rebuilds is no longer needed to find the slow step.
- 2026-09-29: Attributed and fixed. On the `--fields` build with the old length path restored behind a temporary switch, the live `--timings` sidecar named `_code_fits` as the running declaration. Three gdb stack samples all stood in `ctor_here_expected` → `Elaborator::whnf` → `SemanticOracle::whnf_type` → `reduce::whnf_type_delta`: the `trivial` route's constructor probe of the expected type `IsTrue(leb(232 + len(spelled), 65536))`. Instrumenting the oracle showed the value machine running out of fuel in 0.5 s (2^20 steps; the depth budget was not the limit). Its documented rule was then "the reducer decides on its own", so the substitution reducer re-ran the computation at full fuel, copying the 15 KB code's term at every step: 20+ CPU-minutes to reach the same out-of-fuel verdict. The hypothesis (a whnf probe meeting a closed Nat sum) was right; the missing piece was that the probe's fast path had a fallthrough.

  Fix (crates/elab/src/oracle.rs): out of fuel in the value domain is now the oracle's answer, for types and terms. The reducer shares nothing, so it cannot finish on less fuel than the machine ran out of; `out_of_fuel_in_the_value_domain_is_the_verdict` pins that claim over every fuel from 0 to 63 on a computing type (it also passes on the old code, since both sides agree there; the discriminating evidence is the run). The same old-path build now fails in 89 s of wall time for the whole build, with `_code_fits` at 1.3 s (two probes of 2^20 steps) reporting `out of fuel reducing a type` at its line in the unchecked certificate, and the kernel refusing `_image`. So the spelled length was never going to pass at the default fuel: the hang hid a refusal. The generated `len_append` chain (the second observation) is plausibly the same fallthrough, reached through `trans`'s unification probes; its generator was removed with the workaround, so that is not confirmed.

  The workaround stays: proving the length over open parts is the right shape and costs milliseconds. `--read-loop` and `--print` still evaluate their length and now meet a fast refusal if their tails outgrow the fuel: [[read-loop-code-length-by-evaluation]].
