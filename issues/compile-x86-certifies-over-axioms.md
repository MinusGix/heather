---
title: compile-x86 certified a program whose proofs rest on an axiom
status: closed
labels: [native,soundness]
area: heather-in-heather
created: 2026-11-16
updated: 2026-11-16
---

`heather compile-x86` printed "N certified program bytes" and published the
certificate for a source function whose body reached an `axiom`, and said
nothing about it. The certificate's theorems (`…_returns`, the lowering and
source agreement) are about the source function, so every axiom the function
reaches is a premise of them: an index bound, a termination measure or a
specification that was assumed and never proved. The bytes carry no check for
any of it; a false bound is an out-of-range read in the binary under a
certificate that reads as unconditional.

Repro (before the fix): `examples/binary-search/search.hthr` with
`midpoint_below` turned from a theorem into an axiom compiles, and neither the
output, the `.s` file nor the certificate mentions an axiom. It is the same
gap `--deny-axioms` closes for `check`; the native driver never read the
provenance record.

Found by reading, while auditing the native path's trusted base (2026-11-16).

## Fixed

After the certificate checks, the driver reads the axioms its declarations
reach (`Elaborator::axiom_violations`, restricted to the certificate module)
and refuses when there are any, naming them; nothing is published and the
unchecked certificate stays for inspection. The library declares no axiom, so
no existing program is affected. Regression test:
`native::a_program_that_rests_on_an_axiom_is_not_certified` over
`crates/cli/tests/fixtures/assumed_mix.hthr`.

A flag that publishes with the axioms listed in the certificate's header would
be the looser reading, if a program is ever wanted that is certified relative
to a stated assumption.
