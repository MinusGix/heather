# CaDiCaL, vendored

The SAT solver behind Heather's certified bit-level decisions
(`crates/sat`, issues/lrat-certified-bitvector-decision.md). Its answers are
untrusted: a refutation comes back as an LRAT proof, which the kernel checks
with `lib/std/tactic/lrat.hthr`, proved sound once. So nothing here is in the
trusted base; a solver bug can cost a failed proof, never a wrong one.

- Upstream: https://github.com/arminbiere/cadical, release `rel-3.0.1`
  (commit c60730422e758ef1cebe7aeddf2dda31c996bf04). MIT, `LICENSE`.
- What is here: `src/` without the two applications (`cadical.cpp`,
  `mobical.cpp`) and the IPASIR wrapper, plus `LICENSE` and `VERSION`.
  Nothing is edited. `crates/sat/build.rs` compiles it with `-DNBUILD`
  (no `configure`, no generated `build.hpp`).
- To update: copy the new release's `src/` over this one the same way,
  update `VERSION` and the commit above, and run `cargo test -p heather-sat`
  through `scripts/test`.
