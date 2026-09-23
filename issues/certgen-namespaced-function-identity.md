---
title: certgen identifies functions by surface name; make it namespace-correct
status: closed
labels: [certgen,modules,design]
created: 2026-09-22
updated: 2026-09-23
---

certgen identifies a function by its **surface declaration name**, and the
2026-09-22 std namespacing refactor ([[type-owned-namespaces]]) moved the
function it is built around, `nat`'s `add`, to `Nat::add(self a, b)`. Nothing
in certgen can currently say "the function `nat::Nat::add`".

## Where the spelling is load-bearing

- `generate_in_language(e, d, …)` (`crates/elab/src/certgen.rs`) passes
  `d.name` to `run_sig_checker`, `sig_peel` and `fn_body_code`, so lookup is by
  spelling, not by global identity.
- Generated identifiers are spliced from the name: `{name}_gen_body`,
  `{name}_gen_arm_zero`, `{name}_gen_conv_in_{caller}`, and so on. For
  `Nat::add` that gives `Nat::add_gen_body`. That is not declarable, or it
  would quietly become a member of `Nat`'s namespace, which is worse.
- `Emission::closure` is a list of name strings (`["add", "viaadd"]`), and
  `LetCall` indices in the fixtures and chain renderer resolve against it.
- The tests fetch the declaration by name: `lib_decl("add")` falls back to
  parsing `nat.hthr`. They also pin `closure == ["add", …]`, and the
  hand-written callers (`viaadd`, `viafield`, `sel3`) call bare `add(a, …)`.
  See `certgen.rs`, `certgen_emissions.rs`, `certgen_nonnat.rs` and
  `certgen_t0param.rs`.

## Current state

`in_language_transcriber` fails with `fn viaadd: unbound name add`. The
heavier certgen emission tests are skipped by the fast lane, but they share
these assumptions and will fail the same way. `lib/certgen_code.hthr` itself was
rewritten to the new names (`d.sub(1).sub(l)`, …) and is not the problem.

## Directions (undecided)

1. **Mangle.** Map `Nat::add` to an identifier-safe stem (`Nat_add`, or a
   module-and-type path) for generated names, and keep name strings in
   `closure`. This is the smallest change, but the spelling-based lookup stays.
2. **Key on global identity.** `closure` holds global identities; generated
   names come from a stable per-global stem; declarations are found by
   resolving the name once, not by comparing `d.name` strings.
3. **Ghost identifiers.** Generator-owned hygienic names that live in no user
   namespace, so an emission can neither collide with nor attach to a type's
   members. This is the most principled; it needs a surface or elaborator
   notion of names that user code can't write.

In every direction the test inputs need the new spelling: `Nat::add(a, …)` or
`a.add(…)` in the callers, and a declaration lookup that understands `Nat::add`.
The reflected IR fixtures (`IR_ADD`, `IR_VIAADD`) should not need to change:
they are shape, not names.

## Log

- 2026-09-23: 2026-09-23: confirmed on master after the receiver-style stdlib merge (875109b8). Five certgen emission tests in the full suite fail this way (`unbound name add`). They are the only remaining red besides the lib_algebra, operators_onto_classes and fmt drift, which were test-side respellings and are fixed. The direction is still undecided.
- 2026-09-23: 2026-09-23: direction 2 chosen (user): key on global identity. Design: docs/certgen-global-identity-design.md (abs identity, declared-name stems with `::`→`__`, collision declines, reference spelling that resolves back). Red targets: certgen, certgen_emissions, certgen_nonnat, certgen_t0param, certgen_tier1.
- 2026-09-23: 2026-09-23: landed (direction 2), per docs/certgen-global-identity-design.md. Functions are keyed on their Ψ index, generated items are named by `Nat__add`-style stems, and the design's §3 was amended. Two scope dependences remain: an emission's reference spellings, and the certificate fold (`cert_body`, resolved by name), are both checked in the elaborator's scope at generation time, so the caller has to elaborate the emission in that same scope. Direction 3 (hygienic names) remains the principled end state.
