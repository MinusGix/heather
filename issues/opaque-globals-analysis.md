---
title: Opaque globals: let code analysis see through u^delta, behind the pull API
status: closed
labels: [kernel,delam,metaprogramming,metatheory,design]
created: 2026-08-11
updated: 2026-08-11
---

Blocker (1) of [[generators-in-the-language]]'s 2026-08-02 expressiveness
verdict, now scheduled as its own kernel round. Global references are opaque
to code analysis: elim^Trm has no recursor branch for u^delta/U^delta
(neutral by ch. 07's stuck laws; reduce.rs is_neutral_term), and since the
definitions round made the elaborator emit Psi-references instead of
inlining, real library code is exactly the shape the recursor cannot see
through.

**The interface is pre-cut** ([[fn-reflection-for-analyzers]],
docs/fn-signature-reflection-design.md): `Elaborator::fn_type_code` is the
pull reflection primitive whose *implementation* this round replaces, and
the body-reflection primitive was explicitly left to be named with this
round. lib/ and the analyzer-slot vocabulary must not notice the swap.

**The route fork the design must settle** (recorded across the referencing
issues, not yet argued through): a recursor branch for globals — an
intensional-analysis extension with ch. 07 obligations — versus
unfolding-for-analysis (u^delta unfolds to its definition body before/during
analysis, riding the definitions machinery's layer-indexed transparency).
Check docs/delam 04/06/07 before picking; the ch. 07 stuck laws currently
*depend* on globals being neutral at layer c.

**Customers waiting on it**: mul-via-add cross-function transcription
in-language ([[retire-rust-transcriber]] stage 2 — deleting the Rust walker
is gated here), the ElabCode reflect direction
([[elabcode-abstraction-layer]]), guard/inj-style generators
([[generators-in-the-language]]).

**Coq-formalization discipline**: if the design touches ch. 05/06 shared
notions, that is a shared-notion edit — flag it loudly and design against
the external formalization first.

## Log

- 2026-08-11: Round LANDED (2026-08-11, managed round; docs/opaque-globals-analysis-design.md). The fork is settled AGAINST both kernel routes, from the book: ch. 06's neutral grammar includes elim^Trm/elim^Typ on box'd globals as neutral PRODUCTIONS with the explicit remark that the blocking follows hu2024layered, plus two syntactic-comparison convertibility rules and ch. 07's matching relation cases -- a recursor branch (route A) is a ch. 06+07 shared-notion edit, and identity-opaque anyway (a tm_global branch abstracts over the global exactly as tm_var abstracts over the variable, so it delivers a hole where the callee identity goes); kernel delta at layer c breaks code-does-not-compute and the definitions round's own pins. What landed instead is unfolding-for-analysis AT THE REFLECTION BOUNDARY, zero kernel diff: (1) the body-reflection primitive is named and cut -- Elaborator::fn_body_code(name) -> BodyCode { arity, callees, code }, pull like fn_type_code, marked+boxed code as the reflection contract (a raw body is exactly what an analyzer cannot use), body-less globals decline (proofs opaque, pinned by test); (2) the marker convention gains convention 3, CALLEE MARKERS -- a cross-function call head becomes a closed lambda-chain over Nat ending in a numeral tag, table tag->name returned beside the code; nullary and body-less callees refused at marking; (3) lib/certgen_code.hthr grows PCall/TFn/TPart plus the first real prefix composition (shift/append/qsnoc), all additive, both shells and slot signatures byte-unchanged; walker Ir numbering is its own (0=self, tag verbatim), mapped to names at readback, closure computed downstream from names as always. The customer is served: mul-via-add generates in-language BYTE-IDENTICAL to the frozen Rust v2 path (the neutrality-decline test flipped to this positive; the decline it guarded is re-homed as the no-generated-instance and body-less declines). One fixture correction: MUL's zero arm now spells Zero, not 0, so the byte-identity tests the cross-function call rather than re-pinning seven's literal-spelling divergence. One recorded expectation corrected: fn_type_code's implementation swap is a NO-OP -- the Psi-read already is unfolding-on-request, final, no ch. 07 obligations because the kernel never learns reflection happened. Suite 1450, count unchanged — coordinator correction: the round's "1450 -> 1452" was fast-lane arithmetic, but every new check lands inside existing test fns (the mul positive and the declines extend in_language_transcriber) or inside the library file's own elaboration (mul_transcribes and the decline pins), so the full suite's closing line stays 1450 passed, 0 failed, verified post-commit after the agent's background run died unread.
- 2026-08-11: Coordinator review residue (2026-08-11), latent not live: global_name_at resolves a Psi index to the BASE name (rsplit '::'), and the callee table, readback and closure computation all run on base names — symmetric with the Rust path today, but the day two modules each declare a certgen-reachable 'add', two Psi bindings map to one string and the failure is a wrong resolution, not a decline (caught only downstream by the certificate check refusing, the marker convention's usual safety net). The fix when a customer appears: carry qualified names (or Psi indices) through BodyCode::callees and let readback shorten for display only.
