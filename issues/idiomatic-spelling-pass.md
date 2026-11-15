---
title: Fixtures and docs use the idiomatic surface, not the generator's explicit style
status: closed
labels: [docs,testing,ergonomics]
created: 2026-08-15
updated: 2026-08-16
---



Spun off [[datarepr-surface-ergonomics]] finding 0, user-ratified
(2026-08-15): the idiomatic spelling —

```heather
Repr_ListTok::fold(Nat, Zero, λ t r b => Succ(b), l)
```

— already checks (n-ary application of a namespace member, unannotated
multi-binder λ in checking position), reads far better than the curried
fully-annotated form the fixtures copy from the generator, and the sugar
"isn't that intricate to unfold into the underlying case" (user). Pass
over the datarepr/reprgen fixtures, hand-runs, and the design doc's
examples.

Open sub-question for the pass: whether **generator emissions** switch
too. The user's rationale (desugaring is simple and reliable) leans yes;
the cost is a deliberate byte-stability flip across every pinned emission,
so it should be its own commit with every changed emission named. The
hand-runs are emission specs, so they follow whichever way the emissions
go — fixtures that are *not* emission specs switch regardless.

## Log

- 2026-08-16: Unblocked-ish (2026-08-16, the repr-access-spellings round): generator EMISSION bytes are unchanged — every generator still writes Repr_N::abs(), N_spec_rec, Impl_R_f::body() — but the surface now has one designed spelling (N::abs, N::spec_rec, Impl(f, N)::body) that resolves to those declarations through an alias, and the minted forms are refused in user source. Two consequences for this issue's pass. First, the fixture half is already done for datarepr/reprgen/obligation-records/record-projection tests: every hand-written certificate and fixture in them now spells the designed form; what still spells minted names is exactly the assertions ABOUT emission text and the hand-forced emissions, which are generated source and should stay. Second, flipping the emissions themselves to the designed spelling is now a pure style choice rather than a compatibility event — the alias means both spellings resolve inside generated mode — so this issue can do it whenever it runs, at the cost of re-baselining the emission-text assertions.
- 2026-08-16: Landed, and the issue closes. The emission sub-question was resolved YES by the user (2026-08-16) — the artifacts are re-parsed surface source, so an idiomatic emission exercises the sugar (n-ary application, unannotated multi-binder λ in checking position) on every generator run, which is a standing regression net no test has to be written for. Emission-style choreography was waived; the changed emissions are named below.

**Verified, not assumed.** The issue's premise is that the sugar already checks, so the round opened with a probe against the built CLI rather than with an edit: `ListTok::fold(Nat, Zero, λ t r b => Succ(b), l)` at a naive repr, the anchor law's statement with the adapted algebra as one unannotated λ inside an equation, and an unannotated multi-binder λ as a declaration body at a curried Π. All three check. **No sugar gap was found anywhere in the pass**, so nothing was left in the explicit spelling and no gap issue was filed.

**The emitters: four edits, all of them local.** The generators already funnelled every application and every λ through two helpers in `crates/elab/src/datarepr.rs`, which is why this is a style pass and not a rewrite.

- `appc` renders `f(a, b)` instead of `f(a)(b)`, and **absorbs** a `()` already sitting on the head: `Repr_N::fold()` + args is `Repr_N::fold(B, s0, r)`, one argument list spilled across the whole curried Π spine. A head with nothing to apply keeps its shape, so the record's field values (`abs: Repr_N::abs()`) and the declarations themselves are untouched.
- `lams` renders one `λ x y z => body` instead of a chain of annotated binders. Every λ these generators emit stands in a checking position — a declaration body at its declared type, or an argument of a call whose head's signature is known — so the domains are determined; the callers still compute the binder types, because they are what the surrounding Π is built from, they are simply not spelled twice.
- Two sites in `reprgen.rs` (`inv_proof`, `abs_proof`) applied a law to its arguments and *then* to its `inv` proofs, one `appc` at a time. Restructured to build one argument list in the law's own binder order, so the emitted citation is fully n-ary rather than `C_inv(a, b)(h)`.
- The three literal clause defaults: an omitted `inv` is `λ r => True`, and `repr::naive()`'s `abs`/`inv` are `λ r => r` / `λ r => True`.

**Every changed emission, by artifact.** datarepr, per repr `N`: `N_spec_rec` (arm bodies); the `Repr_N` record's `C_abs`, `C_inv` and `fold_law` field types; `Repr_N::abs()` and `Repr_N::inv()` bodies where the clause is defaulted or naive; `Repr_N::mk_C()` bodies at `repr::naive()`; each `Repr_N::C_abs()` / `C_inv()` theorem, statement *and* defaulted proof; `Repr_N::fold()`'s statement and body on both routes (naive and via-abs); `Repr_N::fold_law()`'s statement and proof; and the via-abs default's four artifacts `N_emb`, `N_emb_inv`, `N_emb_abs`, `N_fold_via_abs`. The assembled `fn N() -> Repr_N` is byte-identical — its fields are 0-ary calls with nothing to apply. reprgen, per transfer: `f_derived`, `f_is_rec`, `f_inv_pres`, `f_abs_alg`, `f_derived_refines`, `f_derived_inv`; the `impl f for R` block is byte-identical. Downstream of the same strings, the **obligations listing** and the `?` reporting hole print the new style, which is where the change is most visible to a person — the naive `ListTok`'s anchor row now reads `ListTok::fold(B, s0, λ a0 a1 b0 => s1(a0, ListTok::abs(a1), b0), r) = ListTok::spec_rec(B, s0, s1, ListTok::abs(r))`.

**Naming did not move, in either direction.** `docs/native/repr-access-spellings-design.md` §2's split still holds byte for byte: the emission spells `Repr_N::abs`, `N_spec_rec`, `Impl_R_f::body`, the surface spells `N::abs`, and the alias is untouched. The flip needed no alias change and the alias needed no style — recorded as an amendment to that document's §8, which had forecast this round and claimed emission bytes were unchanged.

**Byte-stability discipline.** Every re-baselined assertion was a `::foo()` → `::foo(` or a λ-shape change and nothing else; no artifact appeared, disappeared, or changed order, and no name changed. That is pinned rather than asserted: `the_idiomatic_and_the_explicit_spellings_are_the_same_term` (`crates/elab/tests/datarepr.rs`) proves by `refl` that the two spellings of one representative fold — and of one representative *law*, where the term is a proof rather than a value — are the same term, at a neutral carrier value and again at a literal.

**The mutation controls, re-verified and then hardened.** Five perturbed-emission controls in `reprgen.rs` cut their mutation out of generated text by string match, so a style flip re-cuts every pattern; three needed new ones (`a_perturbed_derived_body_is_refused_by_its_own_refines`, `a_callee_step_closed_by_the_wrong_callees_refines_is_refused`, `a_callees_inv_hypothesis_paid_by_the_wrong_lemma_is_refused`), and `a_perturbed_base_case_is_refused` needed a genuinely different one — `(Zero)(` no longer exists, and `::fold(Nat, Zero,` is sharper than its predecessor, which had also hit the `fold_law` citation beside the body. The `assert_ne!(bad, text, "the mutation must apply")` guard caught every one of them, which is exactly the failure it was written for. The hardening is the round's one addition beyond style: `refused` now **distinguishes a parse error from a refusal**, because the failure mode a re-cut pattern creates is text that no longer parses and a control that is green for a reason unrelated to the property it names. Both halves of §3.3 note 5's paired control (the `sym` deletion refused at `UnC`, the same mutation still checking at `BinC`) survive the flip unchanged.

**What else switched.** Non-emission fixtures: `crates/elab/tests/support/mod.rs` (`bin_base`, `BIN_CANON`, `BIN_MIN`, `UNARY_CANON`, `BIN_ADD` — the hand-written `Bin`/`Un` carriers and their lemmas), the inline `impl` clauses and `datarepr` clauses in `obligation_records.rs`, the hand-written certificates in `repr_access.rs` and `record_projection_size.rs` (including its hand-forced `Rp` record, which is an emission spec and follows the emissions), `crates/cli/tests/fixtures/obligations.hthr`. Hand-runs that *are* emission specs — the three in `reprgen.rs` that write out what the generator emits, and the four forced emissions the decline controls feed back in — followed the emissions, which is what makes them still hand-runs of the real thing. Docs: `docs/native/datarepr-design.md` (the `impl` sketch, the trivial-`inv` clause shape, the callee-spelling note, plus a §1.4 as-landed amendment recording the flip), `docs/language/classes/obligation-records-design.md` (its two printed-statement examples, which were stale on *naming* since the access round and are now correct on both counts), `docs/native/repr-access-spellings-design.md` §7–§8.

**`lib/` was not touched, and that is a finding rather than an omission.** No `datarepr`, `impl` or generated artifact exists anywhere under `lib/`. Its ~150 curried applications are declarations that genuinely *are* curried (`fn leb(n: Nat) -> (m: Nat) -> Bool`), not text copied from a generator, so they are outside this issue's premise entirely.

**Left open, with an owner.** certgen emits surface source too and keeps the older style at three sites (`cert_app`'s `{name}({rec_arg})({others})`, the fuel wrappers' `eval(f, p)(e, b)`, `emit_instance`'s annotated λ chain). Deliberately not flipped here: the charter names datarepr/reprgen, and those emissions are pinned by the two whole-library acceptance tests that dominate suite wall time. Filed as [[certgen-emission-idiomatic-style]] with the three sites, the assertions that would re-baseline, and the parse-error guard above named as the thing to carry over.

Tests: +1 (`the_idiomatic_and_the_explicit_spellings_are_the_same_term`); ~20 assertions re-baselined across `datarepr.rs`, `reprgen.rs`, `obligation_records.rs`, `repr_access.rs` and `crates/cli/tests/check.rs`. Suite 1634 -> 1635 on a plain full `scripts/test`; `scripts/bench --check`: 18 comparisons within thresholds.
