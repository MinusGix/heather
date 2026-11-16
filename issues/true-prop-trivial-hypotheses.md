---
title: A real True, and what pays a definitionally-trivial hypothesis
status: closed
labels: [design,stdlib,frontend,ergonomics]
created: 2026-08-15
updated: 2026-08-16
---



Spun off [[datarepr-surface-ergonomics]] item 3 (2026-08-15). Naive/
trivial-`inv` reprs spell `inv` as `Zero = Zero`, so every generated
`refines` signature carries `h0: (Zero = Zero)` and every consumer passes
`refl`. Two separable halves:

1. **A real `True`** with a canonical inhabitant, so the spelling stops
   being a pun. Small, stdlib-shaped; relates to
   [[default-inhabited-nonempty]]'s ladder.
2. **Who pays a definitionally-trivial hypothesis.** Coordinator's
   recommendation (pending user verdict): keep the registry statement
   UNIFORM — `refines` always takes the `inv` hypotheses — because every
   consumer of the registry (reprgen's callee steps, the certgen
   composition, future dispatch) then handles one shape, and statement
   specialization would put a branch in every consumer to remove an
   argument that generators already pay invisibly. The human-facing noise
   is better addressed by auto-discharge (elaborator fills a hypothesis
   whose type is definitionally `True` / has a registered canonical
   inhabitant) as a general ergonomic feature, not a datarepr special
   case.

## Log

- 2026-08-15: User ratified both halves (2026-08-15): a real True is valuable; general auto-discharge is wanted as a feature in its own right. The recommendation stands as the plan: uniform registry statement, True now, auto-discharge as a general elaborator feature later.
- 2026-08-16: User verdicts (2026-08-16), settling both halves' mechanisms. Half 1: True := Unit — the kernel already has Unit^l with eta-as-proof-irrelevance (crates/kernel/src/conv.rs ~1225, every term of Unit type convertible), so a prelude True over kernel Unit gets judgmental uniqueness of the inhabitant with no sort question at all; the SProp-vs-Prop dilemma dissolves rather than being decided (survey: Coq's separate sTrue stayed siloed behind a boxing boundary; Lean made all of Prop strict; Agda's idiomatic ⊤ is the eta-record trick — Heather is in Agda's position with the eta rule already in the kernel). One dressing want: True should PRINT as True, not as its Unit spelling. Half 2: auto-discharge is NOT resolver-based — the licensing property is per-binder intent, not per-type inhabitedness (Inhabited(Nat) says nothing about whether omitting a Nat argument is meaningful), and a search per omitted position has real cost. Mechanism instead: DEFAULT ARGUMENT VALUES declared at the binder (h0: inv-statement := True::intro) — the binder stays in the signature so the ratified uniform-statement shape survives, generators keep passing explicitly, omission is substitution not resolution. User notes the general tool is wanted anyway, including defaults that run a tactic search over the surrounding context. The mini-round is now: prelude True/trivial over kernel Unit + printing dress-up, flip the defaulted inv from Zero = Zero to True, update emissions as they fall (user: no need to choreograph emission flips — actively iterating). Defaults-at-binders is its own feature, natural home near [[named-arguments]].
- 2026-08-16: HALF 1 LANDED (2026-08-16); half 2 is re-homed at [[named-arguments]] and this issue closes.

WHAT `True` IS. The kernel's `Unit^0` claimed as a surface type name in `lower_named` (crates/elab/src/inductive.rs), not a declaration and not a library file. Level 0 unconditionally, like `Fin`: the surface spells one `True`, and the positions that want it — a `datarepr`'s `inv`, which is `(r: R) -> Type` — are level-0 positions, so there is no level to write and none to recover. In EXPRESSION position it is the code `⌜Unit^0⌝` for free: `expr_as_ty` -> `elab_ty` -> `code_of` already had a `Unit` arm, so `λ (r: R) => True` needed no new machinery at all.

THE INHABITANT is `trivial`, a bare name, NOT the log's example `True::intro`. Two reasons, both from the codebase rather than from taste: bare is what this surface already does for every inhabitant of a kernel type with no declaration (`Zero`, `Succ`, `refl`, `FZ`/`FS`), and `A::b` is ONE LEXER TOKEN whose owner is a module or an applied obligation owner (`Impl(add, BinNat)::refines`) — so `True::intro` would resolve as the module `True`, i.e. `::` would be lying about what `True` is. It checks at any `Unit^l` (level read off the expected type) and, unlike `refl` and `FZ`, it also INFERS, at `Unit^0`.

RESIDENCY, logged on [[prelude-option-and-friends]] as that issue's line: not `lib/std`, not `crates/elab/src/prelude.hthr`. Forced, not chosen — prelude.hthr is surface source and the surface has no spelling for kernel `Unit`, so a prelude-source `True` was not writable; and an `inductive True { intro }` in lib/std would throw away the entire point, which is η-as-proof-irrelevance giving JUDGMENTAL uniqueness of the inhabitant. Always in scope for the same reason `Nat` is.

SHADOWING follows the `FZ` rule in both namespaces, and all three cases are tests: a declared `inductive True` wins in type position, a local or global `trivial` wins in expression position, and `Bool`'s `True` CONSTRUCTOR is untouched because a constructor is not a type name — the proposition and the constructor coexist in one file.

PRINTING is at the display boundary, nothing stored: `dress_true` (crates/elab/src/lib.rs) rewrites the kernel's `Unit 0` spelling to `True` inside `display_type`'s output, which is the same string-level boundary `display_paths` de-mangles minted names at. Unambiguous because the kernel prints `Unit {level}` and a level renders as a numeral with no leading zero. Its customers are the goal listing (statement AND context entries) and the checking-position mismatch message. FINDING: `heather obligations` and `?` needed nothing — their statements are synthesized SOURCE TEXT and never render a kernel type, so they print `True` because the clause says `True`. The dress-up is only for the paths where a kernel `Type` reaches a human.

THE INV FLIP. Both producers now emit `λ (r: R) => True` — `written_clauses`'s omission default and `repr::naive`. Generated `refines`/law signatures therefore bind `h0: True` and consumers pass `trivial`; the registry statement is unchanged in SHAPE (the binder is still there), which is the ratified half. One real consequence: an omitted closure law `C_inv` can no longer be `refl`, so it is `trivial` — decided by a new `Clauses::inv_trivial`, true when `inv` was omitted and when it was written out as `λ (r: R) => True`. Read off the clause's AST BEFORE splicing: the first attempt asked the clause TEXT and failed, because an inline clause reaches `Clauses` as a splice placeholder and its text is gone by then. Deliberately NOT recognized: an `inv` that is definitionally `True` behind a NAME (`inv := bin_inv`) keeps `refl` — exactly what every `inv` got before — and the writer supplies the closure law; the general answer is defaults-at-binders, i.e. half 2.

NEGATIVE CONTROLS, all pinned: `refl` at a defaulted `inv` is refused (`refl` needs an `=` expected type — the ordinary diagnostic, no `True`-specific case), `trivial` at an equation is refused naming `True`, and a repr whose `inv` is WRITTEN (`BinNat`, `BinC`, `UnC`) is untouched in both directions. Proof irrelevance is pinned positively: `p = trivial` and `p = q` at `True` both close by `refl`, and so does the generated law's own value against `trivial`.

FINDING, filed as [[datarepr-law-clause-inv-binders]] (docs/native/datarepr-design.md §1.4 note 5, now standalone): a law's hypothesis is the repr's OWN `inv`, and two trivially-inhabited `inv`s are not convertible with each other. `BinNat` and `BinMin` could share one `bin_succ_abs_law` while both were `Zero = Zero`; they no longer can, and the fixture carries the same theorem twice differing only in a binder neither body mentions. Note 5's own deferred fix (apply a clause to the binders the statement quantifies over) is what would fix it — defaults-at-binders would not, since that fills an argument at a CALL and this fills a binder at a DECLARATION.

Emissions that changed, all and only at reprs whose `inv` is defaulted (`ListTok`, `StkTok`/`TreeR`, `BinMin`, every `repr::naive()`): `Repr_N::inv()`'s body, every statement that mentions it (the `C_abs`/`C_inv` laws, `fold_law`, `Impl_R_f::refines` and `refines_inv`), and the `C_inv` default proofs. Byte-identical at `BinNat`, `BinC` and `UnC`.

Tests +32 (1602 -> 1634): crates/elab/tests/true_prop.rs is new (11 — the surface, both positions, an open type parameter, printing at the goal listing and at a context entry, and five controls), datarepr.rs +4 for the flip and its controls, and the h0 binders of the datarepr/reprgen/obligation-records/CLI fixtures move to `True` where the repr's `inv` is defaulted. Full `scripts/test`: 1634 passed, 0 failed. `scripts/bench --check`: 18 comparisons within thresholds. Docs: datarepr-design.md §1.4 notes 5 and 6 and the as-landed clause-defaults bullet.
- 2026-08-16: Closing (2026-08-16). Half 1 is landed above and nothing remains here. Half 2 — who pays a definitionally-trivial hypothesis — is not deferred but RE-HOMED: the mechanism is per-binder DEFAULT ARGUMENT VALUES (`h0: inv-statement := trivial`), decided in this issue's 2026-08-16 verdict and owned by [[named-arguments]]; it is not a resolver and not an `Inhabited` search, so nothing about it belongs to a `True` issue. The one piece of residue this round produced has its own owner too: [[datarepr-law-clause-inv-binders]].
