---
title: Datarepr surface ergonomics: probed pain points and automation candidates
status: open
labels: [design,frontend,ergonomics,compiler]
created: 2026-08-15
updated: 2026-08-15
---



An ergonomics audit of the datarepr surface (2026-08-15, coordinator +
user request), after the v1 arc completed: what is annoying to state, what
could be automated, what takes more to say than it should. Every claim
below was **probed against the built CLI** on scratch files, not read off
the fixtures — which matters, because the first finding is that the
fixtures overstate the pain.

## Finding 0: the fixtures teach a worse language than we have

Every fixture and hand-run spells the fold maximally explicitly:

```heather
Repr_ListTok::fold()(Nat)(Zero)(λ (a0: Tok) => λ (a1: List<Tok>) => λ (b0: Nat) => Succ(b0))(l)
```

Probed: all of that curry-and-annotate is optional today. This checks:

```heather
Repr_ListTok::fold(Nat, Zero, λ t r b => Succ(b), l)
```

— n-ary application of a namespace member without the 0-ary `()`, and
unannotated multi-binder λ in checking position. The explicit style is the
*generator's* (defensible: emissions should not lean on inference), and the
hand-runs copied it because they are emission specs. But docs and any
example a user learns from should use the idiomatic spelling. Cheap,
self-contained pass.

## Genuine gaps, probed

1. **Transfers have no surface syntax at all.** `reprgen` is a Rust API;
   `datarepr N for S := repr::naive()` is the only generator reachable from
   a `.hthr` file. A user cannot write "derive the Impl of `length` at
   `ListTok`" in source. This is the single biggest gap — the entire
   transfer machinery is invisible to the language. Natural spellings to
   design: `impl length for ListTok := derived;` (mirroring the datarepr
   mint form), or a `repr::transfer(length)` payload. Interacts with
   [[generators-in-the-language]] (don't design a syntax that fights the
   eventual meta-layer home) and with [[certifying-generator]] (certgen has
   the same gap; one design should serve both).

2. **`impl` clauses require named top-level declarations.** Probed: an
   inline `λ …` at `refines :=` is refused ("not a shape this round can
   spell"). So every hand override costs three named top-level artifacts
   plus the impl block naming them. The user already asked (§1.2 review
   note, 2026-08-14) for a first-class `impl fn ListTok::length(…) { body }`
   spelling with the refines proof attached. That plus item 1 probably
   collapse into one design: the impl declaration as the *site* where a
   body is given, a proof is attached, or derivation is requested.

3. **The `inv = True` junk hypothesis.** Naive/`True` reprs spell `inv` as
   `Zero = Zero`, so every generated `refines` signature carries
   `h0: (Zero = Zero)` and every consumer passes `refl`. Uniformity of the
   registry statement vs. noise in every signature — the fix could be
   statement specialization when `inv` is definitionally `True`, or a real
   `True` with a canonical inhabitant so at least the spelling stops being
   a pun. Design call, small but visible everywhere.

4. **`fold`/`fold_law` are required clauses but have a canonical default.**
   The clause form already defaults omitted `C_abs`/`C_inv`/`fold_law` to
   `refl` (probed in `written_clauses`), but `R`, `abs`, `inv`, `fold`,
   `mk C` are required. `Bin` defines its fold *through* `abs`
   (`spec_rec ∘ abs`), which makes `fold_law` nearly refl — and that shape
   is available to every repr as a default (`fold := via abs`), since the
   correctness basis "need not be what runs" (design §1.2). With that
   default plus `inv := True` defaulted, a minimal real repr is
   `R`, `abs`, one `mk` per constructor, and only the laws that aren't
   refl. Automation candidate with a clear semantics; also gives the suite
   a fold-not-defined-through-abs control point it currently lacks (the
   recorded control limit at §3.3's as-landed note 5).

5. **Generated names leak into user source.** Hand-written certificates
   must spell `Repr_ListTok::…`, `Impl_ListTok_length::…`,
   `ListTok_spec_rec` — all minted names. [[unnameable-generated-names]]
   owns the marker question, but the *legitimate* access points deserve
   designed spellings too, and today there are two of them
   (`ListTok().mk_Cons(t)` vs `Repr_ListTok::mk_Cons()`), the split forced
   by [[theorem-field-projection-oom]] and
   [[receiver-method-shadows-record-field]] — two workarounds a user has
   to know to hold the fixture style in their head.

6. **Proof-term verbosity in hand overrides.** Every congruence is an
   explicit `j` with a fully-spelled motive, chained by `trans`; the BinC
   hand-runs repeat a five-line recursor spelling a dozen times (the test
   file abbreviates it with a *Rust* helper because the surface theorem
   can't). `let` exists in bodies (probed; bidirectional, good error), but
   there is no local abbreviation usable at proof scale and no
   rewrite/calc facility. [[congruence-by-anti-unification]] covers the
   cong half; the calc-chain half has no owner. This taxes exactly the
   users the cost basis is *for* — hand-override authors.

Minor, recorded: a numeral where a constructor is expected declines at the
image-spine reader ("honest syntactic predicate") — fine as a decline, but
Nat-literals in spec fns are common enough that desugaring numerals to
constructors at spec-side reading is worth a thought when the fragment
next widens.

## Suggested order

Finding 0 is a doc/fixture pass, no design. Items 1+2 are one design
round (the impl-declaration surface), the highest-value. Item 4 is a
small self-contained round with a test-coverage bonus. Items 3 and 5 are
design calls to settle inside whichever round touches them first. Item 6
is meta-layer roadmap pressure, not a datarepr round.

## Log

- 2026-08-15: User verdicts (2026-08-15): finding 0 RATIFIED incl. docs ([[idiomatic-spelling-pass]]); item 1 discussion open — 'derived feels a bit mystical', autoderive-by-default and repr-generator-owned-vs-caller-owned to settle ([[impl-declaration-surface]], the anchor); item 2 RATIFIED, inline expressions regardless + first-class conceptualization (same anchor); item 3 delegated to coordinator recommendation ([[true-prop-trivial-hypotheses]]); item 4 RATIFIED ([[repr-fold-via-abs-default]]); item 5 confirmed wanted ([[repr-access-spellings]]); item 6 confirmed — file wanted-tactic issues ([[calc-equational-chains]], [[proof-scale-abbreviations]]). This issue is now an index over those; the impl-declaration discussion continues on its anchor.
- 2026-08-15: Items 1 and 2 RESOLVED (2026-08-15) by the obligation-records implementation round (docs/obligation-records-design.md; spun off as impl-declaration-surface). Item 1 — transfers have a surface: 'impl length for ListTok := derive();' runs the transfer generator at declaration time and fails with the generator's decline reason verbatim, and the Impl it registers is consumable by a later transfer as an ordinary callee. The spelling is the one this issue guessed at, minus the bare-keyword form: a route is an ordinary application ('derive()', 'via_derived(p)') so it can become an ordinary metafunction when the meta layer can synthesize an argument's expected type. Item 2 — impl clauses take any surface expression: the generated skeleton carries a placeholder that is replaced by the user's AST before elaboration, so an inline lambda, match or let-block body and an inline proof at refines all work, at both impl and datarepr clauses. The three-named-artifacts tax is gone; what remains of it is ASCRIPTION (the surface has no expression ascription production, so a statement you want VISIBLE still costs one named theorem — recorded as the deferral to revisit first if inline proofs get long). The 'impl fn' spelling the §1.2 review note asked for was NOT built and was superseded in discussion: the record framing was ratified in round 2 and the block is the form. Finding 0 (the fixtures teach a worse language than we have) is untouched by this round.
