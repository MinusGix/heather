---
title: Default fold := via abs in the datarepr clause form
status: closed
labels: [design,compiler,ergonomics]
created: 2026-08-15
updated: 2026-08-15
---



Spun off [[datarepr-surface-ergonomics]] item 4, user-ratified
(2026-08-15). The clause form already defaults omitted `C_abs`/`C_inv`/
`fold_law` to `refl`; `fold` stays required though `Bin` shows the
canonical default by hand — fold *through* `abs` (`spec_rec ∘ abs`),
under which `fold_law` is (nearly) refl. The correctness basis need not
be what runs (design §1.2), so this default is semantically clean.

With `fold := via abs` and `inv := True` defaulted, a minimal real repr
is `R`, `abs`, one `mk` per constructor, and only the non-refl laws.

Bonus the round should collect: a repr whose fold is NOT defined through
`abs` becomes expressible as the deliberate case, giving the suite the
control point §3.3's as-landed note 5 records as missing (the
`refines_inv` transport direction is unobservable when fold is defined
through `abs`).

## Log

- 2026-08-15: Reshaped by the obligation-records design (docs/language/classes/obligation-records-design.md §1.2 FINDING C, §5): this issue and the slot mechanism both want to give an OMITTED clause a meaning, and they disagree. Settled direction there: omission keeps (and gains) the meaning 'take the default', an OPEN obligation is written explicitly as 'field := ?', and a clause that is neither is checked as today — so the two rounds do not collide as long as ordering holds. If the rounds merge, that one sentence is the whole rule; if they do not, the slot round lands '?' first so this round has an unambiguous omission to define. The bonus this issue records (a repr whose fold is NOT through abs, as the missing §3.3 control) is untouched.
- 2026-08-15: UNBLOCKED (2026-08-15): the obligation-records implementation round landed the clause rule this issue was waiting on, and landed it as one sentence — omitted takes the default, '?' demands and reports, anything else is checked as today (docs/language/classes/obligation-records-design.md §1.2, §5). '?' is a REPORTING HOLE, not deferral: it fails the declaration at its own span printing the synthesized statement, so there is no open state for an omitted-clause default to be confused with, and FINDING C is dissolved rather than adjudicated. This round can now proceed independently: it defines what OMITTED produces (fold := via abs, inv := True) and touches nothing the '?' path does; the clause-reading code it wants is crates/elab/src/datarepr.rs written_clauses, which now splices ASTs and records provenance per clause but is otherwise the same shape. The bonus control (a repr whose fold is NOT through abs) is still uncollected.
- 2026-08-15: LANDED (2026-08-15), and the round's premise needed one correction. What omission now means: 'inv' defaults to True (the naive spelling 'λ (r: R) => (Zero = Zero)'; a prelude True stays [[prelude-option-and-friends]]') and 'fold' defaults to the fold THROUGH abs, so a repr's required clauses are R, abs and one mk per constructor — the minimal real repr the issue predicted, plus the laws that are not refl (at Bin that is Succ_abs, and only it). Omitting 'fold' used to be an error, so docs/native/datarepr-design.md §1.4 gains an as-landed note; the '?' path is untouched at both clauses ('fold := ?' is still the data-field refusal, 'fold_law := ?' still prints the anchor, and both are now tests).

  THE FINDING: the defaulted fold_law is NOT refl, and cannot be. Reading Bin's hand-written anchor schematically shows what fold-through-abs needs that the Repr record does not state — a map S -> R, because the repr-side step holds its child at the CARRIER while the spec recursor hands one at S. Bin supplies 'bin_of_nat' there, and the general form of it is no new machinery: it is the spec recursor over the constructor IMAGES. So the default emits that embedding, and because 'abs ∘ emb = id' is a theorem and not a conversion, it emits the anchor law as an induction. Four artifacts, all generated from the repr's own laws: N_emb (spec_rec over the images); N_emb_inv : (x: S) -> inv(emb x), one closure law per arm applied to the IHs; N_emb_abs : (x: S) -> abs(emb x) = x, one commutation law per arm — that is where N_emb_inv is spent — then a j chain over the recursive positions with the IH; and N_fold_via_abs(B, s⃗, x) : spec_rec(B, s⃗ ∘ (abs ∘ emb), x) = spec_rec(B, s⃗, x), the recursor-level equation fold_law reduces to at x := abs(r), each arm rewriting abs(emb(a)) to a and each recursive call by the IH, one explicit j per position, trans-chained. fold_law itself is then 'λ B s⃗ r h => N_fold_via_abs(B, s⃗, abs(r))'. The sharper statement of what the default is: AT A REPR WHOSE IMAGES ARE CERTIFIED, THE FOLD ANCHOR IS DERIVABLE RATHER THAN AN INDEPENDENT OBLIGATION. One consequence for the test suite, recorded because it looks like a gap: no negative control can exhibit a repr whose image laws hold and whose defaulted fold_law fails, so the controls aim at the laws instead (an omitted law that is not refl is still owed; a wrong abs is still refused).

  The naive repr keeps the spec recursor directly rather than taking the default — at abs = id the embedding would be a round trip to reach what is already at hand — so every emission the generators have ever produced is byte-identical.

  Provenance: 'heather obligations' now lists the two data clauses that HAVE a default, 'inv' and 'fold', as defaulted/supplied with the type they are checked against as the statement column. They are still not obligations in §1.1's sense (a '?' at either is refused as a data field); the row exists to answer the question the defaults created — did this repr take the default here?

  THE BONUS CONTROL, collected: 'UnC' (crates/elab/tests/support/mod.rs) is a repr of Nat on a unary carrier whose fold recurses on the CARRIER, under a canonical-form inv. Both halves are load-bearing, which the issue did not anticipate: at inv = True the motive refines_inv transports is constant, so the direction is unobservable however the fold is defined. At UnC the two sides of fold_law are two different stuck terms and deleting the 'sym' out of the generated refines_inv is refused — the control design §3.3's as-landed note 5 records as missing. Its complement is a test too (the same mutation still checks at BinC), so the note cannot be 'fixed' by accident. UnC also transfers double_spec end to end, which is the first transfer over a repr the generator cannot see through.

  MILESTONE: 'impl double_spec for BinMin := derive()' — a transfer over a repr that wrote no fold and no inv — checks and computes (doubling the representation of two yields four). The generator consumes Repr_BinMin::fold()/fold_law() without knowing that neither was written.

  Tests: +12 (datarepr.rs +5 incl. 3 negative controls and an axes test at an open element type and a two-recursive-children arm; obligation_records.rs +3; reprgen.rs +4). Unchanged by design: Bin's hand-written fold, every naive emission, the CLI listing's shape.

  Interaction left alone: a defaulted inv still puts an 'h0: (Zero = Zero)' binder in every law statement (§1.4 note 5's friction, [[true-prop-trivial-hypotheses]]) — the default makes it silent to WRITE, not absent. The four new generated globals are minted top-level names like N_spec_rec and inherit [[unnameable-generated-names]]'s question, nothing new.
