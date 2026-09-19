---
title: Both calculator showcases use none of the proof ergonomics the language grew for exactly their shapes
status: open
labels: [showcase,ergonomics,proofs,syntax,stdlib]
created: 2026-09-19
updated: 2026-09-19
---

The two calculator showcases are the language's shop window, and they are
written in the language of a month ago. Two features landed specifically for the
shapes those files are full of, and neither file uses them once.

| feature | landed for | uses in `lib/` | uses in either showcase | shapes in `calc_text` wanting it |
|---|---|---|---|---|
| `⟨p, q⟩` anonymous constructors ([[conjunction-introduction-syntax]], closed 2026-08-30; `docs/logic-connectives-design.md` §4.1) | nested conjunction certificates | 17 in `lib/function_ir.hthr` | **0** | 20 `And(` calls, nested three deep |
| `calc { }` equational chains ([[calc-equational-chains]], closed 2026-08-18) | `trans`/`j` towers with spelled motives | `lib/std/nat.hthr` | **0** | 24 `trans(`, 11 `j(` |

`sum_grammar`, `product_grammar` and `paren_grammar` are the worst of it: each
builds its `span` field as a `trans(…, cong_spell(…, trans(…, cong_cons(…,
cong_append_r(…)))))` tower, and each `valid` field as `And(And(And(…), …),
And(…, …))`. `calc`'s own closing entry names hand-override certificates as the
users its case was made for; these are those, and they were never converted.

Worth doing for three reasons, in order: the showcase is what a reader judges the
language by; a feature with no use outside the file it was born in is not
evidence that it works; and the conversion is the cheapest way to find out what
`calc` and `⟨⟩` still cannot express — the kind of finding a real client produces
and no amount of reasoning does, which is how every language feature on this
tracker got its ranking.

Scope note. The `⟨⟩` and `calc` conversions are pure surface and carry no term
growth. Do **not** bundle them with the other readability change these files want
— turning the `RunSpec`/`OpRun` ∧ towers into named records
([[showcase-spec-relations-as-records]]) — because that one adds Σ layers
to a file that already needs more than 8 GiB cold and cannot be cached
([[elaborator-canonical-type-spelling]]). Separate rounds, so a cold-check
regression has one candidate cause.

Two taxes on any round here, both measured: this module's image is 483 M nodes
against a 256 M budget, so it is never stored and `--only` has nothing to replay
([[check-only-no-stored-image]]) — a recheck is ~95 s however small the edit, so
batch the edits. And `scripts/perf ab` cannot measure a `.hthr` change at all
today: it compares two *binaries* and would refuse this as one binary against
itself ([[perf-ab-source-patch]]).

## Log

- 2026-09-19: Two more repetitions in `docs/showcase/calc_text.hthr`, noticed while reading it
  for [[record-type-partial-application]]. Both are pure surface, both belong in
  this issue's batch (the ~95 s tax is per recheck, not per edit), and **neither
  needs a language feature that does not exist**:

  - The `recur:` parameter type is spelled out in full four times — lines 324,
    336, 347 and 372 — as `(next: Cursor<Char>(source)) -> nat::Lt(list_len(rest(
    source, next)), list_len(rest(source, begin))) -> Checked(k, source, next)`,
    differing only in the tier `k`. A plain `fn Recur(level: Nat, source, begin)
    -> Type { … }` should collapse all four: `docs/types-as-expressions.md`
    already makes a `fn` returning `Type` first class, and a parameter whose type
    is a call to one is the shape `RefinesOn` uses in `lib/ir_v1.hthr`.
  - The three `checked_*` fixpoints annotate their λ binders — `λ (next:
    Cursor<Char>(source)) (smaller: nat::Lt(…)) => …` — against an expected Π,
    where `docs/surface-function-types.md` §5.2 says the annotation is a
    readability aid and the expected domain is what the binder is pushed with. So
    `λ next smaller => …` should check, and three of the file's longest lines go.

  If the first one holds it **reprices [[type-declaration-form]]**, which is why
  it is worth doing here rather than there: that issue's own log says the
  load-bearing use of a `type` form is exactly this seven-fold repetition, and if
  a `fn … -> Type` alias already collapses it then `type` is left with the
  justification the issue ranks lowest — a highlighting and reading cue. Both
  bullets are predictions from reading, not findings; one recheck settles them.
- 2026-09-19: **`⟨⟩` landed everywhere, `calc` landed in three of six places, and both of the
  predictions in the entry above are settled — one true, one false.** Two clean
  rechecks of the file, and `calc_parser`'s six `And(` towers went on the same
  pass. The converted image is 483,281,749 nodes against 483,322,044 before, so
  the conversion is term-neutral as the scope note assumed.

  What landed: all 9 `And(` towers in `calc_text` and all 6 in `calc_parser` as
  `⟨⟩`, including `⟨⟨⟨l.at_level, l.valid⟩, trail_spaces⟩, ⟨r.at_level, r.valid⟩⟩`
  — the shape the table counted. A `fn Recur(level, source, begin) -> Type`
  collapsing the four spelled-out `recur:` parameter types. `calc` chains in
  `checked_run`, `operator` and `finish_text`.

  **Finding 1 — the table's "worst of it" is wrong, and finding that out is what
  the conversion was for.** `sum_grammar`, `product_grammar` and `paren_grammar`
  are the three places a `calc` chain does *not* pay, and their span towers are
  unchanged. The reason is `Derivation::cong_spell(x, y, p)`, which takes both
  endpoints **explicitly** — the tower already writes every intermediate a chain
  would write, and the chain spelling restates each one a second time as the
  step's endpoint. Converted, `sum_grammar`'s span grows from 3 lines to 11 and
  says nothing new. `calc` pays against a tower whose intermediates are
  *implicit*, which is what `checked_run`, `operator` and `finish_text` have (3-
  and 4-leaf `trans` spines through `head.suffix` / `initial_rest`). Leaf count
  was the wrong proxy; whether the tower's lemmas already name their endpoints is
  the right one, and that is how the next file should be ranked.

  **Finding 2 — terse `cong` in a calc step is refused at 4 of the 15 sites this
  file offers it, and the boundary is wider than
  `docs/calc-equational-chains-design.md` §3 records.** §3 has it as one
  cross-type constructor case. Measured:

  | site | context | what it said |
  |---|---|---|
  | `checked_run` | `Cons(·, rest(…))` at `Char` | `sum type` against `El` |
  | `sum_grammar`, `product_grammar` | `Plus(·, …)` / `Times(·, …)` at `Expr` | `True` against `El`, under `constructor value ▸ inr ▸ inl ▸ pair ▸ pair` |
  | `paren_grammar`, `finish_text` | `spell(d, ·)` | the endpoints print *identically* to the differing position and it still declines |

  The last row is the one worth acting on and is filed as
  [[lgg-error-hides-the-implicit]]: `lgg.rs` matches the witness pair by
  structural `==` with no conversion (deliberate —
  [[congruence-by-anti-unification]] §3 decision 2), but the error renders only
  the surface, so it reads as a contradiction. The difference is in an implicit
  type argument the renderer drops, and a reader cannot act on the message.

  Consequence for the `yields` fields: they keep their nested `j` with
  hand-written motives. A chain there was the most attractive conversion in the
  file — two `cong(l.yields)` / `cong(r.yields)` steps against two motives that
  each restate `Plus(l.derivation.meaning(), r.derivation.meaning())` — and it is
  exactly what the elaborator refuses.

  **Finding 3 — the second prediction above is false, with a reason.**
  `λ next smaller => checked_expr(source, next) decreasing tail` does **not**
  check: *"this recursive call's obligation names a binder the generator cannot
  type, and a mutual group cannot fall back to stating it at the call
  (`docs/mutual-recursion-design.md` §4): annotate the binder, or lift the call
  out of the pattern that introduces it."* `docs/surface-function-types.md` §5.2
  is right about the *elaborator* — the expected Π does push the domain — but the
  `decreases` obligation generator reads the binder's *written* type, and a
  mutual group has no second chance to state it. The three long lines stay, and
  the annotation is load-bearing rather than decorative. §5.2 currently reads as
  unconditional and has been given the caveat.

  **Finding 4 — the first prediction holds, so [[type-declaration-form]] is
  repriced** (logged there). A `fn … -> Type` alias already collapses the
  repetition that issue calls its load-bearing use, so `type` is left with the
  justification it ranks lowest.

  Two notes for whoever takes round 2. `docs/showcase/calc_text.hthr` is in **no
  test** — `crates/elab/tests/showcase_calculator.rs` includes `calc_parser` and
  not it — so it is verified only by a hand `heather check`, which on this desktop
  is 4:24 cold rather than the ~95 s quoted in the body above. And nothing in
  `calc_text` now wants `⟨⟩` or `calc` and does not have it; what the file still
  wants is [[showcase-spec-relations-as-records]], in its own round.
