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
