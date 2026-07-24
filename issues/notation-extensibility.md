---
title: "Notation: how open, and open along which axis"
status: open
labels: [frontend, syntax, design]
created: 2026-07-24
updated: 2026-07-24
---

[[surface-syntax]] states the position as "a **fixed grammar** of common
patterns and special symbols … parsed context-free; **no user parser
extensions, ever**", with decorated operators (`+_Z`, `⟦R⟧_s`) and a curated
unicode table. The open question recorded there — "which decoration
positions are in the fixed set" — is the small version of a larger one the
user has flagged uncertainty about: is the Lean/Coq notation-DSL route
actually as bad as the anti-goal assumes, and is a rich fixed grammar really
enough for a system that targets mathematics?

## The distinction that matters

"Extensible notation" bundles two independent axes, and they have very
different costs:

1. **Lexicon openness** — may users introduce new *symbols* (operators,
   bracket pairs) and give them meaning? Cheap, predictable, and where
   nearly all the notational value lives.
2. **Shape openness** — may users introduce new *grammatical forms*: new
   binders, ternaries, new syntactic categories, literal syntaxes? This is
   the expensive one.

Lean's arcaneness is almost entirely axis 2, and the root cost is not
aesthetic: an extensible grammar makes **parsing depend on the elaboration
environment**. What you can parse depends on what you imported and what is
`open`. That single fact is what forces macro hygiene machinery, wrecks
error recovery (failures surface inside expansion), complicates incremental
parsing and tooling, and produces the notation-collision and
precedence-interaction pain that Coq is the cautionary tale for. Heather
currently gets `parse_file: &str -> File` as a total, context-free function
and treats the AST as the stable contract; axis 2 is what would take that
away.

So the pessimism is warranted, but for a sharper reason than "arcane", and
it does not automatically extend to axis 1.

## Precedents worth copying from, roughly in order of relevance

- **Agda's mixfix** — users declare names with holes (`_+_`,
  `if_then_else_`, `_[_]=_`) plus fixity. The lexicon is wide open; the
  *shapes* are limited to mixfix. This carries essentially all of Agda's
  mathematical notation with no macro language at all. Tellingly, Agda found
  exactly **one** extension necessary beyond it: a declarative `syntax`
  form for **binder** notation (`syntax Σ A (λ x → B) = Σ[ x ∈ A ] B`) —
  still shape-limited, still not a macro system.
- **Haskell/ML** — symbolic operators from a fixed lexical class plus fixity
  declarations. Simplest thing that works; no bracket or ternary forms.
- **Scala** — precedence determined *lexically by the leading character*.
  Worth noting because it is the trick that keeps a wide operator lexicon
  genuinely context-free.
- **Coq** — notation levels, scopes, `%` delimiters, reserved notation. The
  cautionary end of axis 2.

## Proposal to pressure-test

Keep axis 2 closed; open axis 1 in the one way that preserves context-free
parsing:

- **Precedence comes from the base operator, not the decoration.** `+_Z`
  parses at `+`'s precedence because it *starts* with `+` (the Scala trick,
  specialised to the decoration grammar). Decoration then never perturbs
  parsing — it only selects which meaning — so the parse is fixed and only
  *resolution* is scope-dependent. This is also what makes decorated
  operators implementable without a notation table at all.
- **Bracket families are curated, hookable, and shape-fixed**: `⟦_⟧`,
  `⌈_⌉`, `⟨_⟩`, `_[_]` are in the grammar with fixed arity; libraries bind
  meanings via traits, not via new syntax.
- **The escape hatch for the residue is the modal layer, not notation.**
  This is the coherent part of Heather's position and it is stronger than
  Lean's: the reason Lean needs `macro_rules` is that its metaprogramming is
  a separate monadic layer over untyped `Syntax`, so generating terms *is* a
  macro. Heather's meta-layer is typed code manipulation inside the language
  ([[surface-syntax]] §metaprogramming), so the "generate a term" half of
  what macros do is already covered, well-typed and kernel-checked. Only the
  "introduce syntax" half is being declined.

## The honest counterargument

Mathlib is real evidence that notation extension earns its keep at scale, and
"a rich fixed grammar is enough" is a claim that gets tested by the *fifth*
domain someone formalises, not the first. Two specific places a fixed
lexicon is known to run out:

- **Binder notation** — `∑ x ∈ s, f x`, `∀ x > 0, P x`, comprehensions, `do`.
  Mixfix cannot express these, which is exactly why Agda added `syntax`. If
  anything from axis 2 belongs in Heather's fixed set, it is one declarative
  binder-notation form of that shape. **This is the concrete decision this
  issue should reach.**
- **Structured literals** — matrices, numeric literals at a user type
  (Lean's `OfNat`), string interpolation. Partly a trait problem rather than
  a syntax problem; worth separating before concluding it needs syntax.

## Why deciding conservatively is safe

The fork is asymmetric: closed → open is an additive change at any later
date, while open → closed breaks every library that used the extension. Ship
the fixed grammar, keep a list of the notations people actually reach for and
cannot express, and revisit with evidence. The list is the deliverable of
this issue in the meantime.

Related: [[front-end-sugar]] (what the sugar layer must cover),
[[surface-syntax]] (the standing taste constraints), [[dependency-policy]]
(`logos` lands with the symbol table).
