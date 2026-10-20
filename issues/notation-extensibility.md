---
title: "Notation: how open, and open along which axis"
status: open
labels: [frontend, syntax, design]
area: language
created: 2026-07-24
updated: 2026-08-11
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

## Proposal (worked out with the user, 2026-07-24)

Keep axis 2 closed; open axis 1 in the one way that preserves context-free
parsing. The organising claim, which the worked examples below support:
**mathematical notation has few shapes and many symbols**, so fix the shapes
in the grammar and let the symbols be open.

### The shape family — all of it

| Shape | Examples | Cost |
|---|---|---|
| Enclosing brackets, fixed arity | `⟦t⟧`, `⌈x⌉`, `‖x‖`, matrix/vector literals | ~free: self-delimiting, so no precedence question exists |
| Infix/prefix, possibly decorated | `a +_Z b`, `a ⊞ b`, `¬p` | needs a precedence answer |
| Big-operator binder | `∑ a ∈ A, e`, `∫ x, f x`, `∏`, `⨆` | one new production |
| Sub/superscript decoration on any of the above | `+_Z`, `⟦R⟧_s`, `∑_{i=0}^n` | lexical |

The binder row is the only genuine addition to the grammar, and **all the
binder examples are one shape**: `SYM binders (clause)? "," body`, body
extending maximally right (so `∑ x ∈ s, f x + 1` takes the whole sum, and
narrowing needs parens — the standard mathematical reading). Fix that one
production and ∑ ∏ ∫ ⨆ ⋂ ⋀ all arrive together. This is Agda's `syntax`
minus the generality: Agda needed a general form because it was retrofitting
one; only the big-operator shape is needed here.

### Classification by character class, not by a declared table

The move that removes the need for any user-side notation declaration: do
not ask "what has been declared?", ask "what *class* is this codepoint in?"
Unicode has largely done the work.

- **Brackets** from `Ps`/`Pe` plus the mirroring pairs — `⟦⟧ ⌈⌉ ⟨⟩`
  classify themselves.
- **Infix operators** from `Sm` / the `Math` property — `⊞`, `⊗`, `⋈` are
  operators because of what they *are*.
- **N-ary binders** need **exactly one curated list** (~20 codepoints:
  ∑ ∏ ∐ ∫ ∮ ⋀ ⋁ ⋂ ⋃ ⨀ ⨁ ⨂ ⨄ ⨆ …), because Unicode genuinely does not mark
  "this operator binds a variable". That list lives in the lexer — first
  party, so parsing stays context-free.

Consequence: "make a PR to core to add a symbol" narrows from *every* new
symbol to *only a new binder symbol* — rare, and exactly the case worth
gating. Everything else works on first use.

### Precedence without declarations

Assign precedence by class, not per symbol: relational-ish (`⊆ ≤ ≡`) at
comparison level, additive-ish (`+ ⊕ ⊎ ∪`) at additive, multiplicative-ish
(`× ⊗ ∘ ∩`) at multiplicative. Someone introducing `⊞` gets additive
precedence automatically from its class; no fixity declaration, no scope
dependence. For decorated operators, precedence comes from the **base**:
`+_Z` binds like `+`, so decoration never perturbs the parse — it only
selects which meaning, and that is ordinary (scope-dependent) resolution.

**The relational class must be a ladder, not one level** — see the judgement
case below.

### Lexical rules

- **Decoration is glued, application is spaced**: `+_Z` is a decorated
  operator, `+ _Z` is `+` applied to the variable `_Z`. Adjacency decides,
  and there is already a precedent for exactly this rule in the tree — the
  hole lexer distinguishes `?p` (named) from `? p` (anonymous) the same way
  ([[goal-holes]], `crates/syntax/src/lexer.rs`).
- **`\sum` is an input method, not a lexeme.** Agda and Lean both do this:
  the editor turns `\sum` into `∑` and the file stores Unicode. Keeps `\`
  out of the lexical namespace and guarantees one spelling per symbol in
  source. Commit early — it is much harder to walk back once files contain
  both spellings. (Interim reality: without an editor input method, symbols
  get pasted.)
- **ASCII is a scarce namespace; spend it on core syntax and put domain
  notation in Unicode.** `?`, `_`, `@`, `:=`, `.` are already spent. Concrete
  payoff: the quotient/setoid bracket must be `⟦⟧` rather than an ASCII
  doubled square bracket, because that collides with a nested list literal —
  `[ [1,2], [3,4] ]` would lex its leading doubled `[` as one bracket token
  and the parse is wrong before anything else happens.

### Three things that turn out not to be notation

Worth stating, because each one otherwise inflates the notation problem:

- **Tactics.** `tactic split` — writing the bare name runs it with the
  context auto-passed — is *auto-application of implicit arguments*, i.e.
  the auto-defer mechanism already designed in [[goal-holes]] (an implicit
  proof parameter marked auto-defer becomes a goal at the call site). A
  declaration modifier plus an elaboration rule; `split x` is then ordinary
  application. Zero notation support needed.
- **Core forms** (`if`/`then`, `∀`/`∃`, `match`). The test: if it needs a
  *typing rule* or a scrutinee-dependent motive, it was never notation.
- **Judgement syntax** — see below; it is a precedence ladder.

### The escape hatch for the residue is the modal layer, not notation

This is the coherent part of Heather's position and it is stronger than
Lean's: the reason Lean needs `macro_rules` is that its metaprogramming is
a separate monadic layer over untyped `Syntax`, so generating terms *is* a
macro. Heather's meta-layer is typed code manipulation inside the language
([[surface-syntax]] §metaprogramming), so the "generate a term" half of
what macros do is already covered, well-typed and kernel-checked. Only the
"introduce syntax" half is being declined.

Matrix/vector literals are the worked example: a bracketed comma-list (a
shape you want anyway) whose *initialisation* is Code-generated by a
meta-function. Syntax stays fixed, semantics is a library.

## Judgement syntax, worked out

`Γ ⊢ t : T` was flagged above as the case most likely to force general
mixfix. It does not, once two different wants are separated.

**(a) The contextual-type judgement is core.** `□(Δ ⊢ T)`, `Trm(Γ ⊢ P)`,
`Code(g ⊢ El(P))` are DeLaM's contextual type former — a built-in form with
a typing rule, arriving with the modal surface. Closed, fixed, no
extensibility question. Probably half of why judgement notation felt
necessary at all.

**(b) User-defined judgements are a precedence ladder.** `Γ ⊢ e ⇓ v`,
`e ⟶ e'`, `Γ ⊨ φ` are already plain binary infix. Only the typing judgement
has three holes, and it decomposes by precedence alone:

```
Γ ⊢ t ⦂ T     parses as     ⊢(Γ, ⦂(t, T))       given  ⦂  tighter than  ⊢
```

No mixfix, no new production — two infix operators at different levels. The
key is not to contest ASCII `:` (already ascription): use `⦂` (U+2982), which
is what Agda's standard library reaches for under the same constraint. It
extends the way one would hope, the ladder being "how much of the formula
does this symbol scope over":

```
Δ ; Γ ▹ (x ⦂ A) ⊢ t ⦂ B        with     ⦂  >  ▹  >  ;  >  ⊢
```

So the concrete requirement this places on the class scheme: **turnstiles and
entailment (`⊢ ⊨ ⊩ ⟹`) are the loosest relational level** — they are a
judgement's main connective — and other relational symbols sit above them.
Overloading (`⊢` for one library's typing relation and another's entailment)
is ordinary resolution by operand type; nothing scope-dependent reaches the
parser.

Two caveats:

- Defining such a relation needs indexed families, so this is naturally
  downstream of [[inductive-compiler]] tier 2 and cannot be exercised before
  then.
- **The hard half is the rule, not the judgement.** Anyone wanting
  `Γ ⊢ t ⦂ T` also wants premises over a horizontal bar, which is not linear
  text and which *no* notation system delivers. The answer: rules are
  ordinary constructors of an indexed family, and two-dimensional rendering
  is a *display* concern — a meta-function `Code(Γ ⊢ T) → Presentation`,
  i.e. the editor-feature-as-a-library idea in [[lsp-from-the-meta-layer]].
  Stating this matters, because "we need rule syntax" is the demand that
  would otherwise drag the design into general mixfix.

## Declined: notation declared in package metadata

Considered and rejected (user's own floated option): declaring fancy symbols
in a package toml, parsed before codegen, with the notation "downgraded" when
not in scope for a file. Two specific problems, neither aesthetic:

1. A file stops being self-contained — it cannot be parsed without build
   metadata. That is precisely the property the fixed grammar was protecting,
   given up for less openness than the class-based scheme already provides.
2. "Downgrade if not in scope" means the same text parses differently
   depending on context, *silently*. That is the Lean problem re-entering
   through the back door, in a worse form, because there is no error to read.

If declared notation is ever wanted anyway, the least-bad shape is **per-file
and lexical** (`use notation …` at the top of the file), so a file still says
everything about how to read itself. Never build metadata.

The boundary that stays simple, and that all of the above preserves:
**parsing is context-free; only resolution (which trait, which instance)
consults scope.**

## The honest counterargument

Mathlib is real evidence that notation extension earns its keep at scale, and
"a rich fixed grammar is enough" is a claim that gets tested by the *fifth*
domain someone formalises, not the first. Two specific places a fixed
lexicon is known to run out:

- **Binder notation** — `∑ x ∈ s, f x`, `∀ x > 0, P x`, comprehensions, `do`.
  Mixfix cannot express these, which is exactly why Agda added `syntax`.
  *Answered by the proposal*: one production for the big-operator shape,
  entered by a curated lexical class. That is the single piece of axis 2
  admitted to the fixed set, and it is admitted as a **shape**, not as a
  user-extensible mechanism.
- **Structured literals** — matrices, numeric literals at a user type
  (Lean's `OfNat`), string interpolation. *Answered*, at least for matrices:
  bracketed comma-list (a shape wanted anyway) plus Code-generated
  initialisation. Numeric literals at a user type are a trait problem, not a
  syntax problem. String interpolation remains genuinely open, and is the
  most likely future axis-2 pressure.

## Open questions

- **General mixfix.** Left out. The trigger for revisiting is explicit: if
  the relational ladder proves insufficient for real judgement-shaped
  notation in practice, not before. `if_then_else_`-style forms are core
  language here, so they are not evidence.
- **Where sub/superscript decoration attaches.** The original
  [[surface-syntax]] question ("which decoration positions are in the fixed
  set") survives: `+_Z` and `⟦R⟧_s` are settled by the adjacency rule, but
  `∑_{i=0}^{n}` — decoration on a *binder* symbol, with braces — is not, and
  it interacts with the binder production's clause slot.
- **Precedence-class boundaries.** The additive/multiplicative/relational
  split is folklore-obvious for common symbols and arbitrary at the edges
  (where does `⋈` go? `∖`? `⨝`?). Needs a written table, and a stated default
  for an `Sm` symbol matching no class.
- **String interpolation**, per above.

## Why deciding conservatively is safe

The fork is asymmetric: closed → open is an additive change at any later
date, while open → closed breaks every library that used the extension. Ship
the fixed grammar, keep a list of the notations people actually reach for and
cannot express, and revisit with evidence. The list is the deliverable of
this issue in the meantime.

Related: [[front-end-sugar]] (what the sugar layer must cover),
[[surface-syntax]] (the standing taste constraints), [[dependency-policy]]
(`logos` lands with the symbol table), [[lsp-from-the-meta-layer]]
(two-dimensional rule display as a meta-function, not syntax).

## Log

- 2026-07-24: Opened after the [[dependency-policy]] discussion surfaced the
  user's uncertainty about whether the Lean route is really as bad as
  [[surface-syntax]]'s anti-goal assumes. Recorded the two-axis distinction
  and the precedents.
- 2026-07-24: Proposal worked out with the user from a concrete wish list
  (quotient brackets, decorated `+_Z`, `∑`/`∫` binders, matrix literals,
  judgement syntax, tactic names). Settled: four shapes, classification by
  Unicode character class with exactly one curated list (N-ary binders),
  precedence by class with turnstiles as the loosest relational level,
  adjacency for decoration, `\sum` as an input method, ASCII treated as a
  scarce namespace (hence `⟦⟧` for the quotient bracket rather than an ASCII
  doubled square bracket, which collides with nested list literals). Judgement syntax resolved as a precedence ladder over infix
  relations using `⦂` rather than `:`, so it does *not* force general
  mixfix; the two-dimensional inference-rule display it implies is a
  presentation concern for [[lsp-from-the-meta-layer]]. Tactics and core
  forms removed from the notation problem entirely. Package-metadata-declared
  notation declined, with per-file lexical `use notation` as the least-bad
  fallback if it is ever wanted.
- 2026-08-09: The || / && question gained a customer: [[bool-operator-designations]] records the doubt about +/* meaning or/and at Bool, with the double-symbol spelling as its likely real answer — the lexicon extension would land here.
- 2026-08-09: Second customer from the operators round's close: a RESERVED GENERIC symbol (∙ or ⋆) for generic theory — never designated at any carrier, no fallback name, so rungs 2/3 never fire and the symbol can ONLY mean a bound index: constitutionally generic, enforced by absence rather than convention. Library taste split suggested: + in the commutative chain (earned connotations), ∙ for bare Semigroup/Monoid theorems where + would whisper commutativity over append. One lexer token; no elaborator change — the constraint-symbol machinery is indifferent.
- 2026-08-09: The || / && customer was served without the mechanism: [[bool-operator-designations]] closed by adding the two symbols to the FIXED lexicon (two-byte tokens, precedence between the comparison rung and +/*, no fallback rung — meaning comes only from designations and binders). This is the cheapest possible axis-1 data point: a lexicon addition that needed no extensibility machinery because the symbol set is still small enough to curate by hand. The question this issue owns — whether users may add symbols — stands unchanged; what the round demonstrates is that a curated addition costs ~4 small edits (lexer, bp table, op_symbol, designations), which is the number an extension mechanism has to beat.
- 2026-08-09: Two more curated-lexicon customers from the algebra cleanup review: [[list-append-symbol]] (++ on the &&/|| recipe, retiring + at List) and [[binder-symbol-as-notation]] (the reserved generic ∙, now with a concrete mechanism: as-notation on declaring binders — class heads and value parameters). [[class-default-operators]] is filed for the day the symbol-slot ceremony stops scaling (Lattice, orders); it leans on the ∙-style curated additions and on no new resolution rung.
- 2026-08-11: The reserved generic `∙` (U+2219) lands as a curated token, via
  [[binder-symbol-as-notation]]. Cost, measured against the four-edit estimate
  this log has been keeping: lexer token, binding-power row, `op_symbol` row —
  and *no* designation row and *no* fallback entry, which is the whole of what
  makes it reserved. So three edits, one fewer than `&&`/`||`/`++`, because a
  symbol whose only meaning is a binder needs no table. One genuinely new
  lexical fact: `∙` is **three bytes**, where every symbol before it was one or
  two, so the lexer grew a three-byte window beside its two-byte one — the
  first real cost of going past ASCII, and it is a five-line one. Precedence
  came from the class scheme above without a decision being needed (a
  dot-shaped operator is multiplicative). The extension-mechanism question
  stands unchanged; the running score is that a curated addition costs three to
  four small edits, which is still the number a mechanism has to beat.
- 2026-08-10: The second curated-lexicon data point landed via [[list-append-symbol]]: `++` costs the same lexer/binding-power/op-symbol/designation edits as predicted, shares additive precedence, and has no fallback. The extension-mechanism question remains unchanged.
