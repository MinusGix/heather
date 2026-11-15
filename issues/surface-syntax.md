---
title: "Surface syntax: Rust-flavored core, match, quote/splice, structured proofs"
status: open
labels: [frontend,syntax,design]
area: language
created: 2026-07-23
updated: 2026-07-24
---

Direction + taste constraints (user, 2026-07-23): Rust as the reference
"good imperative syntax" (not literally; more implicitness acceptable given
proof-system realities). Explicit anti-goals: Rust's macro/proc-macro
story; Lean's programming syntax; Lean's goal-mutating tactic style (not
structural enough); the full arcaneness of Lean
notation/syntax-extension. Notation position: a **fixed grammar** of common
patterns and special symbols in the core language — decorated operators
(`+_Z`, `⟦R⟧_s`), a curated unicode symbol table — parsed context-free;
**no user parser extensions, ever**. DSL-like support is a later question;
the principled route is quotation + `match code` + meta-functions over deep
embeddings (riding the modal layer), not syntax categories.

Organizing principle: Rust macros and Lean elaboration towers are both
metaprogramming *outside* the object language. DeLaM's point is that staged
metaprogramming with intensional analysis is *inside* the typed language —
so the surface exposes the modal layer as ordinary well-typed programming,
not a bolted-on macro system.

## match (case analysis)

Rust shape; the theory intrudes only at the motive (sums/W are positive —
motive not recoverable by projection, per [[front-end-sugar]]):

- Checking position: `match e { Inl(x) => …, Inr(y) => … }` — motive from
  expected type. Covers most code.
- Inference position: postfix ascription `match e { … } : T`
  (non-dependent) and `match e as z -> M { … }` (dependent motive binding
  z).
- **Recursion is a separate form**: `rec e as z -> M { Zero => …,
  Succ(n, ih) => … }` — eliminators surfaced honestly, ih bound in the
  pattern. Termination-checked recursive `fn` → `rec` is later sugar.
- Nested patterns via a simple pattern-matrix pass to nested
  `case`/`fst`/`snd`; η-for-pairs makes `let (a, b) = p` transparent.

## quote / splice (the modal layer)

- Contextual code type: `Code(Δ ⊢ T)` (ASCII `|-` accepted; levels
  inferred). Keep the turnstile.
- Quotation `code { e }`: checking-only, exactly like kernel `box` — Δ and
  T come from the expected type; the form carries no annotations,
  mirroring the kernel instead of fighting it.
- `let code u = e;` — surface `letbox` as a Rust let. Scrutinee position
  is inferable, so this always elaborates.
- In-quote splices: `$u` (identity subst), `$u[a, b]` (explicit delayed
  substitution — surface `u^δ`; visible because it is semantically
  meaningful, and it is the Miller-pattern shape the unifier keys on).
- **`${expr}` inline splice = ANF-hoisting sugar**: elaborator lifts the
  expression to a fresh `let code u = expr;` above the quote and
  substitutes `$u`. MetaML ergonomics; the [[box-synthesis-gap]] meta-ANF/
  letbox invariant holds *by construction*. Stage discipline is free from
  contextual typing: a hoisted splice mentioning quote-locals is a scope
  error unless routed through an explicit substitution.
- **Flagship: `match code u { Zero => …, Succ($n) => …, App($f, $s) => … }`**
  — intensional analysis as pattern matching on syntax, lowered to the
  fixed-shape 37-branch recursor structs; splice-patterns bind code
  variables; telescope ih's/globals surface as named per-arm bindings;
  exhaustiveness is structural (the fixed-shape branch structs were built
  for this). This is where the rawest kernel machinery becomes the most
  familiar surface idiom.

## Proofs (structural, programming-flavored)

1. Now: term-mode proofs (a proof is a `fn` returning an `Id`), plus a
   small set of structured forms — `have`, `show`, `calc`,
   `induction`/`cases` — each a **documented mechanical desugaring** into
   eliminators (auditable-lowering doctrine applied to proofs). Structural
   by construction: no goal-state monad to leave in a mess. `calc` +
   decorated operators covers most equational reasoning; `induction` is
   `rec` with a propositional motive.
2. Later: tactics are meta-layer functions over code —
   `Code(g ⊢ Goal) → Code(g ⊢ Proof)`-shaped — written, typed, and checked
   in the language, output checked by the kernel. Heather needs no
   separate tactic framework; its object language is one. "Proofs feel
   like programming" becomes literal.

## Open representation questions (pressure-test first)

- Pattern-matrix compilation details (order, defaults, guards?) — wants
  design before [[inductive-compiler]] tier 1 lands.
- Exact lexical form of quote/splice markers (`code {}`/`$`/`${}` as
  proposed, or alternatives) — user has syntax ideas brewing; the surface
  AST is the stable contract, the grammar is swappable.
- Decorated-operator grammar: which decoration positions (subscript tag,
  bracket families) are in the fixed set.

## Log

- 2026-07-23: Opened from the syntax discussion; records taste
  constraints, the match/rec split, the quote/splice + ANF-hoisting
  design, match-code, and the two-layer proof story.
- 2026-07-23: Sketch round 0 written: docs/sketches/surface-v0.md@4acf2fe — Nat proofs/calc, holes + where-discharge (multiple goals = Ψ-metas), inductives, staged pow (three splice spellings), open-code substitution, match-code with default-arm sugar, Compile teaser. Findings: adopt $ident auto-hoist; substitution is $u[x := t] not call-shaped; Code = ordinary type + three magic forms (Rust-Box framing); default arms lower via identity_branches. Open: calc step spelling, positional subst shorthand, unnamed holes, field patterns, layer inference vs meta fn.
- 2026-07-23: Sketch round 1 (docs/archive/surface-v1.md) after user review of round 0. Decided: real operator/method syntax everywhere (parens type-app frees < for comparison); match/rec/induction strongly unified — IH = structural self-call (recursive theorems), explicit-ih pattern demoted to fallback; calc steps use :=, no 'by'/proof-mode ever; 'on ?name := expr' in-block discharge replaces where (positional filling rejected as goal-stack brittleness); split/on gives named per-constructor goals, expression-match stays primary (on-arms are leaves); auto-holes via implicit proof params (xs[i]). Explored: implicit quotation by checking type (contaminate style) — principled (box is checking-only), decision deferred to a nested-staging round 2; $ stays explicit regardless. Runtime-code question answered via deep-embedding AST + reify/reflect at the layer boundary (no kernel changes). Trait leaning: coherent-by-default, first-class dictionaries as escape.
- 2026-07-23: Sketch round 2 (docs/archive/surface-v2.md). Decided: implicit quotation adopted — justified by the structural fact that DeLaM has no code-of-code (□ is layer-m only, code is layer v/c), so staging is exactly two-level and the boundary-is-variables rule ($ marks meta-level variables; fns/operators/literals are shared lexicon) keeps it readable. .code on top-level fns for write-once/extract-later (elaborator quotes the elaborated term; intensionality = the accepted syntax-keying contract; elaboration determinism becomes a documented guarantee). Goal naming: callee-parameter-name defaults with provenance, discharge-by-statement (on _: P := e, discharges all matching), explicit names win; principle: proof-parameter names are API. Partial evaluation is library meta-functions, not kernel; mechanical binding-time derivation earmarked far-future. End-to-end narrative sketch (write fn -> lower via match code -> Compile instance -> run) composes with no macro layer anywhere.
- 2026-07-23: Sketch round 3 (docs/archive/surface-v3.md). (1) Context-specific compilation: smart instances over smart resolution — ctx-parametric ir(ctx) with forall-ctx equiv proven once (certifying-generator's prove-once shape at instance granularity); dedup by coarse (syntax, descriptor) keying; context facts can carry proofs, making optimization guards propositions. (2) Goals are code (a hole's statement is □(Γ ⊢ Ty l)), so goal-solvers are ordinary untrusted-by-construction meta-functions; on _: _ := solver(goal, …) surface form; goal merging/subsumption is expressible today as plain hole-programming, set-level transformer syntax deferred. (3) pow vs specialize_pow corrected per review: binding-time split, not a boundary move; routes = hand-staging now, BTA later, certified partial evaluator as in-thesis endgame (tractable: object language total, stuckness syntactic). Threads 1+3 converge: context-specific compilation = certified PE at instance level.
- 2026-07-24: Equality/binding notation DECIDED (2026-07-24): merge onto a single `=` (ML/OCaml-style, disambiguated by `let`): `let x = e` binds, `a = b` is propositional equality (the Id former). Rationale: Rust needs `==` only because its `=` is *mutation*; Heather's `let x = e` is definitional binding — exactly how math overloads `=` for definitions vs equations — so the `==` distinction was unmotivated here. Heather is even safer than ML: `a = b` lives in *type* position, more separated from let-RHS value position than ML's value-level `=`. Kept: `:=` for obligation *discharge*/substitution (calc `= rhs := proof`, `on ?g := e`, `[x := t]`) — introduce(`=`) vs discharge(`:=`) stays visually distinct. `==` is lexed but rejected by the parser with a 'write `=`' hint (C/Rust muscle memory). No prop-vs-decidable *operator* split wanted (user): a single `==`... no — a single `=` proposition, trait-resolved decidability later (decide when DecEq exists, else 'can't be decided at runtime'), method `x.eq(y)` for named decision procedures. Implemented: lexer Eq token + EqEq-rejected, ty()/calc use `=`, prelude + all suites migrated. Note: docs/sketches rounds 0-3 predate this and still show `==`; this log supersedes.
- 2026-07-24: Block/hole surface DECIDED and implemented with [[goal-holes]]: (1) blocks are `{ stmt* expr on_stmt* }` — a real statement grammar, arriving now rather than with `apply`, since holes need somewhere to be discharged; `let x (: T)? = e;` is the only statement so far and is an *inlined alias*, not a kernel binder (the `fn`-definition doctrine), so Γ is unchanged and shadowing is decided by binding position. (2) Anonymous-hole lexeme reconciled — the sketches spelled it both `?_` (v1) and `?` (v2/v3); `?` wins, and `_` stays purely the discharge wildcard (`on _: P`). Named-vs-anonymous is settled in the *lexer* by adjacency (`?p` named, `? ` anonymous), so the parser never faces the ambiguity. (3) `on` is trailing-only — order-free among themselves, but after the result expression; every sketch example already reads that way and it removes all lookahead. `let`/`on` stay contextual keywords (an expression is never continued by a bare identifier), so both remain usable as ordinary names. (4) Holes are checking-only, like `refl`: the expected type *is* the goal's statement, so a hole with nothing to check against has nothing to defer. Consequence to know: `sym(?p)` is refused (implicit-taking callees infer their explicit arguments) and wants `@sym(a, b, ?p)` until the unifier postpones — see [[elab-unifier-completeness]]. (5) `?bound.1` — the checker's ordinal-dedup suffix — is part of the goal name, joined in the `on`-target parser; a goal name never carries a method call, so there is no clash with `.f(…)`.
- 2026-07-24: Notation extensibility promoted to its own issue, [[notation-extensibility]] — the 'which decoration positions are in the fixed set' open question turned out to be the small version of 'is the fixed-grammar position right at all' (user uncertainty, 2026-07-24: is the Lean method really as bad as the anti-goal assumes). Recorded there: the two axes (open *lexicon* vs open *grammar shapes*) are independent, Lean's cost is almost entirely the second and its root is that an extensible grammar makes parsing depend on the elaboration environment — which is what we would be giving up, since parse_file is currently total and context-free and the AST is the stable contract. Proposal to pressure-test: precedence comes from the base operator so decoration never perturbs the parse (Scala's leading-character trick), curated shape-fixed bracket families hooked by traits, and the modal layer — not notation — as the escape hatch, which is coherent precisely because our metaprogramming is typed code manipulation rather than an untyped Syntax macro layer. Honest counterargument also recorded: binder notation (∑ x ∈ s, f x) is the known gap a mixfix-style lexicon cannot reach, and one declarative binder form (Agda's `syntax`) is the concrete decision that issue should reach.
- 2026-11-05: gardener: cites a file it shares with [[compile-typeclass-design]] (`docs/archive/surface-v1.md`); [[datarepr-separation]] (`docs/archive/surface-v2.md`); [[nested-goal-discharge]] (`docs/archive/surface-v3.md`).
