---
title: "Syntax with binding as a library: signatures, well-scoped terms, substitution laws proved once"
status: open
labels: [stdlib,mathematics,metatheory,design,syntax]
area: mathematics
milestone: [math-binding-syntax,hih-kernel-model]
created: 2026-11-10
updated: 2026-11-10
---

Area 3 of the 2026-11-10 ranking. Minus: "I'd be good with generic
binding syntax though I'm unsure if there's any problems." So the first
round is a design note with probes that looks for the problems.

`lib/kernel_model`, `lib/native/runtime/rt*.hthr`, FunctionIR and the
e-graph's terms each define their own variables and their own renaming,
shifting or substitution, with their own lemmas. The Rust kernel's
history says this is where defects live (the shift-and-compare guards,
`weakening-is-a-proxy` in the project notes).

## Scope of the design round

- The representation: a binding signature as data (constructors with
  arities that say how many variables each argument binds), terms indexed
  by scope, in the style of Allais et al.'s universe of syntaxes or of
  Autosubst's sigma calculus. State which Heather inductive form carries
  it (`IWf` at a `Nat` index) and what the kernel pays to evaluate a
  generic traversal against a hand-written one.
- Renaming and substitution once, with identity, composition and the
  interchange laws; a normaliser for substitution expressions as a `simp`
  set or a reflective tactic ([[simp-tactic]]).
- The questions that could sink it, each with a probe:
  1. Do the kernel's layered contexts (`Σ; Ψ′`, code under `□`,
     `docs/delam/04–06`) fit one signature, or do they need two sorts of
     variable with a mixed substitution?
  2. Does a generic term stay cheap to evaluate, or does the signature
     interpretation cost a constant factor that a reflected IR cannot
     pay ([[function-ir-evaluable-quadratic]])?
  3. Can an existing client be an instance without restating its
     theorems: start with `kernel_model`'s `Tm`.
  4. Does typing over a generic signature keep usable inversion, given
     no UIP?
- `/mnt/project-files/heather-model/generic_syntax_probe.hthr` is an
  earlier probe in this direction; read it first.

## Done when

`docs/generic-binding-syntax-design.md` answers the four questions with
checked probes, and either a first library round is filed with
`kernel_model` as its client or the note records why hand-rolled syntax
stays.

## What it assumes from elsewhere

- **[[kernel-model]]** owns the model of reduction. Assumed here: only
  that its term type is the first candidate instance.
- **[[datatype-container-algebras]]** owns containers for ordinary
  inductives. Assumed here: nothing; a binding signature is a container
  with extra structure and may reuse its vocabulary.
- **[[definitional-inversion-domain-model]]** is the largest client in
  sight.
