---
title: "Dependency policy: kernel at zero, crates above it"
status: open
labels: [meta, kernel, tooling]
created: 2026-07-24
updated: 2026-07-30
---

The tree is currently dependency-free: `Cargo.lock` has exactly the four
workspace crates. That happened by default rather than by decision; this
issue makes it a decision, because the two halves of the tree want opposite
answers.

## The kernel stays at zero

`crates/kernel` is the trusted base of a proof assistant: its bug set is the
soundness set. A dependency there is trusted-base surface area nobody on
this project wrote, a supply-chain question that gets awkward exactly when
Heather starts *certifying* things, and a hole in the workspace's
`unsafe_code = "forbid"` (which binds our code, not `smallvec`'s). The
kernel also needs nothing: de Bruijn terms, the substitution algebra,
conversion, and a budget-bounded `Debug` are all first-party by nature.

Should that ever change, the entry price is an auditing story
(`cargo-deny`/`cargo-vet`), decided *before* the first dependency lands, not
after.

Note this is not an argument against crates in general — it is an argument
about one crate. Everything above the kernel (`syntax`, `elab`, `cli`) has
no trust story to protect and should spend freely.

## Adopted above the kernel (2026-07-24)

- **`ariadne`** — diagnostic rendering, **in the CLI only**. Chosen over
  `codespan-reporting`/`annotate-snippets`/`miette` for multi-label reports
  with connecting lines: a goal listing is inherently multi-span (hole raised
  here, `on` that matched nothing there, candidate goals elsewhere).
  Structured errors (`ElabError`, `GoalReport`) stay in `elab`; only the CLI
  knows how to paint. That keeps the dependency at the edge, leaves library
  consumers (tests, a future LSP) unaffected, and makes swapping renderers a
  one-file change. `ElabError::render(&src)` is the thing it replaces.
  Lands with [[cli-check-diagnostics]].
- **`clap`** (derive) — once the CLI has more than `check <file>`. Same
  issue.
- **`insta`** — snapshot tests for the goal listing and diagnostics. The
  listing is a *rendering* whose exact text is the deliverable, and
  substring assertions (`rendered.contains("k : Nat")`) are a weak proxy for
  "does this read well". Safe against the OOM rule: kernel `Debug` is
  budget-bounded, so a snapshot cannot blow up.
- **`logos`** — the lexer. Modest today (119 hand-written lines → ~40
  declarative ones, spans built in, maximal munch correct by construction
  instead of by a hand-maintained two-char table). The real argument is
  forward: the curated symbol table of [[notation-extensibility]] is far
  nicer as derive attributes than as one `match` arm per symbol. Adopt with
  that work, not as a standalone refactor.

## Declined, with reasons (so this is not re-litigated)

- **Parser combinators** (`chumsky`, `winnow`, `nom`) — keep the hand-rolled
  recursive descent. Error messages and recovery are the thing a language
  front-end is *for*, and hand-rolled wins there; the grammar leans on
  contextual keywords (`on`/`let`/`match` are ordinary idents),
  position-sensitive rules (`=` means one thing in `ty()`, another in
  `let`), and parser-level desugaring (`calc` → nested `@trans`). Migrating
  ~700 working lines buys little.
- **`proptest`/`quickcheck`** — the hand-rolled seeded generators are the
  right design and adopting these would fight it twice: well-typed term
  generation is domain logic no library supplies, and shrinking-with-a-
  printed-counterexample is precisely what CLAUDE.md forbids (the
  counterexample is a kernel term). Seed-only failure output is a deliberate
  OOM guard.
- **`thiserror`** — marginal. It tidies the trivial variants; the one
  `Display` that matters (the goal listing) is custom rendering anyway.

## Deferred

Performance crates (`rustc-hash`, `smallvec`, arenas) are premature and, more
to the point, not the lever: the thing that would matter at
[[inductive-compiler]] term volume is hash-consing `Rc<Term>` with a
conversion cache, which is a kernel design change we would write ourselves
(see the zero-dep rule above). Measure first.

`salsa` for incremental re-checking: only once something interactive exists
— see [[lsp-from-the-meta-layer]].

## Log

- 2026-07-30: [[cli-check-diagnostics]] landed *without* the diagnostics-rendering dep: a single-span caret line is ~15 lines of std (`snippet` in crates/elab/src/lib.rs), so the renderer question stays open until something needs multi-label reports (the goal listing kept its listing shape instead). The candidate list stands as options, not commitments; `render_snippet` is now the thing a renderer dep would replace.
