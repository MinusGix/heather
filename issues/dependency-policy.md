---
title: "Dependency policy: kernel at zero, crates above it"
status: open
labels: [meta, kernel, tooling]
area: infrastructure
created: 2026-07-24
updated: 2026-11-09
---

The tree began dependency-free: `Cargo.lock` contained exactly the four
workspace crates. That happened by default rather than by decision; this
issue made it a decision, because the two halves of the tree want opposite
answers. Since then `sha2` has landed as a cache test oracle and
`typed-arena` as the kernel's one shipped, exactly pinned dependency. Both
exceptions and their audit boundaries are recorded below.

## The kernel stays at an audited minimum

`crates/kernel` is the trusted base of a proof assistant: its bug set is the
soundness set. A dependency there is trusted-base surface area nobody on
this project wrote, a supply-chain question that gets awkward exactly when
Heather starts *certifying* things, and a hole in the workspace's
`unsafe_code = "forbid"` (which binds our code, not `smallvec`'s). The
The kernel's proof semantics need nothing: de Bruijn terms, the substitution
algebra, conversion, and a budget-bounded `Debug` are all first-party by
nature. The storage-mechanics exception below does not implement a judgment.

That changed once, deliberately, on 2026-08-26. `typed-arena = "=2.0.2"` is
the kernel's sole dependency. The exact version is pinned; it has no
transitive dependencies; and its complete 635-line implementation was read
before adoption, including the small unsafe core that maintains stable
addresses while chunks grow. The dependency supplies allocation and
destruction mechanics only: no term, reduction, conversion, or proof rule is
delegated to it. The kernel's value graph uses its stable references to make
recursive ownership unrepresentable and to replace an ad-hoc thread-local
destruction protocol. That is a smaller practical trust boundary than owning
both the proof rules and a custom arena implementation here.

Any further kernel dependency still pays the original entry price: pin it,
audit its complete reachable implementation before it lands, record why its
semantics do not enter the proof judgment, and prefer no-transitive-dependency
crates small enough to review directly. `cargo-deny`/`cargo-vet` remains the
right next step if this ceases to be a one-crate exception.

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

Performance crates (`rustc-hash`, `smallvec`) are premature and, more
to the point, not the lever: the thing that would matter at
[[inductive-compiler]] term volume is hash-consing `Rc<Term>` with a
conversion cache, which is a kernel design change we would write ourselves
(see the zero-dep rule above). Measure first.

`salsa` for incremental re-checking: only once something interactive exists
— see [[lsp-from-the-meta-layer]].

## Log

- 2026-08-26: **First shipped kernel dependency: `typed-arena` 2.0.2, exactly
  pinned.** A 100,000-node forced value graph showed that stack-safe evaluation
  was still followed by stack-recursive `Rc` destruction. A temporary
  per-thread drain avoided the crash but made destruction a hidden global
  protocol. The arena makes environment and closure ownership query-local;
  graph edges are references and destruction is flat. `typed-arena` was chosen
  over `bumpalo` because it runs payload destructors (the graph still contains
  `Rc`, `Vec`, and syntax), and over handle arenas because stable references
  express the evaluator's immutable graph directly. Its complete 635-line
  source was audited before adoption and it adds no transitive crates.
- 2026-08-06: **First dependency in the tree, and it is a dev-dependency: `sha2`, in `crates/cache` only.** `Cargo.lock` is no longer just the workspace crates (it gains `sha2` and nine transitive crates; the RustCrypto stack is not small, which is worth noticing even for a dev-dep). The case is the mirror image of the one that made `crates/cache`'s SHA-256 first-party (`docs/infrastructure/cache-v1-design.md` §2): that argument says a trust-bearing hash must be ours, and it is exactly *because* it is ours that "probably correct" is not good enough. `sha2` is therefore adopted as an **oracle to disagree with us**, never as an implementation — `crates/cache/tests/sha256.rs` asserts byte-identical digests over every length 0..=300, multi-block inputs to 1 MiB, and six adversarial chunkings, which is a stronger criterion than the five published vectors it joins. Shipped code links nothing; `cargo build -p heather-cache` still resolves to the workspace alone. The general rule this instances: *a first-party implementation of a frozen specification should be differentially tested against a mainstream one, and a dev-dependency is the cheap way to do it* — the same shape as the fresh-vs-replay oracle in [[parallel-checking-and-caching]]. It does **not** loosen the kernel's zero (dev-dependencies included, per `docs/infrastructure/benchmarking.md`); the kernel has no frozen-spec module to test this way. No divergence was found on adoption.
- 2026-07-30: [[cli-check-diagnostics]] landed *without* the diagnostics-rendering dep: a single-span caret line is ~15 lines of std (`snippet` in crates/elab/src/lib.rs), so the renderer question stays open until something needs multi-label reports (the goal listing kept its listing shape instead). The candidate list stands as options, not commitments; `render_snippet` is now the thing a renderer dep would replace.
- 2026-09-17: 2026-09-17: the first `unsafe` in first-party code, and the first crate to say `deny` where the workspace says `forbid`: crates/cache's SHA-256 gained the CPU's SHA-extensions path (one `#[allow(unsafe_code)]` on the intrinsic function and one on its dispatch), after the walk it feeds was measured at 318 MB/s scalar against ~2.2 GB/s with the extensions ([[merkle-walk-cold-share]]). The `sha2` route — already a dev-dependency as the test oracle — was measured first and ran at the same rate, so the crate keeps zero shipped dependencies. User position: the forbid is a strong guideline, not a wall, and SHA is hard to get wrong badly; the oracle tests check both paths against each other on any machine that has the extensions.
- 2026-09-26: 2026-09-26: `heather-numeral` (`crates/numeral`) joins the kernel's dependency set, first-party: `Term::NatLit` now carries its `Numeral`, an arbitrary-precision natural (docs/language/wide-numerals-design.md). It was written here, has no dependencies and no `unsafe`, and is shared with `syntax` and `elab` so a numeral is one type at every stage — a crate of its own only so the syntax crate need not depend on the kernel. Judgment-relevant surface: `is_zero`, `pred` (borrow across limbs) and `limbs`, each unit-tested with the normalization invariant (`Big` exactly above `u64::MAX`, top limb nonzero) that makes structural equality numeric equality. Parsing and display are not judgments.
- 2026-11-05: gardener: cites a file it shares with [[native-process-fixed-cost]] (`docs/infrastructure/cache-v1-design.md`); [[perf-tracking-consistent-environment]] (`docs/infrastructure/benchmarking.md`); [[type-value-memo-hit-rate]] (`docs/infrastructure/benchmarking.md`).
- 2026-11-09: `mimalloc` adopted above the kernel as the process allocator for everything that links the elaborator ([[global-allocator]]). It enters through `heather-elab-lib`/`heather-elab-unit`, not the kernel: `heather-kernel-lib` still depends on `typed-arena` and `heather-numeral` only, and a kernel linked alone keeps the system allocator. Transitive: `libmimalloc-sys` (vendored C, built with `cc`).
