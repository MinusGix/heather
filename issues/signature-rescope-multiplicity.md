---
title: What is left of shift_global after the signature memo: Psi-multiplicity times signature size
status: open
labels: [kernel,conversion,performance]
area: kernel
created: 2026-09-19
updated: 2026-10-25
---

With [[global-ref-rescope-per-occurrence]] fixed (2026-09-19), the *occurrence*
axis of `shift_global` is closed: a cold width-one
`heather check docs/showcase/calc_parser.hthr` turns 4,772,510 `u^δ` occurrences
into **12,263** signature fills, a 99.74 % memo hit rate, and the run's rescoped
nodes fall 38.82 M → **17.55 M** for −8.9 % of kernel gate.

What remains is a different shape: **Ψ-multiplicity × signature size**, roughly
12 M nodes of signature and 5.5 M of definition body (the 3,161 eager rescopes on
the rewriter path, `reduce.rs`'s cold `whnf`, which the lazy global offset
deliberately left alone).

A fill is large because these declared Δ/types are large — `calc_parser::Grammar`
~3,440 nodes per fill, `parser_contracts::Certified` ~7,400. A binding fills more
than once only because conversion's and typing's `push_tele` must rebuild the
cache, since after a push an index denotes a different binding. The items whose
rescope column barely moved are exactly the high-multiplicity ones:
`calc_parser::checked_expr` 396 fills, `Grammar` 375, `Certified` 174 — and for
`Grammar` the arithmetic closes exactly, 375 × 3,440 ≈ its remaining 1,290,053
nodes. `Certified` is also the one item the memo made *slower* (+2.8 %, ~14 ms):
174 fills against only 94,025 occurrences is the worst amortization on the board.

Two candidates, and a measured price to judge them by. This round priced a
rescoped node at **~112 ns** (21.26 M nodes bought 2.38 s of gate on furnace,
width one).

1. **Do not materialize the declared context at all** — the candidate
   [[global-ref-rescope-per-occurrence]] deferred: thread the global offset
   (`value::Env::gshift`) through `Conv::subst` / `apply_subst_ty` the way
   `docs/kernel/lazy-global-offset-design.md` threads it through definition bodies, so a
   signature is *read* at an offset rather than copied. Ceiling: the ~12 M
   signature nodes, ≈ **1.3 s of a 24.3 s gate, about 5 %**. It reaches only the
   value-domain sites — both `typing.rs` sites (`Type::GlobalTy`,
   `Term::GlobalTm`) stay on the memo regardless — and it needs its own adequacy
   equation, the analogue of the lazy-offset design's
   `eval(shift_global(k, t), ρ) = eval(t, ρ) at offset k`.
2. **Attack the multiplicity instead of the walk.** 375 fills for one binding is
   the surprising number here, not 3,440 nodes per fill. The rebuild is forced
   because the key is a Ψ-*index*; a key of (binding identity, shift amount)
   would still differ after a push, but sibling scopes at the same telescope
   depth could share. Whether that is most of the 375 is unmeasured — the first
   step is a histogram of fills per (binding, depth), not a design.

Per [[kernel-acceleration-policy]], 5 % is not on its own a reason to put a
lazy-offset path through conversion's substitution comparison; if candidate 1 is
ever done the reason should be the design one — that the kernel never copies a
declared context — with the `sigs`-versus-`refs` pair in `scripts/timings` as the
thing to watch. Candidate 2 is cheaper to investigate and has no adequacy
argument at all, so it goes first if this is picked up.

Measurement protocol, since two attempts at the parent round's numbers were
wrong: interleave before/after samples from two binaries built in one script,
assert each binary's provenance behaviourally (run it and check its `--timings`
header for the counter under test), and on furnace `touch` every source before
each build — the checkout is an rsync of the working tree and a `target/`
persisted on the `/work` volume makes cargo judge a reverted tree fresh, which
silently produces two byte-identical binaries. A desktop measurement under load
read this round's win as −2.9 % instead of −8.9 % and invented a +35 % regression
that does not exist.

## Log

- 2026-09-19: The measurement protocol this issue's last paragraph describes in
  prose is now a tool: `scripts/perf ab` (`perf/README.md`). It builds both
  binaries, parks a copy of each, interleaves the samples, asserts provenance
  (hashes must differ; `--marker COLUMN` requires the after binary to emit a
  `--timings` column the before one does not), warns on load average, and reports
  counters apart from seconds — with `separate` as a verdict only when the two
  sample sets are disjoint, and a delta inside the spread printed as not a result.
  `--base REV` uses a reused git worktree, `--patch FILE` reverses a diff in place
  for a box without `.git`, `--touch` defeats the stale-artifact trap, `--replay`
  re-renders for free.

  Validated against the round that closed [[global-ref-rescope-per-occurrence]] by
  re-running it through the harness: the counters reproduce the by-hand furnace
  numbers exactly (`global_sig_rescopes` 12,263, `shift_global_nodes` 38,815,029 →
  17,551,478, 24 columns unmoved), which is the cross-machine invariant, while the
  seconds differ by environment as they should — on a quiet desktop the gate reads
  −11.7 % against furnace's −8.9 %, and `parser_contracts::Certified`, the one item
  that regressed +2.8 % on furnace, is −8.0 % here. So that regression is
  environment-local and not a property of the change; the fills-per-occurrence
  reasoning above stands, but the +2.8 % should not be quoted as its evidence.
- 2026-10-25: From docs/surveys/segmap-survey.md §2: candidate 1 stays a weight-0 thinning (a constant offset, composing by addition), which is all a lazy signature read needs. A cutoff (invariant (I) of the lazy-offset design) would need a weight-1 offset, i.e. northeast c then north k; but the boxed sites materialize for trap 2 (boxes compare by ==), not for lack of a cutoff, so a richer offset type alone would not make them lazy.
- 2026-11-05: gardener: cites a file it shares with [[env-lookup-depth]] (`docs/surveys/segmap-survey.md`); [[open-payload-shift-copies]] (`docs/surveys/segmap-survey.md`); [[perf-dashboard]] (`perf/README.md`).
