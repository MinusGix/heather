---
title: Say which let multiplies a slow proof, and suggest have
status: open
labels: [elaboration,diagnostics,proofs,performance]
area: language
created: 2026-09-25
updated: 2026-09-28
---

When a proof checks slowly because a shared `let` is traversed along many
paths through its term, nothing says so. The 216 s `read_print_after_read` was found by
bisection ([[proof-let-substitution-cost]]). `have` (docs/have-design.md) is
the fix a person can apply, but only once they know which let to apply it
to.

## Proposal

After an item elaborates, compare its term's tree size with its shared size.
Both are cheap: a pointer set for the shared size, memoized counting for the
tree size. When the ratio is large, report the `let` that contributes the
most duplicated work. A neutral application (a theorem call, or a field of
a parameter) is a useful candidate for `have`, but neutrality does not prove
that hiding its value preserves checking: later conversion can rely on the
alias being equal to the same application. In the print proof the verified
candidates are `w`, `st`, `ln` and `counted` (the anchor issue's 2026-09-25
table).

Open: whether this is a warning on every check or a `check --review` lint
(it adds a walk per item). The rule for lints that re-elaborate does not
apply; this one only walks the finished term.

## Acceptance

- The unsplit print proof, written with `let`s, names at least one of those
  four lets.
- No report on the library as it stands, or each report is a real candidate.
- Neutral applications whose alias identity is used by a later `refl` do
  not receive an unverified automatic fix.
- Analysis is bounded by the shared graph, not its expanded tree; names and
  source spans survive shadowing, uses under binders, and declaration retry.

## Log

- 2026-09-28: Investigation at `3b3817aa`; no compiler change. Recommended
  first delivery: an opt-in structural report through `check --review`, with
  conditional advice. Promotion to a default warning needs library-wide
  precision and overhead evidence. This walk does not re-elaborate, so the
  existing rule about expensive recognizers does not itself decide the tier.

### Neutrality is a ranking hint, not a safety proof

Two small probes were checked with the existing release CLI, kernel width
one and the repository's memory/CPU/core limits. Both `let` variants check;
both `have` variants fail with `NotConvertible` at the final `refl`:

```text
fn consume(x, y: Nat, p: x = y) -> Nat { x }
fn demo(f: Nat → Nat, n: Nat) -> Nat {
    let x = f(n);
    consume(x, f(n), refl)
}
```

The same counterexample applies to an opaque theorem, not just a parameter:

```text
theorem refl_at(n: Nat): n = n { refl }
fn consume(n: Nat, p, q: (n = n), e: (p = q)) -> Nat { n }
fn demo(n: Nat) -> Nat {
    let p = refl_at(n);
    consume(n, p, refl_at(n), refl)
}
```

Neither value has a reduct to lose. What disappears is the definitional
identity between the alias and its right-hand side. Therefore say “consider
`have` if later proofs do not need this binding's value”; do not claim that
neutrality alone licenses a fix. A checked rewrite can establish that an
individual suggestion preserves checking, but it is a separate, bounded
review probe, not part of the cheap structural analysis. Reuse the existing
transactional speculation discipline and suppress recursive lint probes.

### Count paths without expanding them

Build a graph of the finished declaration's body and statement, including
terms inside types, application annotations, substitutions, local contexts,
motives and branches. Give term and type allocations separate identity
namespaces. Do not descend into referenced global bodies: the question is
the syntax this declaration hands to the gate. Count repeated child edges
with their multiplicity, even when they point to the same allocation.

An iterative postorder gives expanded subtree sizes
`S(v) = 1 + sum(S(child))`. Reverse postorder propagates root-to-node path
counts `P(child) += P(parent)` once per child edge. Unique reachable nodes
give the shared size. Both passes cost O(V + E) with a per-declaration memo,
even when the expanded tree is exponential. Use saturating counts, explicit
node/edge limits and a completeness flag; saturation must not wrap or be
presented as an exact estimate. Avoid recursive traversal on unbounded depth.

The tree/shared ratio is a screening signal. Require substantial absolute
duplicated mass too: repeated tiny leaves and common annotation allocations
are ordinary sharing, not necessarily a useful source rewrite. For a
binding represented as an origin boundary, `(P - 1) * S` estimates repeated
subtree work. Rank by that burden, not `P` alone. Candidate scores overlap
along a chain, so do not add them or present them as predicted savings.
`have` also adds binder/application annotations and retains its value's
check; a counterfactual structural cut or a checked source rewrite is needed
to estimate its actual benefit. Structural counts do not predict reduction
cost or future kernel memo hits.

Do not reuse `module_image::term_image_nodes` / `type_image_nodes`: they
serialize into a `Writer` to count, traversing the expanded tree and building
its bytes. `emission_walk` is also a tree walker and deliberately skips some
substructure. They are references for variant coverage, not suitable engines
for this diagnostic.

### Source attribution is the first implementation spike

`statements::elaborate_let` creates `Alias` with name, depth and term, but no
source span. The alias is gone from the finished kernel syntax. Moreover,
`lib.rs::resolve` returns an owned `Term`, and `shift_local(0)` shallow-clones
that root: its child allocations remain shared, but its original root
address is not a reliable marker for uses. Nonzero shifts can rebuild the
children too. Goal filling and emission happen before `gate_bodied` and can
change allocations again. Merely mapping `Alias.term` pointers back to names
will miss candidates, including uses under binders.

Record stable binding IDs and written spans in declaration-attempt state.
Prototype a resolved source dependency graph to explain multiplication
across named lets, alongside the actual emitted graph that measures syntax
growth. Source dependencies must respect lexical binding identity and
shadowing; raw name counts or raw lookup counts include dead/speculative
work and are insufficient. The spike must establish how surviving use
origins propagate through shallow root clones, shifts and goal substitution
before claiming exact per-let attribution. A source-only graph can rank
heuristically, but cannot account exactly for inserted type annotations.

Keep tracking opt-in initially. Clear it on retry and completion with
`DeclAttempt`; speculative/generated bindings must not leak findings. The
emitted pair is available immediately before `gate_bodied`, including theorem
proofs that will subsequently be discarded. Stage lint findings there and
publish through the existing success/parallel-pass transaction. An optional
debug report can be available before a slow or fuel-exhausted gate, but must
remain distinct from a successful-item warning. Cache replay should preserve
the chosen activation policy; confirm that a prior non-review cached slice
does not silently defeat a later review request.

### Validation method

Start with deterministic counts and candidate names rather than timing:

- `lin` versus `fan` at growing depth; repeated expensive values without a
  multiplying chain; and an unreachable let chain.
- `have` barriers, transparent `dep`, both neutral counterexamples above,
  shadowed names, open values reused beneath a lambda, and annotations that
  mention the aliases.
- Retry, failed/generated declaration suppression, cache/review transitions,
  saturation, and identical results at worker widths one and eight.
- Restore the unsplit print proof as a durable fixture; the anchor issue's
  synthetic generator and original unsplit experiment were not committed.
  Pin a finding on at least one of `w`, `st`, `ln`, `counted`, then verify
  each proposed rewrite by checking it. Sweep the current library and inspect
  every finding before selecting thresholds.

Use `scripts/perf ab` for enabled/disabled analyzer overhead, and its
`--source-patch` mode for any claimed benefit from replacing selected lets.
Use `scripts/timings` for counter attribution, consistent kernel width, and
`--cache --only` to force source elaboration of a target over a replayed
prefix. A warm check that replays the target is not an analyzer measurement.
The existing `have.rs` fan-out test supplies a useful exact-counter control.
No full suite was run for this issue-only investigation; the probes establish
the safety counterexamples, not diagnostic precision or performance.

### Library candidates checked on 2026-09-28

The follow-up source round found useful candidates in the current, already
split library. Changed `ran` in `elf64_read_loop::eof_counts`, the two `back`
results in `elf64_read_loop::eof_from`, and `w`, `st`, `ln` in
`elf64_read_print::print_formats` to `have`. Their projected state aliases
remain `let`; later proofs still see those definitions.

Measured with `scripts/perf ab --source-patch`, the existing release binary,
kernel width one, and current source copies under the architecture modules'
public import names. The initial four candidates were measured with three
interleaved cold pairs; the final six-edit patch with two pairs. Each side's
counts reproduced exactly across its final samples:

| Item | Queries before → after | Misses before → after | Evaluator steps before → after |
|---|---:|---:|---:|
| `eof_counts` | 54,255 → 10,964 | 9,453 → 815 | 1,018,503 → 52,161 |
| `print_formats` | 22,078 → 3,624 | 7,354 → 677 | 724,825 → 37,392 |
| `eof_from` | 211,379 → 96,915 | 63,463 → 14,332 | 16,200,341 → 900,034 |

The experiment also tried `formatted` in `eof_print_tail`: queries rose
1,090 → 1,196 while evaluator steps fell only 9,984 → 9,665. That edit was
dropped. The initial `eof_counts` and `print_formats` gate medians fell about
95% and 93%, respectively, with disjoint sample ranges; whole-module wall
samples still overlapped because the untouched `eof_from` dominated that
check. Its repeatedly projected `eof_chunk` / `eof_retry` theorem results
were the next candidates. The final A/B overlapped a focused test rerun and
reported high host load; use its exact counters as the result, not a timing
claim. Final raw tables and the replayable report are under `target/perf-ab/`
(not committed).

All candidates passed source checking. The full suite on the initial four
edits reached 3,054 passed before `read_loop_process` hit its CPU rail; an
isolated rerun of that version hit the same rail. No assertion failure was
reported. The two additional `back` changes address the unchanged expensive
proof those checks kept revisiting. Final plain full `scripts/test` on all
six edits: **3,057 passed, 0 failed, 5 ignored**. Both read-loop and read/print
mutation-control targets passed; the read-loop process used 134 CPU seconds,
within its 300-second rail. `git diff --check` and `scripts/issue check`
passed (the tracker reports one unrelated pre-existing status warning).
This is a manual library improvement, not an implementation of the diagnostic
or a library-wide precision sweep.
