# Checked parser combinators

Implementation: `lib/std/parser.hthr` is a facade that reexports the focused
components in [`lib/std/parser/`](../lib/std/parser/README.md). Use
`-L lib/std -L lib/std/parser` and `import parser;`; every operation, type
and certificate below is then `parser::name`, and the components stay
importable on their own with the same identities.
Examples and tests: `crates/elab/tests/parser_library.rs` and
`docs/showcase/calc_parser.hthr`.

## Core interface

`Parser<T,A>` holds a dependent `run` operation. On a particular source list
and starting cursor it returns either `Success<T,A>(source,begin)` or
`Failure<T>(source)`. A success contains a value, an ending cursor over the
same source, and a proof that the cursor did not move backwards.

`Cursor<T>(source)` contains an offset, its bound, and `source = source`.
That last field preserves actual source endpoints in the type: offset bounds
alone allowed equal-length sources to interchange in the prototype. It is
ordinary checked equality, not allocation identity or an axiom. The remaining
input is `drop(source,offset)`.

Use `parser::run(p, source)` to return just the value or a diagnostic. Use
`p.run(source,begin)` for a dependent reply, or `parser::observe` to compare
values, ending offsets, and diagnostics without comparing cursor/forward
witnesses. `complete(p, expected)` additionally requires end-of-input.

The library works over an open token type. Token recognition takes
`T -> Option<A>`, so it can simultaneously recognize and produce a value
without requiring a global token equality instance.

## Combinators

| Operation | Meaning |
|---|---|
| `pure(value)` / `fail(expected)` | Empty success / retryable failure |
| `token(expected)` | Accept one arbitrary token |
| `recognize(pick, expected)` | Accept a token when `pick` returns `Some` |
| `p.map(f)` | Transform a successful value |
| `p.bind(next)` | Value-dependent sequencing |
| `bindD(B, p, next)` | Return `Dep<A>(B)`, with a second value in `B(first)` |
| `p.then(q)` / `p.before(q)` | Sequence, retaining right / left value |
| `p.choice(q)` | Committed, ordered choice |
| `p.attempt()` / `p.commit()` | Permit retry / force commitment on failure |
| `p.optional()` | Absence on retryable failure |
| `p.lookahead()` | Restore cursor on success; preserve failures |
| `p.many(progress)` / `p.some(progress)` | Checked unbounded repetition |
| `repeatN(n, p)` | Finite repetition returning `Counted<A>(n)` |
| `eof(expected)` / `p.complete(expected)` | End-of-input checking |

The associated top-level function spellings remain available. `Counted<A>(n)`
contains a list and a proof that its length is exactly `n`; finite repetition
also works for empty-success parsers. This representation uses the existing
list laws rather than introducing a second vector implementation.

For example, the acceptance suite checks these ordinary compositions:

```heather
parser::token<Nat>(1).map(Succ).before(parser::eof<Nat>(99))
parser::many(parser::token<Nat>(1), parser::token_consumes<Nat>(1))
parser::repeatN(3, parser::pure<Nat,Nat>(7))
```

## Progress certificates

`Consumes<T,A>(p,k)` is an operation-indexed class proving that every successful
run advances by at least `k`. Certificates are first-class values supplied
explicitly to repetition; the interface does not depend on speculative global
instance search.

- `recognize_consumes` and `token_consumes` establish one-token progress.
- `map_consumes`, `attempt_consumes`, and `commit_consumes` preserve a bound.
- `bind_consumes` adds the first bound to a uniform continuation bound.
- `weaken_consumes` lowers a bound using checked natural-number ordering.
- `choice_consumes` preserves a bound shared by both alternatives.
- `consumes_zero` uses the intrinsic forward witness for any parser.
- `some_consumes` proves positive progress for one-or-more repetition.
- `fail_consumes` establishes any bound vacuously for an always-failing parser.

`many` requires the one-token certificate. A custom operation can supply its
own proof; a nullable parser cannot merely borrow another operation's proof.
The suite rejects both `many(pure(...), token_consumes(...))` and the analogous
attempt to repeat lookahead. Internally the certificate supplies the strict
offset increase, a checked list lemma converts it to a decrease in remaining
input, and ordinary well-founded lowering validates the recursion.

## Failure and diagnostics

`Failure(source)` retains a valid source cursor, expected-item identifiers,
and `Retryable` or `Committed`. Public `ErrorView` replaces the cursor by its
token offset. Expected identifiers are `Nat`; a grammar owns their meanings
and any presentation adapter. No string lexer, character-position mapping,
or implicit context-label stack is included.

- A mismatch and end-of-input are retryable at the attempted position.
- Sequencing commits a later failure if its prefix consumed input.
- Choice runs its right alternative at the original cursor only when the
  left failure was retryable.
- If both tried alternatives fail, the farther diagnostic wins. On ties,
  expected identifiers merge in stable left-to-right order, suppressing newly
  introduced duplicates. The final retry status comes from the right branch,
  independently of which diagnostic is retained.
- `attempt` restores retry permission while retaining the farther error.
- `commit` upgrades failures; it creates no persistent hidden success flag.
- `optional` and `many` propagate committed failures. They do not hide a
  malformed consumed construct.
- Lookahead restores the cursor on success and preserves failure commitment.
  Use `attempt(lookahead(p))` for retryable lookahead failure.

These are executable semantics, covered by positive and negative controls.
The calculator maps diagnostic identifiers back to its existing `ParseError`
constructors, preserving all prior error examples.

## Behavioral proofs

`Sound<T,A>(p,R)` proves a source-span postcondition for every success:
`R(source, begin, end, value)`. It makes no promise that the parser succeeds.

- `pure_sound` proves empty-span identity and the returned value.
- `recognize_sound` proves exactly one-token movement and that recognition of
  the actual input head selected the returned value.
- `map_sound` transports a postcondition through a proved value transformation.
- `bind_sound` composes two postconditions through an intermediate cursor and
  a value-dependent continuation.
- `choice_sound` preserves a postcondition shared by both alternatives.
- `certify_at` returns successful data together with the postcondition witness;
  `Certified` exposes `value`, `end`, `forward`, and `evidence` directly.
- `recognize_certified` packages token recognition with its certificate.
- `recognized_head` supplies the selected head token and exact suffix boundary.
- `forget_post` exposes internally constructed evidence as a `Sound` law;
  `certified_map_at` and `certified_finish_at` compose such replies with checked
  laws relating their projections to ordinary map/rebase.
- `complete_sound` preserves a postcondition and adds an empty final remainder.

The library also proves observational map identity/composition, bind units and
associativity **including commitment**, attempt idempotence, lookahead's zero
movement, identity remainder, and suffix composition (`drop_add`). Bind's laws
are for parser-valued continuations; they do not assert equivalence of arbitrary
low-level callbacks that inspect relevant movement witnesses.

Observation omits internal cursor and forward proofs. A value type `A` can
itself contain proofs, as `Counted` and `Dep` do: choose a value projection when
comparing their data if equality of those relevant proofs is not intended.
No general proof irrelevance or function extensionality is assumed.

The calculator additionally instantiates these tools with an independent
production grammar and an open-input success theorem. See
[Calculator grammar soundness](calculator-grammar-soundness.md). No general
completeness theorem for ordered choice is claimed.

## Recursive grammars and the calculator

`guarded` provides a recursive capability callable only at a strictly later
cursor. It is an ordinary library function checked through well-founded
recursion, not an unrestricted fixed point or a public fuel parameter.

`after_at` exposes the decrease supplied by a consuming prefix. `extend_at`
handles an optional consuming operator and its recursive right-hand parser.
Both own the cursor-rebasing arithmetic. `bind_at` and `or_at` compose replies
at a fixed source/cursor, including deferred alternatives.

The calculator constructs independent grammar evidence in nonrecursive
production bodies, with three adjacent checked recursive functions supplying
the recursive capabilities. Same-position calls go forward through the mutual
group's ranks; back edges require library-proved decrease in remaining input.
`parse_expr`, `parse_factor`, and `parse_atom` project ordinary replies from
those certified results. The public `parse` entry point completes `grammar()`.
Its precedence, right association, parentheses, error cases, and open-input
compilation agreement are preserved. `parse_sound` proves that every success
has a well-formed derivation spelling exactly the supplied tokens.

The production proofs currently need explicit cursor/certificate composition.
[Certificate ergonomics](../issues/parser-certificate-ergonomics.md) owns the
follow-up improvement, using this proof as its client.

## Representation and cost evidence

The first implementation uses derived suffixes. It can rescan prefixes, and
it is not advertised as linear time on long linked-list input. Source checking
and future extracted execution must be measured separately; proof erasure has
not been assumed. `CachedCursor` remains an explicitly checked alternative
representation for subsequent optimization, tracked in
`issues/parser-cached-cursor-cost.md`.

The reproducible smoke sweep is:

```
scripts/test --fast -p heather-elab --test showcase_calculator -- --nocapture
```

`check_nested_parser_costs` reuses the checked calculator image, checks each
generated result, then reports
single-worker evaluator steps and serialized checked-delta bytes. Delta bytes
include syntax and registry metadata as well as proofs: this is a growth proxy,
not a claim to count proof nodes exactly. The measurements exclude loading the
library/calculator and cover depths 1, 2, 4 and 8, not just flat token counts.

The following measurements are the **2026-09-14 initial parser**, before the
proof-carrying calculator migration. They are retained as historical evidence;
the sweep runs against the current source when invoked.

| Depth | Nested composition bytes | Eval steps | Parentheses bytes | Eval steps |
|---:|---:|---:|---:|---:|
| 1 | 26,377 | 827 | 8,766 | 2,562 |
| 2 | 52,918 | 1,009 | 10,995 | 4,006 |
| 4 | 105,896 | 1,446 | 15,453 | 7,785 |
| 8 | 211,852 | 2,644 | 24,369 | 18,907 |

Observed checked-delta growth is approximately linear in this sweep.
Parenthesis evaluator work is superlinear, consistent with repeated list
traversal. This is bounded evidence for the selected initial implementation,
not a universal complexity proof or a long-input performance guarantee.

## Validation

Current focused library/calculator acceptance: **5 passed, 0 failed**. The
source module contains the open-input laws; Rust acceptance adds generic
clients, error-policy cases, false-certificate and source-forgery controls,
independent grammar witnesses/refusals, axiom audits, and the depth sweep.
The depth sweep now shares the calculator fixture's checked image: all depth
cases remain, with one fewer Rust test function than the initial library run.
The initial prototype remains a separately checked artifact.

Full `scripts/test`: **2672 passed, 0 failed, 5 ignored** (2026-09-15).
Tracker and whitespace checks pass.
