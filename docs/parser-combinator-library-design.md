# A parser library with compositional contracts

Status: **implemented initial library**, 2026-09-14. See
`docs/parser-library.md` for the checked API, validation and explicit limits. Owner: `issues/parser-combinator-library.md`.

The signatures below are mathematical API sketches, not claimed to compile
as written. The proposal uses existing dependent records, type-valued
functions, checked recursion, and operation-indexed law classes. Surface
feasibility and proof-term costs must be established before freezing it.

## 1. The central split

Build an intrinsically input-safe parser with separately composable,
parser-indexed certificates for progress and meaning:

- A reply cannot invent a remainder or move a successful parse backwards.
- `Consumes(p, k)` proves a lower bound on consumption on every success.
- `Sound(p, R)` proves that successful values describe the consumed segment.
- Stronger certificates express completeness, determinism of a specification,
  and equivalence where a client actually needs those properties.

These are proofs about an operation, following the existing operation-indexed
class design. They are not unchecked flags attached to a parser and need not
be inferred by unrestricted proof search. Combinators provide constructors
for the relevant certificates; explicit certificate application is the
fallback when class inference cannot recover an index.

This gives ordinary parser composition a stable carrier type. It avoids
forcing clients to transport between `Parser(k + 0)` and `Parser(k)` simply
to state a monad law. Strong dependent guarantees remain available through
operation-indexed evidence and result families.

## 2. Input identity and positions

For the first implementation the source is an immutable `List<Token>`.
Every cursor is indexed by that same source:

```
Cursor(source) = { identity : source = source;
                   offset : Nat; within : offset <= length(source) }
remaining(c) = drop(source, c.offset)
Segment(source, start, end) = take(drop(source, start), end - start)
```

A success at cursor `start` returns `end : Cursor(source)`, a value, and
`start.offset <= end.offset`. The source index prevents mixing remainders
from different inputs; the ordered positions identify an actual suffix,
not merely another list whose length happens to be small enough.

Start/end cursors identify a consumed segment without allocating a prefix
list on every success. Clients may materialize the segment on demand.
Rebasing is composition of ordered cursor movement on the same source.
The library proves identity, transitivity, segment concatenation, and the
corresponding remainder laws once.

This is a logical model, not a decision to rescan a linked list from its
beginning at every token. A practical cursor may cache `rest` and carry a
coherence proof `rest = drop(source, offset)`. Advancing then takes the tail
in constant list-structural work. Prototype the cached representation and its
proof costs before selecting it. Do not claim proof erasure or constant
elaboration cost merely because a field is called a proof.

## 3. Replies: distinguish success, retry and commitment

Schematic core:

```
Parser(Token, A).run : (source) -> (start : Cursor(source)) -> Reply(start, A)

Reply(start, A) =
    Success(value : A, end : Cursor(source), forward : start <= end)
  | Failure(retry : Retry | Committed, diagnostic : Diagnostic(source))
```

A failure offers no success remainder. Its retry status says whether choice
may run another alternative at the original start. Its diagnostic carries a
valid source position, expected items, and context. The error position can
be ahead of the restored start after backtracking. These are separate facts.

Proposed observable semantics:

1. Token mismatch or end-of-input produces a retryable failure at the current
   cursor. Token recognition advances exactly one token on success.
2. Sequencing propagates the first failure. If its first parser advanced,
   any failure of the second is committed; an already committed failure
   remains committed even when no token was consumed.
3. `p.or(q)` returns a success or committed failure from `p` immediately.
   Only a retryable failure runs `q`, from the original start.
4. If both tried branches fail, retain the farther diagnostic. At equal
   positions combine expected items by a deterministic rule. The final
   retry status follows the executed alternative; diagnostic selection does
   not change whether the failure is committed.
5. `attempt(p)` makes failures retryable, retaining their diagnostic position.
   It leaves successes and their consumption unchanged. It is a deliberate
   backtracking boundary, including for commitment inside `p`.
6. `commit(p)` upgrades failures to committed. It is scoped; no persistent
   hidden cut flag travels through successful results.
7. `optional(p)` returns absence only for retryable failure. A consumed malformed
   construct remains an error. `many(p)` similarly stops only on retryable
   failure and propagates committed failure.
8. `lookAhead(p)` restores the start on success. It preserves failures and
   their retry status; use `attempt(lookAhead(p))` when failure should rewind.
   Its success meaning is about a witnessed inspected span, not a falsely
   claimed consumed span.
9. `eof` succeeds without movement exactly at the end. `complete(p)` sequences
   `p` with `eof` and projects the value.

For the calculator this means that after a recognized `+`, failure to parse
its right operand is a committed error, not a fallback to the left operand.
The same applies after an opening parenthesis. Preserve the existing public
error cases through an explicit diagnostic-to-`ParseError` adapter.

Expected-item merging also needs a concrete equality/order policy. Use stable
expectation identifiers initially; displaying or deduplicating arbitrary token
values must request the corresponding capability, not silently assume every
open token type has decidable equality. Context labels are explicitly supplied
by grammar authors rather than inferred from bind nesting.

Do not assert a commutative or distributive alternative algebra. Ordered
choice and commitment are observable. The core bind laws and any choice
laws must be proved against these exact reply and diagnostic semantics.

## 4. Progress as a quantitative certificate

```
Consumes(p, k) : every success from s to t has s.offset + k <= t.offset
```

Every parser has the zero certificate from its intrinsic forward evidence.
`Consumes(p, 1)` is sufficient for repetition. It says nothing about whether
`p` ever succeeds; an always-failing parser satisfies it vacuously, and its
repetition correctly produces an empty list.

Combinators construct certificates:

| Operation | Success lower bound |
|---|---|
| `pure`, `eof`, `optional`, `many`, `lookAhead` | 0 |
| token recognition | 1, with a stronger exact-consumption law |
| `map(p, f)` | the bound of `p` |
| `bind(p, q)` | `a + b` when `p` consumes at least `a` and every `q(x)` at least `b` |
| `p.or(q)` | `min(a, b)` |
| `attempt(p)`, `commit(p)` | the bound of `p` |
| `repeatN(n, p)` | `n * a` |
| `some(p)` | at least `a`, requiring positive progress for its repeated tail |

A dependent continuation may supply a stronger bound depending on its first
value; the uniform rule is a convenient specialization. Choice can likewise
have a stronger externally proved bound than the conservative minimum.

```
many(p) requires Consumes(p, 1) : Parser(Token, List<A>)
repeatN(n, p) : Parser(Token, Vec<A>(n))
```

Finite repetition needs no positive-progress premise: it recurses on `n`.
Unbounded repetition decreases the remaining input length using its
certificate. `many(pure(x))` is refused because its premise cannot be proved.
No run-time silent truncation and no user-declared unchecked "consuming" bit.

`many` also proves that its values and consumed span admit a partition into
successful iterations, and that it stopped at a retryable failure. Calling
that partition maximal requires a specification of the parser's ordered
operational behavior; it is not automatically longest-prefix recognition
for every language relation that happens to be sound for the parser.

## 5. Meaning and dependent results

Use a relation over a source span and value:

```
R(source, start, end, value) : Type
Sound(p, R) : every successful observation of p supplies R
```

A source-span relation can express context-sensitive checks. For a portable
grammar, specialize it to a relation `Language(segment, value)` which does
not inspect unrelated source positions. Keep that locality property explicit
when proving framing or independence from appended input.

The compositional rules mirror execution:

- Pure: empty segment and the given value.
- Token: singleton segment and the recognition predicate.
- Map: a witnessed original value satisfying `R`, with its mapped result.
- Bind: an intermediate cursor and first value, the first relation on the
  first span, and the value-dependent second relation on the second span.
- Choice: evidence of one of the successful branch relations. This soundness
  statement deliberately does not promise either branch will be tried.
- Many: an ordered sequence of adjacent spans and a derivation for each
  returned value. Repetition's progress proof excludes empty successful spans.

For successful outputs whose validity is essential to downstream code,
return the evidence as part of a dependent value. A `certify` adapter can
turn a parser plus a soundness certificate into a parser producing a value
and its specification witness. A separate certificate keeps the basic
executable representation from accumulating every possible proof at once.

Dependent bind should be a real primitive capability:

```
bindD : Parser(A) -> ((a : A) -> Parser(B(a))) -> Parser(Σ a:A. B(a))
```

Ordinary bind is the nondependent specialization followed by projection.
Examples include parsing a length followed by exactly that many elements,
an instruction whose operands depend on its opcode, or a well-scoped syntax
tree indexed by a parsed environment. The API need not reduce these to
unvalidated pairs plus later partial checks.

A parsed length cannot make invalid input well typed: the parser still fails
if it cannot construct the required vector or witness. Predicate refinement
also needs a checked decision procedure or explicit proof-producing parser;
arbitrary undecidable propositions are not magically executable.

## 6. Soundness, completeness and equivalence are different promises

Soundness alone is vacuous for an always-failing parser. For the calculator,
state an independent grammar relation fixing precedence, right association,
and parentheses, then prove success soundness. The existing compilation
agreement theorem remains useful but does not establish that grammar law.

Completeness must name both the grammar and the parsing policy. A relation
saying "there exists a derivation" does not make committed ordered choice
explore that derivation. Prove completeness for a grammar-directed parser
under suitable disjointness/lookahead conditions, or relative to an explicit
ordered recognition specification. Do not advertise completeness of arbitrary
`or` from completeness of its operands.

Use pointwise observational equivalence:

```
p ≈ q : for every source and start, observe(p.run(start)) = observe(q.run(start))
```

Observation includes value, end offset, and failures' retry status and
normalized diagnostics. It excludes internal coherence and termination
witnesses. This avoids assuming function extensionality or general equality
of proof-carrying records. A weaker recognition equivalence can intentionally
ignore diagnostics, but must have a different name.

Target laws: map identity/composition, bind units/associativity, preservation
of cursor movement by map, certificate weakening/composition, attempt
idempotence, and lookahead's zero movement. Prove rather than assume their
side conditions and diagnostic behavior. `p.or(q) ≈ q.or(p)` is generally false.

Ignoring internal witnesses creates a further proof obligation: a lawful
parser must respect cursor equivalence (same source/offset, potentially
different bounds or coherence proofs). Require or prove this respectfulness
for the combinators and any custom implementation admitted to the law-bearing
interface. Guarded builders likewise need an extensionality argument for
recursive continuations and their accessibility evidence. Arbitrary dependent
functions can inspect relevant witnesses; extensional behavior does not follow
merely by omitting those witnesses from `observe`. The existing checked
well-founded unfolding machinery is a precedent, not a substitute for this
library proof. When result values themselves carry relevant evidence, choose
and state the value equivalence as well; ordinary value equality is the default,
not an assumed theorem that all proofs are interchangeable.

Use ordinary extractable evidence for witnesses needed to compute or prove
termination. Do not squash the intermediate cursor of a bind derivation and
then assume it can be extracted into ordinary data. Irrelevant propositions
may be appropriate for selected transport/coherence fields only after their
elimination requirements have been checked against Heather's actual formers.

## 7. Total recursive grammars

Do not export an unrestricted fixed point on parsers. A success-progress
certificate cannot justify a call made before success, and does not rescue
left recursion.

The primitive guarded builder runs at a particular cursor and receives a
recursive continuation callable only at a strictly later cursor:

```
fix(body).run(start)
body(start, recur)
recur : (later : Cursor(source)) -> (start < later) -> Reply(later, A)
```

Its implementation uses checked well-founded recursion on remaining input.
Cursor-indexed sequencing exposes its intermediate cursor and movement
witness to the continuation. After a consuming token parser, it can produce
the strict evidence needed to call `recur`. Ordinary nonrecursive parsers
embed into this cursor-indexed layer; the common combinators should share
implementations rather than diverge into two semantics.

This is the important prototype: prove that a library-level builder and its
sequencing API can hide termination plumbing without pretending `recur` is
an unrestricted `Parser(A)`. Prototype mutual grammars using a family of
nonterminals and a lexicographic `(remaining input, precedence rank)` call
permission, or retain checked adjacent declarations initially. Same-position
calls must decrease rank; moving back to a higher rank requires consumption.

The calculator's expr/factor/atom organization is the acceptance example.
A later `chainRight1` can encapsulate its repeated right-associative pattern.
Left-recursive and ambiguous generalized parsing are separate designs; do
not introduce fuel into the public result or silently change the grammar to
make an unrestricted fixed point appear total.

## 8. Design prototypes before implementation is committed

1. Cursor/reply representation over an open token type. Prove suffix identity,
   composition and strict progress; reject an invented remainder. Compare
   derived and cached suffix representations.
2. Map and dependent bind. Prove pointwise laws on neutral inputs with
   dependent output types. Demonstrate parser-indexed certificate construction
   without assuming a general function-equality principle.
3. Failure/choice truth table: consuming failure, rewound failure with a
   farther error, equal-position expectation merging, explicit commitment,
   optional malformed constructs and lookahead. Pin observable behavior.
4. Prove `many` from `Consumes(p,1)` and finite `repeatN` without that premise.
   Accept a custom parser with separately proved progress; refuse nullable
   unbounded repetition.
5. Guarded recursion and calculator grammar relations. Preserve all existing
   AST/error examples and the compilation theorem; add grammar soundness.
   State completeness's scope separately before undertaking that proof.
6. Inspect checked term size and elaboration scaling for nested bind, nested
   parentheses, repeated spans, and certificate reuse. No baseline claims
   from flat token counts alone. Share named laws and avoid storing growing
   consumed-prefix lists or duplicated derivation trees in every result.

The first implementation round should be these cursor/reply/composition
prototypes. Freeze the executable representation and public recursive-builder
syntax only after those evidence and cost checks, then implement the wider
combinator collection and migrate the calculator.

## 9. First prototype findings (2026-09-14)

The initial cursor, dependent composition, observation laws, and single-source
guarded recursion now have a checked prototype in
`docs/showcase/parser_core.hthr`; see `docs/parser-core-prototype.md` for scope
and validation. One representation correction is essential: the offset/bound
fields alone did not distinguish equal-length sources. The prototype retains
source endpoints through an explicit `source = source` field. Cached suffixes
have a separate coherence proof. Failure policy, progress/semantic classes,
general respectfulness and composition cost scaling remain design/prototype
work; this result does not freeze the full API.


## 10. Library implementation (2026-09-14)

`lib/std/parser.hthr` and the component modules in
[`lib/std/parser/`](../lib/std/parser/README.md) now implement the combinator
collection, dependent bind,
operation-indexed `Consumes`/`Sound` certificates, committed diagnostics,
repetition, finite checked-length repetition, and guarded grammar helpers.
The calculator uses it and retains its prior AST/error/compiler equations.
The API guide records the intentional adaptations: explicit certificates,
`Counted(n)` lists for finite repetition, numeric diagnostic identifiers, and
derived source suffixes with a measured depth sweep. An independent calculator
grammar relation and cached-cursor optimization remain separately tracked;
no completeness or linear-runtime claim is made.


## 11. Independent calculator grammar (2026-09-15)

The calculator now specifies productions through a derivation tree, checked
precedence levels, structural spelling and AST interpretation. Certified
recursive results connect those productions to exact source suffixes. The
public parser projects ordinary successes, and its `Sound` certificate follows
from the stored evidence; `complete_sound` closes the final suffix. See
[the grammar proof](calculator-grammar-soundness.md) for the open-input theorem
and the remaining ergonomics work. Canonical printing has its own issue and
must establish acceptance of generated spellings by the actual parser.
