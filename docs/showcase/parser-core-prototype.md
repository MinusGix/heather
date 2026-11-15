# Parser core: first checked prototype

Implementation: `docs/showcase/parser_core.hthr`.
Acceptance: `crates/elab/tests/parser_core.rs`.
Design owner: `issues/parser-combinator-library.md`.

## What is checked

The prototype is ordinary Heather source; it adds no compiler or kernel rule.
It provides source-indexed cursors, forward-only successful replies, a parser
record with a dependent `run` field, pure/map/bind, a genuinely dependent bind,
and a cursor-indexed sequencing form that exposes movement to its continuation.

`Dep<A>(B)` packages a first value and a second value in its dependent family.
`token_with_proof` recognizes an arbitrary open token and constructs evidence
indexed by that recognized value, using dependent bind. It does not rely on a
closed `Nat` example for the dependent output's well-formedness.

Checked laws include map identity/composition, bind left/right units and
associativity, observation-preserving rebasing, rebase associativity, initial
remainder identity, and cached/derived remainder coherence. These quantify
over open sources, arbitrary replies (including errors), and open value types.
The bind associativity law uses ordinary parser-valued continuations; it does
not claim that arbitrary callbacks inspecting forward-proof terms are
observationally interchangeable.

`guarded` gives its body a recursive capability accepting only a strictly
later cursor. `drop_length_strict` derives the corresponding decrease in
remaining input; the named recursive discharge uses that checked lemma.
The client `count_body` supplies only offset progress. Empty-input and
open-element two-token equations check the generated recursion's computation.
`token_at` also has an open-element value/ending-position equation.

## Finding: an index name does not preserve source identity by itself

The initial record contained only an offset and a proof that the offset was
within the source length. A negative test showed that `start([2])` could
inhabit `Cursor([1])`: those fields have the same types after their equal
lengths compute. Merely writing a source value parameter did not prevent
that conversion.

The checked representation adds `identity: source = source`. This field
retains the actual endpoints in the record's type, and the same negative test
now rejects source substitution. Constructors discharge it with `refl`.
This distinguishes logical source values, not allocation identity; definitionally
equal sources remain interchangeable. It is an ordinary relevant equality
field, not a new nominal primitive or an assumption of proof irrelevance.

Cached cursors additionally carry a suffix and equality to `rest(source,cursor)`.
The suite refuses a fabricated cached suffix even when its length is correct.
It also refuses an out-of-bounds cursor, backwards success, same-cursor
recursion, an invalid dependent witness, and an incorrect counting equation.
A clean declaration after the negative cases checks session recovery.

## Representation and proof costs

The derived cursor computes its suffix with `drop(source, offset)`. Repeated
token stepping through this representation rescans prefixes at the source
level. The cached representation advances its stored suffix by one list step;
`advance_cached` proves coherence using `drop_succ`. Its theorem checks
agreement on an open source and open cursor.

This does **not** establish linear end-to-end execution or elaboration:
coherence proofs still traverse source structure, order decisions examine
bounds, and no native representation or erasure policy has been selected.
The parser record currently uses derived cursors; cached cursors are an
alternative representation probe, not an advertised performance optimization
of the parser implementation. A nested composition/cached-stepping cost probe
remains necessary before freezing the representation.

A direct nested-match proof of bind associativity was refused by the kernel.
Factoring the argument through `rebase_associativity` and `bind_rebase` gives
an accepted open-input proof. The library should expose those smaller movement
laws rather than require clients to reconstruct nested dependent matches.
No compiler workaround or unchecked axiom was added.

## Deliberate prototype boundary

Failures currently carry a `Nat` placeholder. There is no choice, commitment,
backtracking, or diagnostic policy in this core probe, so its equations do not
establish laws for the richer reply semantics proposed in the design.

The prototype also does not yet implement `Consumes`, `Sound`, unbounded
repetition, a general witness-respectfulness certificate, mutual precedence
ranks, or a calculator migration. The recursive builder is checked for one
nonterminal over one fixed source. These remain subsequent library work;
the public API is not frozen.

## Validation

Focused `scripts/test --fast -p heather-elab --test parser_core`: **2 passed**.
The two Rust tests check the source module's definitions and theorems, then
exercise seven invalid programs and recovery. Timing is not an acceptance
threshold. Full `scripts/test`: **2668 passed, 0 failed, 5 ignored**.
Tracker and whitespace checks pass.
