# Parser components

[`../parser.hthr`](../parser.hthr) is the public interface: a facade that
reexports every operation, type, and certificate below. The implementation
and proofs are ordinary Heather modules in this directory:

| Module | Responsibility |
|---|---|
| `parser` (facade) | Reexports the components; declares nothing of its own |
| `parser_core` | Source-indexed cursors, replies, execution, observations, cursor laws |
| `parser_contracts` | `Post`, `Sound`, `Bound`, `Consumes`, `Certified`, evidence projection, and `CompleteSpec` |
| `parser_diagnostics` | Commitment, retry, expected-token merging, and their laws |
| `parser_combinators` | Pure values, mapping, dependent sequencing, choice, lookahead, and composition laws |
| `parser_primitives` | Recognition, tokens, end-of-input, complete parsing, and recognition/span proofs |
| `parser_recursion` | Guarded recursion and proofs for recursive continuations |
| `parser_repetition` | Consuming repetition and exact-count repetition, with progress evidence |

## Imports

Module names are flat file stems, so supply both `-L lib/std` and
`-L lib/std/parser`; the facade's export edges then find the components.
`import parser;` is the whole library. For example:

```heather
import parser;
import list;
import result;

fn next_number() -> Parser<Nat,Nat> {
    parser::token<Nat>(1).map(Succ)
}
theorem example(): parser::run(next_number(),[2]) = Ok<Nat,ErrorView>(3) {
    refl
}
```

When checking the standard-library directory itself, the CLI adds descendant
directories to that target's import search automatically, so the whole tree
is checked with simply `heather check lib/std`.

A reexport is the original declaration under a second visible path
(`docs/modules-design.md` §3.4): `parser::token` and
`parser_primitives::token` are one function, `parser::Consumes` and
`parser_contracts::Consumes` one class, and a certificate built through
either spelling is accepted by the other. A client may import a component
directly, alone or beside the facade, without ambiguity or conversions;
qualified use through the component still works. Axiom audits report the
component that owns a proof, not the facade.

## Dependency and proof boundaries

The core has no dependency on another parser component. Contracts depend only
on the core. Diagnostics depend on contracts and the core; combinators also
use diagnostics. Primitives, recursion, and repetition build on combinators
and the lower layers, without depending on one another.

General contract definitions belong in `parser_contracts`; rules establishing
those contracts for a particular operation belong beside that operation.
Recognition-specific relations and exact head/suffix witnesses live with
recognition. Cursor arithmetic and suffix laws stay with the cursor model.

`CompleteSpec` strengthens a successful parse with an empty remainder. It is
not a completeness theorem saying that every valid input is accepted.
General completeness, boundary-preservation contracts, and printer round-trip
contracts remain future work; this split adds no new semantic guarantees.

The shared fixture in `crates/elab/tests/support/parser.rs` loads these modules
in dependency order for the parser and calculator acceptance tests. The parser
tests check this fixture once per process, then fork independent clients from
its checked semantic image. Every client proof and refusal is still checked.
CLI users get the module order through ordinary imports.
