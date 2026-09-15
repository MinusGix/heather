# Parser components

The core representation lives in [`../parser.hthr`](../parser.hthr). The
remaining components are ordinary Heather modules in this directory:

| Module | Responsibility |
|---|---|
| `parser` | Source-indexed cursors, replies, execution, observations, cursor laws |
| `parser_contracts` | `Post`, `Sound`, `Bound`, `Consumes`, `Certified`, evidence projection, and `CompleteSpec` |
| `parser_diagnostics` | Commitment, retry, expected-token merging, and their laws |
| `parser_combinators` | Pure values, mapping, dependent sequencing, choice, lookahead, and composition laws |
| `parser_primitives` | Recognition, tokens, end-of-input, complete parsing, and recognition/span proofs |
| `parser_recursion` | Guarded recursion and proofs for recursive continuations |
| `parser_repetition` | Consuming repetition and exact-count repetition, with progress evidence |

## Imports

Heather currently uses flat module names and has no reexports. Supply both
`-L lib/std` and `-L lib/std/parser`; import each component whose declarations
you use. Importing `parser` alone provides the core, not the full library.
For example:

```heather
import parser;
import parser_combinators;
import parser_primitives;
import list;
import result;

fn next_number() -> Parser<Nat,Nat> {
    parser_primitives::token<Nat>(1).map(Succ)
}
theorem example(): parser::run(next_number(),[2]) = Ok<Nat,ErrorView>(3) {
    refl
}
```

Receiver calls such as `.map` continue to work when their component is
imported. Qualified names use the component that owns the declaration:
`parser_primitives::token`, `parser_combinators::bind`, and
`parser_repetition::many`. No types or proof classes are duplicated for a
facade. A future module-reexport facility can restore a single umbrella import.

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
