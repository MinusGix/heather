# Result propagation

`e?` extracts the success payload of `result::Result<A,E>` and propagates its
error from the nearest function or lambda. Ordinary nested blocks and match
arms are transparent. A successful body still writes `Ok(value)`. There is no
implicit wrapping or error conversion; use `map_err` explicitly when needed.

```heather
import result;
fn next(r: Result<Nat,Nat>) -> Result<Nat,Nat> {
    let n = r?;
    Ok(Succ(n))
}
```

The postfix `?` is attached to its operand. Prefix `?` and `?name` remain proof
goals, including in call arguments. `r??` unwraps two nested Results. Calls,
operators, field reads, indexing, collection/record values, local bindings,
and ordinary matches compose with propagation. Failure selects the first `?`
in written expression order; an unselected match arm does not propagate.
A lambda is a separate boundary even when it appears inside a larger function.

## Library and trust boundary

`lib/std/result.hthr` declares `Result<A,E> { Ok(value:A), Err(error:E) }`,
`map`, `and_then`, `map_err`, and `unwrap_or`. The module must be imported.
The parser lowers a value context `K[e?]` to
`result::and_then(e, λ value => K[value])`. `and_then` is an ordinary Heather
function defined by a match: the Ok arm calls the continuation and the Err
arm returns the same error. Ordinary elaboration therefore fixes both
carriers to Result and unifies the error types. Every generated term follows
the existing elaborator and kernel checker. No trusted rule, host exception,
or new kernel term is involved.

Written applications retain their argument structure and inference. Private
slots use the parser's shared fresh-name counter, including across nested
lambda boundaries. A continuation stays outside a nested written block or
match: that scope packages its success value in a local Result, and an outer
`and_then` propagates its error. This preserves lexical binding, field/method
resolution, and implicit-instance lookup without classifying bare patterns.
It is an implementation boundary; ordinary blocks do not catch errors.

A generated local success continuation uses `result::map` where its terminal
`Ok` can be stripped. When the callback's input domain is known but its result
type is not, the elaborator infers that generated callback's body, unifies the
result through the existing application solver, and subjects the resulting
application to ordinary checking. This fallback applies only to the parser's
unspellable propagation binders. Source lambdas keep their existing inference
policy. No scratch metavariable enters the callback's context: its input
domain must be fully solved first. The private-syntax guard runs before
substitution, so ordinary deferred arguments incur no new type traversal.

## Deliberate boundaries

- This slice implements Result propagation. Option propagation and a generic
  propagation protocol are separate decisions, not inferred from constructor
  spellings. `map_err` is explicit; there is no From-style error conversion.
- A non-tail match with a written dependent motive cannot simply reuse that
  motive after its continuation changes the result type. It is refused with
  a suggestion to use a Result-returning helper. Ordinary inferred motives
  and tail matches remain on the usual match elaboration path.
- Propagation is not a type-level operation or proof discharge. Direct `?`
  propagation in types, `on` proofs, meta-function bodies, or quotation is
  outside this slice. A lambda owns its own body boundary.
- This is syntactic continuation expansion. Non-tail written scopes keep
  their outer continuation separate; no general compiler-scaling claim is made.
  A shared typed continuation representation would need an elaborator-level
  design if a real client makes this cost material.

## Runnable customer and verification

`docs/showcase/result-parser.hthr` parses two natural-number tokens joined by
Plus. It uses a nested `parse_atom(parse_plus(left.rest)?)?` call, preserves
specific parse errors, and checks for trailing input. A second recursive
`collect` client stops at the first failing list element. Its handwritten-match
version remains as an equivalence reference; an open-input `refl` theorem
checks that both spellings compute identically. Closed equations exercise
success, empty input, wrong tokens, missing operands, and trailing input.

The acceptance target is `crates/elab/tests/result_propagation.rs`; it also
covers generic neutral inputs, nested Results, first-error order, unselected
branches, transparent blocks, lambda boundaries, and lexical scope.
Wrong result carriers, mismatched error types, and false equations must fail.

The parser-generated callback fallback is covered by the non-tail block and
shadowing examples: removing it leaves the callbacks deferred with an unknown
result type. Prefix proof goals also work inside a propagation continuation,
with their ordinary declaration-scoped `on` discharges.

Final validation: plain `scripts/test` reports **2,640 passed, 0 failed,
5 ignored**. The isolated kernel benchmark comparison retains 12 Nat timing
failures on unchanged kernel sources (`issues/kernel-benchmark-nat-baseline-drift.md`).
Tree-sitter's new fixtures and query checks pass; its whole-library scan
retains an independently reproduced pre-existing `match code` error
(`issues/tree-sitter-match-code-scrutinee.md`). Neither baseline was rewritten.
