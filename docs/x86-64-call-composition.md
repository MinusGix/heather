# Straight-line source-call composition

`build-x86 file.hthr caller --callee leaf --arg A --arg B -o program`
accepts a bounded straight-line caller over two `BitVec(64)` inputs. The caller
can use `let` bindings, Add/Sub/AND/OR/XOR, `bitvec::ofNat(64, literal)`, and
calls to the explicitly selected arithmetic leaf. Either call argument may
be an expression, including an earlier call result. Original arguments and
intermediate values can remain live across calls.

For example, `examples/x86-native/composition.hthr` computes:

```heather
fn caller(left: BitVec(64), right: BitVec(64)) -> BitVec(64) {
    let saved = bitvec::bor(64, left, right);
    let first = leaf(right, left);
    let second = leaf(bitvec::add(64, first, right), bitvec::ofNat(64, 3));
    bitvec::bxor(64, saved, second)
}
```

With `leaf(a, b) = bitvec::sub(64, a, b)`, arguments 20 and 22 produce exit
status 3. Arguments 18446744073709551615 and 1 exercise wrapping arithmetic
and produce status 255.

## Selection and limits

Reflection uses resolved identities in the elaborated source, including
elaborated-away `let` bindings. It admits at most 64 expression nodes and four
call occurrences in that expanded expression. A repeatedly used binding can
therefore repeat its computation or call; this first selector does not provide
common-subexpression elimination. Calls are pure within the selected leaf
fragment, so this does not change the source result.

The selector evaluates binary expressions left to right. R14/R15 retain the
original inputs; RBX/RBP/R12/R13 provide four temporary registers. The leaf's
existing contract preserves all six. Values needed across calls stay in those
registers. RDI/RSI receive the selected argument values and RAX carries the
return. Excess register pressure produces an explicit unsupported-spilling
error. The existing 128-instruction executed-trace limit and final image bounds
also apply.

The entry-only caller reserves eight bytes for call alignment and restores RSP
before returning to the Linux entry fragment. Its temporary registers are not
saved for an external caller: this path does **not** export a reusable caller
ABI contract. The arithmetic leaf retains its generic native call contract.
General call graphs, recursive or indirect calls, branches in callers, caller
spills, and externally callable composed wrappers remain outside this profile.

The original forwarding, stack-local, and two-placement examples keep their
specialized lowering. They continue exercising stack-memory footprints and
relocation; the new general path calls one placed leaf fragment repeatedly.

## Checked boundary

One source theorem over arbitrary input words checks the reflected expression
against the actual caller definition. One generic callee summary carries the
existing source/refinement, return, RSP, memory-effect, and preserved-register
claims. Each call supplies its own checked valuation and input-register facts,
plus the fetched execution and access premises for the actual placed bytes.

The producer records known register values with named equalities. Ordinary
instructions transport those equalities through register updates and checked
arithmetic. At a call boundary it discards scratch-register knowledge and
recovers preserved registers and RAX through the callee contract. It does not
assume scratch values survive, or substitute host arithmetic for a proof.

The final source-result equality checks the computed value against the original
caller applied to the command-line arguments. That equality and the register
facts establish the Linux exit request. Fetched-trace composition, syscall
fetch, exact ELF bytes, stack-access permissions, alignment, and final RSP
restoration use the existing checked machinery. Linux loading and syscall
delivery retain the assumptions described in [the call profile](x86-64-calls.md).

The composed caller is certified for the selected executable arguments; it is
not a generic machine-level caller summary. The callee summary and the caller's
source-expression theorem are generic.

## Validation

`native_composition` builds and runs both input cases above with no external
toolchain, requiring one summary definition and two applications/compositions.
Focused controls reject a stale source expression, incorrect register evidence,
a non-selected callee, excess calls, and register pressure requiring spills.
Existing native tests retain byte, fetch, frame, and summary-interface refusal
coverage. The new executable test runs in the full test lane.

Final validation on 2026-09-19: plain `scripts/test` passed **2823 passed,
0 failed, 5 ignored**, including the existing native profiles and the promoted
20-node scaling gate. No kernel, proof-library, or resource-budget changes were
needed.
