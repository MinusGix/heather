# Reusable composed-function summaries

> **Burned in B2 (2026-10-24).** The code this document describes was deleted with the
> per-function certificate path (`docs/native-program-logic-design.md` §3.2); `compile-x86`
> compiles through the verified lowering instead (`issues/function-ir-verified-lowering.md`).
> The document stays for its reasoning. The last commit with the code is `82521eab`.

`build-x86 --callable-caller` adds a reusable native summary for a composed
source function. The executable entry calls that function, which calls the
explicitly selected arithmetic leaf. The outer entry consumes the composed
summary's result contract when proving its Linux exit request.

```sh
cargo build -p heather-cli
(ulimit -v 6291456 -t 300; target/debug/heather build-x86 \
  examples/x86-native/composition.hthr caller --callee leaf --callable-caller \
  --arg 20 --arg 22 -o target/x86-native/callable \
  --cache-dir target/native-images)
./target/x86-native/callable
printf 'exit status: %s\n' "$?"
```

The example exits 3. Inputs 18446744073709551615 and 1 exercise full-width
wrapping and exit 255. Output paths must be fresh, as for the other native
commands. `--callable-caller` requires an explicit `--callee`.

## Register and stack profile

The leaf selector uses RAX, R11, R10, R9, R8, RCX, and RDX in that order.
The caller derives the leaf's actual destination-register set and first reserves
untouched scratch registers for live values. Two hold the original
inputs; the remainder hold shared expression results. A RAX-only leaf leaves
four caller temporaries; a leaf that also writes R11 leaves three. Each
retained scratch-register equality is checked against the actual leaf states.
RBX, RBP, and R12–R15 are untouched by either function and covered by the
composed function's native ABI contract.

Shared values and call results are selected once, with last-use tracking.
The bounds are four distinct calls, 64 expanded source-expression nodes, and
128 executed instructions. If the untouched scratch pool cannot hold the
inputs and live values, selection retries with progressively larger subsets of
leaf-clobbered scratch registers. Only values that remain live across a call
are saved and restored, each in a distinct caller-owned word. The frame is sized
from the maximum simultaneous save count, with padding for call alignment.
Demands beyond six scratch registers still require general expression spilling;
ABI-preserved register allocation remains future work. The entry-only composition path is
also available without the flag and retains its six callee-preserved registers.

`examples/x86-native/sharing.hthr` reuses both arithmetic and call results,
selects two distinct calls, and exits 50 for arguments 20 and 22.
`examples/x86-native/multi_register.hthr` keeps a value live across a leaf
requiring RAX and R11 and exits 108 for the same inputs.

`examples/x86-native/stack_save.hthr` requires a borrowed R11 value to survive
two leaf calls. It saves and restores that live value around each call using
the same checked slot, with different values stored before the two calls;
arguments 20 and 22 produce status 88, while
18446744073709551615 and 1 produce status 4.

`examples/x86-native/multi_stack_save.hthr` keeps R10 and R11 live across a
leaf call. Its two saved words share a 24-byte frame with one padding word;
arguments 20 and 22 produce status 66, while
18446744073709551615 and 1 produce status 253.

The summary's entry template is:

```text
MachineState(write_gpr(Rsp, 0x401ff8, gprs), flags, rip, memory)
```

Its parameters are arbitrary `gprs`, `flags`, `rip`, and `memory`; in particular,
input words and incoming ABI-register values are neutral, not command-line
literals. `requires(before)` is equality to this template. This records the
fixed stack profile honestly: it is not a summary for arbitrary incoming RSP.
The entry's real CALL supplies exactly this normalized register shape.

The composed function reserves an odd number of eight-byte words, keeping the
child call base 16-byte aligned. With no saves or one save, the frame is eight
bytes and the child return word starts at 0x401fe8. With two simultaneous saves,
the frame is 24 bytes: saved words start at 0x401fe0 and 0x401fe8, padding at
0x401ff0, and the child return word at 0x401fd8. Slot access walks RSP in checked
eight-byte steps and returns it to the call base before each child call.
The function restores its incoming stack position before RET; its post-return
RSP is 0x402000. Its memory footprint is the union of actual saved words and
child return words, excluding untouched padding. The parent's return word at
0x401ff8–0x401fff remains protected. Stack contents and file contents at entry
are otherwise arbitrary. Access, capacity, canonical-address, and fetch
premises are still required when applying the summary to an execution.

## How the proof composes

The emitted `*_composed_summary(gprs, flags, memory, rip)` is a `CallSummary`
indexed by the exact executed instruction list and `*_composed_post`.
The list includes the child calls and the leaf instruction segments in execution
order. It is an execution trace, not a contiguous static byte fragment.
Before checking the states, the generator checks each suffix of this declared
list against the expected next instruction and checks its exact end. A stale
instruction fails at `*_composed_instruction_N` under default fuel, before
whole-execution conversion at the final summary.

The generic proof carries named register equalities through caller instructions.
At each child boundary it uses the existing leaf summary to recover the leaf's
source result, native preserved registers, memory effect, and restored RSP.
A generic valuation uses `ofNat_toNat` to supply arbitrary width-64 input words;
there is no assumption that these words evaluate to literals. Reserved scratch
registers have separately checked implementation-specific preservation facts.
These are small generic proofs over an arbitrary leaf-entry state; each call
instantiates them instead of reducing the preceding caller's entire state.

The composed postcondition contains:

- The result of the actual source caller on its incoming RDI/RSI values.
- Return to the word originally stored at the incoming RSP.
- The native post-RET RSP relation and preservation of RBX/RBP/R12–R15.
- `WritesOnly` for the child return-word footprint, unioned with the caller's
  save words when present, observed through the stack byte reader; file contents
  remain unchanged.

Word-write effects compose across child calls. A checked word-disjointness
witness and byte-read equalities protect the original return word. The
source-expression theorem connects the symbolic result to the caller definition.

Saving checks the selected register and RSP against the exact byte-store model.
Eight checked reads and the word roundtrip theorem reconstruct arbitrary saved
words over neutral incoming memory. Each live saved-word equality is carried through
writes to other slots and the child CALL using checked byte-disjointness, and
through the leaf using its memory-effect contract. A restore transports that equality through the actual
load and register update. Contents of the dead save slot may remain changed;
restoring the register and RSP does not claim to restore all memory bytes.
Named instruction equalities also catch stale save/restore operands before
comparing whole memory values.

The concrete executable supplies `CallPremises` for the composed stream using
actual byte fetches, access proofs, and canonical successor equalities.
`use_call_summary` yields the caller's execution and postcondition, and the
entry appends that execution to its trace. The final exit proof uses
`*_caller_contract.result_correct`; it no longer closes a separate
concrete-input caller-result theorem. No new kernel rule or axiom is added.

The restricted summary can be instantiated with different argument words,
register values, flags, and memory. More stack positions or deeper source call
graphs require further frame work. It is not a SysV adapter or an external
object-file export. Linux loading and syscall-delivery assumptions remain those
of [the original call profile](x86-64-calls.md).

## Validation and follow-ups

`native_callable` checks and executes the ordinary and wrapping examples, with
one composed-summary definition, two leaf-summary applications, and one outer
summary application. The generic test checks neutral registers and memory,
rejects stale code and postcondition interfaces, refuses a missing entry
condition, and rejects a canonical step that clobbers RBX under stale facts.
Shared-value and multi-register fixtures also check generic neutral-state
summaries and execute their ELF images. `native_stack_save` checks ordinary
and wrapping inputs with two checked save/restore pairs reusing one word.
`native_multi_stack_save` checks two simultaneously live saved words on ordinary
and wrapping inputs. The neutral-state tests additionally reject wrong save and
restore registers, missing restores, overlapping slots, and incomplete write
footprints. Mutation controls inject an unreported
clobber of a live caller register and require a type mismatch. The declared-code
mutation leaves all state definitions and proofs unchanged and must fail at
its precise instruction-index theorem.

The completed sharing and local-refusal work is recorded in
[caller value sharing](../issues/x86-caller-value-sharing.md) and
[local code diagnostics](../issues/x86-composed-summary-refusal-fuel.md).
[Checked saves](../issues/x86-composed-caller-register-saves.md) cover the
original one-slot profile. [Multiple save slots](../issues/x86-composed-caller-multi-slot-spills.md)
records the frame allocation and simultaneous-save extension. The proof-library definitions, kernel rules, and resource limits are unchanged.

Final validation on 2026-09-19: plain `scripts/test` passed **2832 passed,
0 failed, 5 ignored**, including simultaneous-save native execution on ordinary
and wrapping inputs and neutral-state acceptance/refusal controls. Checking
budgets remain unchanged. The CLI unit target used 277.0 CPU-seconds of its
300-second limit; [test CPU headroom](../issues/x86-composed-summary-test-cpu-margin.md)
tracks further reductions in repeated checking.
