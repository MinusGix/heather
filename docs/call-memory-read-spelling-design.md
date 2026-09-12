# Reading a stack byte without reading the file — design

Deliberate perf round on `issues/function-ir-x86-proof-scaling.md`'s K2 lever,
2026-09-12, design pass. Workload: the generated call certificate
`heather build-x86 examples/x86-native/reused_callee.hthr caller --callee leaf
--arg 21 --arg 1`, release, furnace, `--kernel-workers 1`, item timings with
the conversion-miss sidecar.

The charter was "fewer, cheaper closed 64-bit bitvector compares per memory
read", with three hypotheses. The measurement moved the answer off all three
of them and onto a fourth thing that no one had looked at: **the certificate's
eight most expensive theorems do not spend their time comparing bitvectors at
all — they spend it walking the 399-byte ELF file list, six times each,
because `call_memory_read` consults the file before the stack and the stack
page lies inside the file's own 64-KiB address window.** The fix is a spelling
change of the callee contract's observation, and the two hypotheses about
bitvector compares are refuted with numbers in §5 and §6.

## 1. The before column

Release build with `--features value-metrics`, one kernel worker, furnace
instance of 2026-09-12; every number in this document is from that instance and
an implementer's after column must come from one too. Untraced whole-workload
run: **wall 54.85 s**, RSS 0.94 GB, 3 505 item rows in the
`caller_native_certificate` module. Summed over those rows:
**49.06 s total, 39.10 s `kernel_gate`, 36.36 M evaluator steps,
236 914 conversion misses.**

Every family above half a second of item total, plus every family this round
names (`n`, total, kernel, evaluator steps, conversion misses):

| family | n | total s | kernel s | steps M | misses |
| --- | --- | --- | --- | --- | --- |
| `read_literal` | 32 | 4.724 | 4.550 | 1.90 | 880 |
| `byte` | 36 | 4.585 | 3.744 | 2.55 | 34 515 |
| `store_equal` | 54 | 3.405 | 2.858 | 4.86 | 20 986 |
| `successor` | 35 | 2.380 | 2.036 | 2.36 | 9 338 |
| `step` | 19 | 2.347 | 1.505 | 1.15 | 13 811 |
| `byte_page` | 167 | 2.267 | 2.126 | 1.46 | 835 |
| `byte_wrap` | 131 | 2.108 | 2.011 | 1.35 | 393 |
| `return_read` | 32 | 1.659 | 1.376 | 1.94 | 1 664 |
| `stack_allowed` | 36 | 1.580 | 1.498 | 1.22 | 1 316 |
| `store_address` | 48 | 0.987 | 0.827 | 1.20 | 5 808 |
| `byte_present` | 167 | 0.985 | 0.659 | 0.14 | 9 018 |
| `store_offset` | 48 | 0.954 | 0.911 | 0.77 | 48 |
| `leaf_fetch` | 16 | 0.934 | 0.680 | 0.57 | 5 074 |
| `write_permission` | 48 | 0.835 | 0.638 | 1.05 | 1 632 |
| `rsp` | 35 | 0.752 | 0.665 | 1.11 | 5 436 |
| `write_literal` | 48 | 0.731 | 0.668 | 0.55 | 240 |
| `byte_found` | 167 | 0.721 | 0.376 | 0.02 | 501 |
| `stack_permissions` | 10 | 0.648 | 0.490 | 0.60 | 3 752 |
| `call_20_callee_applied` | 1 | 0.645 | 0.235 | 0.18 | 2 034 |
| `trace` | 36 | 0.632 | 0.061 | 0.04 | 675 |
| `code_drop` | 168 | 0.624 | 0.352 | 0.03 | 335 |
| `read_address` | 32 | 0.621 | 0.595 | 0.45 | 28 |
| `literal_permissions` | 6 | 0.582 | 0.500 | 0.69 | 1 890 |
| `leaf_summary_suffix` | 9 | 0.556 | 0.186 | 0.30 | 1 277 |
| `call_10_callee_applied` | 1 | 0.551 | 0.165 | 0.10 | 1 833 |
| `return_value` | 4 | 0.530 | 0.438 | 0.63 | 880 |
| `store_byte` | 48 | 0.523 | 0.412 | 0.60 | 4 624 |
| `return_reads` | 4 | 0.514 | 0.458 | 0.74 | 608 |
| `call_20_callee_local_outside` | 8 | 0.495 | 0.465 | 0.38 | 568 |
| `call_10_callee_local_outside` | 8 | 0.481 | 0.451 | 0.38 | 568 |
| `dead_frame_byte` | 1 | 0.219 | 0.214 | 0.05 | 4 |
| `call_20_callee_return_outside` | 1 | 0.171 | 0.164 | 0.17 | 176 |
| `call_10_callee_return_outside` | 1 | 0.171 | 0.164 | 0.17 | 176 |
| `local_outside_written_offset` | 8 | 0.135 | 0.129 | 0.13 | 8 |
| `return_outside_protected_offset` | 8 | 0.134 | 0.128 | 0.13 | 8 |
| `local_outside_protected_offset` | 8 | 0.134 | 0.128 | 0.13 | 8 |
| `return_outside_written_offset` | 8 | 0.133 | 0.128 | 0.13 | 8 |
| `local_outside_excluded` | 72 | 0.113 | 0.062 | 0.00 | 456 |
| `return_outside_excluded` | 72 | 0.112 | 0.062 | 0.00 | 456 |
| `local_outside_different` | 64 | 0.046 | 0.036 | 0.01 | 192 |
| `return_outside_different` | 64 | 0.046 | 0.035 | 0.01 | 192 |

The brief's family table is the one from the 2026-09-11 log entry and is
**stale**: it reports `store_equal` at 11.3 s/24.5 M steps, `byte` at 10.2 s,
`return_read` at 7.7 s/15.2 M and `write_permission` at 5.0 s/12.6 M. The three
kernel rounds since then took the whole certificate from 86 s of kernel to
39 s, and they did not take it uniformly: `write_permission` is now 0.64 s of
kernel, a sixth of what the brief quotes, and `store_equal`'s evaluator steps
fell by 5×. Any ranking of levers taken from those numbers is wrong, which is
why §5 and §6 refute two of the three chartered hypotheses.

`read_literal` is not a flat family. Eight of its thirty-two items —
`read_literal_28_0 … _7`, the byte reads at the `LoadStack64` after the callee
returns — cost **0.510 to 0.539 s each (0.497–0.523 s kernel, 186–189 k
evaluator steps, 95 misses)**. The other twenty-four are the same theorem at
other states and cost **0.015–0.030 s each (14.5–21.1 k steps, 5 misses)**. The
eight are 4.08 s of the family's 4.72 s, and they are this round.

## 2. The unit: a stack address is inside the file's window

`call_memory_read` (`lib/elf64_calls.hthr`) is

    call_read_choice(static_elf64_read(memory.file, address),
                     stack_page(address), memory.stack(address))

and `static_elf64_read` (`lib/elf64_load.hthr`) decides membership by a 48-bit
window test, `is_zero_bits(48, bxor(48, drop_low(16, 48, address), ofNat(48, 64)))`,
and then indexes the file list, `file.nth(toNat(16, take_low(16, 48, address)))`.
The window is the whole 64-KiB range at 0x400000 — and the owned stack page at
0x401000 is **inside it**. So for a stack address the window test *succeeds*,
and the `None` that sends `call_read_choice` to the stack branch is produced by
`nth` running off the end of the file: a unary walk of all 399 elements, every
time.

Probe, on a 399-byte file list and the certificate's own literal address
spelling (`probes/t_unit_fileread.hthr` and siblings in the scratchpad):

| probe | ms | evaluator steps |
| --- | --- | --- |
| `static_elf64_read(file, 0x401ff0) = None` | 178.9 | 31 493 |
| `stack_page(0x401ff0) = True` | 14.5 | 9 411 |
| `file.len() = 399` | 22.7 | 5 997 |

31 493 steps per file lookup, and `read_literal_28_0` is 188 850 steps: **six
lookups, and essentially nothing else.** The evaluator-step count of that item
is the file-list walk to three significant figures. The closed bitvector
compares the charter was written about — the `is_zero_bits(64, bxor(64, …))`
per write link — are 10 500 steps for the whole seventeen-link chain
(§4, shallow probe), a twentieth of one lookup.

This also makes the cost *linear in the size of the compiled program*: a
certificate for a bigger function pays a longer walk at every stack byte it
reads through the contract. That is the reason to fix it now and not to wait
for [[kernel-native-bitvector-values]], which would not touch it.

## 3. Mechanism 1 — the contract read route

### 3.1 What the kernel actually evaluates

`certify_return_target` in `crates/cli/src/native/calls.rs`, `from_contract`
branch, emits (verbatim from the generated certificate):

    theorem caller_native_read_literal_28_0(gprs, flags, stack):
        call_stack_access().read(caller_native_state_28(…).memory,
                                 caller_native_word_401ff0()) = imm_byte0(caller_native_word_14())
    { trans(cong_fn<Option<BitVec(8)>, BitVec(8)>(call_read_value,
        caller_native_call_20_callee_memory_effects(…)(caller_native_word_401ff0(),
            caller_native_call_20_callee_local_outside_0(…))), refl) }

The contract's `WritesOnly` is over `call_memory_read`, so its application at
the literal address has type
`call_memory_read(state_28.memory, lit) = call_memory_read(state_20.memory, lit)`,
and the theorem's own left-hand side is `call_stack_access().read(…)`, i.e.
`stack_observation`, i.e. `memory.stack(lit)`. Every seam between those two
spellings forces a `call_memory_read` to whnf, and each one walks the file.

`HEATHER_CONV_MISS_TRACE=caller_native_read_literal_28_0`, reduced by
(head pair, site, ms) — 95 misses, of which two:

    218.772 ms  Id/Id  site: App < Lam < Lam < Lam
    211.263 ms  Id/Id  site: Refl < App < App < Lam < Lam < Lam
      0.735 ms  Sigma/El(?)  site: App < Snd < … < Fst < Fst < App …   (×~30)
      ≤0.04 ms  El^δ/Sigma, El^δ/Sum                                    (×~60)

430 ms of the item's 497 ms of kernel are those two misses: the `cong_fn`'s
`Id` argument (both memories read) and the closing `refl` (both read again).
The ~20 ms of `Sigma/El(?)` is the projection residue
[[elaborator-canonical-type-spelling]] owns and will survive this round.

### 3.2 The probe

Four probe modules build the certificate's *own* memory spelling — a chain of
`CallMemory(file, call_memory_write(previous, <literal address>, elf_byte(b)).stack)`
links, three stored words (the caller's local at 0x401ff0, the call's return
address at 0x401fe8, the callee's frame slot at 0x401fe0), over a 399-byte file
— and read byte 0 of the deepest word, the shape `read_literal_28_0` has. The
`WritesOnly` fact is a hypothesis of the probe theorem, exactly as the summary
supplies it in the certificate.

| probe | route | ms | steps |
| --- | --- | --- | --- |
| `t_chain_contract_read` | `WritesOnly(call_memory_read, …)`, today's spelling | 362.0 | 114 971 |
| `t_chain_contract_stack` | `WritesOnly(stack_observation, …)` | **19.0** | **11 232** |
| `t_chain_refl` | plain `refl`, no contract | 19.3 | 13 492 |
| `t_chain_refl_shallow` | `refl` through the caller's word alone | 10.9 | 10 581 |

**19×.** The two cheap routes are indistinguishable from each other: once the
file is out of the way, what is left is the write-chain walk, and that walk is
what the twenty-four cheap `read_literal` items in the workload already cost
(14.5–21.1 k steps). The probe agrees with the workload to within the depth
difference, which is the cross-check that the probe is measuring the right
thing.

A second probe set, identical but with the memory spelled as
`word_write_8(call_stack_access(), value, m, base)` instead of with literal
addresses, gives 888.9 ms / 217.9 ms / 142.7 ms for the three routes: the
`bitvec::add(64, base, ofNat(64, j))` ripple in each link then costs more than
the read does. That is `certify_call_memory`'s literal re-spelling earning its
keep, and it is a warning for the implementation: **do not state the new lemmas
over `word_write_*` and let a use site meet them at a literal chain.**

### 3.3 The spelling to emit

State the leaf contract's memory effect over `stack_observation` rather than
`call_memory_read`, and carry the file's constancy as its own field so the
interface is not weakened:

1. `lib/std/arch/x86_64/call_frame.hthr`: `NativeIntegerCallContract<M, A>` is
   already parametric in `read`, so no change is needed there for the
   observation itself. Add nothing to that record; the file field belongs to
   the `CallMemory` instance, not to the generic contract (see §3.4).
2. `crates/cli/src/native/calls.rs`, `emit_leaf_summary`: instantiate
   `summary_post`'s contract at `<CallMemory, BitVec(8)>(stack_observation, …)`,
   and supply `memory_effects` from `word_stack_effect_8` (frame branch) or
   `writes_only_equal(stack_observation, NoWrites, …, refl)` (no-frame branch).
   **`lib/elf64_calls.hthr` already proves `word_stack_effect_0 … _8`** — the
   `stack_observation` twins the brief asked whether existed. No new library
   lemma is needed for this step.
3. `summary_post` gains a conjunct `after.memory.file = before.memory.file`.
   In both branches `after.memory` converts to a chain of `call_memory_write`,
   whose `.file` is the argument's `.file` definitionally, so this is `refl` —
   checked once, in the summary, not per byte.
4. `certify_callee_contract`: `callee_memory_effects` keeps its shape with the
   new observation; add `callee_preserved_file` projecting the new conjunct.
5. `certify_return_target`, `from_contract` branch: the proof becomes
   `trans(<instance>_callee_memory_effects(…)(lit, outside), refl)` — the
   `cong_fn(call_read_value, …)` wrapper disappears with the `Option`.
6. Anywhere the `call_memory_read`-level fact is still wanted, derive it with a
   **new library lemma** in `lib/elf64_calls.hthr`:

       theorem memory_writes_of_stack_writes(before, after: CallMemory,
           writes: BitVec(64) → Type, files: after.file = before.file,
           effects: WritesOnly(stack_observation, writes, before, after)):
           WritesOnly(call_memory_read, writes, before, after)

   proved by congruence of `call_read_choice` in its first and third arguments
   under the address binder. It is checked **open**, so it never evaluates a
   file lookup; it restores exactly the statement today's contract makes.

This is the design-preserving fix: the certificate still justifies the
preserved local byte by the callee's declared footprint, and with lemma (6) it
can still state that footprint at the full memory observation. Nothing about
the proof boundary moves.

### 3.4 What else meets this type

The rule from the bar: a spelling change that names a type regresses every
reader that reconstitutes it.

- `NativeIntegerCallContract<M, A>` is instantiated in `emit_leaf_summary`,
  `certify_callee_contract`, and in three refusal controls in
  `crates/cli/src/native/calls.rs`'s test module (`contract_restores_rsp`,
  `missing_frame_release`, and the `stale_summary`/`wrong_summary_interface`
  pair, which must keep refusing). All must move together; the record itself
  does **not** change, only its `read`/`A` arguments at these sites.
- `WritesOnly(call_memory_read, …)` also appears in `frame_checks` in the same
  test module and in `CallMemoryPolicy`'s users. Those are about byte writes to
  a *named* address and are not on this path; leave them at `call_memory_read`.
- `word_stack_effect_*` currently has no user. Giving it one means the
  perturbed-library mutation control now has a live theorem to perturb — good,
  but it is a new coverage surface; expect the mutation controls' runtime to
  move slightly.

### 3.5 Projected saving

The eight `read_literal_28_*` items go from 0.510–0.539 s to the cost of their
twenty-four siblings plus the ~20 ms of `Sigma/El(?)` residue, i.e. ~0.03 s
each, on the probe's 19× and on the workload's own cheap-sibling evidence.

**Item total 49.06 s → ~45.2 s; `kernel_gate` 39.10 s → ~35.3 s, −9.7%.**

`dead_frame_byte` (0.214 s of kernel, one item, a `call_memory_read` at a
stack address proved by `refl`) is the same unit and is *not* included above;
see §7.

### 3.6 The variant that was not chosen

Because every state in the trace is spelled concretely, the same eight
theorems close by plain `refl` — the certificate does not need the contract to
read that byte at all. That is free (no library change), and it additionally
retires `call_{10,20}_callee_local_outside_*` (16 items, 0.976 s total,
0.916 s kernel) and the `local_outside` `WordOutside` complex (~0.30 s) as dead
code, for **~5.1 s** instead of ~3.8 s.

It is not the recommendation. The contract route is what makes the certificate
independent of how the callee's body happens to be spelled, and deleting its
only use here would leave the callee's local-frame footprint asserted by the
summary and consumed by nobody. Take §3.3; if it turns out to be more work than
it looks, this variant is the documented fallback, and the coordinator should
be told before it is taken.

## 4. Mechanism 2 — word-granular exclusion: refuted

`certify_word_outside` does emit exactly what the brief describes: 64
`is_zero_bits(64, bxor(…)) = False` refl theorems and 72 `word_prefix_excluded`
steps per `WordOutside`, twice (return slot and local slot). Measured, those
items are **0.317 s of item total and 0.195 s of kernel across both
instances** — the `*_different` families are 64 items for 0.046 s, i.e. 0.7 ms
per closed 64-bit compare, because the addresses differ in their low bits and
the compare settles almost immediately. Add the four `*_offset` families
(0.536 s total, 0.513 s kernel) and the whole `certify_word_outside` output is
under 0.9 s of item total.

A word-granular lemma would therefore be worth at most a few tenths of a
second, and it is the expensive kind of library work: it needs
`bitvec::add(64, base, ofNat(64, k))` for `k < 8` to preserve the high 61 bits
of an aligned base, which is a new bounded-carry result on top of the
`bitvec-bounded-add-sub` round. **Do not do it.** The premise it was filed on —
one 64-bit compare per (written byte, protected byte) pair being a material
share — was true of the 2026-09-11 numbers and is not true of these.

The `callee_local_outside` items (0.976 s total, 0.916 s kernel for 16) are the
one part of the "outside" machinery that is material, and they are not
compares: each is a `j`-rewrite of the `rsp` equality under a
`¬WordPrefixWrites` motive. They are consumed by the contract read route and
survive §3.3 unchanged.

## 5. Mechanism 3 — the store family spelling: refuted

`store_equal` is 54 items, 3.405 s total, 2.858 s kernel, 4.86 M evaluator
steps — not the 24.5 M the brief quotes. The largest item,
`store_equal_23_1`, is 0.087 s (0.075 s kernel, 123 k steps, 568 misses).
Traced and summed by head pair:

    Sigma/El(?)   n=84    50.3 ms
    Id/Id         n=1      2.1 ms
    El^δ/Sigma    n=65     1.9 ms
    El^δ/Sum      n=418    1.4 ms

Of 73 ms of kernel, **50 ms is `Sigma/El(?)`** — projections out of an
application whose type is `El(app(code, arg))` against an inline `Σ`
annotation, the residue [[elaborator-canonical-type-spelling]] owns and the
2026-09-12 attribution already assigned elsewhere. The bitvector compare the
hypothesis blamed (`bxor(64, add(base, j), query)` under the `query` binder) is
a single `Id/Id` miss worth 2.1 ms. The kernel is matching these by spine
already; there is nothing here for a generator re-spelling to take.

The same reduction for `byte_34_0`, the largest of the `byte` family (0.251 s
kernel), gives `El^δ/Sigma` 59.0 ms, `Vec/Sigma` 32.1 ms, `El(?)/Wf` 28.8 ms,
`Sigma/Sigma` 6.3 ms, `Id/Id` 4.4 ms: an inductive-spelling profile, not a
memory-read one. `successor_20` is `Sigma/Sigma` 47.0 ms over nine misses.
Neither is a compares-per-read problem and neither is in this round.

## 6. Out of scope

- The `Sigma/El(?)` bucket (14 740 misses, 8.9 s in the sidecar) is
  [[elaborator-canonical-type-spelling]]'s. It is the largest single thing left
  in the certificate after §3 lands and it is an elaborator round, not a
  generator one.
- `byte`/`byte_page`/`byte_wrap`/`byte_present`/`byte_found` — the fetch route,
  11.7 s of item total across 668 items. The fetch route already avoids the
  file walk through `static_elf64_read_split` (that is what `byte_present` is),
  which is why `byte_found` costs 0.02 M steps for 167 items. Its remaining
  cost is `Vec`/`Wf` spelling, §5.
- `K1`, a native closed-bitvector value in the evaluator
  ([[kernel-native-bitvector-values]]). Orthogonal: it would not touch the file
  walk, and the file walk is what §3 is about.
- `byte_page` and `byte_wrap` (4.1 s of kernel over 298 items) are closed
  48- and 64-bit compares proved by `refl` — genuinely K1's shape, genuinely
  not re-spellable here, since each states a different address.

## 7. The bar

Measured on one furnace instance, before and after, release,
`--features value-metrics`, `--kernel-workers 1`, the same `--timings`
invocation as §1.

1. Whole-workload: the certificate's **item total at or below 49.06 s** and
   **`kernel_gate` at or below 39.10 s**, with the projection of §3.5 being
   ~45.2 s and ~35.3 s. A result inside a second of the before column means the
   change did not land; re-read §3.1 before shipping it.
2. **Every family row from §1 recorded again**, not only the ones that moved.
   The point of the whole table is that a rise elsewhere is visible: the
   contract's observation is a named type and §3.4 lists its other readers.
3. The eight `read_literal_28_*` items at or below 0.05 s each, and the
   twenty-four cheap `read_literal` siblings unchanged.
4. Full `scripts/test`, green, in the background — the **plain** suite, not
   `--fast`: this touches `lib/` and the generator, so the semantic images must
   be rebuilt. `crates/cli/tests/native*.rs` and the perturbed-library mutation
   controls are part of what must pass, and §3.4 predicts movement in the
   latter's runtime.
5. `crates/cli/src/native/calls.rs`'s refusal controls still refuse:
   `stale_summary`, `wrong_summary_interface`, `missing_summary_fetch`,
   `invented_successor`, `overlapping_word`, `live_slot_cannot_change`,
   `return_slot_cannot_change`. A contract spelling that lets any of these
   through is the failure mode this change can have.

Optional, only after the above is green: `dead_frame_byte` (0.214 s of kernel)
is one `call_memory_read` at a stack address and pays one file walk. It is
emitted only in the `twice` configuration and it deliberately demonstrates the
*full* memory observation of a dead frame slot, so do not simply restate it
over `stack_observation` — that would weaken what it shows. If it is worth
0.2 s, the honest route is a `list::nth` past-the-end lemma
(`xs.len() ≤ i → xs.nth(i) = None`, a six-line induction in `lib/std/list.hthr`)
plus a `call_memory_read` shortcut keyed on it; the probe says the length is
5 997 steps against the walk's 31 493, so that route is worth about 5× on the
unit, not 19×.

## 8. Verification items

For the implementing pass's first hour. **If one of these refutes the design,
STOP and report before working around it.**

1. `grep -n "call_memory_read\|stack_observation" crates/cli/src/native/calls.rs
   lib/elf64_calls.hthr` and confirm `callee_memory_effects` has exactly one
   consumer (`certify_return_target`'s `from_contract` branch). If it has more,
   §3.3 step 5 is incomplete and each other consumer needs lemma (6).
2. Re-run `probes/t_chain_contract_read` and `probes/t_chain_contract_stack`
   (copies in the round's scratchpad; they need
   `-L probes/arch -L lib/std -L lib`, where `probes/arch` holds the
   `lib/std/arch/x86_64/*.hthr` files renamed to the module names
   `crates/cli/src/native.rs`'s `SUPPORT` table bundles them under — `heather
   check` cannot otherwise resolve `import x86_64;`). The 362 ms/19 ms split is
   the whole basis of §3.5. If the gap is not there on the implementer's
   instance, the box changed and every projection needs redoing.
3. Write `after.memory.file = before.memory.file` as a standalone theorem
   against the leaf summary's `after` **before** wiring it into `summary_post`,
   and check that `refl` closes it in both the frame and no-frame branches. If
   it does not — if `call_run` over the instruction list does not expose the
   file field definitionally — §3.3 step 3 is wrong, and the choice becomes
   either a `call_run`-preserves-file induction (real library work, re-cost it)
   or §3.6's variant.
4. Check that `word_stack_effect_8`'s statement meets the certificate's
   memories without a `word_write_*` detour: state one use at a literal-address
   chain and confirm it is ~19 ms, not ~143 ms (§3.2's second probe set). If it
   is the larger number, the contract is being met at the `word_write_*`
   spelling and the ripple adds are back.
5. After the change, re-trace one `read_literal_28_*` item with
   `HEATHER_CONV_MISS_TRACE` and confirm the two ~215 ms `Id/Id` misses are
   gone and nothing new above 1 ms replaced them. An item that is fast for a
   different reason than §3.1 says is not the fix this document describes.

## 9. Result

Implemented 2026-09-12 on a later furnace instance than §1's. That instance is
gone, and the replacement drifted about 4.5% slower over the session's two
hours, so **every number below comes from one paired job** (scratchpad
`j6.log`): build, after run, `git apply -R` the diff, build, before run, build,
after run again — three workloads back to back, release,
`--features value-metrics`, `--kernel-workers 1`, the §1 invocation.

    BEFORE   rows=3475  total=51.999 s  kernel_gate=42.709 s  37.08 M steps  236 914 misses
    AFTER    rows=3477  total=47.631 s  kernel_gate=38.490 s  36.15 M steps  237 888 misses
    AFTER (repeat)      total=47.737 s  kernel_gate=38.612 s

**Item total −4.37 s (−8.4%); `kernel_gate` −4.22 s (−9.9%).** §3.5 projected
−9.7% of kernel; the repeat run is 0.1 s from the first, so the spread is a
tenth of the effect. Wall fell 57.5 s → 53.1 s.

### 9.1 Every family of §1, before and after

| family | n | before s | after s | before kernel s | after kernel s | after steps M | after misses |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `read_literal` | 32 | 4.808 | **0.957** | 4.626 | **0.840** | 0.91 | 816 |
| `byte` | 36 | 4.776 | 4.781 | 3.911 | 3.912 | 2.55 | 34 515 |
| `store_equal` | 54 | 3.625 | 3.600 | 3.056 | 3.043 | 4.86 | 20 986 |
| `successor` | 35 | 2.517 | 2.500 | 2.156 | 2.146 | 2.36 | 9 338 |
| `step` | 19 | 2.463 | 2.494 | 1.581 | 1.593 | 1.15 | 13 811 |
| `byte_page` | 167 | 2.356 | 2.303 | 2.195 | 2.150 | 1.46 | 835 |
| `byte_wrap` | 131 | 2.180 | 2.137 | 2.073 | 2.034 | 1.35 | 393 |
| `return_read` | 32 | 1.768 | **1.494** | 1.491 | **1.289** | 1.94 | 1 664 |
| `stack_allowed` | 36 | 1.625 | 1.642 | 1.537 | 1.561 | 1.22 | 1 316 |
| `store_address` | 48 | 1.056 | 1.061 | 0.889 | 0.894 | 1.20 | 5 808 |
| `byte_present` | 167 | 1.018 | 1.027 | 0.681 | 0.692 | 0.14 | 9 018 |
| `store_offset` | 48 | 0.997 | 0.956 | 0.951 | 0.911 | 0.77 | 48 |
| `leaf_fetch` | 16 | 0.984 | 0.980 | 0.721 | 0.719 | 0.57 | 5 074 |
| `write_permission` | 48 | 0.897 | 0.902 | 0.687 | 0.698 | 1.05 | 1 632 |
| `rsp` | 35 | 0.818 | 0.816 | 0.725 | 0.725 | 1.11 | 5 436 |
| `write_literal` | 48 | 0.765 | 0.730 | 0.698 | 0.666 | 0.55 | 240 |
| `byte_found` | 167 | 0.749 | 0.750 | 0.390 | 0.393 | 0.02 | 501 |
| `stack_permissions` | 10 | 0.680 | 0.685 | 0.517 | 0.525 | 0.60 | 3 752 |
| `call_20_callee_applied` | 1 | 0.646 | 0.653 | 0.242 | 0.244 | 0.18 | 2 034 |
| `trace` | 36 | 0.695 | 0.649 | 0.068 | 0.066 | 0.04 | 675 |
| `code_drop` | 168 | 0.653 | 0.640 | 0.369 | 0.360 | 0.03 | 335 |
| `read_address` | 32 | 0.633 | **0.552** | 0.605 | **0.528** | 0.45 | 28 |
| `literal_permissions` | 6 | 0.630 | 0.626 | 0.544 | 0.540 | 0.69 | 1 890 |
| `leaf_summary_suffix` | 9 | 0.579 | 0.576 | 0.194 | 0.193 | 0.30 | 1 277 |
| `call_10_callee_applied` | 1 | 0.541 | 0.579 | 0.147 | 0.168 | 0.10 | 1 833 |
| `return_value` | 4 | 0.558 | 0.539 | 0.460 | 0.448 | 0.63 | 880 |
| `store_byte` | 48 | 0.561 | 0.556 | 0.445 | 0.440 | 0.60 | 4 624 |
| `return_reads` | 4 | 0.552 | 0.512 | 0.494 | 0.458 | 0.74 | 608 |
| `call_20_callee_local_outside` | 8 | 0.502 | 0.506 | 0.470 | 0.475 | 0.38 | 568 |
| `call_10_callee_local_outside` | 8 | 0.486 | 0.488 | 0.455 | 0.457 | 0.38 | 568 |
| `dead_frame_byte` | 1 | 0.222 | 0.236 | 0.219 | 0.233 | 0.05 | 4 |
| `call_20_callee_return_outside` | 1 | 0.175 | 0.179 | 0.168 | 0.171 | 0.17 | 176 |
| `call_10_callee_return_outside` | 1 | 0.171 | 0.170 | 0.164 | 0.163 | 0.17 | 176 |
| `local_outside_written_offset` | 8 | 0.139 | 0.138 | 0.132 | 0.130 | 0.13 | 8 |
| `return_outside_protected_offset` | 8 | 0.140 | 0.137 | 0.134 | 0.130 | 0.13 | 8 |
| `local_outside_protected_offset` | 8 | 0.137 | 0.138 | 0.130 | 0.131 | 0.13 | 8 |
| `return_outside_written_offset` | 8 | 0.139 | 0.133 | 0.134 | 0.128 | 0.13 | 8 |
| `local_outside_excluded` | 72 | 0.116 | 0.116 | 0.064 | 0.064 | 0.00 | 456 |
| `return_outside_excluded` | 72 | 0.115 | 0.116 | 0.063 | 0.064 | 0.00 | 456 |
| `local_outside_different` | 64 | 0.047 | 0.047 | 0.037 | 0.036 | 0.01 | 192 |
| `return_outside_different` | 64 | 0.047 | 0.048 | 0.036 | 0.036 | 0.01 | 192 |

Outside that list, exactly two families are new — `call_10_callee_preserved_file`
and `call_20_callee_preserved_file`, the §3.3-step-4 projections, at 0.030 s and
0.031 s (0.020 s of kernel each) — and no family gained 0.03 s. The whole
certificate's rise is 0.061 s against a 4.37 s fall, which is the answer to §3.4's
question about what else meets this type: nothing that costs anything. Note in
particular `leaf_summary` (0.298 → 0.306) and `leaf_summary_suffix`
(0.579 → 0.576): moving the summary's `memory_effects` from
`word_memory_effect_8` to `word_stack_effect_8` is free, and `dead_frame_byte`
(0.222 → 0.236) is untouched, as intended.

`read_literal` fell because eight of its thirty-two items did, and the other
twenty-four did not move at all: `read_literal_17_*` 0.0156–0.0176 → 0.0157–0.0175,
`read_literal_32_*` 0.0286–0.0304 → 0.0276–0.0305. The eight:

| item | before s (kernel) | after s (kernel) | before steps | after steps | misses |
| --- | --- | --- | --- | --- | --- |
| `read_literal_28_0` | 0.5246 (0.5113) | 0.0610 (0.0543) | 188 850 | 63 543 | 95 → 87 |
| `read_literal_28_1` | 0.5531 (0.5342) | 0.0590 (0.0523) | 188 161 | 63 400 | 95 → 87 |
| `read_literal_28_2` | 0.5442 (0.5307) | 0.0577 (0.0511) | 187 719 | 63 338 | 95 → 87 |
| `read_literal_28_3` | 0.5386 (0.5249) | 0.0567 (0.0500) | 187 580 | 63 377 | 95 → 87 |
| `read_literal_28_4` | 0.5414 (0.5240) | 0.0570 (0.0505) | 186 835 | 63 214 | 95 → 87 |
| `read_literal_28_5` | 0.5336 (0.5204) | 0.0559 (0.0495) | 186 696 | 63 253 | 95 → 87 |
| `read_literal_28_6` | 0.5332 (0.5198) | 0.0550 (0.0484) | 186 254 | 63 191 | 95 → 87 |
| `read_literal_28_7` | 0.5344 (0.5210) | 0.0547 (0.0480) | 185 939 | 63 054 | 95 → 87 |

**Nine to ten times cheaper, and about 10% over the bar's 0.05 s.** §7 point 3
is the one point of the bar this round does not clean; §9.3 says what the
remaining 55 ms is and why neither half of it is this round's.

### 9.2 The verification items

1. **Pass.** `callee_memory_effects` has exactly one consumer,
   `certify_return_target`'s `from_contract` branch (`calls.rs:326`). Nothing
   else in the generator or the library reads it, so the new library lemma
   `memory_writes_of_stack_writes` ships with no in-tree caller: it is the
   interface guarantee, not a step of any proof.
2. **Pass.** On this instance `t_chain_contract_read` is 322.7 ms / 114 971
   steps and `t_chain_contract_stack` 18.2 ms / 11 232 steps — 17.7×, against
   §3.2's 19×. `t_chain_refl` 16.5 ms and `t_chain_refl_shallow` 10.2 ms are
   unchanged in relation to it, so the box is the same box §3.2 described.
3. **Pass, in both branches.** Appending
   `theorem q_file_const(before: MachineState<CallMemory>):
   call_run(call_stack_access(), caller_native_leaf_summary_code(), before).memory.file
   = before.memory.file { refl }` to a generated certificate and re-checking it
   succeeds for `reused_callee` (frame) and for `calls` (no frame).
   `call_next` threads `CallMemory(memory.file, …)` through every instruction of
   both summaries, so the field is definitionally the argument's and the
   conjunct of §3.3 step 3 costs one `refl` in the summary.
4. **Amended — see §9.4.** The probe §8 item 4 asks for, a direct
   `word_stack_effect_8` application met at a literal-address chain, is
   222.8 ms / 152 895 steps (its `call_memory_read` twin,
   `word_memory_effect_8`, is 411.1 ms). But that is not a shape the
   certificate has: `word_stack_effect_8` is applied once, inside
   `emit_leaf_summary`, at a bound `before.memory` and a symbolic
   `rsp - 8`, and the contract reaches the read site as an abstract
   `WritesOnly` over two state functions — item 2's 18.2 ms shape. The workload
   confirms it: `leaf_summary` moved by 0.008 s.
5. **Pass.** Re-tracing `caller_native_read_literal_28_0` with
   `HEATHER_CONV_MISS_TRACE`, the two `Id/Id` misses of 218.8 ms and 211.3 ms
   are gone. Exactly one miss in the item now exceeds 1 ms:

       13.648 ms  Id/Id        site: Refl < App < App < Lam < Lam < Lam
       15.06 ms   Sigma/El(?)  site: App < Snd < Snd < Snd < … (n=24)
        3.25 ms   Sigma/El(?)  site: App < Snd < Snd < Fst < Fst < App … (n=5)
        1.97 ms   Sigma/El(?)  site: App < Snd < Snd < Fst < Fst < App … (n=3)
        ≤0.7 ms   everything else (Pi/El(?), El^δ/Sum, El^δ/Sigma, El(?)/El(?))

### 9.3 What the remaining 55 ms is

13.6 ms is the closing `refl`, and it is the right cost: with the file out of
the way it walks the seventeen-link write chain to state 20, which is what the
twenty-four cheap siblings pay for their whole item. Nothing but §3.6's variant
removes it, and §3.6 is not the recommendation.

About 22 ms is `Sigma/El(?)`, spread over 33 misses. §3.1 measured it at ~20 ms
before the change and said it would survive; it did, unchanged, and it is now
two fifths of the item. It is the projection residue of reading
`callee_contract.memory_effects` out of `callee_post.left` out of
`callee_applied.right` — [[elaborator-canonical-type-spelling]]'s, as §6 says.
The design's ~0.03 s projection came from the cheap siblings, which are both a
shallower chain and a *five*-miss item; it did not account for this item
carrying 87.

### 9.4 Deviations from §3.3

- **§3.3 step 4 (mechanical).** The file conjunct is appended as the third
  member of `summary_post`'s right-nested `∧`, so `callee_preserved_rsi`'s
  proof moves from `callee_post.right` to `callee_post.right.left` and
  `callee_preserved_file` is `callee_post.right.right`. The summary's `ensures`
  becomes `⟨NativeIntegerCallContract(…), ⟨refl, refl⟩⟩`.
- **§3.4 (as directed).** The `contract_restores_rsp` / `missing_frame_release`
  pair in the test module moved to
  `NativeIntegerCallContract<CallMemory, BitVec(8)>(stack_observation, …)` with
  `writes_only_equal(stack_observation, …)`, so the file has one spelling of
  the contract. `frame_checks` and `CallMemoryPolicy`'s users stayed at
  `call_memory_read`, and `dead_frame_byte` stayed at `call_memory_read`.
- **§8 item 4.** The item's probe is not decisive, because the shape it
  constructs — the word-store effect theorem meeting a literal chain — does not
  occur anywhere in the certificate. The check that *is* decisive is the
  `leaf_summary` family across the paired run, and a future round re-using this
  document should read item 4 that way. The 222.8 ms figure still stands as a
  warning: state nothing over `word_write_*` where a use site will meet it at
  literal addresses.
- **§7 point 3, not met.** The eight items land at 0.055–0.061 s, not ≤0.05 s;
  §9.3 attributes 22 ms of that to a bucket §6 puts out of scope.
- **§7's optional `dead_frame_byte` item, not taken**, since point 3 is not
  clean. Its cost is unchanged at 0.236 s and the `list::nth` past-the-end
  route §7 describes is still the honest one.

### 9.5 The suite

Plain full `scripts/test` (not `--fast`), through `furnace run`, twice — once on
the change and once as a re-verification after the paired measurement:

    == suite: 2581 passed, 0 failed, 5 ignored ==

`crates/cli/tests/native*.rs` and the perturbed-library mutation controls are in
that count. The refusal controls of §7 point 5 live in
`crates/cli/src/native/calls.rs`'s `call_stack_semantics_and_refusals`, which
runs in the `heather-cli` **bin** target (the crate's `--lib` target has no
tests); it passes, so `stale_summary`, `wrong_summary_interface`,
`missing_summary_fetch`, `invented_successor`, `overlapping_word`,
`live_slot_cannot_change` and `return_slot_cannot_change` all still refuse.
`stale_summary` and `wrong_summary_interface` refuse against the *new*
`summary_post`, which is the one that matters here.

### 9.6 Files

- `lib/elf64_calls.hthr`: `memory_writes_of_stack_writes`, proved by congruence
  of `call_read_choice` in its file and stack arguments, checked open.
- `crates/cli/src/native/calls.rs`: `emit_leaf_summary`'s `summary_post`,
  footprint proof and `ensures`; `certify_callee_contract`'s
  `callee_contract`, `callee_preserved_rsi`, `callee_memory_effects` and the
  new `callee_preserved_file`; `certify_return_target`'s `from_contract` read
  proof; the two refusal controls §3.4 names.
