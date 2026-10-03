# Width-bounded `add`, `sub`, and `neg`

`issues/bitvec-width-bounded-defaults.md` owns this round;
`issues/kernel-acceleration-policy.md` says why the answer is a library
definition and never a kernel case for a definition's shape.

## The swap

`lib/std/bitvec.hthr` defined `add(n, a, b)` as
`iterate_increment(n, a, toNat(n, b))` — one increment per unit of the second
operand's unsigned value, so a machine-width operand asked for up to `2^64`
steps, and `sub`, `neg`, `signed_overflow_add`/`_sub` and `signed_lt_bit`
inherited that cost. `ripple_add`/`ripple_sub`/`ripple_neg` already ran one
column per bit of width and were already proved equal to them.

The ripples are now the definitions:

- `add := ripple_add`, `sub := ripple_sub`, `neg := ripple_neg`. The
  `ripple_*` names stay — `add` *is* `ripple_add`, so `ripple_add_eq_add`,
  `add_eq_of_ripple_add` and their siblings are `refl` and every proof and
  emitted certificate that names them keeps working unchanged.
- The iterated forms are `iter_add`, `iter_sub`, `iter_neg`. The equations
  that carried the induction are `iter_add_eq_add`, `iter_sub_eq_sub`,
  `iter_neg_eq_neg`, with transports `add_eq_of_iter_add`,
  `iter_add_eq_of_add`, `sub_eq_of_iter_sub`, `iter_sub_eq_of_sub`,
  `neg_eq_of_iter_neg`.
- `add_comm` and `add_sub_cancel` keep their statements; their `toNat`-counted
  proofs moved to `iter_add_comm` and `iter_add_sub_cancel` and the canonical
  ones are those transported. `ripple_add_comm` and `ripple_add_sub_cancel`
  are now aliases of them.
- The ripple definitions and `carry_majority`/`borrow_next` moved up the file
  to sit above `add`; only their position changed.

`toInt` and `mul` are unchanged, for the reasons the issue records: `toInt`'s
negative branch stopped costing the magnitude when `int::sub` became one
synchronous `subNatNat` descent, and `mul` is blocked not by its own spelling
but by `ofNat` above `2^n`, whose `mod_succ` loop subtracts `2^n` once per
iteration. A width-bounded `mul` wants a shift-and-add spelling or a
run-friendly `ofNat`; neither is this round.

## What the swap costs, and the fallout it caused

The ripple matches on the *width*, so it produces all `n` columns whatever the
operands are. The iterated form matches on the *count*, and on an open vector
`increment` is stuck at the first bit. So the two trade places: the ripple is
cheap where the count is large, and the iterated form is cheap where the count
is a small literal and the vector is open. Three consequences showed up.

- **`add(n, a, zero) ≡ a` is gone.** `iter_add` absorbed a zero count
  definitionally; the ripple does not. `bitvec::add_of_toNat_zero(n, a, b, h)`
  with `h : toNat(n, b) = 0` is the replacement.
  `lib/elf64_calls.hthr`'s `stored_word_preserves_return` was the only site:
  it passed `outside.byte0`, whose type names
  `bitvec::add(64, protected, ofNat(64, 0))`, where a bare `protected` was
  expected. It now transports with `j` over that lemma. (The symptom was
  `OutOfFuel`, not `NotConvertible` — the kernel spends the budget trying to
  reduce two 64-column ripples over an open vector before giving up.)
- **`lib/std/arch/x86_64/x86_64_block.hthr`'s `short_branch_target_8`/`_6`**
  asserted `add(64, rip, sign_extend(…)) = iterate_increment(64, rip, k)` by
  `refl` over an open `rip`. They now transport through `iter_add_eq_add`;
  the statements are unchanged.
- **`lib/std/arch/x86_64/x86_64_calls.hthr`'s `add_negative`** did its
  increment/decrement bookkeeping on the definitional unfolding of `add` and
  `sub`. Its argument is now stated over `iter_add`/`iter_sub`
  (`iter_add_comm`, `increments_decrements`, `iterate_increment_toNat`) and
  transported back at both ends. The statement is unchanged, so
  `crates/cli/src/native/calls.rs`, which emits `add_negative` for CALL
  displacements, is untouched.

- **The FunctionIR x86 lowering** (`crates/elab/src/function_ir_x86_lower.rs`)
  emits the same `short_branch_target … = iterate_increment(…)` step for
  branch spans and targets. Its four `refl`s became the same transport; the
  emitted statements are unchanged.
- **`add` and `sub` no longer differ at the head.** Both are ripples that agree
  on every sum bit and differ only in the column carry, so a negative control
  between them costs the width squared instead of one δ-step: at width 8 the
  kernel still says `NotConvertible`, at width 64 the budget runs out first.
  `add_and_sub_differ` in `crates/elab/tests/lib_std_bitvec.rs` pins both, and
  the stale-source control in `crates/elab/tests/function_ir_x86.rs` accepts
  either refusal. Whether the width-64 case is calculus-inherent or a strategy
  artefact is a question for `issues/kernel-acceleration-policy.md`; the
  refusal itself is correct either way.

Nothing else moved: the x86 and FunctionIR customers name `iterate_increment`
directly with small literal counts and it keeps its name, and the native call
emitter goes through `add_eq_of_ripple_add`, which is now definitional.

## Probes

One furnace box, one release build, `heather check` on a one-theorem file.
Loading `lib/std` alone is 3.17 s / 110 MB, so these are all at the floor.

| case | before | after |
| --- | --- | --- |
| `signed_overflow_add(64, s, s)`, `s` a computed sign-1 sum | `OutOfFuel` | ok, 3.26 s |
| `toInt(64, s)` negative at width 64 | ok (already a rail) | ok, 3.23 s |
| `signed_lt_bit(64, s, zero(64))` at the `2^63` boundary | `OutOfFuel` | ok, 3.25 s |
| `toNat(64, add(64, ofNat(64, 0), ofNat(64, 4096)))` | `OutOfFuel` | ok, 3.25 s |
| the same through `iter_add` | `OutOfFuel` | `OutOfFuel`, 3.21 s |

The "before" refusals are the depth budget of
`issues/kernel-native-depth-budget.md` doing its job; before that they aborted
the process. The shape claim is that the three deferred acceptance cases moved
from *no verdict at all* to the cost of loading the library, not that any
number here is a benchmark.

An open-operand single `add` is measurably but not interestingly more
expensive than the iterated form: 3.49 s against 3.19 s for one width-64
comparison over an open vector.

## Deliberately left

- `mul` and `ofNat` above `2^n`, as above.
- The byte-offset idiom in `lib/std/arch/x86_64/x86_64_calls.hthr` and
  `lib/elf64_calls.hthr` (`bitvec::add(64, pointer, ofNat(64, k))` for
  `k` under eight, over an open pointer) still names `add`. Re-pointing it at
  `iter_add` was tried and rejected: it has to be done consistently across
  `WordPrefixWrites`, `WordOutside`, `stack_word` and the certificates
  `crates/cli/src/native/calls.rs` emits, and a partial respelling makes the
  two spellings meet under conversion and costs *more*. With the zero offset
  transported, the layer checks as it is.
