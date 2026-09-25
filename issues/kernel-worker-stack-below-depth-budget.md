---
title: Kernel workers overflow their 2 MiB stack where the serial gate says OutOfFuel
status: closed
labels: [kernel,diagnostics,parallelism]
created: 2026-09-25
updated: 2026-09-25
---

A `heather check` at the default eight kernel workers aborts the process with
a stack overflow in a `heather-kernel-N` thread where the same file at
`--kernel-workers 1` is refused cleanly with `OutOfFuel`. A SIGABRT is not a
verdict ([[kernel-native-depth-budget]]).

The pool spawns its workers with `std::thread::Builder` and no
`stack_size` (`crates/elab/src/pool.rs`), so they get Rust's 2 MiB default.
`NATIVE_DEPTH_LIMIT` (`crates/kernel/src/reduce.rs`) is sized against an
8 MiB stack. That is the main thread's size, and it is the size
`scripts/test` gives every thread through `RUST_MIN_STACK=8388608`. The suite
therefore cannot see this; only a direct CLI run can. With
`RUST_MIN_STACK=8388608` set, the eight-worker run below answers
`OutOfFuel` like the serial one.

Repro (`import nat; import logic;`, release build, default width):

```heather
theorem flip_sides(rest, s, c: Nat, lt: rest * 1099511627776 + s < c * 1099511627776 + 0):
    1099511627776 * rest + s < 1099511627776 * c {
    Nat::lt_congr_iff(rest * 1099511627776 + s, 1099511627776 * rest + s, c * 1099511627776 + 0, 1099511627776 * c,
        Nat::cong(λ (x: Nat) => x + s, rest.mul_comm(1099511627776)), c.mul_comm(1099511627776)).mp(lt)
}
```

Found in [[nat-div-mod-lemma-kit]]'s round, where a first spelling of
`decimal_line::step_fits` did this. The le/lt literal conversion in
[[le-lt-conversion-linear-in-literal]] logged the same abort on 2026-09-18.

## Plan

- Give the pool's workers the stack the depth budget was sized for
  (`Builder::stack_size`, the same 8 MiB), or derive the budget from the
  thread's actual stack. The first is one line. The second keeps the two
  from drifting apart again.
- A regression control that runs a refusing item through the pool at width
  > 1 *without* `RUST_MIN_STACK`, for example as a CLI test that clears the
  variable for its child.

## Question left open

Why `flip_sides` is expensive at all. `rest * 2^40` with `rest` open
unfolds `mul` on its literal second argument, one step per unit, somewhere
in checking the `lt_congr_iff` instance. The landed `step_fits` keeps the
literal on the left (`2^40 * rest`) and costs nothing. Whether conversion
should ever reach that unfolding belongs with
the run-arithmetic classes of [[nat-run-algebra-primitives]], not
here.

## Log

- 2026-09-25: Landed. `NATIVE_STACK_BYTES` (8 MiB) sits beside `NATIVE_DEPTH_LIMIT` in `crates/kernel/src/reduce.rs` as the stack the budget was measured against, and the pool spawns its workers with it (`Builder::stack_size`, `crates/elab/src/pool.rs`). The pool is the only thread spawn in the compiler. Plan item 1 took the one-line route. Deriving the budget from the actual stack is left undone: nothing else spawns a kernel thread, and the constant now names the pairing. Regression control: `kernel_workers.rs::a_deep_refusal_is_a_verdict_at_every_width` runs `fixtures/deep_refusal.hthr` (the repro above) at widths one and eight with `RUST_MIN_STACK` removed and asserts exit 1 with `OutOfFuel`. With the `stack_size` line commented out it fails at width eight, as the control should. The main thread still takes whatever `ulimit -s` gives it. That is 8 MiB by default on Linux, and a smaller one would bring the same abort back for width one. The open question below, why `flip_sides` is expensive at all, stays with [[nat-run-algebra-primitives]].
