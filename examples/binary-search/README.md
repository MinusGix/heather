# A proved binary search

`search.hthr` is a binary search written in Heather, compiled to x86-64, and
proved to find where a byte belongs in a sorted span. It also proves that the
textbook midpoint `(lo + hi) / 2` is wrong for 64-bit words. `main.c` wraps the
search in a command-line tool.

## Build it and run it

From the repository root, on x86-64 Linux with a C compiler:

```sh
cargo build --release -p heather-cli
mkdir -p target/binary-search
target/release/heather compile-x86 examples/binary-search/search.hthr lower_bound \
  -o target/binary-search/search.s --cache-dir target/native-images
cc -std=c11 -O2 examples/binary-search/main.c target/binary-search/search.s -o target/binary-search/lowerbound
printf 'aabccdz' | target/binary-search/lowerbound 99    # 3: where 'c' goes
printf 'aabccdz' | target/binary-search/lowerbound 255   # 7: past the end
```

`compile-x86` checks every proof in the file before it emits anything, and
the assembly comes with a certificate (`search.certificate.hthr`) that the
kernel checks too: the machine code computes the Heather function.

## The program

```text
runtime fn lower_bound_in(s: List<u8>, n, key, lo, hi: u64) → u64 decreases (hi - lo).toNat() {
    if h: lo < hi {
        let mid = lo + ((hi - lo) >> 1);
        if less: s.byte_within(n, mid).zero_extend(56) < key {
            lower_bound_in(s, n, key, mid + 1, hi)
        } else {
            lower_bound_in(s, n, key, lo, mid)
        }
    } else {
        lo
    }
}

runtime fn lower_bound(s: List<u8>, n, key: u64) → u64 { lower_bound_in(s, n, key, 0, n) }
```

`lower_bound` answers the first offset whose byte is at least `key` (C++'s
`std::lower_bound`, Rust's `partition_point`). The loop halves `[lo, hi)`
each step.

The `decreases` clause says the range `hi - lo` gets smaller on each call.
Both calls go through the midpoint, and Heather proves this itself:
`bv_omega` reads `x >> 1` as half of `x`, rounded down, so the facts about
the midpoint are each one line.

```text
theorem midpoint_from(lo, hi: u64, h: lo < hi): lo <= lo + ((hi - lo) >> 1) { bv_omega }
theorem midpoint_below(lo, hi: u64, h: lo < hi): lo + ((hi - lo) >> 1) < hi { bv_omega }
```

## The midpoint everyone writes

The obvious midpoint is `(lo + hi) / 2`. For words it is wrong: the sum can
wrap past `2^64`, and the result then lands below `lo`. Joshua Bloch found
this bug in the JDK's `Arrays.binarySearch` in 2006, nine years after it
shipped. Heather states the bug as a theorem:

```text
theorem naive_midpoint_escapes(): ¬((lo, hi: u64) → lo < hi → lo <= (lo + hi) >> 1) {
    λ claim => {
        let lo: u64 = 0x8000000000000000;
        let hi: u64 = 0x8000000000000001;
        decide_bit_false<lo <= (lo + hi) >> 1>(refl, claim(lo, hi, decide_bit_true<lo < hi>(refl)))
    }
}
```

The counterexample is checked by evaluation. At `lo = 2^63` and
`hi = 2^63 + 1` the sum wraps to `1`, so the midpoint is `0`. The program
uses `lo + (hi - lo) / 2`, and `midpoint_from` and `midpoint_below` above
prove that it stays in `[lo, hi)`.

## What is proved

The specification needs the span to be sorted. `Ascending(s, n)` says so,
offset by offset. `Below(s, n, key, r)` says every byte before `r` is below
`key`, and `Above(s, n, key, r)` says no byte from `r` to the end is.

The main theorem says the answer splits the span at the right place:

```text
theorem lower_bound_splits(s: List<u8>, n, key: u64, asc: Ascending(s, n)):
    And<lower_bound(s, n, key) <= n,
        (j: u64) → j < n → Iff<s.byte_within(n, j).zero_extend(56) < key, j < lower_bound(s, n, key)>>
```

In words: a byte is below `key` exactly when it comes before the answer.

It rests on the loop's invariant:

```text
theorem lower_bound_in_splits(s: List<u8>, n, key, lo, hi: u64, asc: Ascending(s, n),
    order: lo <= hi, fits: hi <= n, below: Below(s, n, key, lo), above: Above(s, n, key, hi)):
    And<lower_bound_in(s, n, key, lo, hi) <= hi,
        And<Below(s, n, key, lower_bound_in(s, n, key, lo, hi)), Above(s, n, key, lower_bound_in(s, n, key, lo, hi))>>
```

What lies below `lo` is below `key`, and what lies from `hi` on is not. Each
step keeps that true. The proof is outside the program, and it follows the
program's own recursion: `induct lower_bound_in(s, n, key, lo, hi)` has one
arm per way the function can go. Each arm sees the tests that led there
under the names the program gave them (`h`, `less`), and an induction
hypothesis `ih` for the call it makes:

- When the byte at `mid` is below `key`, every byte up to `mid` is too,
  because the span ascends. So `Below` holds at `mid + 1`.
- When it is not below `key`, no byte from `mid` on is. So `Above` holds at
  `mid`.
- When the range is empty, `lo = hi`, and the two sides meet.

The proof never mentions the termination argument or the equations of the
function: the induction principle reuses the function's own. An arm left out
is closed by `known` (a hypothesis, a side of a conjunction, `omega` or
`bv_omega`) when it can be; here every case needs a line of thought.

The theorems are checked with the rest of the file:
`heather check examples/binary-search/search.hthr`.

## What the proof does not cover

- **The C driver** reads the input, checks that it is sorted (the theorem's
  `Ascending`), and prints the answer. It is outside the proof.
- **The comparison with other implementations** is a test, not a theorem.
  `crates/cli/tests/native_binary_search.rs` builds the tool as above and
  compares its answer with Rust's `partition_point` on sorted spans of every
  length up to 70, at every key that matters for each.
