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
    on ?dec1 := { right_smaller(lo, hi, h) };
    on ?dec2 := { left_smaller(lo, hi, h) };
}

runtime fn lower_bound(s: List<u8>, n, key: u64) → u64 { lower_bound_in(s, n, key, 0, n) }
```

`lower_bound` answers the first offset whose byte is at least `key` (C++'s
`std::lower_bound`, Rust's `partition_point`). The loop halves `[lo, hi)`
each step.

The `decreases` clause says the range `hi - lo` gets smaller on each call.
Heather cannot see that alone, because both calls go through the midpoint, so
the two `on` lines discharge it with `right_smaller` and `left_smaller`. Those
two lemmas rest on what the midpoint is:

```text
theorem midpoint_toNat(lo, hi: u64, h: lo < hi):
    (lo + ((hi - lo) >> 1)).toNat() = lo.toNat() + ((hi - lo) >> 1).toNat()
theorem midpoint_from(lo, hi: u64, h: lo < hi): lo.toNat() <= (lo + ((hi - lo) >> 1)).toNat()
theorem midpoint_below(lo, hi: u64, h: lo < hi): (lo + ((hi - lo) >> 1)).toNat() < hi.toNat()
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
uses `lo + (hi - lo) / 2`, and `midpoint_from` and `midpoint_below` prove
that it stays in `[lo, hi)`.

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
step keeps that true. It goes by induction on the same measure as the
program, one case per branch:

- When the byte at `mid` is below `key`, every byte up to `mid` is too,
  because the span ascends. So `Below` holds at `mid + 1`.
- When it is not below `key`, no byte from `mid` on is. So `Above` holds at
  `mid`.
- When the range is empty, `lo = hi`, and the two sides meet.

Each case takes one step of the loop with
`simp_only(lower_bound_in, discharge := bv_omega)`. Heather generates an
equation per branch of a function, and `simp_only` picks the one the facts
in scope decide: with the range not empty and the byte below the key, the
call is the call at `mid + 1`.

The theorems are checked with the rest of the file:
`heather check examples/binary-search/search.hthr`.

The range facts about `mid` (`mid < n`, `mid + 1 <= hi`, `j <= mid`) are
each one `bv_omega` in the invariant's context. `bv_omega` reads `mid`
through its `let` and cannot see through the shift that its addition does
not overflow; it then keeps `mid` whole, a number bounded by the facts that
mention it (`docs/tactics/bv-omega-design.md` §5.1).

## What the proof does not cover

- **The C driver** reads the input, checks that it is sorted (the theorem's
  `Ascending`), and prints the answer. It is outside the proof.
- **The comparison with other implementations** is a test, not a theorem.
  `crates/cli/tests/native_binary_search.rs` builds the tool as above and
  compares its answer with Rust's `partition_point` on sorted spans of every
  length up to 70, at every key that matters for each.
