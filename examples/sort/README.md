# A proved in-place sort

`sort.hthr` is an insertion sort written in Heather, compiled to x86-64, and
proved to sort the bytes of a span in place. The proof ends in one line: the
compiled sort computes the library's `List::insertion_sort`, which is already
proved to sort. `main.c` wraps it in a command-line tool that sorts its input.

## Build it and run it

From the repository root, on x86-64 Linux with a C compiler:

```sh
cargo build --release -p heather-cli
mkdir -p target/sort
target/release/heather compile-x86 examples/sort/sort.hthr sort_in_place \
  -o target/sort/sort.s --cache-dir target/native-images
cc -std=c11 -O2 examples/sort/main.c target/sort/sort.s -o target/sort/bytesort
printf 'hello world' | target/sort/bytesort    # " dehllloorw"
```

`compile-x86` checks every proof in the file before it emits anything, and
the assembly comes with a certificate (`sort.certificate.hthr`) that the
kernel checks too: the machine code computes the Heather function. The C
side calls it as

```c
uint64_t sort_in_place(uint8_t *bytes, uint64_t length);
```

## The program

```text
runtime fn List::insert_below(mut self s: List<u8>, n, j, x: u64) → u64 decreases j.toNat() {
    if h: 0 < j {
        if larger: x < s.byte_within(n, j - 1).zero_extend(56) {
            s.put_within(n, j, s.byte_within(n, j - 1));
            s.insert_below(n, j - 1, x)
        } else {
            s.put_within(n, j, x.truncate(8, 56));
            j
        }
    } else {
        s.put_within(n, j, x.truncate(8, 56));
        j
    }
}

runtime fn List::sort_from(mut self s: List<u8>, n, i: u64) → u64 decreases (n - i).toNat() {
    if h: i < n {
        s.insert_below(n, i, s.byte_within(n, i).zero_extend(56));
        s.sort_from(n, i + 1)
    } else {
        i
    }
}

runtime fn sort_in_place(s: List<u8>, n: u64) → Mutated<List<u8>, u64> {
    let mut s = s;
    let end = s.sort_from(n, 0);
    Mutated(s, end)
}
```

`mut self` makes the span a place the function writes: `s.put_within(n, j, b)`
stores byte `b` at offset `j`, and the compiled code writes the caller's
buffer. `sort_from` walks `i` up the span; everything before `i` is already
sorted. `insert_below` takes the byte that was at `i` and walks down, moving
each larger byte up one place, and drops it where the first byte that is not
larger was. The usual inner loop of insertion sort, as a recursion that the
compiler turns into a loop.

Both loops are measured. `insert_below` stops because `j` falls, and
`sort_from` because `n - i` does. Unlike the binary search, Heather discharges
both decreases on its own.

## What is proved

The specification is the library's. `s.SortedPerm(R, out)` says `out` is
`R`-sorted and a permutation of `s` (`lib/std/data/sorting.hthr`). The
headline:

```text
theorem sort_in_place_sorts(s: List<u8>, n: u64, sized: s.len() = n.toNat()):
    s.SortedPerm(BitVec::unsigned_le, sort_in_place(s, n).after)

theorem sort_in_place_is_insertion_sort(s: List<u8>, n: u64, sized: s.len() = n.toNat()):
    sort_in_place(s, n).after = s.insertion_sort(BitVec::unsigned_le)
```

`.after` is the span as the function leaves it. The second theorem follows from
the first in one step, because a list has only one sorted permutation under a
linear order (`sorted_perm_unique`). So the compiled loop is equal, as a
function on lists, to the textbook functional insertion sort.

The proof has two layers, one per loop.

**One insertion.** Split the span at `j` as `ys ++ [z] ++ rest`: the sorted
bytes before `j`, the free place, and the rest. Then

```text
theorem insert_below_inserts(ys: List<u8>, z: u8, rest: List<u8>, n, j: u64, b: u8,
    sized: (ys ++ Cons(z, rest)).len() = n.toNat(), at: ys.len() = j.toNat(), sorted: ys.Sorted(BitVec::unsigned_le)):
    List::insert_below(ys ++ Cons(z, rest), n, j, b.zero_extend(56)).after = ys.insert_ordered(BitVec::unsigned_le, b) ++ rest
```

The loop that shuffles bytes up a buffer is the functional `insert_ordered` on
the prefix. It goes by induction on `j`, one case per branch, each a `calc`
chain:

- When the byte below `j` is larger, it moves up, and the induction
  hypothesis inserts `b` into what is left. Inserting below the last element
  is inserting before it (`insert_ordered_snoc`).
- When it is not larger, `b` lands at `j`. The prefix with `b` at its end is
  sorted, and it holds `b` and `ys`, so it is the insertion
  (`insert_ordered_unique`).
- When `j` is `0`, the prefix is empty.

**The outer loop.** `sort_from_sorts` is the invariant: if the bytes before
`i` are sorted, `sort_from` leaves a sorted permutation. Each pass
(`sort_from_step`) splits the span at `i`, reads the byte there, uses
`insert_below_inserts` to see the longer sorted prefix, and chains the
permutations (`perm_middle`, `perm_of_picks`). It goes by induction on what
is left, `n - i`.

The general facts the proof needed went into the library rather than staying
here: list splits and updates in `lib/std/data/list_window.hthr`
(`split_at`, `split_last`, `update_append_r`, `take_all`), and sorted lists
grown at the end in `lib/std/data/sorting.hthr` (`sorted_snoc`,
`insert_ordered_snoc`, `insert_ordered_unique`).

The theorems are checked with the rest of the file:
`heather check examples/sort/sort.hthr`.

## What the proof does not cover

- **The C driver** reads standard input and writes the sorted bytes back. It
  is outside the proof.
- **The comparison with other implementations** is a test, not a theorem.
  `crates/cli/tests/native_sort.rs` builds the tool as above and compares its
  output with Rust's `slice::sort`. It runs on reversed, constant and
  pseudorandom inputs of every length up to 100, over narrow and wide
  alphabets.

## Rough edges

- The key goes to `insert_below` as a word, `x: u64`, and is stored with
  `x.truncate(8, 56)`. The natural spelling reads the byte at `j` inside the
  loop, then stores over it, and the compiler does not yet allow a read
  before a store to the same span within one function
  (`issues/rt-file-read-before-store.md`).
- The proofs cite the generated branch equations by name
  (`List::insert_below::True::True` and so on). A tactic that unfolds a
  measured function at its hypotheses would remove them.
- The outer loop's invariant goes by induction on a `Nat` standing for
  `n - i`, with the step as its own lemma. The direct `decreases` proof that
  `if h: i < n` would give is refused by the kernel today
  (`issues/theorem-branch-on-measured-fn-goal.md`).
- `insert_below` spells the read below `j` twice rather than binding it with
  `let`, which the companion generator does not yet read
  (`issues/runtime-mut-self-let-read-walk.md`).
