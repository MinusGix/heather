# A span that carries its length

Status: design, 2026-11-17, with the first pieces probed. Decisions are
Minus's (2026-11-17): a span is a record that carries its length, and a
read takes a found proof that the index is inside; *"junk values as a
default API are usually a mistake; they're a sign of needing better
automation."* Builds on `span-statements-design.md` (a function of spans
stated by its spans) and `docs/language/sequencing-surface-design.md` §21, §23
(loops over words, loops at a `mut self` receiver).

## The goal

`examples/sort/sort.hthr` reads as the algorithm, with its theorems kept:

```
runtime fn Bytes::sort({n: u64}, mut self s: Bytes(n)) → … {
    for i in 0..s.len() {
        let key = s[i];
        let mut j = i;
        while 0 < j ∧ key < s[j - 1] { s[j] := s[j - 1]; j := j - 1; }
        s[j] := key;
    }
}
```

and the same for `examples/readme/lines.hthr`, binary search and the UTF-8
validator. Today the span is a `List<u8>` with a word `n` passed beside it,
every read is `byte_within(n, i)` (which answers 0 past the end: a junk
value), bytes are compared through `zero_extend(56)`, and the loops are
written as measured recursion by hand.

## The record

```
record Bytes(n: u64) { bytes: List<u8>, sized: bytes.len() = n.toNat() }
fn Bytes::len({n: u64}, self s: Bytes(n)) → u64 { n }
fn Bytes::at({n}, self s: Bytes(n), i: u64, inside: ∥i < s.len()∥ := bv_omega) → u8
fn Bytes::put({n}, self s: Bytes(n), i: u64, v: u8, inside: ∥i < s.len()∥ := bv_omega) → Bytes(n)
```

- **The length is in the type**, so `put` keeps it by construction and a
  loop's measure over `s.len()` is a measure over `n`, which no store
  touches.
- **`sized` is a plain field, not a squash.** The unifier reads a record's
  value parameter from a field that mentions it; under `∥…∥` it cannot
  (a squash is never released, so nothing may be solved from inside one),
  and `Bytes(n)`'s `n` would then be uninferable at every call. The field
  costs nothing at run time: the layout carries `bytes` as the span and `n`
  as its length word, and the proof field has no layout.
- **`s[i]` is `s.at(i)` and `s[i] := e` is `s := s.put(i, e)`**, the
  mapping `[A; n]` already has (`Vec::at`/`Vec::put`). The found proof is
  `bv_omega` over the context, so a read under the loop's test `i < s.len()`
  needs nothing written. The body of `at` reads `byte_within`, whose 0 past
  the end is unreachable: a proof is in hand.
- Bytes compare as bytes: `key < s[j - 1]` is `u8`'s `<`, with no widening.

## Compiling it: a second meaning, proved once

The span reflector (`rt_file_reflect.hthr`) gives a reflected program `FTm`
a meaning `FTm::sem` over a `List<u8>` and a length word. A function over
`Bytes(n)` gets a second meaning `FTm::over` (`rt_bytes.hthr`) that threads
`Bytes(n)` instead, and one agreement theorem (`FTm::over_runs`) says that
the two agree when the record's `bytes` and `n` are the list and word `sem`
reads. Because `Bytes::put` unfolds to the store `sem` performs
(`Bytes::stored_under`, `with_byte_within`) and `Bytes::at` to the same
read, a function of a `Bytes(n)` *is* its reflection's meaning over the
record, by conversion: the generator emits no per-function proof.

`runtime fn f` of a `Bytes(n)` (`runtime_bytes`, runtime.hthr) compiles
the reflection written out as a function of the record's bytes and `n`,
`f::bytes`, and publishes `f::runs_bytes`: at every record `s`, `f(s, …)`
and `f::bytes(s.bytes, n, …)` agree (`Over`: the record's bytes after are
the code's span after, and the values are one).

- **A loop** (`rt_bytes_loop.hthr`) is the analogue of `counted_held` for
  laid records: the pass over the record agrees with the pass over its
  bytes (`FTm::tail_over_runs`), and `FFun::counted_over` turns the
  function's own equation into agreement with the counted iteration. The
  equation is read off the lifted loop's `f::ext` and `f::irrel`; the
  function and its measure are taken at every length (`FFun::OverRun`),
  because the recursion `f::rec` is: `n` is a capture the loop passes on.
- **A call** of another runtime fn of a `Bytes(n)` reads it, in the
  program's tables, as its code `g::bytes`, and over the record as `g`
  itself. The caller's world keeps its promise (`BWorld::agrees_each`)
  from each callee's own `g::runs_bytes`, read with the callee's code a
  parameter (`HWorld::at`) so the kernel never unfolds a callee's passes;
  the caller's theorem is proved the same way, at its callees as
  parameters.

## Facts reach the loops

A loop lifted to a method (§23 of the sequencing note) is a function of its
own; what the body proves must come from its parameters. Three pieces:

1. **`invariant P`.** A `while` may state an invariant, checked at the entry
   and at each recursion (found proofs at the call), assumed in the body as
   a squashed parameter, and available after the loop together with the
   negated test. The insertion sort's inner loop states `j <= i`.
   A fact the loop cannot change (the enclosing `for`'s `i < s.len()`) is
   given to it without being stated (sequencing note §23.5).
2. **Short-circuit tests.** `0 < j && key < s[j - 1]` lowers to nested
   tests, so `s[j - 1]` is elaborated under `0 < j`, and `j - 1` does not
   wrap. `&&` and `||` bind looser than the relations (Minus,
   2026-11-17), so this reads as in Rust.

As built: `docs/language/sequencing-surface-design.md` §23.4 and §23.5.

## Probed so far

In a scratch module, before any of it is in the library:

- `Bytes(n)` with `len`/`at`/`put` as above elaborates; `s.at(0)` under
  `if h: 0 < s.len()` finds its proof.
- A lifted loop at a `Bytes(n)` receiver needs the implicit `{n}`: the
  loop lifter now passes an implicit parameter the state's or a capture's
  type mentions as a capture, placed before the receiver whose type names
  it.
- A `for` whose upper bound reads the state (`0..s.len()` while `s` is
  stored to): `s.len()` steps to `n`, which no store changes, and
  `bv_omega` reads a word call that steps to a local as that local
  (`Shape::Alias`), so the measure's decrease is proved as written.
- The sort written as nested lifted loops over `List<u8>` with a word key
  compiles (`compile-x86`) and agrees with `qsort` on random inputs.
- The whole insertion sort over `Bytes(n)` elaborates and sorts by
  evaluation (`lib/_tests/native/runtime/runtime_lifted_loops_tests.hthr`,
  `Bytes::sort`): the final `s[j] := key` reads `j <= i` at the inner
  loop's result.
- The insertion sort's inner loop over `Bytes(n)`, with its invariant,
  elaborates in about 2 s. It took 15 s while a found proof that reads a
  `let`'s value was searched for at every copy of the body the
  companions make (`issues/squashed-found-proof-searched-per-copy.md`).

## Not built

- A loop whose parameters include facts (an `invariant`, or a test it runs
  under, such as the sort's inner loop's `∥j <= i∥` and `∥i < s.len()∥`):
  the function of the record at a state needs the facts there, which the
  code does not carry.
- `let key = s[i]` unannotated before a loop (the sort writes `: u8`).
- `u8` parameters across the native boundary (span writers take and return
  64-bit words for now; `issues/runtime-repr-narrow-words.md`).
- A loop whose state is two locals besides the receiver (its state record
  has no runtime layout yet).
