# A span that carries its length

Status: design, 2026-11-17, with the first pieces probed. Decisions are
Minus's (2026-11-17): a span is a record that carries its length, and a
read takes a found proof that the index is inside; *"junk values as a
default API are usually a mistake; they're a sign of needing better
automation."* Builds on `span-statements-design.md` (a function of spans
stated by its spans) and `docs/language/sequencing-surface-design.md` §21–22
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
`Bytes(n)` gets a second meaning `FTm::over` that threads `Bytes(n)`
instead, and one agreement theorem says that the two agree when the record's
`bytes` and `n` are the list and word `sem` reads. Because `Bytes::put`
unfolds to the same store `sem` performs (`with_byte_within`), and
`Bytes::at` to the same read, each generated pin still closes by
conversion: the generator emits no per-function proof beyond what laid
records already get. A counted loop's agreement is the analogue of
`counted_held` for laid records, proved once over `FFun::rounds`.

## Facts reach the loops

A loop lifted to a method (§22 of the sequencing note) is a function of its
own; what the body proves must come from its parameters. Three pieces:

1. **Captured facts.** A hypothesis in scope about captures only (the
   enclosing `for`'s `i < s.len()`) is passed to the lifted loop as a
   squashed parameter and found again by `bv_omega` inside.
2. **`invariant P`.** A `while` may state an invariant, checked at the entry
   and at each recursion (found proofs at the call), assumed in the body as
   a squashed parameter, and available after the loop together with the
   negated test. The insertion sort's inner loop needs `j ≤ i < s.len()`.
3. **Short-circuit `∧` in a condition.** `0 < j ∧ key < s[j - 1]` lowers
   to nested tests, so `s[j - 1]` is elaborated under `0 < j`, and `j - 1`
   does not wrap. (Rust's `&&` reads the same once the parser gives `&&`
   lower precedence than comparisons; that is a surface change for Minus.)

## Probed so far

In a scratch module, before any of it is in the library:

- `Bytes(n)` with `len`/`at`/`put` as above elaborates; `s.at(0)` under
  `if h: 0 < s.len()` finds its proof.
- A lifted loop at a `Bytes(n)` receiver needs the implicit `{n}`: the
  loop lifter now passes an implicit parameter the state's or a capture's
  type mentions as a capture, placed before the receiver whose type names
  it.
- A `for` whose upper bound reads the state (`0..s.len()` while `s` is
  stored to) reads the bound once at the entry, as Rust does, and the
  lifted loop takes it as a capture; before, the measure read the rebound
  receiver and its decrease was not provable.
- The sort written as nested lifted loops over `List<u8>` with a word key
  compiles (`compile-x86`) and agrees with `qsort` on random inputs.

## Not built

- `Bytes` in the library, `FTm::over` and its agreement, the generator
  reading a `Bytes(n)` parameter.
- Captured facts, `invariant`, short-circuit `∧`.
- `u8` parameters across the native boundary (span writers take and return
  64-bit words for now; `issues/runtime-repr-narrow-words.md`).
- A loop whose state is two locals besides the receiver (its state record
  has no runtime layout yet).
