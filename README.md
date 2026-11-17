# Heather

> This README was written by Claude, with the maintainer's feedback.

Heather is a dependently typed programming language and theorem prover. A
function and the theorems about it are written together, and the function
compiles to x86-64 machine code with a proof that the code computes it. A
small kernel checks every proof, so what is proved about a function holds
for the code that runs.

The examples below are taken from files in this repository, and a test
keeps them in step.

## A function and its theorems

<!-- checked: examples/readme/words.hthr -->
```rust
runtime fn clamp(x, lo, hi: u64) → u64 {
    if x < lo {
        lo
    } else if hi < x {
        hi
    } else {
        x
    }
}

// Inside the bounds, clamping changes nothing.
theorem clamp_inside({x, lo, hi: u64}, above: lo <= x, below: x <= hi): clamp(x, lo, hi) = x {
    split_all; all_goals { bv_omega }
}

// Whatever `x` is, the answer is within the bounds.
theorem clamp_within(x: u64, {lo, hi: u64}, ordered: lo <= hi): lo <= clamp(x, lo, hi) ∧ clamp(x, lo, hi) <= hi {
    split_all; all_goals { bv_omega }
}

// So clamping twice is clamping once.
theorem clamp_twice(x: u64, {lo, hi: u64}, ordered: lo <= hi): clamp(clamp(x, lo, hi), lo, hi) = clamp(x, lo, hi) {
    split_all; all_goals { bv_omega }
}
```

`split_all` takes a case for each branch of `clamp`, and `bv_omega` settles
the arithmetic on machine words in each case.

`runtime fn` marks a function to be compiled:

```sh
heather compile-x86 examples/readme/words.hthr clamp -o clamp.s
```

```asm
    cmp    %rsi,%rdi        # x < lo ?
    jae    1f
    mov    %rsi,%rax        # lo
    jmp    3f
1:  cmp    %rdi,%rdx        # hi < x ?
    jae    2f
    mov    %rdx,%rax        # hi
    jmp    3f
2:  mov    %rdi,%rax        # x
3:  ret
```

Before writing the file, the kernel checks that this code returns what
`clamp` returns. The compiler is written in Heather and proved correct
([what the proof covers](docs/native/compiler-theorem.md)).

## Loops

A function over a span of bytes compiles to a function of a pointer and a
length, and its tail recursion compiles to a loop. This one counts lines:

<!-- checked: examples/readme/lines.hthr -->
```rust
// How many of the span's bytes from `i` are newlines, added to `count`.
runtime fn List::newlines(self span: List<u8>, length, i, count: u64) → u64
    decreases (length - i).toNat() {
    if h: i < length {
        if span.byte_within(length, i) = 10 {
            span.newlines(length, i + 1, count + 1)
        } else {
            span.newlines(length, i + 1, count)
        }
    } else {
        count
    }
}

// At most one newline a byte.
theorem List::newlines_at_most(self span: List<u8>, length, i, count: u64,
    started: i <= length, room: count.toNat() + (length - i).toNat() < 2 ^ 64):
    span.newlines(length, i, count) <= count + (length - i) {
    induct List::newlines(span, length, i, count); all_goals { bv_omega }
}

// `wc -l`: the newlines among the span's first `length` bytes.
runtime fn List::count_lines(self span: List<u8>, length: u64) → u64 {
    span.newlines(length, 0, 0)
}

theorem List::count_lines_at_most(self span: List<u8>, length: u64): span.count_lines(length) <= length {
    let bound = span.newlines_at_most(length, 0, 0, bv_omega, bv_omega);
    bv_omega
}
```

`induct` is induction along the function's own recursion: one case for each
branch, with the claim already known for the recursive call.

## Writing to memory

A `mut self` span is a buffer the function writes to. This is insertion
sort, in place:

<!-- checked: examples/sort/sort.hthr -->
```rust
// Opens a hole for `key` in the sorted bytes before `j`, whose place `j` is
// free: each byte above `key` moves up one. Answers where the hole is.
runtime fn List::sift(mut self s: List<u8>, n, j, key: u64) → u64 decreases j.toNat() {
    if h: 0 < j {
        let below = s.byte_within(n, j - 1);
        if larger: key < below.zero_extend(56) {
            s.put_within(n, j, below);
            s.sift(n, j - 1, key)
        } else {
            j
        }
    } else {
        j
    }
}

runtime fn List::sort_from(mut self s: List<u8>, n, i: u64) → u64 decreases (n - i).toNat() {
    if h: i < n {
        let key = s.byte_within(n, i);
        let hole = s.sift(n, i, key.zero_extend(56));
        s.put_within(n, hole, key);
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

theorem sort_in_place_sorts(s: List<u8>, n: u64, sized: s.len() = n.toNat()):
    s.SortedPerm(BitVec::unsigned_le, sort_in_place(s, n).after) { … }

theorem sort_in_place_is_insertion_sort(s: List<u8>, n: u64, sized: s.len() = n.toNat()):
    sort_in_place(s, n).after = s.insertion_sort(BitVec::unsigned_le) { … }
```

`.after` is the buffer when the function returns. The first theorem says it
is sorted and a permutation of the input. The second says it is exactly what
the library's functional insertion sort computes.
[`examples/sort/`](examples/sort/README.md) has the proofs and wraps the
compiled code in a command-line tool.

## SHA-256

`lib/native/crypto/` is SHA-256 written in Heather. The hashing state is a
record laid out over bytes:

<!-- checked: lib/native/crypto/sha256_context.hthr -->
```rust
laid(endian := BigEndian) record Sha256 { hash: [u32; 8], working: [u32; 8], schedule: [u32; 64], count: u64 }

// What Rust must agree on with the compiled code: how many bytes a
// context is, and where the digest is once the message has ended (the
// hash value's thirty-two bytes). Numerals, because Rust's copies are
// generated from them (`crates/linked/generated/CONSTANTS.tsv`), and each
// is held to the declaration below.
def SHA256_CONTEXT_BYTES: Nat = 328;
def SHA256_DIGEST_AT: Nat = 0;

theorem Sha256::bytes_is(): Sha256::stored().layout.size = SHA256_CONTEXT_BYTES { refl }
theorem Sha256::digest_at_is(): Sha256::hash_part().offset = SHA256_DIGEST_AT { refl }

// The context a span holds.
fn Sha256::of(ctx: List<u8>) → Sha256 { Sha256::stored().get(ctx, 0) }

// One word of each array.
fn Sha256::hash_word(i: Nat, inside: i < 8) → Part<Sha256, u32>(Sha256::stored()) { Sha256::hash_part().then(Part::element(Stored::u32_be(), 8, i, inside)) }
fn Sha256::working_word(i: Nat, inside: i < 8) → Part<Sha256, u32>(Sha256::stored()) { Sha256::working_part().then(Part::element(Stored::u32_be(), 8, i, inside)) }
fn Sha256::schedule_word(i: Nat, inside: i < 64) → Part<Sha256, u32>(Sha256::stored()) { Sha256::schedule_part().then(Part::element(Stored::u32_be(), 64, i, inside)) }

// Where a word is: four bytes for each word before it, past where its
// array begins, which is the word the bodies add to.
theorem Sha256::hash_word_at(i: Nat, inside: i < 8): Sha256::hash_word(i, inside).offset = i * 4 + Sha256::hash_at.toNat() { refl }
theorem Sha256::working_word_at(i: Nat, inside: i < 8): Sha256::working_word(i, inside).offset = i * 4 + Sha256::working_at.toNat() { refl }
theorem Sha256::schedule_word_at(i: Nat, inside: i < 64): Sha256::schedule_word(i, inside).offset = i * 4 + Sha256::schedule_at.toNat() { refl }
theorem Sha256::count_word_at(): Sha256::count_part().offset = Sha256::count_at.toNat() { refl }

// What compiled code reads and stores there, as the context.

// Schedule word `i`, read by the accessor four bytes a word past where
// the schedule begins.
theorem Sha256::schedule_read(ctx: List<u8>, cn, at: u64, i: Nat, here: i < 64, place: at.toNat() = i * 4 + Sha256::schedule_at.toNat(), inside: at.toNat() + 4 <= cn.toNat()):
    ctx.u32_be_within(cn, at) = vector_index(Sha256::of(ctx).schedule, i, here).zero_extend(32) {
    ctx.u32_be_within_part(cn, at, Sha256::schedule_word(i, here), 0, refl, place, inside)
}
```

Its methods compile to functions that read and write those bytes in place:

<!-- checked: lib/native/crypto/sha256_stream.hthr -->
```rust
runtime fn Sha256::init(mut self s: Sha256) → u64 {
    s.hash := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
    s.count := 0;
    0
}

runtime fn Sha256::absorb(mut self s: Sha256, message: List<u8>, mn, j, fill: u64) → u64
    decreases (mn - j).toNat() {
    if h: j < mn {
        let filled = s.push(fill, message.byte_within(mn, j).zero_extend(56));
        s.absorb(message, mn, j + 1, filled)
    } else {
        fill
    }
}
```

The library proves that hashing a message this way gives the digest that
FIPS 180-4 specifies:

<!-- checked: lib/native/crypto/sha256_stream_agreement.hthr -->
```rust
theorem Sha256::digest_spec(s: Sha256, message: List<u8>, mn: u64, sized: message.len() = mn.toNat()):
    Sha256::digest(Sha256::finish(Sha256::update(Sha256::init(s).after, message, mn).after).after)
        = Sha2::sha256().digest(message) { … }
```

A second theorem, `Sha256::linked_digest`, says the same of the bytes the
compiled code leaves in memory. Rust links that code through
`crates/linked`:

<!-- checked: crates/linked/src/sha256.rs -->
```rust
pub fn digest(message: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(message);
    hash.finish()
}
```

## Optimizer rules

The optimizer rewrites code by rules, and a rule is a theorem about machine
words marked `rule`. The library's rules are written this way, and a program
can add its own:

<!-- checked: examples/x86-native/own_rule.hthr -->
```rust
rule theorem sub_self({w: Nat}, a: BitVec(w)): a - a = 0 { ring }

runtime fn first_and_nothing(s: List<u8>, n: u64) → u64 {
    if h: 0 < n {
        s.byte_within(n, 0).zero_extend(56) + (n - n)
    } else {
        0
    }
}
```

```sh
heather compile-x86 --explain-optimizer examples/x86-native/own_rule.hthr first_and_nothing -o own_rule.s
```

```text
  …
  t9 = t1 - t1 = 0   by sub_self
  t10 = t8 + 0 = t8   by add_zero
```

`--explain-optimizer` lists the rules the compiler used. The program's
`sub_self` removes the subtraction, and the library's `add_zero` then
removes the addition. The compiler uses a rule's proof to justify each
rewrite, so a new rule cannot make the compiled code wrong
([design](docs/native/optimizer-rules-design.md)).

## Mathematics

Heather is also a general theorem prover:

<!-- checked: examples/readme/sums.hthr -->
```rust
// 0 + 1 + … + n.
fn Nat::triangle(self n: Nat) → Nat {
    match n {
        Zero => 0,
        Succ(k) => k.triangle() + n,
    }
}

theorem Nat::triangle_closed(self n: Nat): 2 * n.triangle() = n * (n + 1) {
    match n {
        Zero => refl,
        Succ(k) => calc {
            2 * Succ(k).triangle() = 2 * (k.triangle() + Succ(k)) := refl,
            = Succ(k) * (Succ(k) + 1) := ring(k.triangle_closed()),
        },
    }
}
```

The standard library (`lib/std/`) includes rationals, constructive reals,
ordered algebra, floating point, regular languages and transition systems.

## Trying it

```sh
cargo build --release -p heather-cli
target/release/heather check --cache examples/readme/words.hthr
target/release/heather compile-x86 examples/readme/words.hthr clamp -o clamp.s
```

The first check of a file also checks the library modules it imports, which
takes a few minutes. `--cache` keeps the results, so later checks take
seconds. Compiling `clamp` takes a few minutes too. The compiled code is for
x86-64 Linux; [`examples/x86-native/`](examples/x86-native/README.md) shows
how to link it from C.

## How it works

- **The kernel** (`crates/kernel`) checks every definition and proof. The
  other parts only produce terms for it to check. Its type theory is DeLaM
  (`docs/delam/`), in which a program can inspect code as syntax.
- **The elaborator** (`crates/elab`) does type inference, pattern matching,
  type classes and tactics.
- **The compiler** (`lib/native/`) is written in Heather. A `runtime fn` is
  compiled by reading the function's own body, and the output is accepted
  because of the proof that comes with it.
- **Memory layout, borrowing of buffers and effects** are library
  definitions, not kernel features.

## Repository layout

- `lib/std`: the standard library. `lib/native`: the compiler and SHA-256.
  `lib/lang`: Heather's lexer, in Heather. `lib/_tests`: tests of the
  library.
- `crates/kernel`, `crates/elab`, `crates/syntax` (lexer and parser),
  `crates/cli` (the `heather` binary), `crates/linked` (compiled Heather
  linked into Rust), `crates/lsp` (editor support).
- `book/`: the language guide. `docs/`: design documents
  ([map](docs/README.md), [roadmap](docs/roadmap.md)).
- `issues/`: the issue tracker.
