# Heather

> This README was written by Claude, with the maintainer's feedback.

Heather is a dependently typed programming language and theorem prover. A
function and the theorems about it are written together, and the function
compiles to x86-64 machine code with a proof that the code computes it. A
small kernel checks every proof, so what is proved about a function holds
for the code that runs.

The examples below are taken from files in this repository, and a test
keeps them in step.

## Example

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

`split_all` splits a proof into one case for each branch of `clamp`.
`bv_omega` then proves each case: it is a decision procedure for linear
arithmetic on fixed-width integers.

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

With the assembly comes a proof about a formal model of x86-64: run on that
model with `x`, `lo` and `hi` in the argument registers, this code returns
`clamp(x, lo, hi)`. The kernel checks the proof before the file is written.
The compiler is written in Heather and proved correct
([what the proof covers](docs/native/compiler-theorem.md)).

## Writing to memory

A `mut self` span is a buffer the function writes to. This is insertion
sort, in place:

<!-- checked: examples/sort/sort.hthr -->
```rust
// Opens a hole for `key` in the sorted bytes before `j`, whose place `j` is
// free: each byte above `key` moves up one. Answers where the hole is.
runtime fn List::sift(mut self s: List<u8>, n, j, key: u64) → u64 decreases j.toNat() {
    if j = 0 { return j; }
    let below = s.byte_within(n, j - 1);
    if below.zero_extend(56) <= key { return j; }
    s.put_within(n, j, below);
    s.sift(n, j - 1, key)
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

A function that writes returns a `Mutated`: the buffer `after` the call, and
the call's `value`. The first theorem says the buffer is left sorted and a
permutation of the input. The second says it is exactly what the library's
functional insertion sort computes.
[`examples/sort/`](examples/sort/README.md) has the proofs and wraps the
compiled code in a command-line tool.

## SHA-256

`lib/native/crypto/` is SHA-256 written in Heather. Its state is a record
laid out over bytes, and its methods compile to code that updates those
bytes in place:

<!-- checked: lib/native/crypto/sha256_context.hthr -->
```rust
laid(endian := BigEndian) record Sha256 {
    hash: [u32; 8],
    working: [u32; 8],
    schedule: [u32; 64],
    count: u64
}
```

<!-- checked: lib/native/crypto/sha256_compression.hthr -->
```rust
// The hash value with the working variables added, word by word (step 4).
runtime fn Sha256::end(mut self s: Sha256) → u64 {
    for i in 0..8 {
        s.hash[i] := s.hash[i] + s.working[i];
    }
    8
}

runtime fn Sha256::run(mut self s: Sha256) → u64 {
    s.expand();
    s.begin();
    s.rounds();
    s.end()
}
```

Hashing a message gives the digest that FIPS 180-4 specifies:

<!-- checked: lib/native/crypto/sha256_stream_agreement.hthr -->
```rust
fn Sha256::digest_of(self s: Sha256, message: List<u8>, mn: u64) → List<u8> {
    let mut s = s;
    s.init();
    s.update(message, mn);
    s.finish();
    s.digest()
}

theorem Sha256::digest_of_spec(self s: Sha256, message: List<u8>, mn: u64, sized: message.len() = mn.toNat()):
    s.digest_of(message, mn) = Sha2::sha256().digest(message) { … }
```

Rust links the compiled code through `crates/linked`:

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
