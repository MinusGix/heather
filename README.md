# Heather

Heather is a dependently typed language in which a program and the theorems
about it are written side by side, in one file, and the program is then
compiled to x86-64 machine code that carries its own proof. A function
marked `runtime fn` is compiled by a compiler written in Heather; what it
emits is checked by the kernel to compute the function it came from, and
everything proved about that function holds of the bytes.

Proofs read like the mathematics they state: methods on the type, `calc`
chains, and tactics (`split_all`, `omega`, `bv_omega`, `ring`, `simp`,
`grind`) where a step is routine. The same language holds the standard
library, the compiler's own correctness proof, and code that Rust links
today (SHA-256 and a lexer, `crates/linked`).

Every Heather example below is checked: each block names the file it is
taken from, and a test (`crates/cli/tests/readme.rs`) holds the README to
those files. The README's own are in [`examples/readme/`](examples/readme/).

## A function, its theorems, its bytes

<!-- checked: examples/readme/words.hthr -->
```heather
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
    let within = clamp_within(x, ordered);
    clamp_inside(within.left, within.right)
}
```

`split_all` splits the goal on each test `clamp` makes, and `bv_omega`
decides the linear facts about machine words left in each case.

`heather compile-x86 examples/readme/words.hthr clamp -o clamp.s` writes the
function as 46 bytes of x86-64:

```text
    add    $-0x70,%rsp      ; its room on the stack
    cmp    %rsi,%rdi        ; x < lo ?
    jae    1f
    mov    %rsi,%rax        ; lo
    jmp    3f
1:  cmp    %rdi,%rdx        ; hi < x ?
    jae    2f
    mov    %rdx,%rax        ; hi
    jmp    3f
2:  mov    %rdi,%rax        ; x
3:  add    $0x70,%rsp
    ret
```

and a certificate beside them, which the kernel checks before anything is
written. It is two theorems put together. The first is the generator's,
published with every `runtime fn`: the program it built from `clamp`'s body
computes `clamp`.

<!-- checked: examples/readme/words.hthr -->
```heather
theorem clamp_program(x, lo, hi: u64): program_eval(clamp::program, 0, [x, lo, hi]) = clamp(x, lo, hi) {
    clamp::agrees(x, lo, hi)
}
```

The second is the compiler's correctness, proved once in
`lib/native/function_ir/`: any program it lowers, called at a function's
label with the arguments in their registers, returns what the program
computes in RAX, keeps the callee-saved registers, and stores nowhere but
its own room on the stack.

<!-- checked: lib/native/function_ir/function_ir_compile.hthr -->
```heather
theorem compiled_returns<M>(functions: List<Function>, placement: List<Place>, program: Prog,
    lowered: lower_program(functions, placement) = Some(program), evaluable: program_evaluable(functions).IsTrue(),
    fetch: FetchAccess<M>, data: ByteReadAccess<M>, last: List<BitVec(8)>, origin: BitVec(64), stack: Stack<M>(fetch, data),
    f: Nat, below: Succ(f) <= functions.len(), arguments: List<BitVec(64)>,
    fits: arity_fits(program_arity(functions, f), arguments.len()).IsTrue(), answer: BitVec(64),
    evaluates: program_eval(functions, f, arguments) = answer):
    Site<M>(fetch, data, program, last, origin).Returns(stack, asm_labels(program)(Succ(f)),
        λ (i: Nat) (s: MachineState<M>) => stack.Passed(arguments, i, s) ∧ 136 * Succ(f) <= i,
        stack.CalleePost(answer))
```

The certificate instantiates it at `clamp`'s program, its lowering (a
literal, checked by evaluation) and `clamp_program`. So `clamp_within` is a
fact about what these bytes return, and nothing in `words.hthr` mentions a
register. The platform around the code (the loader, stack alignment, the C
caller) is outside the proof.

## SHA-256, compiled and proved

`lib/native/crypto/` is SHA-256 as Heather source. Rust links the compiled
functions (`heather_linked::sha256`), and the library proves that what they
leave in memory is the digest FIPS 180-4 specifies.

The context is a record laid over bytes: the declaration chooses where each
field lies, and publishes how the record is bytes and where each field is
for the compiled code to read and store.

<!-- checked: lib/native/crypto/sha256_context.hthr -->
```heather
laid(endian := BigEndian) record Sha256 {
    hash: [u32; 8],
    working: [u32; 8],
    schedule: [u32; 64],
    count: u64
}
```

Functions of it are `mut self` methods. Each compiles to a function of a
byte span, and a store to a field becomes a store at that field's offset:

<!-- checked: lib/native/crypto/sha256_stream.hthr -->
```heather
runtime fn Sha256::init(mut self s: Sha256) → u64 {
    s.hash := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
               0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
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

runtime fn Sha256::update(mut self s: Sha256, message: List<u8>, mn: u64) → u64 {
    s.take(message, mn, s.count)
}

runtime fn Sha256::finish(mut self s: Sha256) → u64 {
    s.close(s.count)
}
```

A word function is compiled at the width the machine has and proved to be
the standard's at the width the standard gives, by evaluation:

<!-- checked: lib/native/crypto/sha256_round.hthr -->
```heather
runtime fn sha256_t2(a, b, c: u64) → u64 {
    let a32 = a.truncate(32, 32);
    let b32 = b.truncate(32, 32);
    let c32 = c.truncate(32, 32);
    let big0 = a32.rotr(2) ⊕ a32.rotr(13) ⊕ a32.rotr(22);
    let maj = (a32 & b32) ⊕ (a32 & c32) ⊕ (b32 & c32);
    (big0 + maj).zero_extend(32)
}

fn sha256_t2_narrow(a, b, c: u32) → u32 {
    let big0 = a.rotr(2) ⊕ a.rotr(13) ⊕ a.rotr(22);
    let maj = (a & b) ⊕ (a & c) ⊕ (b & c);
    big0 + maj
}

theorem sha256_t2_low(a, b, c: u64):
    sha256_t2(a, b, c) =
        sha256_t2_narrow(a.truncate(32, 32), b.truncate(32, 32), c.truncate(32, 32)).zero_extend(32)
{ refl }

theorem sha256_t2_narrow_spec(s: Sha2State(32)):
    sha256_t2_narrow(s.a, s.b, s.c) = Sha2::sha256().t2(s)
{ refl }
```

And the whole stream: first on the record, then on the bytes the compiled
code leaves.

<!-- checked: lib/native/crypto/sha256_stream_agreement.hthr -->
```heather
theorem Sha256::digest_spec(s: Sha256, message: List<u8>, mn: u64, sized: message.len() = mn.toNat()):
    Sha256::digest(Sha256::finish(Sha256::update(Sha256::init(s).after, message, mn).after).after)
        = Sha2::sha256().digest(message) { … }

// The linked hash, on the bytes: a span that holds any context, after the
// code of `init`, `update` over the message and `finish`, has the
// specification's digest where the context lays its hash value.
theorem Sha256::linked_digest(span: List<u8>, s: Sha256, length: u64, message: List<u8>, mn: u64,
    holds: Sha256::stored().Holds(span, length, s), sized: message.len() = mn.toNat()):
    Sha256::finish::bytes(
        Sha256::update::bytes(
            Sha256::init::bytes(span, length).after,
            length, message, mn).after,
        length).after
        .window(SHA256_DIGEST_AT, 32 + SHA256_DIGEST_AT) = Sha2::sha256().digest(message) { … }
```

`Sha256::init::bytes` and its fellows are what the generator publishes for
each `runtime fn`: the function as the compiled code runs it, over the span.
The Rust side is a thin wrapper that hands the linked functions a buffer:

```rust
let mut hash = heather_linked::sha256::stream::Sha256::new();
hash.update(b"abc");
let digest: [u8; 32] = hash.finish();
```

## Plain mathematics

The same language, with nothing compiled:

<!-- checked: examples/readme/sums.hthr -->
```heather
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

The library has real numbers (constructive, with interval enclosures),
rationals, ordered algebra, regular languages, transition systems,
interaction trees, floating point and more, under `lib/std/`.

## Trying it

```sh
cargo build --release -p heather-cli
target/release/heather check --cache examples/readme/words.hthr
target/release/heather compile-x86 examples/readme/words.hthr clamp -o clamp.s
```

The first check of a file elaborates the library modules it imports and
takes a minute or two; `--cache` keeps them, and later checks take seconds.
To link the result from C or Rust, see
[`examples/x86-native/`](examples/x86-native/README.md).

## How it fits together

- **The kernel** (`crates/kernel`) checks every declaration. Its type theory
  is DeLaM, a dependent layered modal type theory (`docs/delam/`), whose box
  modality gives a program intensional access to code as syntax. That is how
  a `runtime fn` is compiled: a generator reads the function's own body and
  publishes its program and the proof that the program agrees with it.
- **Compilation is certifying.** The compiler (`lib/native/`) is an ordinary
  Heather function, privileged operationally and never logically: what it
  emits is accepted because of the certificate it comes with.
- **The elaborator** (`crates/elab`) does inference, pattern matching,
  classes and tactics; it is outside the trusted base.
- **Disciplines are libraries.** Layout, lending of spans, and the effects a
  program may perform are Heather definitions and analyses over code, not
  kernel features.

## Layout

- `lib/std` — the standard library; `lib/native` — the compiler and the
  native SHA-256; `lib/lang` — Heather's lexer in Heather; `lib/_tests` —
  probes, mirroring `lib/`
- `crates/kernel` — the trusted checker; `crates/elab` — elaboration;
  `crates/syntax` — lexer and parser; `crates/cli` — the `heather` binary;
  `crates/linked` — compiled Heather linked into Rust; `crates/lsp` — editor
  support
- `book/` — the language guide (`mdbook build`); `docs/` — design documents,
  starting from [`docs/roadmap.md`](docs/roadmap.md)
- `issues/` — the issue tracker (`scripts/issue`, `issues/README.md`)
