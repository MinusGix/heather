# A proved UTF-8 validator

`utf8_check.hthr` is a UTF-8 validator written in Heather, compiled to x86-64,
and proved to answer exactly what a strict UTF-8 decoder answers. It comes as
a command-line tool two ways: `utf8check.hthr` is a whole program in Heather,
with no C, that exits with the verdict; `main.c` wraps the compiled function
in a C tool that also prints where the first bad byte is.

## Build it and run it

From the repository root, on x86-64 Linux with a C compiler:

```sh
cargo build --release -p heather-cli
mkdir -p target/utf8
target/release/heather compile-x86 examples/utf8/utf8_check.hthr utf8_valid_up_to \
  -o target/utf8/utf8.s --cache-dir target/native-images
cc -std=c11 -O2 examples/utf8/main.c target/utf8/utf8.s -o target/utf8/utf8check
printf 'h\xc3\xa9llo \xe2\x82\xac \xf0\x9f\x98\x80' | target/utf8/utf8check   # valid
printf 'ab\xed\xa0\x80cd' | target/utf8/utf8check                           # invalid at byte 2
```

`compile-x86` checks every proof in the file before it emits anything, and
the assembly comes with a certificate (`utf8.certificate.hthr`) that the
kernel checks too: the machine code computes the Heather function.

### With no C

```sh
target/release/heather write-elf examples/utf8/utf8check.hthr -o target/utf8/utf8valid
printf 'h\xc3\xa9llo \xe2\x82\xac' | target/utf8/utf8valid; echo $?   # 0
printf 'ab\xed\xa0\x80cd' | target/utf8/utf8valid; echo $?           # 1
```

`utf8check.hthr`'s `main` is the whole program:

```text
runtime fn main(mut io: Io, buf: ByteBuffer(65536)) → Partial(Mutated<Io, u64>) {
    let mut buf = buf;
    let mut filled: u64 = 0;
    let mut going: u64 = 1;
    let mut failed: u64 = 0;
    while 0 < going {
        let room = 65536 - filled;
        let r = io.read_into(Io::stdin(), buf, filled, room);
        let bad = room < r.result;
        buf := r.buf;
        failed := if bad { 1 } else { 0 };
        going := if bad { 0 } else if r.result = 0 { 0 } else { 1 };
        filled := if bad { filled } else { filled + r.result };
    }
    let m = utf8_status(buf, BitVec::ofNat(buf.len()), filled, failed);
    Pointed::ret(Mutated(io, m.value))
}
```

It reads standard input into its buffer until a read brings nothing, then
lends the buffer to `utf8_status`, which runs the validator over the bytes
read, and exits with its answer: 0 for UTF-8, 1 for not, 2 when the read
failed or the input filled the buffer. `write-elf` builds a Linux executable
of about 3.7 KB with nothing linked in, and the kernel checks a certificate
that the executable is the compile of `main::source`, the program the
generator made of `main`. Two theorems say what that program does:

- `main::reads`: the source's behaviour, read against any world (any input,
  any outcome of each read), is `main` itself, started from a zeroed buffer;
- `utf8_status_answers`: after a read that did not fail and left room,
  `utf8_status` answers 0 exactly when the bytes read are UTF-8
  (`utf8::is_utf8(span.take(filled))`).

## The program

The validator is ordinary code over a span of bytes, `s` with its length `n`
(`runtime fn` marks a function the compiler turns into machine code):

```text
runtime fn utf8_valid_from(s: List<u8>, n, i, left: u64) → u64 decreases left.toNat() {
    if h: 0 < left {
        let b = s.byte_within(n, i).zero_extend(56);
        if b < 0x80 {
            utf8_valid_from(s, n, i + 1, left - 1)
        } else if b < 0xC0 {
            i
        } else if b < 0xE0 {
            if h2: 1 < left {
                if utf8_two_at(s, n, i) = 0 { i } else { utf8_valid_from(s, n, i + 2, left - 2) }
            } else {
                i
            }
        } else if …            // three and four bytes, the same shape
    } else {
        i
    }
}

runtime fn utf8_valid_up_to(s: List<u8>, n: u64) → u64 { utf8_valid_from(s, n, 0, n) }
```

It looks at the lead byte, checks that enough bytes are left, and hands the
sequence to `utf8_two`, `utf8_three` or `utf8_four`. Those check the
continuation bytes' `10xxxxxx` headers, assemble the scalar value with shifts
and masks, and refuse what a strict decoder refuses: overlong forms (`C0 80`
for NUL), the surrogates `D800`–`DFFF`, and values above `10FFFF`. The answer
is the offset where the first bad sequence starts, or `n` when there is none.

`left` counts the bytes still to read, so every recursive call visibly
shrinks it; that is the loop's termination proof, found automatically.

## What is proved

The specification is `lib/std/text/utf8.hthr`: `utf8::encode`, which turns a
`String` (a list of Unicode scalar values) into bytes, and `utf8::decode`, a
strict decoder (Rust's `str::from_utf8` rules). The library already proves the
two inverse: `decode(encode(s)) = Some(s)`, and `decode(bytes) = Some(s)`
only when `encode(s) = bytes`.

The headline theorem says the compiled function accepts exactly the
encodings of strings:

```text
theorem utf8_valid_up_to_iff(s: List<u8>, n: u64, sized: s.len() = n.toNat()):
    (utf8_valid_up_to(s, n) = n) ↔ (∃ t: String, utf8::encode(t) = s)
```

It rests on the loop's agreement with the decoder at every offset:

```text
theorem valid_from_decides(s: List<u8>, n, i, left: u64,
    sized: s.len() = n.toNat(), here: i.toNat() + left.toNat() = n.toNat()):
    utf8_valid_from(s, n, i, left).eq_bit(n) = utf8::is_utf8(s.drop(i.toNat()))
```

## How the proof goes

The program and the decoder are written differently on purpose. The program
compares words against bounds (`b < 0xE0`, `code < 0x800`); the decoder reads
header bits and joins payloads with `concat`. The proof meets them in three
layers.

1. **Bytes.** A claim about one byte is checked at all 256 by evaluation
   (`Fintype::all<u8>`), so `cont_word` (the program's `c & 0xC0 = 0x80` is
   the decoder's continuation header) and the payload facts (`c & 0x3F` is
   the decoder's six payload bits) are each one line.
2. **Sequences.** `two_decides`, `three_decides` and `four_decides` say the
   helper refuses exactly when the decoder's step for that class fails. Each
   rewrites the helper into its tests (`split_all; all_goals { refl }`),
   turns the assembled word into the decoder's number (`code2_word`: a `calc`
   through `bv_omega`), and turns the word comparisons into the decoder's
   (`at_least_word`, `below_word`).
3. **The loop.** `valid_from_decides` goes by induction on `left`, one case
   per branch of the loop. Each case takes one step of the loop: Heather
   generates an equation per branch of a function, measured loops included,
   and `simp_only(utf8_valid_from, discharge := bv_omega)` picks the one
   the facts in scope decide (bytes left, not ASCII, a continuation byte:
   the answer is `i`). The five deepest branches (a three- or four-byte
   sequence checked, a four-byte one cut off) still cite their equation by
   name, `utf8_valid_from::True::False::False::False::True::True::True` and
   so on: `simp_only` does not reach a branch seven tests deep yet
   (`issues/simp-only-deep-branch-equations.md`). The decoder side of the case is one of `valid_one`,
   `valid_two`, …, which say what the decoder does on a lead byte of each
   class.

The loop lemma is stated over a window (`valid_window_decides`): the
bytes it reads may come from a longer buffer. `valid_window` and
`valid_prefix` say what the loop answers for the first `filled` bytes of a
buffer of `n`, which is what a program that reads into a buffer and lends it
to the loop asks.

The theorems are checked with the rest of the file: `heather check
examples/utf8/utf8_check.hthr`.

## What the proof does not cover

- **The C driver** reads the input and prints the answer. It is outside the
  proof. `utf8check.hthr` has none, but it does not print yet: a program
  whose branches make different calls on Linux is the next step
  (docs/native/io-programs-design.md §4.2).
- **The ELF and `main::reads` meet at the source.** The certificate says the
  executable is the compile of `main::source`, and `main::reads` says what
  `main::source` does; one theorem from the executable's bytes to `main` is
  the compiler theorem's (docs/native/compiler-theorem.md).
- **`main`'s whole run.** That the loop reads the whole input before the
  verdict is what the program says, not a theorem about it yet; the test
  checks it.
- **The offset of a bad byte.** The theorem is about the `valid` answer.
  That the offset printed for invalid input is the start of the first bad
  sequence (Rust's `Utf8Error::valid_up_to`) is not stated yet; the test
  below checks it.
- **The specification itself.** That `utf8::decode` is the UTF-8 the world
  uses is checked from outside: `crates/cli/tests/native_utf8.rs` builds the
  tool as above and compares its answer with Rust's `str::from_utf8` on every
  class boundary (overlong forms, surrogates, the last scalar value and the
  first past it, cut-off sequences) and on pseudorandom input.
