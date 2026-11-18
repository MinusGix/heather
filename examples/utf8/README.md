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
runtime fn main(mut io: Io) → Partial(Mutated<Io, u64>) {
    let mut buf: List<u8> = List::replicate(0, 65536);
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
  any outcome of each read), is `main` itself. Its buffer is a local the
  program makes zeroed, which the source holds as a buffer of its data
  segment;
- `utf8_status_answers`: after a read that did not fail and left room,
  `utf8_status` answers 0 exactly when the bytes read are UTF-8
  (`utf8::is_utf8(span.take(filled))`).

## The program

The validator is ordinary code over a span of bytes, `s` with its length `n`
(`runtime fn` marks a function the compiler turns into machine code). Its
heart is Unicode's own table of well-formed byte sequences (The Unicode
Standard, Table 3-7), written as it is printed:

```text
runtime fn sequence_length(lead, next1, next2, next3: u64) → u64 {
    let b = lead.truncate(8, 56);
    let c1 = next1.truncate(8, 56);
    …
    if b < 0x80 {
        1
    } else if b < 0xC2 {
        0
    } else if b < 0xE0 {
        if c1 & 0xC0 = 0x80 { 2 } else { 0 }
    } else if b < 0xF0 {
        if c1 & 0xC0 = 0x80 ∧ c2 & 0xC0 = 0x80 ∧ (b ≠ 0xE0 ∨ 0xA0 <= c1) ∧ (b ≠ 0xED ∨ c1 < 0xA0) { 3 } else { 0 }
    } else if b < 0xF5 {
        if … ∧ (b ≠ 0xF0 ∨ 0x90 <= c1) ∧ (b ≠ 0xF4 ∨ c1 < 0x90) { 4 } else { 0 }
    } else {
        0
    }
}

runtime fn sequence_at(s: List<u8>, n, i: u64) → u64 {
    sequence_length(↑s.byte_within(n, i), ↑s.byte_within(n, i + 1), ↑s.byte_within(n, i + 2), ↑s.byte_within(n, i + 3))
}

runtime fn utf8_valid_from(s: List<u8>, n, i, left: u64) → u64 decreases left.toNat() {
    if h: 0 < left {
        let k = sequence_at(s, n, i);
        if k = 1 {
            utf8_valid_from(s, n, i + 1, left - 1)
        } else if k = 2 {
            if room: 1 < left { utf8_valid_from(s, n, i + 2, left - 2) } else { i }
        } else if …            // three and four bytes, the same shape
        } else {
            i
        }
    } else {
        i
    }
}

runtime fn utf8_valid_up_to(s: List<u8>, n: u64) → u64 { utf8_valid_from(s, n, 0, n) }
```

The table answers how long the sequence at a byte is, or 0 when none starts
there. The narrow ranges after `E0`, `ED`, `F0` and `F4` are where the
strict decoder's rules live: they rule out overlong forms (`E0 80 80`), the
surrogates `D800`–`DFFF` (`ED A0 80`) and values above `10FFFF`. The loop
steps over each sequence the table takes, while enough bytes are left. The
answer is the offset where the first bad sequence starts, or `n` when there
is none.

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
is the table of byte ranges; the decoder reads header bits, joins payloads
with `concat` and checks the scalar value it assembled (not overlong, not a
surrogate, at most `10FFFF`). Three tools do the meeting, and the proof is
mostly the statements.

1. **The table against the decoder, by `bv_decide`.** For each length,
   `two_takes` says the decoder takes a sequence the table takes, and
   `two_refuses` that after a lead byte of that length it refuses one the
   table refuses; `length_two` says which lead bytes the table answers 2
   for. `split_all` first turns the decoder's step into its tests
   (`seq2_is_some`), and `bv_decide` proves the rest as one circuit on four
   bytes: it reads the table's `if`s without splitting them, and the
   decoder's number comparisons (`code.toNat() < 0x800`) as comparisons of
   words.
2. **Bytes, by their class.** `class_two` and its kin say which class the
   decoder gives a lead byte, each one line: `simp_only` takes the
   decoder's equations and `bv_decide` discharges the tests. `ascii`,
   `valid_two`, `cut_two` and so on then say what the decoder does on a
   byte list that starts with such a byte.
3. **The loop, by its own induction.** `valid_window_decides` goes by
   `induct utf8_valid_from`: one case per branch of the loop, each with the
   loop's tests as hypotheses and the step already taken. A case is one
   `rewrite`: the window's lemma for what the table answered
   (`win.takes_two(i, …)`, its answer found by `assumption`: the decoder goes on
   after the two bytes the table took; `win.short_two`: the bytes end inside
   the sequence; `win.refused`: the table took nothing), and the induction
   hypothesis for the bytes after the sequence.

The loop lemma is stated over a window (`Window`): the bytes it reads may
come from a longer buffer. `valid_window` and `valid_prefix` say what the
loop answers for the first `filled` bytes of a buffer of `n`, which is what a
program that reads into a buffer and lends it to the loop asks. The last step
to strings is the library's `utf8::is_utf8_iff`.

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
