---
title: A byte string reaching a write is a constant buffer of the program's Source
status: open
labels: [native,runtime-fn,literals]
area: heather-in-heather
milestone: [hih-native-heather]
created: 2026-11-16
updated: 2026-11-16
---

D3 of docs/native/io-programs-design.md §5: a byte-string literal reaching a
write is a constant buffer of the `Source` (its initial bytes in the data
segment, never written). The surface half is built ([[byte-string-hex-escape]]
owns what it cannot spell yet): `b"valid\n"` elaborates to the list (or
vector) of its bytes. The native half is not: a `runtime fn` program that
writes one,

```
let w = io.write_from(Io::stdout(), b"hi\n", BitVec::ofNat(0), BitVec::ofNat(3));
```

is refused by the reflector, "`Cons` onto a byte buffer: a buffer is written
in place (`with_byte`), not consed onto" (`rt_reflect.hthr`), because the
closed list is read as a buffer being built.

What it needs, from what is there (the machine half is already built:
`Buffer { capacity, initial }` and `initial_stores` in
`lib/native/native_source.hthr`):

- **The reflection**: a closed list of bytes in a buffer operand is a
  constant, a term of its own in the reading (a `Let` of a byte constant,
  `Bytes(n)` its code), not a `Cons` chain.
- **The lowering**: the constant gets a buffer of its own past the
  parameters' (`Loc::InBuffer`), the `Source` lists it with
  `initial := bytes`, and the lowering is refused if anything other than a
  write (or a lent function that only reads it) is handed that buffer, so
  "never written" is a fact the lowering checks rather than assumes.
- **The theorem**: `Program::reads` gains the constant buffers' `held`
  facts, which are `initial_stores` read back at `start`, proved once for
  every list of constants, never per program (the same move as D2's
  zero buffers: the generator states the parameter form and instantiates).

Done when a `runtime fn` program writes `b"valid\n"` and `write-elf` builds
it with no per-program proof, and a native gate holds its output.
