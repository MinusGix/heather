---
title: "Build emitted code with a chained builder that hands out its labels"
status: open
thread: Make compiler correctness proofs elegant
labels: [native,x86,design,ergonomics]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-17
updated: 2026-11-17
---

Emitted code is nested constructors under a root function, read inside
out, with labels as hand-counted successors
(`docs/library/program-and-proof-style.md` §2):

```
let start = then(p.known_to(layout, known, at, R8), Block([MovRI(R9, BitVec::ofNat(capacity))])).clamp(R8, R9, Succ(names));
let room = then(start, Block([SubRR(R9, R8)])).known_to(layout, known, len, Rdx).clamp(Rdx, R9, Succ(Succ(names)));
…
Compiled(asked.read_back(layout, out, buf, result, names), Succ(Succ(Succ(Succ(names)))))
```

## Wanted

- Sequencing as a method, in the order the code runs (`p.then(item)`, or
  an instruction's own method: `.mov(R9, capacity).sub(R9, R8).syscall()`).
- Labels from the builder: `fresh` hands out the next name and the builder
  carries the count, so no emitter writes `Succ(Succ(names))` and none
  returns a count it worked out by hand.
- Whether the surface is methods, a block form or a parsed assembly
  notation is open; a sketch of each against `Prog::reads` decides.

The `Succ(n)` to `n + 1` sweep (its own thread) leaves
`lib/native/native_compile*.hthr` to this.

## Done when

`Prog::reads` and `Prog::clamp` read top to bottom as the instructions
they emit, with no `Succ` and no label arithmetic.

Related: [[native-emission-context]], [[native-syscall-model]],
[[emitted-code-claims-without-positions]].

## Log

- 2026-11-17: filed from Minus's review of `lib/native/native_compile*.hthr` (`docs/library/program-and-proof-style.md`).
- 2026-11-17: a prototype over the four Linux calls (a context record,
  fragments, a builder with the open block and `fresh` labels, a call
  convention record), each emitter equal to today's by `refl`, and one
  `extends` theorem in place of the `within_` lemmas. Minus's review of it:
  much better; `sys.second`/`sys.third` say positions where the call's own
  argument names would say more; nested `fresh` lambdas are unfortunate;
  can the types make wrong code harder to write; registers could be more
  abstract without becoming a list of fields. Proposed next: arguments
  named per call and passed whole, labels from scopes (`scope`, `repeat`,
  `unless`) with a `Label` type, and the calls' offset arithmetic compiled
  as function IR so the emitter holds no scratch registers (unchecked).
