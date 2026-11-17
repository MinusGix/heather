---
title: "An emission context, and calls passed as the shapes they are"
status: open
thread: Make compiler correctness proofs elegant
labels: [native,design,proofs,ergonomics]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-17
updated: 2026-11-17
---

Every emitter in `lib/native/native_compile.hthr` and every lemma about one
takes the same values spelled out (`docs/library/program-and-proof-style.md`
§1):

```
fn Prog::reads(self p: Prog, layout: Layout, known: List<Fact>, out: List<Nat>, fd, buf, at, len, result: Nat, capacity: Nat, names: Nat) → Compiled
theorem Prog::within_reads(self p: Prog, layout: Layout, known: List<Fact>, out: List<Nat>, fd, buf, at, len, result, capacity, names: Nat):
    p.Within(p.reads(layout, known, out, fd, buf, at, len, result, capacity, names).prog)
```

and a proof then writes the call a third time (`let whole = p.reads(layout,
known, out, fd, buf, at, len, result, capacity, names).prog;`).

## Wanted

- One record for what travels together: the layout, the facts known as the
  statement starts, the words live after it, the next free label. Emitters
  and the `within_`/`goes_` lemmas are stated over it and its helpers live
  on it.
- A call passed as its `CallShape` (`Reads(fd, buf, at, len, result)` is
  already a value), not as five operands.
- What a lemma concludes as a record with named fields where it is more
  than one fact (`CallFits`, `Hosted` and `CallsBuilt` are the pattern).
- Not everything bundled: a record no theorem is stated over stays
  parameters.

## Done when

`Prog::reads`, `writes`, `opens`, `closes` and their lemmas take a context
and a call, and no proof restates an emitter's argument list.

Related: [[native-assembler-builder]], [[native-emission-total]],
[[native-syscall-model]], [[native-run-lemmas-bundled]].

## Log

- 2026-11-17: filed from Minus's review of `lib/native/native_compile*.hthr` (`docs/library/program-and-proof-style.md`).
