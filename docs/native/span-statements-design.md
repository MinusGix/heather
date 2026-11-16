# Stating a function of spans by its spans

`docs/native/compiler-theorem.md` states what a compiled function of spans
does through `Prog::ComputesOver`: a `Lending` (a table of counts, a list
of addresses, a file, a row of marks), a `Loan` over that lending's spans,
the whole argument list with each span's address and length as two free
words among `[a0, a1, …]`, the file before, and an `Ending`. That is what
the proof needs. What the statement means is what the function's Rust
signature says: given a `&mut [u8]` holding `bytes` and a `&[u8]` holding
`more`, the code returns `f(bytes, more).value` and leaves
`f(bytes, more).after` where `bytes` was. This note is how the statement is
made to read that way (issues/span-certificate-statements.md). Nothing is
proved anew: the form below follows from `Prog::ComputesOver` by one lemma.

## The statement

```heather
record Slice { at: BitVec(64), bytes: List<BitVec(8)> }
inductive Borrow { Shared(slice: Slice), Mut(slice: Slice) }

code.ComputesOn(machine, f, room, borrows, words, answer, leaves)
```

`room` is the stack the function asks for below its return address,
`borrows: List<Borrow>` the function's spans in the order it takes them, `words` its arguments after them, `answer` the word in RAX and
`leaves` the bytes each span holds afterwards. A certificate for
`copy_span(out: span mut, text: span, count, from)` reads

```heather
theorem copy_span_native_returns<M>(machine: Machine<M>, s0, s1: Slice, a4, a5: BitVec(64)):
    copy_span_native_code().ComputesInto(machine, 0, 0, [Mut(s0), Shared(s1)], [a4, a5],
        native_tool_spans::copy_span(s0.bytes, s0.length(), s1.bytes, s1.length(), a4, a5))
```

`ComputesInto` is the form for a function that writes its first span, as
a `runtime fn` returning `Mutated` does: it is `ComputesOn` with the
result's `value` for the answer and its `after` left in the first slice,
the other slices as they were (`Borrow::left`). A reader states
`ComputesOn` itself, with its value and the slices' own bytes.

Everything the old statement took separately is read off the borrows:

| Old | Now |
|---|---|
| `addresses: List<BitVec(64)>` | each slice's `at` (`Borrow::addresses`) |
| the file `Cons(span, rest)` | each slice's `bytes` (`Borrow::bytes`); the file is exactly the function's spans |
| `marks: List<Bool>` | `Mut` or `Shared` (`Borrow::marks`) |
| `a0, a1` free, tied to the span by a clause of the precondition (`ArgsLent`) | `slice.at`, `slice.length()`: the argument list is `Borrow::words(borrows) ++ words` |
| `counts` (how many buffers each function of the program takes) | not in the statement; the lemma takes it and asks that function `f`'s count is `borrows.len()` |
| `top` and the `Loan` premise | bound inside `ComputesOn`: at every `top` with `machine.Lends(top, borrows)` |
| `Ending(word, buffers)` | `answer` and `leaves`, or the source function's `Mutated` result (`ComputesInto`) |

The length word is the visible gain. The source function takes each span's
length as a parameter (`copy_span(out, length, text, size, count, i)`), and the old
statement left it a free word that a conjunct deep in `Stack::LentOver`
equated to the span's length. Now the theorem says `s0.length()`.

## Decisions

**Marks are the borrow's constructor.** A row of marks beside a list of
spans can disagree with it in length and says nothing at the span it is
about; `Mut(s)` and `Shared(s)` are Rust's two borrows. `Borrow::marks`
maps the list to the row, and at a literal list it evaluates to the literal
row the certificate already checks its stores against
(`program_stores_within`), so no new check is needed.

**Views do not appear.** A program whose functions lend views of a span to
each other (`compiled_returns_marked`) has a row of marks for each
function. The exported function's statement uses only its own row, which is
what its caller lends; the callees' rows are how the proof goes, not what
the export promises. So such a certificate has the same `ComputesOn`
statement, proved from `Ending::returns_marked` instead of
`Ending::returns_written`.

**A reader is the case with no `Mut`.** The compiler's theorem for a
program that stores into no span is stated at a lending that writes nothing
(`Lending::reading`), which is not the lending `Borrow::marks` gives by
conversion (two functions that agree at every index). The lemma therefore
takes any `written` that allows no more than the borrows do, and moves the
loan and the stores across by `Loan::narrow` and `Stack::wrote_in_wider`.

**The `Loan` stays a premise, under a name.** `machine.Lends(top, borrows)`
is `Loan` at the borrows' spans: they end below 2^47, a store below `top`
misses them, and a store into a `Mut` one stays inside it and misses the
others, the stack and the code. It is a law about the memory `M`, which the
theorem does not fix, so it cannot be replaced here by a statement about
addresses (disjoint ranges) without choosing a memory model. For the byte
memory model that statement exists (`DataRegion::loan`). Deriving `Lends`
from "the `Mut` slices are disjoint from every other slice and from the
stack below `top`" over that model is the follow-up: the verdicts for it
exist over address intervals (`SpanSet::disjoint`,
`lib/std/data/set/span_set.hthr`).

**The names are `Slice` and `Borrow`, not `Span` and `Lent`.** Both of
those are taken by records that certificates import (`Span` in
`function_ir_learn`, `Lent` in `function_ir_lower_reads` and `rt_io`), and
record names are global. `Slice` is also Rust's word for the thing.

**The file is exactly the function's spans.** The old certificate is over
any file whose first buffers are the function's (`rest: Buffers()`). No
caller uses the extra buffers: a call from inside the program is the
lowering's business, and a Rust caller lends what the signature names. The
general theorem stays in the certificate as `_returns_over`, and
`_returns` is its instance at the borrows.

## What is built

- `lib/native/function_ir/function_ir_borrows.hthr`: `Slice`, `Borrow`,
  `Machine::Lends`, `Prog::ReturnsOn`, `Prog::ComputesOn`,
  `Prog::ComputesInto`, the lemma
  `Prog::computes_on` from `Prog::ComputesOver`, and
  `compiler_correct_on`, the compiler's theorem in this form.
- `compile-x86` states each span certificate's `_returns` this way
  (`crates/cli/src/native/verified.rs`).
- Probes: `lib/_tests/native/function_ir/function_ir_borrows_tests.hthr`.

## Not done here

- The per-function form (`Prog::Implements`,
  issues/compiled-function-implements.md) curries the words; a span form of
  it would curry the slices too. It waits on that round's shape.
- `Stack::InMemory` and `Stack::AnsweredOver` still sit under `ReturnsOn`.
  Restating them over the list (each slice readable at its address) is a
  rename of the same content and can follow.
