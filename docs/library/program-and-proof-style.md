# Definitions, data and proofs: what elegant means here

A style for code that is proved about, written from Minus's review of
`lib/native/native_compile*.hthr` on 2026-11-17. That code was written in
the order it was needed, and its proofs inherit how its definitions and its
data are spelled: a proof cannot be shorter than the statement it proves,
and a statement cannot be shorter than the call it is about. So the order
of repair is the order of this document: definitions, then data, then
proofs. `docs/proof-patterns.md` is the companion on what a proof costs the
kernel; this one is about what a reader sees.

The standard: a file about a compiler should be about a quarter the size
the first working version is, and easy to read. Nothing in the language
stops that. Where something does, it is a gap to file, not a reason
(`docs/proof-patterns.md`'s rule: a workaround names the issue that would
retire it).

This is a first statement. The rules are meant to be refined against the
rewrites they call for; each names the code it was read off.

## 1. Definitions

**Related data goes in a structure, above all when theorems, functions and
helpers would gather around it.** An emitter that takes `(layout, known,
out, names)` and its lemma that takes them again are one context written
out twice:

```
fn Prog::reads(self p: Prog, layout: Layout, known: List<Fact>, out: List<Nat>, fd, buf, at, len, result: Nat, capacity: Nat, names: Nat) → Compiled
theorem Prog::within_reads(self p: Prog, layout: Layout, known: List<Fact>, out: List<Nat>, fd, buf, at, len, result, capacity, names: Nat): …
```

The five operands are already a value (`CallShape::Reads(fd, buf, at, len,
result)`), and the four that travel together are a record that every
emitter, every `within_` lemma and every `goes_` lemma would take. The test
for a structure is that second half: several declarations would be stated
over it and helpers would live on it. A result bundles the same way: what a
lemma concludes about one emission (the code is in the program, each check
held, the run goes through) is a record with named fields
(`CallFits`, `Hosted`, `CallsBuilt` in `native_compile_correct.hthr`), not a
nested conjunction read by counting `.right`.

**Do not overbundle.** Two values that happen to be passed together once
are two parameters. A record no theorem is stated over and no method lives
on is a tuple with a name.

**A hypothesis does not restate its callee's body.**

```
emitted: (match region.scopes() { False => None, True => region.code(p, layout, out, names) }) = Some(c)
```

is the inside of a function written in a statement because the stage has
no name. Name the stage and state the hypothesis over the call
(`region.emits(…) = Some(c)`), spell the body with the combinator it is
(`region.scopes().guard(region.code(…))`), and take it apart with `cases`.
Better where it can be had: make the operation total. Emission fails only
where a check fails (`word_fits`, a capacity looked up, `scopes`,
`call_fits`). An emitter that takes the check's proof returns code, not an
`Option` of it, and there is no `None`/`Some` to invert at any use: a
partial operation takes a found proof, it does not return a junk value or a
maybe to be refuted later.

## 2. Data

**Programs are built, not spelled as nested constructors.**

```
let start = then(r0, Block([MovRI(R9, BitVec::ofNat(capacity))])).clamp(R8, R9, Succ(names));
let r1 = then(start, Block([SubRR(R9, R8)]));
```

Assembly as raw arrays of blocks under a root function reads inside out. A
builder chains in the order the code runs (`r0.mov(R9, capacity).clamp(R8,
R9).sub(R9, R8)`), and an operation on a value is a method on it
(`p.then(item)`, never `then(p, item)`): the same rule as methods on the
type everywhere else in the library. Whether the builder is methods, a
block form, or a parsed notation is a design question; that the reader sees
instructions in order is not.

**Roles come from a model, not from literals.** `Rdi`, `Rsi`, `Rdx`, `Rax`
and the number `0` in an emitter are the Linux `read` call written out at
its use. A description of a system call (its number, where its arguments
go, where its result comes back) that `read`, `write`, `open` and `close`
instantiate makes one emitter and one theorem of four, and makes the
theorem say something general ("for any call placed by this convention").
Scratch registers are named by role the same way.

**Numbers are written as numbers.** `Succ(names)` is a holdover; write
`names + 1`, and `names + 4` for `Succ(Succ(Succ(Succ(names))))`. `Succ` is
for a pattern and for where the constructor is what the proof needs.
A count that looks like magic (`let done = names + 4`) should not be
written at all: a label comes from the builder (`fresh`), which is also why
it is right.

**Lists are written as lists.** `Cons(x, xs)` is the constructor; a reader
thinks `[x] ++ xs` or `x :: xs`. Prefer the notation wherever the language
has it, and file where it does not (`[x] ++ ys` has no carrier today,
[[list-literal-left-of-append]]).

## 3. Proofs

**A proof does not restate what it is about.**

```
let whole = p.reads(layout, known, out, fd, buf, at, len, result, capacity, names).prog;
```

is the statement written a third time. With the context a record and the
call a value this is `cx.reads(call).prog`, or not needed.

**A fact that holds by construction is not a lemma.** "An emitter only
appends" is proved once per emitter today (`within_reads`, `within_writes`,
`emits_extends`: several hundred lines). If an emitter returns the code it
adds and sequencing appends, it holds for every emitter at once
([[emitted-code-claims-without-positions]]).

**`calc` chains are the good form**: keep them, and prefer a designated
relation (`<=` for `Prog::Within`) to a `trans` with its endpoints spelled.

**No written motives and no transported matches.** A `match … as λ b => …`
in a proof, or a `j(sym(e), λ o _ => <the function body again>, …)`, is the
elaborator's work written by hand. The forms that replace them: `match h:`,
`cases h`, `induct f(…)`, `simp_only(f, h₁, h₂)`, `subst`, `known`. Where
none fits, that is the gap to file (`Region::paired` is the current worst
case).

**A lemma with a dozen parameters is missing a structure**, the same rule
as §1 seen from the proof side (`Target::goes_repeat`). Programs as
interaction trees may deserve their own surface form where `ITree::bind(…,
match … { … }, k)` is written three times in one proof.

**Tactics come after this, not instead of it.** A tactic that closes an
ugly goal leaves the ugly statement in the file.

## Where this is tracked

- [[native-emission-context]]: the context record, call shapes passed
  whole, results as records.
- [[native-emission-total]]: emission that takes its checks' proofs.
- [[native-assembler-builder]]: the builder, `then` as a method, labels by
  `fresh`.
- [[native-syscall-model]]: call numbers and registers from a description.
- [[emitted-code-claims-without-positions]]: code added, not programs
  extended; claims that compose.
- [[native-run-lemmas-bundled]]: `Region::paired`, `Target::goes_repeat`
  and the interaction-tree forms.
- The `Succ(n)` to `n + 1` sweep has its own thread; it leaves
  `lib/native/native_compile*.hthr` to the builder work above.
