# Definitions, data and proofs: what elegant means here

A style for code that is proved about. A proof inherits how its definitions
and its data are spelled: it cannot be shorter than the statement it proves,
and a statement cannot be shorter than the call it is about. So the order
of repair is the order of this document: definitions, then data, then
proofs. `docs/proof-patterns.md` is the companion on what a proof costs the
kernel; this one is about what a reader sees.

The standard: a file about a compiler should be about a quarter the size
its first working version is, and easy to read. Nothing in the language
stops that. Where something does, it is a gap to file, not a reason
(`docs/proof-patterns.md`'s rule: a workaround names the issue that would
retire it).

The examples are schematic, an emitter of machine code and the lemmas
about it, so that they stay true as the library changes. Which library
code falls short of a rule, and the work to fix it, is in the issues listed
at the end, not here.

This is a first statement, from Minus's review of the native compiler's
proofs on 2026-11-17. The rules are meant to be refined against the
rewrites they call for.

## 1. Definitions

**Related data goes in a structure, above all when theorems, functions and
helpers would gather around it.** An emitter that takes what it is given
piece by piece, and its lemma that takes the pieces again, are one context
written out twice:

```
fn Prog::emit_copy(self p: Prog, layout: Layout, known: List<Fact>, live: List<Nat>, from, to, len: Nat, labels: Nat) → Compiled
theorem Prog::within_emit_copy(self p: Prog, layout: Layout, known: List<Fact>, live: List<Nat>, from, to, len, labels: Nat): …
```

The values that travel together are a record that every emitter and every
lemma about one would take, and the operands are a value of their own (the
call being compiled). The test for a structure is that second half: several
declarations would be stated over it and helpers would live on it. A result
bundles the same way: what a lemma concludes when it is more than one fact
(the code is in the program, each check held, the run goes through) is a
record with named fields, not a nested conjunction read by counting
`.right`.

**Do not overbundle.** Two values that happen to be passed together once
are two parameters. A record no theorem is stated over and no method lives
on is a tuple with a name.

**A hypothesis does not restate its callee's body.**

```
emitted: (match region.scoped() { False => None, True => region.code(cx) }) = Some(c)
```

is the inside of a function written in a statement because the stage has
no name. Name the stage and state the hypothesis over the call
(`region.emit(cx) = Some(c)`), spell the body with the combinator it is,
and take it apart with `cases`.

**Better where it can be had: make the operation total.** An emitter fails
only where a check fails. One that takes the check's proof returns code,
not an `Option` of it, and there is no `None`/`Some` to invert at any use:
a partial operation takes a found proof, it does not return a junk value or
a maybe to be refuted later.

## 2. Data

**Programs are built, not spelled as nested constructors.**

```
let start = then(r0, Block([MovRI(R9, BitVec::ofNat(capacity))])).clamp(R8, R9, Succ(labels));
let r1 = then(start, Block([SubRR(R9, R8)]));
```

reads inside out. A builder chains in the order the code runs
(`b.set(R9, capacity).clamp(R8, R9).minus(R9, R8)`), and an operation on a
value is a method on it (`p.then(item)`, never `then(p, item)`): the same
rule as methods on the type everywhere else in the library. Whether the
builder is methods, a block form, or a parsed notation is a design
question; that the reader sees instructions in order is not.

**Roles come from a model, not from literals.** Four registers and a
number written in an emitter are one system call's convention written out
at its use. A description of a call (its number, where its arguments go,
where its result comes back) that every call instantiates makes one
emitter and one theorem of several, and makes the theorem say something
general ("for any call placed by this convention"). Scratch registers are
named by role, or handed out, the same way.

**Numbers are written as numbers.** Write `n + 1`, and `n + 4` for
`Succ(Succ(Succ(Succ(n))))`. `Succ` is for a pattern and for where the
constructor is what the proof needs. A count that looks like magic
(`let done = labels + 4`) should not be written at all: a label comes from
the builder, which is also why it is right.

**Lists are written as lists.** `Cons(x, xs)` is the constructor; a reader
thinks `[x] ++ xs` or `x :: xs`. Prefer the notation wherever the language
has it, and file where it does not.

## 3. Proofs

**A proof does not restate what it is about.**

```
let whole = p.emit_copy(layout, known, live, from, to, len, labels).prog;
```

is the statement written a third time. With the context a record and the
call a value this is `cx.emit(call).prog`, or not needed.

**A fact that holds by construction is not a lemma.** "An emitter only
appends" proved once per emitter is a family of lemmas with counted
lengths. If an emitter returns the code it adds and sequencing appends, it
is one theorem about all code.

**`calc` chains are the good form**: keep them, and prefer a designated
relation (`<=`) to a `trans` with its endpoints spelled.

**No written motives and no transported matches.** A `match … as λ b => …`
in a proof, or a `j(sym(e), λ o _ => <the function body again>, …)`, is the
elaborator's work written by hand. The forms that replace them: `match h:`,
`cases h`, `induct f(…)`, `simp_only(f, h₁, h₂)`, `subst`, `known`. Where
none fits, that is the gap to file.

**A lemma with a dozen parameters is missing a structure**, the same rule
as §1 seen from the proof side. A construction a proof writes out several
times (a bind over a match on an event, say) may deserve its own surface
form.

**Tactics come after this, not instead of it.** A tactic that closes an
ugly goal leaves the ugly statement in the file.

## Where this is tracked

The issues hold the library code each rule was read off and what is left
to do; they close as the code is fixed, and this section shrinks with them.

- [[native-emission-context]]: the context record, calls passed whole,
  results as records.
- [[native-emission-total]]: emission that takes its checks' proofs.
- [[native-assembler-builder]]: the builder, `then` as a method, labels
  from the builder.
- [[native-syscall-model]]: call numbers and registers from a description.
- [[emitted-code-claims-without-positions]]: code added, not programs
  extended; claims that compose.
- [[native-run-lemmas-bundled]]: run lemmas with too many parameters,
  written-out matches, the interaction-tree forms.
- [[list-literal-left-of-append]]: `[x] ++ ys` has no carrier.
