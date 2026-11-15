# Multi-width parametric bitvectors: what the paper means for Heather

Status: **survey**, 2026-10-25. Source: Siddharth Bhat, Léo Stefanesco,
George Rennie, John Regehr, Tobias Grosser, *Sound and Complete Solving for
Multi-width Parametric Bitvectors via Principled Reductions*, PACMPL 10
(OOPSLA2), article 379, October 2026 (<https://doi.org/10.1145/3839511>,
CC BY 4.0), committed beside this note as `docs/papers/3839511.pdf`. Section,
table and lemma numbers below are the paper's. Follow-up is in §8. Read
against master at `6bce3b3`.

The paper is about proving bitvector facts whose widths are variables:
"for all widths `u < v ≤ w`, `sext(zext(a, u, v), v, w) = zext(a, u, w)`".
That is the shape of every width-generic compiler rewrite (LLVM's
InstCombine, Alive2's checks), and it is the shape of Heather's own
open-width `BitVec` laws and of the per-operation theorems a proved-once
compiler needs when it lowers narrow values into 64-bit registers.

The paper has one idea and two uses for it. The idea is to give every width
its mask, `2^w − 1`, and keep every value zero-extended into one common
width. One use turns a problem with many widths into one problem with a
single width, which a fixed-width solver then answers in one query. The
other decides the linear-bitwise fragment *for all widths at once*, by
finite-state transducers. Both are implemented in Lean; the transducer
procedure is verified there end to end through k-induction and LRAT.

---

## 0. The answer in brief

1. **Heather already uses the paper's central relation, in the native
   lane.** The verified lowering represents a one-bit value in a 64-bit
   register as `values(1, id).zero_extend(63) = word` (`Held::Rep`,
   `lib/native/function_ir/function_ir_lower.hthr`). That is the paper's
   compatibility relation (Definition 4.1) at global width 64. The library
   already proves two cases of its correspondence lemma (Lemma 4.2), for
   add and subtract: `BitVec::add_zero_extend_mask` and
   `BitVec::sub_zero_extend_mask`, structurally in the width. Table 2 is
   the full list of per-operation rules for carrying FunctionIR's narrow
   widths (2–63) into the verified lowering, which refuses them today
   (`word_only`). §3 sets that out and gives the one rule Heather has not
   yet found, the signed comparison.
2. **Heather's `BitVec` is the paper's bitstream, as a definition.** A
   `BitVec(n)` is `n` Booleans, least significant first, and add, subtract
   and the bitwise operations are ripple folds with carry state. The
   kernel's bit-transducer fold class (`crates/kernel/src/eval/transduce.rs`)
   already sees these folds as the Mealy machines that Table 3 writes down.
   So a transducer decision procedure (§4) would be easier to prove sound
   in Heather than in Lean, whose `BitVec` is built on `Fin 2^n` and needs
   a separate bitstream view to get there.
3. **A width-generic decision procedure is worth having, but as a tactic
   with a customer, not now.** Its customers are the hand-proved open-width
   laws (`add_comm` took a round of its own) and, later, the rewrite rules
   of optimisation passes written in Heather (`hih-passes`). The procedure
   would reify the goal, build the transducer, and check safety. It can be
   proved sound once in Heather, with an untrusted host search that hands
   the kernel an inductive invariant to check. §4 gives the rungs. Filed as
   `issues/bitvec-width-generic-decision.md`.
4. **The bounded single-query path needs a SAT certificate checker first.**
   Collapsing many widths into one QF_BV query only pays if something
   decides QF_BV queries, and in Heather that is
   `issues/lrat-certified-bitvector-decision.md`, still at the
   investigation rung. The paper gives that issue a second customer, and
   the reduction itself (unverified in the paper) is a structural induction
   that Heather can prove instead of trusting (§5).
5. **One correction for anyone porting the paper's tables:** the signed
   less-than row of Table 2, as printed, is wrong when both operands are
   negative. A brute-force check over widths 1–6 finds 1,365
   counterexamples, against none for the corrected form (§6).
6. **`bv_omega` is the other approach, and it stays.** It lifts word
   arithmetic to `Nat` without wrap-around (`docs/bv-omega-design.md`).
   That is the int-blasting direction the paper's related work contrasts
   itself with. It answers questions about `toNat` that the transducer
   procedure does not ask, and the transducer procedure answers bit-level
   identities with wrap-around that `bv_omega` refuses by design. They
   complement each other.

---

## 1. What the paper contributes

**The theory (§3).** PBV_n is a multi-sorted language: width variables
range over naturals, and bitvector variables have types `BitVec w` for a
width expression `w` (constants, variables, `min`, `max`, `+`). Typing needs
equality of width expressions. The paper defines it semantically (equal under
every assignment) and implements it as syntactic equality. PBV_0 is QF_BV,
and PBV_1 is the single-width theory of the authors' earlier procedure (their
reference [5], OOPSLA 2025).

**The reduction PBV_n → PBV_1 (§4, Table 2).** Fix one global width `o`.
Every width becomes a `BitVec o` holding its value. Every bitvector becomes
a `BitVec o` with the precondition `x & mask(w) = x`, where
`mask(w) = (1 ≪ w) − 1`. Every operation is computed at width `o` and masked
back to its result width. Masking is needed only where high bits can become
dirty (add, multiply, complement, the sign fill). Comparisons and equality
read the masked values directly. The correctness argument is one relation:
a mono-width model *represents* a multi-width one when every value is the
zero-extension of the narrow value (Definition 4.1), and represented
models satisfy the same formulas (Lemma 4.2, by induction on well-typed
syntax). Equisatisfiability (Theorem 4.3) needs `o` larger than any width in
the model. The formula grows only linearly (Table 5: input size about 40,
output about 375).

**Bounded solving (§4, §6.3).** Instantiate `o` (say 65) and the whole
multi-width problem is one QF_BV query covering every width assignment
below `o`. Alive2's way is one query per assignment, `o^k` queries for `k`
widths. The motivating InstCombine rewrite takes 18.5 hours that way and
511 ms this way. In the paper this pipeline is unverified up to the QF_BV
query, which Lean's `bv_decide` then checks through LRAT.

**Unbounded solving (§5, Table 3).** For the linear-bitwise fragment
(add, subtract, multiply by a constant, bitwise operations, truncation and
both extensions, comparisons), represent a width by its mask *bitstream*
`1^w 0^ω`, which is a unary encoding, and a value by its binary bitstream.
Every operation is then a finite-state transducer over the tuple of input
bits: add is a ripple-carry adder with one carry bit of state, `zext` is
`x & m_v & m_w`, `msb` uses `m_w & ~m_(w−1)`, and equality is a two-state
machine that latches on the first difference. A predicate is valid for all
widths iff the composed transducer only ever outputs true (Theorem 5.2,
mechanised in Lean). Lemma 5.1 (`m & (m + 1) = 0` iff `m = 2^k − 1`) shows
that masks stay inside the fragment, so no variable shift is needed.
Safety is checked by a verified k-induction checker (CaDiCaL plus LRAT
certificates checked in Lean) or by the faster, unverified rIC3.

**Implementation (§6).** Lean has a tactic `bv_multi_width` and a command-line
tool that reads SMT-LIB. Like Heather's tactics, it keeps two syntaxes: an
intrinsically well-typed one (indexed by width expressions) for the
soundness proof, and an untyped one for the metaprogram. A projection
connects them, so certificates found for the untyped automaton apply to the
typed term.

**Evaluation (§7).** 528 problems: Alive's 200 single-width problems, 309
new multi-width InstCombine extension problems, and 19 ROVER RTL problems
with up to 12 widths. The bounded solver proves 506. The unbounded solver
proves 385 for all widths, against 265 for the CVC5 parametric-bitvector
solver, which reduces to nonlinear integer arithmetic. Problems with
multiplication by a variable fall outside the fragment and come back
`unknown`.

---

## 2. Where Heather already stands

| paper | Heather today |
|---|---|
| `BitVec w`, width a natural | `record BitVec(n: Nat) { bits: [Bool; n] }`, least significant bit first (`lib/std/bitvec/bitvec.hthr`). Widths are unbounded. |
| bitstreams, value padded with zeros | the same vector, read as a prefix. The width is literally the length, so it is already unary. |
| transducers for add, sub, the bitwise operations | the library *defines* `add`/`sub`/`neg` as ripple-carry folds and the bitwise operations as pointwise folds. The kernel classifies these folds as bit transducers, with carry state, for closed evaluation (`issues/kernel-native-bitvector-values.md`, rounds 2–3). |
| compatibility, `ρ̄(x) = zext_o(ρ(x))` | `Held::Rep` for `Bit`: `values(1, id).zero_extend(63) = word` |
| Lemma 4.2 for add and sub | `BitVec::add_zero_extend_mask`, `BitVec::sub_zero_extend_mask` (landed 2026-09-30 for `tr`'s narrow arithmetic, `issues/function-ir-narrow-arithmetic.md`) |
| multi-width IR | FunctionIR: every `Node` carries its own `width`. There are no extension or truncation nodes yet, and shift counts are immediates. |
| width-generic laws | hand-proved: `band_comm`, `bor_comm`, `bxor_comm`, `xor_self`, `add_comm`, `add_sub_cancel`, `truncate_zero_extend`, `truncate_sign_extend`, the two `*_zero_extend_mask` laws. Every one is in the linear-bitwise fragment. |
| int-blasting (CVC5-berger's route) | `bv_omega`, linear and wrap-free, over `toNat` |
| `bv_decide` (bit-blast, SAT, LRAT) | `issues/lrat-certified-bitvector-decision.md`, open at the investigation rung |

One difference matters for anything that reflects goals. Heather's
extensions take a *delta* and put type-level addition in the result type:
`zero_extend(extra): BitVec(n) → BitVec(extra + n)`, and
`sign_extend(extra): BitVec(Succ(n)) → BitVec(extra + Succ(n))`. `Nat::add`
recurses on its second argument, so `Succ(e) + u` does not reduce to a
`Succ` at an open `u`. The paper's running example, sign-extending a value
that was zero-extended by at least one bit, therefore cannot be stated in
Heather without a transport along `Nat::add_succ_left`. The paper (§6.5),
Lean and LLVM all pass the *target* width instead. For a reflective
procedure this means the reifier has to see through width transports, the
paper's `IsEq`, or that the library should add target-width spellings.
That decision belongs to the decision-procedure issue, once a goal needs it.

---

## 3. The native lane: narrow widths are Definition 4.1 at width 64

> **Since 2026-11-10** the verified lowering holds narrow values as this
> section proposes: `Kind` has `Narrow(w)` (the value zero-extended, the
> compatibility relation at 64) and `Low(w)` (only the low `w` bits
> right, what an ADD, a SUB or a left shift leaves), and settles the
> second into the first by a shift left and back rather than a mask
> (`lib/native/function_ir/function_ir_lower.hthr`, "Narrow widths";
> the laws are `lib/std/bitvec/bitvec_resize.hthr`). The signed
> comparison by sign flip, below, is still to do
> (`issues/function-ir-narrow-arithmetic.md`). The rest of this section
> is as written on 2026-10-25.

The verified lowering (`function_ir_lower.hthr`) holds values of two kinds:
`Word`, a 64-bit value as itself, and `Bit`, a 1-bit value zero-extended.
Arithmetic at any other width is refused (`word_only`, "a node at another
width is refused"). The shared lowering that published `tr` lowered widths
0–64 with zero-extended registers and masked add/subtract, but B2 retired
that path. Its laws remain in the library; its selection rules did not
survive. Bringing narrow widths into the proved-once compiler means
generalising `Kind` to "width `w`, held zero-extended":

```
values(w, id).zero_extend(64 − w) = word      (w ≤ 64; Word and Bit are w = 64 and w = 1)
```

This is exactly Definition 4.1 with `o = 64`. Then each node's correctness
lemma is the matching row of Table 2, and Lemma 4.2's induction is what
`Region::lower_correct` already does node by node. The rows sort into three
classes:

- **Mask-free.** Constants (a literal fitting the width), `Move`, AND, OR,
  XOR, unsigned less-than and equality. Pre-masked inputs give a pre-masked
  output, and unsigned order and equality read the zero-extended values
  unchanged. Each needs one "zero-extension commutes" lemma and no new
  instruction.
- **Mask after.** Add, subtract, negate, shift left: the 64-bit operation,
  then AND with `2^w − 1`. The library already has add and subtract. At
  `w ≥ 32` the mask does not fit AND's sign-extended imm32 and needs a
  `MOV r, imm64` first, which is what the old lowering did with a scratch
  register.
- **Signed comparison**, which `function-ir-narrow-arithmetic` still lists
  as open. The paper's Table 2 gives a three-way choice on the sign bits
  (corrected in §6). For x86 a better form is the sign flip:

  ```
  slt_w(a, b) = ult(a ⊕ 2^(w−1), b ⊕ 2^(w−1))
  ```

  It is an XOR with an immediate on each operand followed by the unsigned
  `CMP`/`SETB` the lowering already proves. That is two instructions and no
  branch. Brute-forced over widths 1–6, it agrees with two's-complement
  order (§6). It sits in the linear-bitwise fragment, so the §4 procedure
  could also prove it once for all widths. The alternative, sign-extending
  both operands to 64 bits with `SHL`/`SAR` by `64 − w` and using the
  signed 64-bit compare, waits on arithmetic shift in the ISA model
  (`issues/function-ir-x86-shift-legalization.md`).

The edge widths need care. Width 0 holds the zero word, and every
operation's result is zero. Width 64 has no mask, and computing `1 ≪ 64`
at run time would be wrong on x86, because `SHL` masks its count to six
bits and the result is 1, not 0. FunctionIR widths are static, so the
masks are immediates and that trap does not arise, but a lemma stated with
`mask(w)` computed by a shift would have to exclude `w = 64`.

Logged on `issues/function-ir-narrow-arithmetic.md`.

---

## 4. A width-generic decision procedure in Heather

**What it would be.** A tactic for goals in the linear-bitwise fragment over
`BitVec` at open widths, with hypotheses that relate widths. It reifies the
goal into an intrinsically width-indexed syntax, the way `omega` and `ring`
reify theirs. A Heather function builds the transducer, and a theorem
proved once says that a transducer whose reachable states all output true
makes the goal hold (Theorem 5.2's soundness direction). Completeness is
not needed for a tactic, which can simply refuse. The direction that
matters is soundness, plus a refusal that names what fell outside the
fragment.

**Why Heather is a good host.** The semantic side of Theorem 5.2 is mostly
the definitions. Heather's `add` is a ripple fold with a carry, so the
lemma "the adder transducer's output stream is `add`'s bits" is an
induction on the width that follows the fold's own recursion. The library
already proves `add_bits_spec` and the ripple equivalences. Masks are the
width itself (a vector of `n` trues, then falses), so the paper's unary
encoding costs nothing to relate. The kernel model's plan
(`docs/kernel-model-design.md`, rung 3, "bit transducers") is to prove the
kernel's transducer class correct in Heather. That rung needs the same
notion of a bit transducer and its output stream that this procedure needs,
so whichever lands first should define it where the other can import it.

**Deciding safety, by rung.**

- *Rung A: an explicit invariant, checked by evaluation.* An untrusted
  host search (Rust, or the Heather tactic itself) computes the reachable
  state set. The kernel checks that the set contains the start state, is
  closed under every input letter, and outputs only true. That is
  evaluation over finite lists, with no SAT solver. It is cheap when the
  reachable set is small. The laws in §2 compose a few adders and equality
  latches, so their reachable sets should be small. The paper's
  benchmarks need 17–104 state bits, so not every problem will fit. The
  first round should measure reachable-set sizes and kernel cost (as
  shapes) on Heather's own laws before going further.
- *Rung B: k-induction or IC3 with a symbolic invariant.* This needs
  bit-blasting and an LRAT check, the same machinery as
  `issues/lrat-certified-bitvector-decision.md`, and should wait for it.
  rIC3's invariant witnesses would also need a SAT check to validate.

**Customers, honestly.** Nothing is blocked on this today. The laws in §2
are already proved by hand, and each cost real work (`add_comm` was a
round: `issues/bitvec-add-commutativity.md`). New ones arrive with each
narrow-width rule of §3 and with each FunctionIR extension node. The large
future customer is `hih-passes`: a peephole or InstCombine-style pass
written in Heather states its rewrites at the node's symbolic width, and
each rewrite is a PBV_n validity. The paper's 309 InstCombine problems are
a ready corpus of such rewrites for testing the tactic.

Filed as `issues/bitvec-width-generic-decision.md` (area `tactics`).

---

## 5. The bounded path, and when it applies

Heather's compiler is proved once, for all inputs, so the theorem it needs
about a rewrite is "for every width", not "for every width below 64". The
bounded path therefore has a narrower use in Heather than in Alive2. It
applies only where the claim really is bounded, such as "for every width
the x86 lowering accepts", which is at most 64, or outside the fragment
(multiplication by a variable, variable shifts), where §4 has nothing to
say.

There the paper's reduction is worth having in proved form. Lemma 4.2 is a
structural induction on well-typed syntax, which Heather proves as a
theorem once, against the paper's unverified translator. What is left is
one QF_BV query at width 65, and deciding that needs bit-blasting and LRAT
(`issues/lrat-certified-bitvector-decision.md`). The reduction gives that
issue a concrete second customer and a reason to accept wide, mask-heavy
problems in its benchmarks.

The tempting shortcut, a case split over the 65 widths followed by
evaluation at each one, is the `o^k` enumeration the paper exists to
replace. It should not be the default even for one width variable.

Logged on `issues/lrat-certified-bitvector-decision.md`.

---

## 6. A correction to Table 2

Table 2 translates `slt(a, b, w)` as

```
ite(msb_w(a) = msb_w(b), msb_w(a) ⊕ ult(a, b), msb_w(a))
```

When both sign bits are 1, this negates the unsigned comparison. But two
negative numbers in two's complement compare the same way as their
unsigned encodings: at `w = 2`, −2 < −1, and `ult(2, 3)` is true, yet the
row gives false. The correct row is `ite(msb(a) = msb(b), ult(a, b),
msb(a))`. A brute-force check over every pair at widths 1–6 finds 1,365
disagreements for the printed row, none for the corrected row, and none
for §3's sign-flip form. The Lean artifact presumably has it right, since
the paper reports no wrong answers. Anyone porting the table should check
the artifact (Zenodo, the paper's reference [4]) rather than the printed
row.

---

## 7. What Heather's experience says back

- **The representation choice paid off here.** `issues/fixed-width-bitvectors.md`
  chose a vector of Booleans over a bounded `Nat`, scoring computation at
  an open width and structural proofs. The paper's whole unbounded method
  rests on reading bitvectors as bit streams, and Lean's `Fin 2^n` encoding
  needed a bridge to get there. In Heather the bridge is the definition.
- **Width equations are where the proof cost is.** The paper's `IsEq` is
  syntactic. Heather's is conversion, and the delta-style extension API
  puts `+` in result types (§2), so a multi-width statement often needs a
  transport before it typechecks. A reflective procedure has to handle
  these in its reifier, or it will refuse the goals people actually write.
- **The kernel's closed-word acceleration and an open-width procedure do
  not compete.** The kernel's transducer class makes *closed* words cheap,
  so certificates that compute at literal addresses stay cheap. The paper's
  procedure proves *open* claims once. A proved-once compiler needs both:
  the first for checking its output by evaluation, the second for stating
  its rules.

---

## 8. Follow-up

Filed:

- `issues/bitvec-width-generic-decision.md` (`tactics`): a reflective
  transducer procedure for the linear-bitwise fragment of multi-width
  `BitVec`, proved sound in Heather. Rung A checks an explicit invariant by
  evaluation, rung B waits on LRAT. The first round measures reachable-set
  sizes on the library's own open-width laws.

Logged:

- `issues/function-ir-narrow-arithmetic.md`: the verified lowering refuses
  narrow widths (`word_only`). Generalising `Kind` to "width `w`, held
  zero-extended" is Definition 4.1 at 64, and Table 2 lists the
  per-operation rules. The signed comparison is the sign flip (§3).
- `issues/lrat-certified-bitvector-decision.md`: the bounded multi-width
  reduction is a second customer, with the reduction proved rather than
  trusted (§5).

Not filed, for want of a customer: target-width spellings of the
extensions (§2), FunctionIR extension and truncation nodes (they arrive
with the first source language that has `i8`/`i32`), and porting the
InstCombine corpus as `lib/_tests` probes (once the tactic exists).
