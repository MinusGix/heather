# A bitvector literal born as a word — design

K1 round 4, design pass. Charter: `issues/bitvector-literal-entry-cost.md`.
The line so far: `issues/kernel-native-bitvector-values.md`,
`docs/native-bitvector-values-design.md` (rounds 2 and 3, §13 for every
correction implementing made).

The charter names two candidates — a packed vector-literal *term*, and an
`ofNat` whose reduction over a closed argument is recognised by round 3's
probe method — and asks for both to be sized against the code before either
is recommended. Both are sized here. The recommendation is neither of them
first: the measurement says the cheapest and largest win on the x86 line is a
**four-line respelling of `bitvec::ofNat`**, hand-run below, worth 3.3× on the
item shape the model actually pays; the packed term is well-formed and small
but has **no customer in `lib/`** as the library is spelled today.

Every number below was measured on the current tree (`c62a3d3`, round 3
landed) on one furnace instance, 2026-09-13, with a release binary built
`--features value-metrics` and a **fresh `--cache-dir` per group**. The
probe files are in `probes/`; the scripts that produced each table are
`probes/r4p1.sh` … `probes/r4p6.sh`.

---

## 1. The fresh before table, and what it corrects

### 1.1 The whole workload

Cold `--cache-dir`, `probes/r4p5.sh` (the `probes/README.md` recipe,
`reused_callee` through `build-x86`, one kernel worker):

| | items | item total s | `kernel_gate` s | steps | misses |
| --- | --- | --- | --- | --- | --- |
| this tree | 5 001 | 100.401 | 71.468 | 48 755 476 | 361 706 |

That is round 3's after column (48 797 992 steps, 361 706 misses,
design §13) to within the instance's own spread, so the tree under every
probe below is the one round 3 left.

### 1.2 The probe table (`probes/r4p1.sh`, width 64 unless named)

| row | what it is | `kernel_gate` ms | steps | misses |
| --- | --- | --- | --- | --- |
| `a3_bits_64` | `from_bits(64, L).bits = L` — **P1**, the charter's row | 3.815 | 3 481 | 582 |
| `a1_xor_64` | `bitvec::bxor` on two literals against a literal | 7.546 | 8 742 | 966 |
| `a4_add_64` | `bitvec::add`, the carry-threading shape | 8.982 | 9 444 | 966 |
| `c1_tonat_64` | `toNat` of a literal | 2.808 | 2 322 | 387 |
| `c2_zero_of_self_64` | `is_zero_bits(bxor(x, x))` | 5.174 | 4 905 | 775 |
| `c2_zero_lit_64` | `is_zero_bits(zero(64))` — no literal at all | 0.375 | 329 | 3 |

`a3_bits_64` reproduces §13's 3 481 steps exactly. **The charter's premise
holds**: the literal has not moved across the whole line.

### 1.3 P2 — the literal separated from its packing (`probes/t_p2_lit_split.hthr`)

Three items per width over the same 64-element alternating literal `L`.
`p2_def_n` is `fn p2_def_n() → [Bool; n] { L }`: the elaboration and the
kernel check of the literal, with **no vector-against-vector conversion in
the item at all**. `p2_lit_n` is `vid(n, L) = L` by `refl` (`vid` is the
identity on vectors, and exists only because a bare `[a, b] = [a, b]` in a
theorem's type parses as a vector *type*; it costs one δ-step). `p2_rec_n`
is `from_bits(n, L) = from_bits(n, L)`; `a3_bits_n` is that plus `.bits`.

| row | item total ms | `kernel_gate` ms | steps | misses |
| --- | --- | --- | --- | --- |
| `p2_def_64` (no conversion) | 3.346 | **2.514** | **2 813** | 193 |
| `p2_lit_64` | 5.739 | 3.902 | 3 429 | 580 |
| `p2_rec_64` | 5.197 | 3.341 | 3 267 | 579 |
| `a3_bits_64` | 5.507 | 3.815 | 3 481 | 582 |
| `p2_def_8` / `p2_lit_8` / `p2_rec_8` | 0.61 / 0.97 / 1.03 | 0.448 / 0.701 / 0.743 | 405 / 461 / 411 | 25 / 76 / 75 |

**This is the correction §2 of the previous design doc still owes.** §13 read
A3's residue as "elaborating and checking a 64-element `Bool` literal", which
is right, and attributed it to the *elaborator* ("its 582 conversion misses
… one per list element"). The split says the elaborator is the smaller half:
of `a3_bits_64`'s 5.507 ms, 3.815 ms is the **kernel gate**, and 2.514 ms of
that — 66 % of the gate, 81 % of the evaluator steps — is already spent by a
declaration that performs no conversion whatsoever. A literal costs ~44
evaluator steps and ~39 µs of kernel gate **per bit just to be checked**, and
one Σ-η comparison of two of them adds only ~670 steps and ~1.3 ms on top.

The consequence for candidate 1 is sharp and favourable: the target is the
kernel's `tm_check` of a chain of 64 `Term::Pair`s, not conversion, and a
term whose typing rule is O(1) in the width removes the larger part.

### 1.4 P3 — `ofNat` against the same value written out (`probes/t_p3_ofnat.hthr`)

`p3_ofnat_*` is `bitvec::ofNat(n, k) = bitvec::from_bits(n, <bits of k>)` by
`refl`; `p3_ctl_*` is that literal against **itself**, the control that
subtracts the literal's own elaboration, check and packing.

| row | `kernel_gate` ms | steps | misses |
| --- | --- | --- | --- |
| `p3_ofnat_64_big` (`0x0123456789abcdef`) | 18.044 | 7 326 | 194 |
| `p3_ofnat_64_one` (`1`) | 18.791 | 6 510 | 194 |
| `p3_ofnat_64_zero` (`0`) | 18.398 | 5 633 | 194 |
| `p3_ofnat_64_small` (`7`) | 18.985 | 6 551 | 194 |
| `p3_ctl_64_*` (the literal, both sides) | 3.60 – 3.68 | 3 267 | 579 |
| `p3_ofnat_8_c0` (`0xc0`, as `model.hthr` spells it) | 2.316 | 983 | 26 |
| `p3_ctl_8_c0` | 0.562 | 411 | 75 |

**A closed `ofNat(64, ·)` costs 18–19 ms of kernel gate, five times the same
value written out as a literal, and the cost does not depend on the
magnitude.** The width law the 2026-09-07 round bought is intact; the
constant it bought it at is 0.30 ms per bit.

### 1.5 P4 — the shape the x86 model actually pays (`probes/t_p4_mov_imm64.hthr`)

`canonical_bytes(MovRI(R9, imm))` against its ten-byte list — the reproducer
of `issues/bitvec-ofnat-large-literals.md`, at the immediate
`0x0123456789abcdef` that `examples/x86-native/calls.hthr` uses. Three
spellings of the same theorem (run with `-L /tmp/archL` holding
`model.hthr` as `x86_64.hthr`):

| row | immediate | the nine bytes | `kernel_gate` ms | steps | misses |
| --- | --- | --- | --- | --- | --- |
| `p4_mov_ofnat` | `ofNat(64, k)` | `ofNat(8, b)` | **47.974** | 1 780 | 126 |
| `p4_mov_mixed` | `ofNat(64, k)` | `from_bits(8, …)` | 32.181 | 4 004 | 526 |
| `p4_mov_lit` | `from_bits(64, …)` | `from_bits(8, …)` | 15.589 | 6 186 | 912 |

The first row is how `lib/` and the reflector spell it. Two thirds of that
item's kernel gate is `ofNat`: 16.6 ms for the one 64-bit immediate and
15.8 ms for the eight 8-bit bytes (1.8 ms each), against 15.6 ms for
everything else including the literals.

**Read the steps column and the seconds column together, once, and then stop
trusting the steps column alone for this issue.** Spelling every literal out
*triples* the evaluator step count (1 780 → 6 186) while cutting the kernel
gate by 67 %. `ofNat`'s cost is run arithmetic — `nat::le_dec` and `nat::sub`
cancelling 64-bit-magnitude `NatRun`s — which `eval_steps` charges one unit
for and the machine charges microseconds for. Round 3's headline metric was
steps; on this issue steps and seconds move in opposite directions, and the
seconds are the ones the bar is set in.

---

## 2. What a literal costs and where

Assembling §1.3 and §1.4 into the per-use breakdown the charter asks for, at
width 64:

| stage | where | cost | evidence |
| --- | --- | --- | --- |
| elaboration of a `[Bool; 64]` literal | `crates/elab/src/expr.rs:937` `check_vec_lit` — 64 × `check_expression` of a constructor against `El(Bool)`, one `shift_local` and one `nat_lit` per element | 0.83 ms, ~193 misses | `p2_def_64` total − gate |
| kernel check of the chain | `typing.rs`'s `Term::Pair` arm, 64 times, each against a fresh `Vec` annotation | 2.51 ms, 2 813 steps | `p2_def_64` gate |
| packing at one conversion | `eval/bits.rs:251` `pack_bit_prefix`, both sides | +1.3 ms, +670 steps | `p2_lit_64` − `p2_def_64` |
| packing at one classified fold | same walk, charged the fold's fuel | see `a1`/`a4` residue | design §13 |
| `ofNat(64, ·)` instead of a literal | `lib/std/bitvec.hthr:241` | 18.4 ms | §1.4 |

The charter's "~20 steps per bit" for `pack_bit_prefix` is the right order for
the *packing*; what it did not say is that packing is the small half. Per bit
at width 64: 44 steps to check the chain, ~10 more to pack it once, and a
further 288 steps' worth of *seconds* if the value arrived through `ofNat`.

### 2.1 Born packed, measured (`probes/t_p5_born.hthr`)

`bitvec::all_ones` and `bitvec::zero` are `repeat_bit`, an `elim_Nat` on the
width with no peeled argument and a `cons` output, which round 3's class
already classifies — so they are *produced* as a `Val::BitRun`. The same
value written as a `[Bool; 64]` literal is 64 `Term::Pair`s. Three rows at
one value:

| row | left | right | `kernel_gate` ms | steps | misses |
| --- | --- | --- | --- | --- | --- |
| `p5_ww_64` | word | word | **0.047** | **0** | **0** |
| `p5_wl_64` | word | literal | 2.492 | 4 166 | 194 |
| `p5_ll_64` | literal | literal | 3.632 | 3 267 | 579 |
| `p5_tonat_word` | `toNat(64, all_ones(64))` | | 0.792 | 241 | 1 |
| `p5_tonat_lit` | `toNat(64, from_bits(64, …))` | | 2.942 | 2 322 | 387 |

This is the whole of candidate 1's case, hand-run without writing the term:
the same value born a word compares to itself in **47 µs and zero evaluator
steps** where the literal costs 3.63 ms — 77× — and a real consumer (`toNat`)
is 3.7× cheaper on the word. Replacing even *one* side with a word already
saves 31 %.

---

## 3. Candidate 1 — a packed vector-literal term

### 3.1 The term

The charter's framing ("the kernel's typing rule checks it in O(1) per bit
against the `Vec` type") invites a *bit criterion in the typing rule*: decide
that `elem` whnfs to a sum of two unit-likes, and let `bits` stand for the
injections. **Do not do that.** It puts a semantic decision about a type into
the trusted typing rule and makes the term's meaning depend on a whnf. The
cheap form has neither problem:

```rust
/// A closed prefix of a `Vec` whose elements are all one of two given
/// terms. Observationally the same as the right-nested Σ-chain
/// `⟨e(b_0), ⟨e(b_1), … ⟨⟩⟩⟩` with `e(0) = zero`, `e(1) = one`, exactly as
/// `NatLit(n)` is the same as `Succ^n(Zero)`.
VecLit {
    level: Level,
    elem: Rc<Type>,
    zero: Rc<Term>,   // the element at a clear bit
    one:  Rc<Term>,   // the element at a set bit
    width: u32,       // 1 ..= BIT_RUN_WIDTH_CAP
    bits: u64,        // bit i is element i; LSB = index 0 = the Vec's head
},
```

`VecLit` is a **compression of a Σ-chain**, not a new value form, and it
names nothing: no `Bool`, no `BitVec`, no two-valued criterion. It is
`NatLit` one former over.

**Typing rule** (`typing.rs`, beside `Term::NatLit` at 1401):

```
Γ ⊢ elem : Ty ℓ      Γ ⊢ zero : elem      Γ ⊢ one : elem      0 < w ≤ CAP
──────────────────────────────────────────────────────────────────────────
              Γ ⊢ VecLit{ℓ, elem, zero, one, w, bits} : Vec^ℓ(elem; NatLit(w))
```

Three checks, independent of `w`: that is the O(1)-per-bit the charter asked
for, without a criterion. Adequacy (§6) is the unfolding identity, proved the
way `NatLit`'s is — by the `TmView`/`reduce` arms below agreeing with the
chain one component at a time.

**An open element type stays structural and is still fine**: `elem` may be
anything, including an open type, because the rule only checks `zero` and
`one` *against* it. What an open `elem` costs is that the *value* side
declines to pack (the bit criterion in `eval/bits.rs` fails), and the term
evaluates to an ordinary `Pair` with a `VecLit` tail — one pair per demanded
bit, still never the whole chain. So the "must stay structural" requirement
is met by the value path, not by refusing the term.

### 3.2 The syntax domain

`Term::NatLit`'s footprint is the template, and it is small. Each site below
gets one arm; the `VecLit` arm is `NatLit`'s arm with a payload instead of a
predecessor.

| site | what the arm does | ≈ lines |
| --- | --- | --- |
| `kernel/src/term.rs:321` | the variant and its doc | 15 |
| `kernel/src/subst.rs:567` | substitute `elem`, `zero`, `one` — three sub-terms, not `w` | 10 |
| `kernel/src/bounds.rs:159,339` | the three sub-terms' bounds | 6 |
| `kernel/src/fmt.rs:233` | `[b,b,…;w]`, budget-bounded per CLAUDE.md | 10 |
| `kernel/src/typing.rs:1401,2316` | the rule above, and the name | 25 |
| `kernel/src/conv/dom.rs:1069` | `TmView::Pair` — `fst` is `zero`/`one`, `snd` is `VecLit(w−1, bits≫1)` or `Triv`, annotations from `Vec`'s own rule | 25 |
| `kernel/src/reduce.rs:322,356,394,1258,1281` | the five `NatLit` pred-sites are about `Nat` *lengths* and are **untouched**; the `VecLit` sites are the `Fst`/`Snd` arms, which reduce through the `TmView` shape | 20 |
| `kernel/src/eval.rs:1022` | straight to `Val::BitRun` when `bit_ty(elem)` fires and `zero`/`one` are its injections; otherwise a `Pair` whose `snd` is the residual `VecLit` | 45 |
| **kernel subtotal** | | **~160** |
| `elab/src/expr.rs:937` `check_vec_lit` | emit `VecLit` when every element checked to the *same two* terms; fall back to the `Pair` chain otherwise | 45 |
| `elab/src/module_image.rs:639,698` | one tag, write/read | 10 |
| `cache/src/merkle.rs:627` | one tag, hash the three sub-terms + `w` + `bits` | 12 |
| `elab/src/certgen.rs:2279` | `mark`'s catch-all arm (a `VecLit` has no binder, so it is `Term::VecLit{..} => that`) | 5 |
| `elab/src/emission_walk.rs:131`, `gendefs.rs:2268`, `inductive.rs:635` | leaf-ish arms beside `NatLit`'s | 10 |
| `elab/src/function_ir_source.rs:406` | unchanged: it reads `Nat` literals | 0 |
| **elab subtotal** | | **~82** |
| tests (§3.5) | | **~200** |

**≈ 250 lines of source, ≈ 450 with tests.** Nothing in `crates/elab/src/wf.rs`
breaks: the `Term::Pair` chains it reads back at 2673 are *record* literals
(a one-constructor tier-0 inductive), not vector literals, and records keep
their `Pair` spelling.

### 3.3 Evaluator entry, `Fst`/`Snd`, shift, fuel

- **Entry.** `eval` of a `VecLit` asks `self.bit_ty(elem)` — the memoized
  criterion already in `eval/bits.rs` — and, when it fires and `zero`/`one`
  evaluate to that `BitTy`'s own injections, builds `Val::BitRun{ level, ty,
  width, bits, tail_len: NatLit(0), tail: Triv }` in O(1). This is a **fourth**
  entry route beside design §3.2's three, and it is the eager one §3.2 said
  was not available at `Term::Pair` — available here precisely because the
  term carries the element *type*, which a `Pair` in the untyped value domain
  does not.
- **`Fst`/`Snd`, `Case` on a bit, `value/shift.rs`**: unchanged. They already
  handle `Val::BitRun` (round 2), and that is the only value a `VecLit`
  produces. When the criterion declines, the residual `VecLit` in `snd` is a
  term, so `shift.rs` never sees it — `subst.rs`'s arm covers it.
- **Fuel.** Charge `spend_n(width)` at entry, for design §8's stated reason:
  charging at most what the structural path charged means nothing that
  succeeds today fails tomorrow, and charging *something* keeps a
  pathological width from being free. Entry is cheaper than the chain's
  check, so this is strictly slack.
- **Round 3's seed-only pack/unpack laws** (`crates/kernel/tests/`) are laws
  about `Val::BitRun`, and a `VecLit` produces exactly the run the packing
  walk produced from the equivalent chain. They gain a generator case, not a
  new law.

### 3.4 Quoting, the oracle, and the certificate's flat table

- **Quoting back.** Nothing changes. `Val::BitRun` has no quote arm today
  beyond the unpack that `TmView` performs; a quoted run is the `Pair` chain,
  which is still a well-typed term. A `VecLit` is a *smaller* spelling of a
  term the kernel already accepts, so quoting never has to produce one.
- **The differential oracle** (`crates/kernel/tests/eval_differential.rs`).
  The `BitRun`↔`Term::Pair` arm landed in round 3 and is documented as *not
  reachable from the generator* because `eval` only produced a run from a
  classified fold. **A `VecLit` makes it reachable**: generate `VecLit`s at
  widths 0, 1, 2, cap−1, cap, cap+1 over a two-valued element type, over
  `Triv` and over neutral tails, and the existing arm is exercised on every
  seed. That is a real gain for the line's standing evidence and is an
  argument for candidate 1 that has nothing to do with speed.
- **The certificate's flat table** (`certgen.rs`). `mark` walks a term to
  rewrite induction-hypothesis uses; a `VecLit` binds nothing and contains
  three sub-terms, so its arm maps `mark` over them. The table itself is
  keyed on terms, and a `VecLit` hashes in `merkle.rs` as a fixed-size node
  — which *shrinks* the table for any literal-bearing item. No verdict moves.

### 3.5 Tests, on the four axes

`docs/testing-generated-terms.md` asks a generated term's tests to vary four
things; three of the five defects it records were hidden by a closed element
type alone, and a `VecLit` over `Bool` is the most closed thing in the repo.

1. **Literal *and* neutral scrutinee** — a `VecLit` eliminated by `Fst`/`Snd`
   and by a classified fold, and the *same* item with the vector coming from
   a binder.
2. **An open element type** — `VecLit` at `elem` a local variable of type
   `Ty ℓ`: the typing rule must accept it, the criterion must decline, and
   the value must be a `Pair` with a `VecLit` tail. This is the axis that
   would hide a bug where the criterion is consulted in the *typing* rule.
3. **A checking position** — a `VecLit` checked against a `Vec` whose length
   is a computed `Nat`, not only computed into.
4. **A negative control** — two `VecLit`s differing in one bit must be
   `NotConvertible` (not `OutOfFuel`), and a `VecLit` whose `one` is not
   canonical at its type must be *rejected by the typing rule*, not silently
   packed.

---

## 4. Candidate 2 — `ofNat` over a closed argument

### 4.1 Why `ofNat` is `Opaque` today — the mechanical answer

`bitvec::ofNat` (`lib/std/bitvec.hthr:241`) is

```
ofNat(n)(x) = from_bit_list(n,
                bits_at_powers(powers_of_two_desc(n, 1, Nil),
                               mod_succ(x, pred(pow(2, n))), Nil))
```

and the only `elim_Nat`-on-a-width in it is `from_bit_list` (line 231), whose
motive is `λ k => List<Bool> → BitVec(k)`.

Follow `crates/kernel/src/eval/transduce.rs`'s probe on that pair:

1. `walk_motive` (line ~505) classifies the one domain, `List<Bool>`. It is
   not a `Vec` in a unit-like Σ-context, so not `Peeled`; it is not finitely
   enumerable, so not `State`. It is **`Carried`**, and a carried argument's
   probe value is a fresh neutral (`PROBE_CARRIED - j`).
2. `peeled == 0`, but `vec_in(cod)` finds the `Vec` inside `BitVec(Succ k)`,
   so the gate at line 158 passes and the step is evaluated.
3. `probe_word_output` applies the step. The step is
   `λ bits => match bits { Nil => …, Cons(b, rest) => cons_bit(k, b, ih(rest)) }`
   — a case split **on the carried neutral**. The value is a stuck neutral,
   not a `Pair`, so `slot_of`/`Val::Pair` fails and the probe returns `None`.
4. `probe_value_output` then asks for a finite or `Nat` codomain; the
   codomain is `BitVec(Succ k)`, `enumerate` declines, `None`.

So: **the class can only read bits out of a peeled `Vec` argument, and
`ofNat`'s bits arrive in a carried `List`.** Nothing about `ofNat`'s name or
spelling is involved; it is the argument mode, read off the motive.

This is also why `bxor`/`band`/`add` classify and `ofNat`, `mul`, `div` do
not (design §13's list): the first three peel vectors, the last three carry
something the step splits on.

### 4.2 Where `ofNat`'s 18 ms actually is (`probes/t_p3b_*.hthr`, `t_p3c_*.hthr`)

Before proposing anything, the premise: the width sweep, and each suspect
removed in turn.

| row | `kernel_gate` ms | steps |
| --- | --- | --- |
| `p3b_ofnat_w8` | 2.532 | 1 007 |
| `p3b_ofnat_w16` | 4.521 | 1 799 |
| `p3b_ofnat_w32` | 11.058 | 3 383 |
| `p3b_ofnat_w63` | 17.673 | 6 452 |
| `p3b_ofnat_w64` | 19.550 | 6 551 |
| `p3b_trunc_w64` — `mod_succ(7, pred(pow(2, 64)))` alone | 0.731 | 775 |
| `p3b_ofnat2_w64` — `ofNat` **without** the truncation | 17.747 | 5 590 |
| `p3b_ofnat3_w64` — without truncation, **literal** powers list | 17.454 | 4 949 |
| `p3c_bits_w64` — `bits_at_powers` alone | 12.281 | 2 562 |
| `p3c_asm_w64` — `from_bit_list` over a literal `List<Bool>` | 9.226 | 3 108 |

Three things this refutes, each of which would have been a plausible guess:

- **It is not the `2^64` overflow.** Width 63 (where `pow(2, n)` fits a
  `u64` run) costs 17.67 ms against width 64's 19.55 — no cliff. The cost is
  0.30 ms per bit at every width from 8 to 64.
- **It is not the truncation.** `mod_succ(7, pred(pow(2, 64)))` is 0.73 ms,
  4 % of the whole; removing it saves 1.8 ms.
- **It is not building the powers list.** Handing the fold a written-out
  64-element powers list saves a further 0.3 ms.

What is left — **17.5 ms of the 19.6** — is `bits_at_powers`'s per-bit
`nat::le_dec`/`nat::sub` against 64-bit-magnitude powers, and
`from_bit_list`'s per-bit `cons_bit` over a `List`. Both are already the
"two-counter folds the kernel cancels run against run" the 2026-09-07 round
chose them for; cancelling a run against a run is O(1) in *steps* and is
evidently ~0.15 ms each in *seconds* at this magnitude.

**Verdict on "a library respelling of `ofNat` into a shape the existing class
already fires on": there is none.** The existing class needs a peeled `Vec`;
`ofNat` has no vector input at all, at any spelling. Every respelling that
keeps the current top-down shape leaves the 17.5 ms where it is (measured,
two ways, above).

### 4.3 But a different respelling is worth 5×, and it is four lines

The module header (`lib/std/bitvec.hthr:180–195`) records why the *obvious*
spelling was rejected on 2026-09-07:

> the low bit by parity, the rest at `half(x)` — peels the argument one
> successor at a time, so a machine-width literal costs `2^64` steps

**That note is stale.** It predates `nat-run-algebra-primitives` (2026-09-09),
after which `half`'s course-of-values window is *classified* — "a permutation
iterated by exponentiation", `crates/kernel/DESIGN.md:~305`. Hand-run
(`probes/t_p3c_ofnat_halves.hthr`), with the whole respelling written as a
probe-local definition:

```
fn odd_bit(n: Nat) → Bool {
    match n { Zero => False, Succ(k) => match k { Zero => True, Succ(l) => odd_bit(l) } }
}

fn ofNatH(n: Nat) → Nat → BitVec(n) {
    match n as λ k => Nat → BitVec(k) {
        Zero => λ x => from_bits(0, []),
        Succ(k, ih) => λ x => cons_bit(k, odd_bit(x), ih(nat::half(x))),
    }
}
```

| row | `kernel_gate` ms | steps |
| --- | --- | --- |
| `p3b_ofnat_w64` — shipped `ofNat(64, 7)` | 19.550 | 6 551 |
| `p3c_half_w64` — `ofNatH(64, 7)` | **3.418** | 3 264 |
| `p3c_half_big` — `ofNatH(64, 0x0123456789abcdef)` | **4.083** | 3 588 |
| `p3b_ofnat_w8` — shipped `ofNat(8, 7)` | 2.532 | 1 007 |
| `p3c_half_w8` — `ofNatH(8, 7)` | **0.800** | 464 |
| `p3_ofnat_8_c0` — shipped `ofNat(8, 0xc0)` | 2.316 | 983 |
| `p3c_half_w8_c0` — `ofNatH(8, 0xc0)` | **0.611** | 492 |

**5.7× at width 64, 3.2× at width 8, and the magnitude independence the
2026-09-07 round bought is kept** — a full-width asymmetric immediate costs
19 % more than `7`, not 2⁶⁰ times more, which is itself the measurement that
proves `half` is classified today. `ofNatH(64, ·)` at 3.4 ms is *cheaper than
writing the same value out as a `from_bits` literal* (3.63 ms, `p5_ll_64`).

Two further properties, both free:

- **Truncation becomes definitional.** `ofNatH` is the low `n` bits of `x` by
  construction, so `mod_succ`/`pow` disappear from the definition entirely —
  and with them `pow(2, 64)`, which does not fit a `u64` run. The module
  header's truncation obligation (`mul` and the header depend on it) is met
  more directly than before, not weakened.
- **The proofs above it.** `ofNat`'s existing rails
  (`issues/bitvec-ofnat-large-literals.md`'s acceptance: the asymmetric,
  high-bit, saturated and five-digit literals at width 64 against
  independently written bit vectors and through `toNat`, with single-bit
  flips refused as `NotConvertible`) are statements about `ofNat`'s *values*,
  not its spelling, so they re-check unchanged. Any `ofNat`-specific lemma in
  `lib/std/bitvec.hthr` needs its proof re-run; that is the implementing
  pass's first job (§8.2).

On the item the model actually pays (`probes/t_p4b_mov_half.hthr` — the P4
theorem with every `ofNat` replaced by `ofNatH`; `canonical_bytes` itself
still uses the shipped `ofNat` for the REX and opcode bytes, so this
**understates** the respelling by two sites):

| row | `kernel_gate` ms | steps |
| --- | --- | --- |
| `p4_mov_ofnat` (shipped) | 47.974 | 1 780 |
| `p4b_mov_half` | **14.396** | 13 742 |
| `p4_mov_lit` (every literal written out) | 15.589 | 6 186 |

**3.3× on the x86 item, from a library-only change, with no kernel diff and
no trusted-base delta.** Note again that steps go *up* 7.7× while seconds go
down 3.3×.

### 4.4 The class candidate 2 proper needs: a `Nat`-state mode

`ofNatH` still produces a **structural** 64-pair chain — 3.4 ms, which is the
literal's own floor (§1.3). To take that to `p5_ww_64`'s 47 µs the fold has
to produce a `Val::BitRun`, and for that the transducer class needs one new
argument mode:

**`ArgMode::NatState`** — a domain whose type δ-whnfs to `Nat`. Its probe
value is a neutral, as a carried argument's is; what changes is what the
probe is allowed to *read* from the resulting value. The step classifies when

```
step k ih x  ⇝  cons( f(x) , ih( g(x) ) )
```

with `f` a `Nat`-scrutinee fold into the bit type and `g` a `Nat`-scrutinee
fold into `Nat`, **both of which the existing `classify_step` decides**
(`eval/probe.rs`, `value/algebra.rs`). The machinery to read them off is
already written: `probe_scaled` (transduce.rs:352) walks the eliminations on
a neutral's spine and calls `classify_step` on each inner `ElimNat`; the only
difference is that here the neutral is the *argument* rather than `ih`, and
that the head's classification must be evaluable at a closed `NatRun` rather
than composable into an affine map.

Running it is then: for each of the `width` bits, evaluate `f` and `g` at the
current closed `NatRun` state through the classified-fold machinery, shift
the bit in, and iterate. No truth table — the state is not finite — so this
is a genuinely new arm beside `Output::Cons`/`Pass`/`Finite`/`Scaled` and
not a widening of one.

Honest costs and risks:

- `odd_bit`'s class. It is a `Nat` fold with a **two-successor window** and a
  `Bool` result — the same window shape as `half`, which is classified, but
  `FoldClass` today has `Affine`/`Sync`/`Opaque` and no finite-valued `Nat`
  fold. Either `odd_bit` is respelled to something already classified, or
  `probe.rs` gains a finite output for `Nat` folds. **This is the item that
  decides whether the class is 200 lines or 500**, and §8.3 makes it the
  implementing pass's first refutable check.
- Adequacy is the same argument as the rest of the line — the substitution
  property of reduction, applied to a neutral state variable — and the
  `DESIGN.md` paragraph gains one clause, not a new section.
- Estimated: `value/transducer.rs` + `eval/transduce.rs` ~250–350 lines,
  `eval/probe.rs` 0–150 depending on the `odd_bit` question, tests ~200.

### 4.5 `ofNat` is where the x86 line's literals live

| spelling | sites in `lib/` |
| --- | --- |
| `bitvec::ofNat(64, ·)` | **218** |
| `bitvec::ofNat(8, ·)` | 63 |
| `bitvec::ofNat(48/52/16, ·)` | 5 |
| `[True, False, …]` vector literals | **0** |
| `from_bits(n, <literal>)` at `n > 1` | 1 |

`lib/elf64_calls.hthr` alone has 95; `lib/std/arch/x86_64/calls.hthr` 64;
`lib/elf64.hthr:12` is `fn elf_byte(n) → BitVec(8) { bitvec::ofNat(8, n) }`,
so every ELF byte in the certificate is an `ofNat`. And
`crates/elab/src/function_ir_source.rs:320` *requires* it: "BitVec constants
must use `bitvec::ofNat(64, literal)`" — the reflector emits `ofNat` for
every constant it lifts out of a source function.

---

## 5. The x86 sizing, and the recommendation with order

### 5.1 Sizing

The workload is 71.468 s of kernel gate over 5 001 items (§1.1). It contains
no `[Bool; n]` literal at all, and one `from_bits` at a width above 1. Every
bitvector constant in it — every immediate, every address, every ELF byte,
every opcode-table key in `model.hthr:1139–1150` — is an `ofNat`.

The item measurement that stands closest to the workload is P4:
`canonical_bytes` of one instruction, which is the shape `caller_native_byte`
(36 items, 4.070 s), `caller_native_byte_page` (167 items, 1.995 s),
`caller_native_byte_wrap` (131, 1.918 s) and `caller_native_write_literal`
(48, 0.585 s) all pay. On it, `ofNat` is **two thirds of the kernel gate**,
and the respelling removes **70 %** of it.

The honest bound, stated as a shape and not a projected number per the
project's rule about that: the respelling moves *every* closed `ofNat`
reduction in the workload by 3–6×, and closed `ofNat` reductions appear in
every byte-equality, address-arithmetic and table-lookup family. It cannot
move the families whose `ofNat` arguments are **open** (`ofNat(64, rest)`,
`ofNat(64, count)` in `elf64_calls.hthr`) — those do not reduce today and
will not reduce after. Whether the whole-workload seconds move enough to meet
`docs/native-bitvector-values-design.md` §9's bar is exactly what the
implementing pass measures, cold, both columns in one job; nothing here
predicts it.

### 5.2 Recommendation

**Order: 4.3, then 4.4, then — only if it has earned a customer — 3.**

1. **Respell `bitvec::ofNat` as `ofNatH`** (§4.3). Library-only, four lines
   plus `odd_bit`, no kernel diff, no trusted-base delta, no new test axis.
   Measured 5.7× at width 64, 3.2× at width 8, 3.3× on the P4 item. It is
   the *only* one of the three that touches the traffic §4.5 counts. It also
   deletes `mod_succ`, `powers_of_two_desc`, `bits_at_powers`,
   `from_bit_list` and the `pow(2, 64)` that does not fit a run — a net
   simplification of the library, which is the right shape for an alpha: a
   respelling costs API churn the project has already decided is cheap here.
2. **The `Nat`-state transducer mode** (§4.4). Takes the respelled `ofNat`
   from 3.4 ms to the `p5_ww_64` floor of 47 µs, and makes every closed
   constant on the x86 line enter the evaluator as a word, which is what the
   charter's title actually asks for. Its own risk is one classification
   question (§8.3), and it should not start until 1 has landed and been
   measured — 1 changes the definition the class would be probing.
3. **The packed vector-literal term** (§3). Well-formed, small (≈250 lines),
   and it removes the largest floor in the *probe* table. But `lib/` contains
   zero vector literals, the reflector cannot emit one, and the certificate's
   flat table has none: **it has no customer today**. Its real standing
   argument is the one in §3.4 — it makes round 3's `BitRun`↔`Pair` oracle
   arm reachable from the generator, which it currently is not. Recommend
   filing it as designed-and-deferred behind a trigger: *a hand-written
   `[Bool; n]` literal on a measured path*, or *the oracle arm wanted
   reachable*. Do not land it as a performance change; it would measure flat
   on this workload, which is round 2's mistake repeated.

If only one round is available, it is 1, and it is small enough that 1 and 2
plausibly fit in one.

---

## 6. Draft paragraph for `crates/kernel/DESIGN.md`

To be inserted **only if candidate 1 lands**, immediately after the "Native
bitvector values" adequacy paragraph (currently ending at line ~349, before
"Conversion compares two vectors…"). Written to sit beside it in register
and to be applied *amended* if implementing corrects it, per design §13's
precedent:

> **A vector literal is a term.** `Term::VecLit{ℓ, elem, zero, one, w, bits}`
> is a closed prefix of a `Vec` all of whose elements are one of two given
> terms, and it is `NatLit` one former over: notation for the right-nested
> Σ-chain `⟨e(b₀), ⟨e(b₁), … ⟨⟩⟩⟩` with `e(0) = zero` and `e(1) = one`,
> exactly as `NatLit(n)` is notation for `Succ^n(Zero)`. Its typing rule
> checks `elem` as a type and `zero` and `one` against it — three judgements,
> independent of the width — and nothing else: the rule contains no
> two-valued criterion and names no library type, so the term means the chain
> whatever `elem` is. Adequacy is that unfolding identity, and it is
> discharged where every other constructor's is: the syntactic view
> (`conv/dom.rs`) hands back the chain's head pair with the `Vec` rule's own
> annotations and a `VecLit` at the shorter width, so every comparison that
> ran on the chain runs unchanged on the literal. What the term buys is
> entry: when `elem` meets the bit criterion and `zero`/`one` are its
> injections, the evaluator reads the whole literal into one `Val::BitRun` in
> constant time — the eager entry route the value domain cannot have at
> `Term::Pair`, available here because the term carries the element type that
> a pair does not. When the criterion declines — an open element type, a
> payload of its own — the literal evaluates to an ordinary pair with a
> shorter `VecLit` behind it, one node per demanded bit, and everything below
> is as it was.

---

## 7. The eagerness sibling

`issues/bitvector-fold-eagerness-at-demand-driven-consumers.md` records that
a classified fold packs its arguments and produces all `width` bits where the
structural chain produced only the bits its consumer forced; on this
workload that cost the `read_literal` family 0.682 → 1.398 s in round 3 and
was the whole of that round's gap. On this tree `caller_native_read_literal`
is 32 items, 1.188 s of gate, 407 011 steps, 816 misses (§1.1's agg).

The issue has two halves, and "born packed" separates them cleanly:

- **The packing half dissolves.** The family's cost is "packing two
  structural literal arguments" — a `pack_bit_prefix` walk of a chain the
  consumer was going to touch one bit of. If the argument arrives as a
  `BitRun` (from candidate 1's term, or from a `Nat`-state-classified
  `ofNat`), there is no walk: the word is already there and the packing cost
  is zero, not deferred. Measured analogue: `p5_wl_64` (word against literal,
  2.492 ms) against `p5_ll_64` (literal against literal, 3.632 ms) — one side
  arriving packed is worth 31 % on its own.
- **The firing half does not.** A `BitRun` is still its whole width by
  construction, so a classified fold still computes 64 output bits for a
  consumer that wanted one. That is the question the sibling issue actually
  poses and neither candidate here answers it.

What *does* change is that the sibling's cheapest candidate answer becomes
viable. The issue lists "fire only when every peeled argument is already a
word (a literal that is not yet packed stays structural)" and notes it is
tuning. Today that rule would switch the class off almost everywhere,
because nothing produces a word at entry. After either candidate here, the
rule becomes a *real* discriminator: arguments that came from a literal or a
classified `ofNat` are words and fire; arguments still being built one bit at
a time are structural and do not. The sibling should be re-read after this
round rather than before it, and its `read_literal` reproducer re-measured,
since the family's inputs are `ofNat` constants (§4.5) whose representation
this round changes.

---

## 8. Verification items for the implementing pass's first hour

Each is cheap and each can refute part of this design. **If one refutes,
stop and report — do not work around it.** That instruction is not
boilerplate: rounds 2 and 3 both stopped at their bar, and §13 records that
the two rounds that did *not* stop produced a misattribution and two fixes on
a wrong diagnosis.

1. **Re-run the fresh before table.** `probes/r4p1.sh` and the P2/P3/P4
   scripts, cold `--cache-dir` each. `a3_bits_64` must be 3 481 steps and
   `p4_mov_ofnat` ~48 ms of gate. If they are not, this tree is not the one
   measured here and nothing below applies. (≈ 3 minutes.)
2. **`ofNat`'s rails, before touching the definition.** Check
   `lib/std/bitvec.hthr` as it stands and list every theorem whose statement
   or proof mentions `ofNat`, `from_bit_list`, `bits_at_powers`,
   `powers_of_two_desc` or `mod_succ`. The respelling is only cheap if the
   first set re-checks unchanged and the second set is deleted with its
   functions. If a theorem's *proof* depends on the top-down spelling — an
   induction over the powers list, say — the respelling is not four lines and
   the estimate in §4.3 is wrong. (≈ 15 minutes.)
3. **`odd_bit`'s classification.** The `Nat`-state mode (§4.4) needs a
   `Nat`-scrutinee fold into `Bool` to be classified. `FoldClass` has
   `Affine`/`Sync`/`Opaque` and no finite output for `Nat` folds. Write the
   20-line probe: a `Nat`-state step, `classify_step` on `odd_bit`, and see
   what comes back. If it is `Opaque` and cannot be made otherwise without a
   new `FoldClass` variant, §4.4's estimate doubles and the round should be
   scoped to item 1 of §5.2 alone. (≈ 30 minutes.)
4. **The respelling's magnitude behaviour at the workload's real arguments.**
   §4.3 measured `7` and `0x0123456789abcdef`. The workload's `ofNat(64, ·)`
   arguments are 0–8 at 205 of 218 sites, and `0x401000`/`0x4000e8`/`0x1000`
   at the rest. Run `ofNatH` at `0x401000` and confirm it sits between the
   two measured points. If a mid-magnitude argument is *worse* than either,
   `half`'s classification has a window this design did not see. (≈ 5
   minutes.)
5. **If candidate 1 is attempted: `size_of::<Term>()` before and after.**
   Round 2's §13 records the same check on `Val` deciding the width cap.
   `VecLit` adds a `Level`, three `Rc`s, a `u32` and a `u64`; if `Term` grows,
   box the payload rather than widening every term in the machine.
6. **If candidate 1 is attempted: the open-element-type item first.** Write
   §3.5's axis-2 test *before* the fast path. A `VecLit` at an open `elem`
   must type-check, must not pack, and must evaluate to a `Pair`. A design
   that only works at `Bool` is the failure mode
   `docs/testing-generated-terms.md` exists to catch, and it is three of the
   five defects it records.
7. **The miss-count signature, on every measurement.** Design §7's rule
   stands: conversion **miss counts must not move**. They did not move across
   rounds 2 or 3 (361 706 both times, and 361 706 again in §1.1). A change in
   the count means a verdict changed shape, not a cost, and is a stop.
8. **Steps are not the metric this round.** §1.5 measured the two moving in
   opposite directions on the same theorem. Gate the round on
   `kernel_gate_ns`, cold, both columns in one furnace job; quote steps
   alongside, never instead.

---

## 9. What this assumes from elsewhere

- **`nat::half` is classified** (`crates/kernel/DESIGN.md:~305`,
  `issues/nat-run-algebra-primitives.md`). §4.3's whole case rests on it, and
  §4.3's own magnitude control is the evidence — but if that classification
  is ever narrowed, `ofNatH` reverts to the 2026-09-07 behaviour the module
  header warns about, which would be a silent, catastrophic regression. The
  respelling's commit should say so, and item 4 of §8 is the standing check.
- **The bit criterion and `BitTy` are as round 2 left them**
  (`crates/kernel/src/eval/bits.rs`, `value.rs`'s `BitTy{elem, zero, one}`).
  Candidate 1's evaluator entry reuses them verbatim; a change to the
  criterion's memo key is a change to §3.3.
- **`BIT_RUN_WIDTH_CAP` is 64** (design §13's correction to §3.4). A
  `VecLit` above the cap must decline to the structural path, not truncate.
- **The reflector's constant form** (`function_ir_source.rs:320`) stays
  `bitvec::ofNat(64, literal)`. If it ever emits a vector literal instead,
  candidate 1 acquires a customer and §5.2's order changes.
- **The certificate's flat table is keyed on terms** (`certgen.rs`,
  `cache/src/merkle.rs`) and tolerates a new fixed-size node. This was true
  for `NatLit`; nothing suggests it is not true here, but §3.4 is the
  paragraph to re-read if an image fails to round-trip.
- **`docs/delam/04–06`** binds the term language. `VecLit` adds no rule to
  the calculus — it is a compressed spelling of a derivation the calculus
  already has, exactly as `NatLit` is — so nothing in 04–06 changes. If the
  implementing pass finds itself wanting a *typing* rule that consults the
  element type's shape, that is no longer true and the design is wrong.

---

## 10. What implementing corrected

The implementing pass ran §8's items first, then landed §5.2's steps 1 and 2.
Same shape as `docs/native-bitvector-values-design.md` §13: each entry names
the section it amends. Step 3 (§3, the packed vector-literal term) was not
attempted and is filed deferred.

### 10.1 §8.3 — `odd_bit` is already classified; no new `FoldClass`

The item that decides whether §4.4 is 200 lines or 500. The answer is 200.
Probed end to end (`probes/t_v3_oddbit.hthr`, a `heather check` rather than a
Rust unit test, which is the cheaper instrument for the question actually
asked — *does the fold cost the magnitude?*):

| row | `kernel_gate` ms | steps |
| --- | --- | --- |
| `v3_odd_small` — `odd_bit(7)` | 0.098 | 65 |
| `v3_odd_mid` — `odd_bit(1 000 001)` | 0.077 | 65 |
| `v3_odd_big` — `odd_bit(81 985 529 216 486 895)` | **0.068** | **65** |
| `v3_notodd_mid` — the *opaque* parity (`not` per successor) at `100 001` | 271.252 | 400 067 |

`odd_bit` is flat in the magnitude at the same 65 steps from `7` to `8.2·10¹⁶`;
the one-successor control is linear and 4 000× more expensive at a magnitude
30 000× smaller. So `odd_bit`'s course-of-values window classifies exactly as
`half`'s does — its step is a *permutation of the carrier's components*, all
projections and no literal, which `read_affine` accepts whatever the
components' type is. §4.4's worry ("`FoldClass` today has `Affine`/`Sync`/
`Opaque` and no finite-valued `Nat` fold") rested on the base case, which the
peeled probe never sees. **No `FoldClass` variant was added and
`eval/probe.rs` was not touched.**

### 10.2 §8.2 — step 1 really is four lines

Nothing outside `lib/std/bitvec.hthr` mentions `from_bit_list`,
`bits_at_powers`, `powers_of_two_desc` or `mod_succ`: not `lib/`, not
`examples/`, not `crates/*/tests`, not the reflector. Every `ofNat` mention
elsewhere is a statement about its *values*. So the four functions were
deleted with the definition and no proof was re-run by hand.

Two things beyond §4.3's "four lines plus `odd_bit`": `import list;` became
unused and was removed, and the stale `mul` comment at the old line 401 (which
described `mod_succ`'s loop) was rewritten. The module header was rewritten as
§5.2 asked, and now records the *dependence* §9 flags — if `half`'s
classification is ever narrowed this definition reverts to costing the
magnitude.

### 10.3 §1.5 — the P4 step counts do not reproduce; the gate does

Re-running §8.1 on the same tree reproduced `a3_bits_64` at **3 481 steps**
exactly and every other probe row's steps to the digit, and `p4_mov_ofnat` at
45.1 ms of gate against §1.5's 47.974. But its *steps* came back 21 312 where
§1.5 records 1 780, and `p4_mov_lit` 13 251 against 6 186. The rows that
differ are exactly the three that need `-L /tmp/archL`; the likeliest cause is
that §1.5's P4 group was measured against a cache directory that was not
fresh, which `probes/README.md` warns produces zeros and, partially warm,
produces undercounts. **The gate seconds — the column §8.8 sets the bar in —
reproduce; the steps column for §1.5 alone should not be quoted again.** This
does not change §1.5's conclusion, which was about seconds.

### 10.4 §8.4 — the respelling is flat at the workload's real arguments

| argument | `ofNat` (shipped) gate ms | the respelling gate ms |
| --- | --- | --- |
| `0` | | 3.029 |
| `8` | 17.725 | 3.141 |
| `0x1000` | | 3.435 |
| `0x401000` | 18.123 | 3.091 |
| `0x4000e8` | | 3.214 |
| `0x0123456789abcdef` | | 4.879 |

Every workload argument sits at or below the small-argument point and well
below the full-width one. `half`'s classification has no window this design
did not see, and the respelling is 5.6–5.9× at the arguments `lib/` actually
passes.

### 10.5 §8.7 — a library respelling *did* move the miss count, by 65

Step 1's two columns are 361 706 and 361 641 misses. §7's rule is about a
*kernel* change, where a moved count means a verdict changed shape; a library
respelling changes which definitions exist at all, and this one deletes four
and adds one. The four deleted declarations and the removed `import list` are
also the whole of the item-count change (5 001 → 4 997). The rule was applied
as written to step 2, whose two columns are the same library.

### 10.6 Step 1 landed and met the bar

Cold, both columns in one furnace job on one instance, the recipe of
`probes/README.md` (`probes/s1b.sh`; and see 10.8 for why a library column
needs its own *build*):

| | items | item total s | `kernel_gate` s | steps | misses |
| --- | --- | --- | --- | --- | --- |
| step 1 before (`c62a3d3` + the doc) | 5 001 | 101.462 | 72.560 | 48 755 476 | 361 706 |
| step 1 after | 4 997 | 92.236 | **63.955** | 46 617 036 | 361 641 |

**−11.9 % of the whole workload's kernel gate**, −9.1 % of the item total.
The chartered families, before → after (seconds of gate):

| family | items | before | after |
| --- | --- | --- | --- |
| `caller_native_byte_page` | 167 | 1.986 | **0.474** |
| `caller_native_byte_wrap` | 131 | 1.917 | **0.425** |
| `caller_native_stack_allowed` | 36 | 1.465 | **0.426** |
| `caller_native_store_offset` | 48 | 0.805 | **0.241** |
| `caller_native_read_literal` | 32 | 1.215 | 1.105 |
| `caller_native_byte` | 36 | 4.090 | 4.007 |
| `call_run_checked` | 1 | 23.680 | 23.291 |

The families that are byte-, address- and page-arithmetic over `ofNat`
constants move by 3.8–4.5×, exactly as §5.1's shape claim said; the two
families whose `ofNat` arguments are open or whose cost is elsewhere barely
move, also as stated. The P4 item (`probes/t_p4_mov_imm64.hthr`) went
45.147 → **17.611** ms of gate, **2.56×** — below §4.3's hand-run 3.3×,
because the shipped `canonical_bytes` respells its own two `ofNat` sites too
and the remaining cost is the literals it compares against.

The full suite is green on this tree: `== suite: 2613 passed, 0 failed,
5 ignored ==`.

### 10.7 Step 2 was built, is correct, and **failed the bar** — §4.4 amended

The `Nat`-state arm was implemented and measured. Both columns cold in one
job, the same library on both sides:

| | items | item total s | `kernel_gate` s | steps | misses |
| --- | --- | --- | --- | --- | --- |
| step 1 only | 4 997 | 91.846 | **63.662** | 46 617 036 | 361 641 |
| step 1 + step 2 | 4 997 | 92.601 | **64.274** | 46 614 730 | 361 641 |

**+1.0 % of kernel gate — above the before column, so the bar fails and the
change is not landed.** §8.7 is satisfied (the miss counts are *identical*:
no verdict changed shape), and steps move by −0.005 %. The probes say the
same thing and say it larger, which is why this is a real regression and not
the instance's spread:

| row | step 1 only | + step 2 |
| --- | --- | --- |
| `p4_mov_ofnat` gate ms | 17.611 | 18.294 |
| `p4_mov_ofnat` steps | 13 742 | 11 680 |
| `v4_half_401000` gate ms | 3.091 | 4.419 |
| `v4_half_401000` steps | 3 384 | 5 906 |

Steps fall and seconds rise — §1.5's lesson a second time, now against the
change that was supposed to exploit it.

**What §4.4 got wrong.** It assumed the arm could read `f` and `g` off the
probe *symbolically* and then compose them — "evaluate `f` and `g` at the
current closed `NatRun` state through the classified-fold machinery" — and
priced that at `p5_ww_64`'s 47 µs floor. It cannot, in this value
representation: a probe value's state variable is a `Head::Var` at a reserved
level and there is no substitution that puts a closed state into it. What is
available is **replay** — the idiom round 3 already chose for the finite
probe — so the arm runs the fold's own step once per bit, at that bit's own
`k` and at the state the last one left, and collects the bits into a word.
That is sound (the reductions are the fold's own, so adequacy is the
representation change alone, and the loop checks each bit closed and each
next state closed rather than assuming it), and it is what the tests confirm.
But it does not remove the per-bit work — it removes only the pair
construction and the Σ-η that follows — and it *adds* a forced whnf of each
intermediate state plus a re-entry into the step closure per bit. On this
library those additions are larger than what the word saves. **§4.4's cost
estimate is void**; the arm reaches a word, not the floor, and the floor was
the whole of its case.

The work is kept where it can be reviewed and resumed rather than discarded:
`docs/patches/bitvector-nat-state-arm.patch` is the whole change — `ArgMode::NatState`,
`Output::NatCons`, `probe_nat_state`, `fire_nat_state`, and four kernel unit
tests on `docs/testing-generated-terms.md`'s axes (a literal state at widths
1/4/8/64, a **neutral** state that must stay structural, a non-two-valued
element type that must decline, and a head bit reading `k` instead of the
state as the negative control, which must decline *and* still reduce to the
right chain). All 16 tests in `eval/transduce.rs` pass with it applied. The
`DESIGN.md` clause §6 asked for was written against the corrected adequacy
argument above and reverted with the change; it is in the patch.

`scripts/bench --check` was not run: the landed tree has no kernel diff, so
there is nothing for it to gate.

### 10.8 A library before/after pair needs two builds

`crates/cli/src/native.rs` bundles every `lib/std/*.hthr` with `include_str!`
and `build-x86` refuses a source library that differs from the bundled one, so
swapping `bitvec.hthr` between two runs of one binary produces
`error: source module 'bitvec' differs from the compiler's bundled proof
library` and no timings at all. Each column needs its own build. Recorded in
`probes/README.md`.

### 10.9 What is left

- §5.2's step 3 (the packed vector-literal term, §3) was not attempted, per
  the brief's scope.
- The `Nat`-state arm is *designed, implemented, tested and refuted on cost*.
  If it is revisited, the question to answer first is the one §4.4 assumed
  away: can the per-bit step application be avoided at all, given that a
  symbolic composition of `f` and `g` needs a substitution the value domain
  does not have? A `VecLit`-style term carrying the state's own program is one
  answer; another is that `ofNat`'s floor is simply the literal's, which §1.3
  measured at 2.5 ms of gate per 64-bit vector and which the respelling
  already reaches (3.1–3.4 ms).
- `docs/bitvec-width-bounded-defaults-design.md:37` still describes `ofNat`'s
  truncation as a `mod_succ` loop. It is a record of the 2026-09-07 round and
  was left as written; the live statement is now `lib/std/bitvec.hthr`'s
  header.
