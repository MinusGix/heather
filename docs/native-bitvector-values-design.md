# Native closed-bitvector values in the evaluator — design

Design pass for `issues/kernel-native-bitvector-values.md` (K1), 2026-09-13.
Workload: the generated call certificate `heather build-x86
examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1`,
release with `--features value-metrics`, `--kernel-workers 1`, item timings.

The charter is the full line, not the constructor alone: the x86_64 line
computes machine words at closed values everywhere, so the per-operation cost
has to fall from a couple of hundred evaluator steps *per bit* to a handful of
steps per operation. Three halves — a representation, a class of accelerated
folds, and the consumers that read a word back into `Nat`/`Bool` — under
`issues/kernel-acceleration-policy.md`: no definition-shape matching, the
accelerated thing is an eliminator applied to a native value, classified by
**evaluating** its step, with the adequacy argument written before the code.

Two things the probes changed before a line of prose was written, both in §3
and §5; they are flagged there as corrections to the charter's sketch.

An ordinary Nat case can also return an unrelated neutral word. Before
walking a candidate transducer's motive, the classifier evaluates the step
at neutral predecessor and recursive-result variables. A neutral whose head
is not that recursive result declines immediately: further applications
cannot turn its unknown head into a word producer or a recognized consumer.
Function and constructor heads continue through the existing classifier,
as do recursive-result heads and their elimination spines, which finite
consumers need. This avoids repeatedly inspecting and enumerating a closed
word result during nested port dispatch; the ordinary case evaluator leaves
the motive lazy. Measurements and regression coverage belong to
[valuation-lookup-case-step-cost](../issues/valuation-lookup-case-step-cost.md).

## 1. The before column

Furnace instance of 2026-09-13 (`ocid1.instance…gvb5vvpq`, VM.Standard.E5.Flex,
8 OCPUs); every number in this document comes from that instance and an
implementer's after column must come from one too. Untraced wall 41.8 s.
Summed over the 3 476 item rows: **36.141 s total, 26.087 s `kernel_gate`,
16.07 M evaluator steps**; run-wide 22.77 M steps and 254 259 conversion
misses.

Every family above 0.45 s of `kernel_gate`, with evaluator steps per item:

| family | n | total s | kernel s | steps M | steps/item | misses |
| --- | --- | --- | --- | --- | --- | --- |
| `byte` | 36 | 4.740 | 3.888 | 2.59 | 71 906 | 34 515 |
| `byte_page` | 167 | 2.252 | 2.096 | 1.46 | 8 752 | 835 |
| `successor` | 35 | 2.091 | 1.740 | 1.69 | 48 195 | 9 338 |
| `byte_wrap` | 131 | 2.079 | 1.976 | 1.35 | 10 284 | 393 |
| `stack_allowed` | 36 | 1.580 | 1.500 | 1.22 | 33 811 | 1 316 |
| `step` | 19 | 1.993 | 1.121 | 0.40 | 21 110 | 13 811 |
| `store_offset` | 48 | 0.921 | 0.880 | 0.77 | 16 083 | 48 |
| `store_equal` | 54 | 1.365 | 0.820 | 0.18 | 3 328 | 20 986 |
| `call_callee_local_outside` | 16 | 0.834 | 0.775 | 0.53 | 33 016 | 1 136 |
| `byte_present` | 167 | 1.019 | 0.685 | 0.14 | 843 | 9 018 |
| `write_literal` | 48 | 0.661 | 0.598 | 0.46 | 9 493 | 240 |
| `read_literal` | 32 | 0.637 | 0.527 | 0.41 | 12 658 | 816 |
| `read_address` | 32 | 0.511 | 0.488 | 0.45 | 14 173 | 28 |
| `call_callee_ready` | 18 | 0.809 | 0.485 | 0.10 | 5 730 | 12 004 |
| `leaf_fetch` | 16 | 0.703 | 0.453 | 0.14 | 8 915 | 5 074 |

The closed-refl families this issue owns — `byte_page`, `byte_wrap`,
`stack_allowed`, `store_offset`, `write_literal`, `read_address`,
`file_correct`, `dead_frame_byte` — are **8.09 s of the 26.09 s gate (31%)
and 5.91 M of the 16.07 M item steps (37%)**, at 13–44 ms and 9–34 k steps
per item with near-zero misses. Their unit is visible in the steps/item
column: `store_offset` is 16 083 steps per item, and one closed width-64
`bitvec::add` measured on its own (§2) is 16 385 steps. Each such item *is*
one closed machine-word operation.

## 2. What the cost is made of, and what a respelling would buy

Measured on the same instance, one theorem per row, each proved by `refl`
against the literal answer (`probes/`, untracked). Evaluator steps, and the
slope in steps per bit of width:

| probe | 8 | 16 | 32 | 64 | steps/bit | misses @64 |
| --- | --- | --- | --- | --- | --- | --- |
| A1 `bitvec::bxor` on literals | 1 414 | 2 834 | 5 674 | 11 354 | 177 | 966 |
| A2 the same fold over `[Bool; n]`, wrappers inlined | 998 | 1 986 | 3 962 | 7 914 | 124 | 966 |
| A3 `from_bits(n, L).bits = L` (no operation at all) | 523 | 987 | 1 915 | 3 771 | 59 | 582 |
| A4 `bitvec::add` on literals | 2 049 | 4 097 | 8 193 | 16 385 | 256 | 966 |
| C1 `toNat` of a literal | 564 | 1 132 | 2 268 | 4 540 | 71 | 387 |
| C2 `is_zero(bxor(x,x))` | 1 375 | 2 715 | 5 395 | 10 755 | 168 | 775 |

Three readings, and they are the reason the design has the shape it has.

**A3 is the floor.** Comparing two closed bit vectors that are already
computed — no operation, just `refl` between a record projection and the same
literal — costs 59 steps per bit and 9 conversion misses per bit. That is the
Σ-η path in `conv.rs`: a `Vec` is a right-nested Σ, so η projects `fst`/`snd`
once per bit and compares the two injections. *A third of every closed
machine-word item is conversion, not computation.* No library respelling
touches it, and no evaluator acceleration touches it either unless the
comparison itself learns about words. This is why §7 (conversion) is in
round 2 and not deferred to round 3.

**A1 vs A2 is what a respelling would buy.** Spelling the same fold directly
over `[Bool; n]` — no `BitVec` record, no `from_bits`/`cons_bit`/`head_bit`/
`tail_bits` — removes about 53 of the 177 steps per bit: a 1.43× on the
operation and nothing at all on the conversion floor or the miss count (966
either way). The wrappers are worth their cost in the library and the design
does **not** propose removing them; the datum is here to say that the ×n
iteration, not the spelling, is the thing, and that a library round cannot
substitute for this one.

**A4 vs A1 is the state.** Ripple add costs 256 steps/bit against `bxor`'s
177: the carry is threaded through `add_bits_next`'s `match` *before* the
recursive call, which is one extra case split and one extra closure per
column. Subtracting A3's floor, the compute halves are ≈ 197 (add) and ≈ 118
(xor) steps per bit.

## 3. Canonical form, and how a word enters and leaves

### 3.1 What the word stands for

`BitVec(n)` is a library record over `[Bool; n]` (`lib/std/bitvec/bitvec.hthr`), and
`[Bool; n]` is the kernel former `Vec^l(Bool; n)`, whose canonical values are
right-nested Σ-pairs `⟨b, ⟨b', … ⟨⟩⟩⟩` (`crates/kernel/src/term.rs`,
`docs/wf-former-design.md` §1.2). `Bool` is tier-0 lowered
(`docs/inductive-tier0-lowering.md` §3): two nullary constructors, so
`False = inl(tag)` and `True = inr(tag)` where `tag` is a proof-irrelevant
Σ-nest of `Unit`s.

The native value therefore stands for a **closed prefix of a `Vec` whose
element type has exactly two canonical inhabitants, both with a canonical
payload**, over an arbitrary tail — the exact analogue of a `NatRun`, which is
a closed prefix of `Succ`s over an arbitrary tail:

```
Val::BitRun {
    level: Level,          // the Vec's level
    elem:  &'v TyClo<'v>,  // the element type; its two injections are the bits
    width: u32,            // 1 ..= WIDTH_CAP, bits actually held
    bits:  u128,           // bit i is element i, LSB = index 0 = Vec head
    tail:  &'v TmClo<'v>,  // the rest of the vector: Triv, a neutral, or another BitRun
}
```

Nothing in it names `BitVec`, `Bool`, or any library definition: the
constructor is generic over the element type, exactly as `NatRun` is generic
over nothing at all because `Nat` is a kernel type. The `bits` field's bit `i`
is `1` when element `i` is the element type's **second** injection (`inr`);
which surface constructor that is, the kernel neither knows nor needs.

**The two-valued element criterion.** A type is a *bit type* when its whnf is
`Sum(L, R)` and both `L` and `R` are **unit-like** — `Unit`, or a Σ-nest
ending in `Unit`, which is precisely the shape `Tag_D`-prefixed nullary
constructors lower to and is proof-irrelevant in `conv.rs` by Unit η. The
predicate is structural, decided once per element type, memoized on the
`TyClo` in the value arena beside the fold-class memo. A *bit value* at such a
type is `Inl`/`Inr` whose payload forces to the canonical inhabitant (a nest
of `Triv`s); anything else does not pack and stays structural. Requiring the
canonical payload is what makes unpacking reproduce the *same* value rather
than a convertible one — see §8.

### 3.2 How a word enters — correction to the charter

The charter says a literal enters native form "at construction, as `su`
saturates into a run". **`su` does not saturate at construction either**, and
the analogue is not available here. `NatRun` enters at exactly two places
(`crates/kernel/src/eval.rs`): the term `NatLit(u64)`, and the
`Frame::NatRunTail` merging frame, which joins a run produced by a fold onto
the run being built. There is **no `Term::VecLit`** — the elaborator emits
nested `Term::Pair` — and a `Pair`'s `snd` is a thunk, so saturating at
construction would mean eagerly forcing the tail of every pair the evaluator
builds, which changes the evaluation order of the whole kernel to buy a
representation for one shape.

So entry is at three places, none of them eager:

1. **The merging frame.** A classified fold (§4) that produces a word
   produces a `BitRun` directly; a `Pair` whose `snd` *already is* a `BitRun`
   and whose `fst` is a bit value merges into it (one more bit, width + 1),
   bounded by `WIDTH_CAP`, above which the outer pair stays structural with a
   `BitRun` tail. This is `Frame::NatRunTail`'s job, rewritten for bits.
2. **Pack-on-demand at conversion** (§7): the Σ-η arm, at a `Vec` type, packs
   both sides and compares words. The walk is the one η would do anyway; it
   stops at the first component that does not pack.
3. **Pack-on-demand at a classified fold** (§4): the fold's arguments are
   packed before the native loop runs, charged the fuel the walk costs.

Routes 2 and 3 are where the type is in hand — conversion is type-directed and
a fold has its motive — which is exactly what the untyped value domain lacks
at `Pair` construction. A packed word is memoized on the value it was packed
from, so a literal that is compared or folded twice packs once.

### 3.3 How a word leaves

By **unpacking one bit**, never by materializing the chain: `BitRun` of width
`w > 1` steps to `Pair{fst: <bit 0>, snd: BitRun of width w-1}`, and of width
1 to `Pair{fst: <bit 0>, snd: tail}`. The Σ annotations are the ones the `Vec`
type rule itself produces (`Eval::vec_ty`, `arena.ty_vec`): `fst_level =
snd_level = level`, `fst_ty = elem`, `snd_ty = Vec(elem; pred)`. This is
literally `Val::nat_run_pred`'s pattern — a run's virtual predecessor is a
freshly built `NatRun`, not the value it came from — and it is what makes
`Fst`/`Snd`, `Case` on a bit, and the neutral path cost O(1) each.

Every `Val` consumer that matches on `Pair` gets a `BitRun` arm that unpacks
first: `shift.rs`, `conv/dom/values.rs`'s `TmView` (Opaque, as `Pair` is
today, with the η arm doing the work), and the eliminator cases in `eval.rs`.

### 3.4 The width cap

**`WIDTH_CAP = 128`, in a `u128`.** The x86 line needs 64-bit addresses and
carries, 52-bit page tests and 48-bit windows; 64 would cover every operation
in `lib/std/arch/x86_64/x86_64.hthr` today. 128 is chosen because the shape
operations (§6) *widen*: `concat(n, m)` and `zero_extend(n, extra)` produce
`m + n`, and a 64-bit `zero_extend` falling off the fast path would make the
accelerated path silently disappear in the middle of a proof — the failure
mode that is expensive to diagnose. The carry does **not** need a 65th bit:
`add_bits` threads it as a separate `Bool` argument, which the transducer
class carries as state (§4).

`Val` is a large enum already; the extra eight bytes over a `u64` variant are
expected to be absorbed. This is a verification item (§11.1), not an
assumption: if `size_of::<Val>()` grows, the implementer falls back to `u64`
and `WIDTH_CAP = 64` and says so in §10.

## 4. The transducer class

### 4.1 What is being classified

There is no eliminator for `Vec`. Every bitvector operation in the library is
`elim_Nat` **on the width**, whose motive at `Succ k` is a function type over
bitvectors, and whose step conses one bit and recurses:

```
bxor(n) = match n as λ k => BitVec(k) → BitVec(k) → BitVec(k) {
  Zero      => λ x y => from_bits(0, []),
  Succ(k,ih)=> λ x y => cons_bit(k, xor_bit(head_bit(k,x), head_bit(k,y)),
                                ih(tail_bits(k,x), tail_bits(k,y))) }
```

Today `classify_step` (`eval/probe.rs`) applies the step to neutral `k`/`ih`,
gets a `Val::Lam`, tries `probe_sync`, which applies it to `Succ x` — a `Nat`
where a bitvector belongs, so `head_bit` is stuck on a non-pair and the
result is neither `Succ^q(ih x)` nor an affine tree — and returns `Opaque`.
The fold then peels one successor per bit. That is the ×n in §2.

The new class is the third `FoldClass`: a **bit transducer**, a Mealy machine
over the bit alphabet. One application of the step, at width position `k`,
reads one bit from each of `a` bitvector arguments and a state `s` from a
finite type, and produces one output bit and a next state, recursing on the
tails:

```
step k ih  x⃗ s  ⇝  cons( out(b⃗, s) , ih( tail(x⃗) , next(b⃗, s) ) )
```

with `out` and `next` **closed** — that is the whole content of the class, and
the table of `out`/`next` over the finitely many `(b⃗, s)` is what the probe
computes.

Argument modes, which the probe must distinguish, all of them present in the
library:

- **peeled** — a bitvector the step projects head and tail from (`bxor`: two;
  `complement`: one);
- **state** — an argument of a finitely enumerable type that the step passes
  on changed (`add_bits`: the carry `Bool`);
- **carried** — an argument passed to `ih` unchanged (`concat`'s `m` and its
  high half; `take_low`'s `m`).

Output modes: **cons** (a bit onto the recursive result), **pass** (the
recursive result unchanged — `drop_low`), and the two consumer modes of §5.
Direction is fixed by the recursion: index 0 first, LSB to MSB, which is the
direction carries run in anyway.

*Finitely enumerable* is the same structural predicate as the bit criterion,
widened: `Unit` (one value), `Sum` of enumerables, `Σ` of enumerables, with a
total count bounded by `STATE_CAP = 16`. `Bool` is two; anything bigger than
the cap is not enumerated and the fold stays `Opaque`.

### 4.2 The probe procedure

Uniform first, tabulated second — the same two-stage shape `probe.rs` already
uses for uniform vs peeled.

1. Apply `step` to `k := PROBE_K`, `ih := PROBE_IH` as today. A `Val::Lam`
   now falls through to the transducer probe instead of straight to
   `probe_sync`/`Opaque`.
2. Read the argument types **from the motive**, not from the definition:
   `M(Succ PROBE_K)` whnfs to a Π-chain, and each domain whnfs to either a
   `Vec` at a successor length (peeled), a finitely enumerable type (state),
   or something else (carried). This is the only place a type is consulted,
   and it is the eliminator's own annotation — not a definition's spelling.
3. **Uniform pass**: apply with each peeled argument a fresh neutral and each
   state argument a fresh neutral. If the value is already `cons(bit, ih(…))`
   with everything closed, the class holds at every bit and no table is
   needed. (`complement` is nearly this, and fails only because `bool::not`
   case-splits.)
4. **Tabulated pass**: for each of the `2^a × |S|` combinations, apply with
   peeled argument `j` := `Pair(bit, PROBE_T_j)` — the bit being the element
   type's injection, the tail a fresh neutral at a reserved level — and the
   state its enumerated value. Require every combination to return
   `cons(closed bit, ih(PROBE_T_1 … PROBE_T_a, closed state'))`, with the
   tails reaching `ih` through *projection paths of the probe variables*
   (`projection_path`, already in `probe.rs`: `tail_bits(k, x)` is
   `fst(snd(x))` through the record, so the spine is `Fst`/`Snd` only).
   Cap the table at `2^a × |S| ≤ 16`; anything larger is `Opaque`.

The probe runs once per step closure and is memoized in the arena, as the
`Nat` classes are. Its fuel is the ordinary fuel: the reductions it performs
are the ones the fold's own first bit would have performed, times the table
size, so the cap is also a fuel bound.

### 4.3 Adequacy

Two halves, and they are different arguments.

**The tails are the substitution property.** In each probed combination, the
probe variables `PROBE_T_j` are neutral and the value that comes back has no
stuck case split on them: the reduction that produced it is therefore a
reduction that holds at *every* instantiation of the tails. That is exactly
the argument the `Nat` classes rest on
(`issues/nat-run-algebra-primitives.md`), applied to the recursive-argument
shape rather than to a successor count. It is what licenses running the
machine over the remaining bits without re-evaluating the step.

**The bits and the state are plain closed evaluation.** The head bits and the
state range over finitely many *closed* values, and the probe evaluates the
step at each one. `out(b⃗, s)` and `next(b⃗, s)` are not claims about a
definition; they are values the evaluator computed. Exhaustiveness is the
finiteness of the element type (two injections, by the bit criterion) and of
the state type (enumerated, bounded by `STATE_CAP`). No induction, no
generalization: a truth table.

Together: for a run-valued width `Succ^w(t)` and native arguments, the fold's
value is the word the machine produces over `w` steps, and each of those steps
is a reduction the evaluator performed or a reduction licensed by
substitution. Iteration over the word is a `u128` loop; the result is a
`BitRun` whose `tail` is the fold at the width's tail, exactly as
`fold_affine` instantiates the tree at the fold at the tail.

### 4.4 The four cases the class must get right

- **`bxor`** — two peeled, no state, cons output. Table of 4. `xor_bit` case
  splits on the first bit, which is why the uniform pass fails and the
  tabulated pass is needed; at closed bits it reduces to a constructor.
  Native: one `^`.
- **`complement`** — one peeled, no state, cons output. Table of 2. Native:
  one `!` masked to the width.
- **`add_bits`** — two peeled, one `Bool` state, cons output. Table of 8. The
  carry reaches `ih` through `add_bits_next`, whose `match carry` sits
  **before** the recursive call precisely so the carry is forced; at a closed
  carry that match reduces, so the probe sees `ih(t_a, t_b, closed)` and not a
  stuck `match`. Native: `a + b + carry` in one `u128` add, with the outgoing
  carry read off the top — but note the class does **not** know it is
  addition: it iterates the table, and a table-driven `u128` loop over 64 bits
  is still four orders of magnitude under 256 steps/bit. Recognizing that a
  particular table *is* addition and collapsing it to one machine add is an
  optimization the implementer may add later, keyed on the table and not on a
  name.
- **The negative control: `bitvec::set`.** Its step takes a `Fin(k)` index and
  case-splits on it (`FZ`/`FS(j)`), and the index is neither a bit of a peeled
  argument nor a value of a bounded state type at an open width: `Fin(k)` at
  neutral `k` does not whnf to a sum, so it is not enumerable, and the probe
  is stuck on a case split on a neutral it cannot instantiate. Classification
  returns `Opaque` and `set` folds one bit at a time, as today. It is not
  refused; it is simply not accelerated, and §6 says what would be needed to
  accelerate it. The same verdict, for the same reason, covers
  `shift_left(n, x, count)`, whose recursion is on the count and whose step
  applies a whole-vector operation rather than reading a bit.

## 5. Consumers into `Nat` and `Bool` — correction to the charter

The charter asks to "reuse the existing `AffineTree` reading where it already
fits (probe it!)". Probed, **it does not fit**, for two independent reasons,
and this is the second correction.

`toNat`'s step is `λ k ih. λ x => bit_value(head_bit(k,x)) + twice(ih(tail_bits(k,x)))`.

1. The affine reading is never even attempted: the outer fold is on the width
   and its step returns a function, so `probe_step` sees `Val::Lam` and goes
   to `probe_sync`.
2. Applied to a bitvector with a closed head bit, the body is not
   `Succ^q(ih.π)`. `nat::add` recurses on its second argument and `nat::twice`
   on its own, so both are stuck on the neutral `ih(tail)`: the value is a
   **neutral whose spine is two `elim_Nat`s over an application of `ih`**, and
   `read_affine` requires a spine of `Fst`/`Snd` only. `AffineTree`'s leaf is
   `Succ^inc(ih.path)` — coefficient one — and this step is `2·ih + b`.

The measurement agrees that the current path is not catastrophic (C1: 71
steps/bit, against `bxor`'s 177) precisely because `twice` and `add` *are*
affine `Nat` folds and the run arithmetic does their work cheaply; what costs
is the per-bit iteration of the width fold around them.

So consumers get their own output mode in the same probe, not a reuse of the
tree:

- **Finite output** (`is_zero_bits`, `sign_bit`, `xor_bits`, the `_bit`
  comparisons): the step returns a value of a finitely enumerable type built
  from the head bit and `ih`. Probe it with `ih` ranging over the *enumerated
  output values* as well as the bits: the step becomes a table
  `(b⃗, s, ih) ↦ out`, i.e. a Mealy machine folded from the MSB end. Native:
  a `u128` loop, or a constant-time identity for the common tables
  (`bits == 0`, top bit). `is_zero_bits`'s early exit at a differing low bit
  (C2: 4 584 vs 10 755 steps at width 64) disappears — both become O(1), and
  the *equal* case, which is the expensive one and the one the certificate's
  refl families hit, is the one that gains most.
- **`Nat` output** (`toNat`, and `unsigned_le`/`unsigned_lt` through it): the
  step at each closed bit combination must be a **`Nat`-run endomorphism**
  `ih ↦ q·ih + r` with `q`, `r` closed runs. This is `AffineTree::Leaf`
  extended with a scale, which the run arithmetic already supports
  (multiplication of run programs, `value/program.rs`). Reading it off the
  probe value means recognizing `elim_Nat` spines over `ih` whose own class is
  affine — i.e. calling `classify_step` on the *inner* folds — which is a
  self-contained addition. Iterating it over a native word is Horner's rule;
  when every `q` is the same (2, for every positional notation), the whole
  fold is `base·2^w + bits`, one program multiplication and one append, and
  `toNat` of a native word is the word's own value as a `NatRun` literal.

**Out of scope for round 3**, refused with `OutOfFuel` if reached at a size
the structural path cannot take: `toInt` (its `int::sub` branch is a second
algebra over a different type), `ofNat` (the *inverse* direction —
`bits_at_powers` is a `List` fold, not a width fold, and its acceleration is
`issues/bitvec-ofnat-large-literals.md`'s business), `div`/`mod`-shaped state
machines, and anything whose state type exceeds `STATE_CAP`. Nothing in this
design ever aborts: an unclassified fold is the fold that runs today.

## 6. Shape operations

Split by whether they are arithmetic on the word (representation half, round
2, cheap) or a classified fold (round 3):

| operation | route |
| --- | --- |
| `concat(n, m, lo, hi)` | transducer, one peeled + two carried; native: shift and or, when `m + n ≤ WIDTH_CAP` |
| `take_low(n, m, x)` | transducer, one peeled; native: mask |
| `drop_low(n, m, x)` | transducer, **pass** output (no cons); native: shift |
| `slice` | `take_low ∘ drop_low`; nothing of its own |
| `truncate` | `take_low`; nothing of its own |
| `zero_extend(n, extra, x)` | `concat` with `zero(extra)`; `zero`/`repeat_bit`/`all_ones` are themselves transducers with **no** peeled argument, so they classify and produce a native word from a closed width alone |
| `sign_extend` | `concat` with `repeat_bit(extra, get(…))`; classifies once `get` at a closed index does (below) |
| `get(n, x, i)` / `set(n, x, i, b)` | needs a **closed `Fin` index**: `Fin(Succ k) ⇝ Unit + Fin(k)`, so a closed index is `Inr^i(Inl ⟨⟩)` — the same unary reading a run does, packed to a `u32`. With that, both are word bit operations. Without it (open index), `Opaque`, per §4.4. |
| `shift_left_one`/`shift_right_one` | their steps use `snoc` and do not recurse with `ih` in a cons position; they are single-step rewrites at a canonical width, and their cost is the `snoc` fold, which is itself a transducer |
| `shift_left`/`shift_right`/`arithmetic_shift_right` | recursion on the count, not the width: `Opaque`. A count-indexed word shift is a possible later class; it is not this line's. |

The pattern worth naming: **nothing here is a case on a definition**. Every
row is the same probe finding a different argument/output mode, and the ones
that do not classify are the ones whose step genuinely does something the
machine cannot express.

## 7. Conversion

The A3 floor (§2) says this is a third of the prize, so it is round 2's, not
round 3's.

**Native against native.** Same `elem` (by the existing type conversion),
same `width`, equal `bits`, and tails convertible → convertible, in O(1) for
the closed case where the tail is `Triv` on both sides. Differing `bits` at a
closed width → **not convertible**, decided in one comparison, which is the
`is_zero_bits`-on-a-difference case the certificate hits in its negative
lemmas. Unequal widths with open tails: cancel the common low prefix —
compare `min(w1, w2)` bits, then continue with the residual words over the
tails. This is `cancel_nat_prefix`'s shape (`conv/dom/values.rs`) and should
sit beside it.

**Native against structural.** Pack the structural side, bit by bit, up to the
native side's width, stopping at the first component that is not a bit value;
then compare words and hand the residue back to η. Packing performs the same
projections η would have performed, in the same order, and the packed prefix
is memoized on the value, so a literal compared against `n` different words
packs once instead of `n` times. If nothing packs, the arm falls through to
today's Σ-η path unchanged — this is a fast path, never a new verdict.

**Placement.** In `Conv::tm_nf`'s `TyView::Sigma` arm, *before* the
neutral-first guard. That guard's doc comment already records why: η on two
64-bit vectors is quadratic, "and a machine word is the common case". The
word comparison is the same observation carried one step further.

**Under an open width.** `Vec(elem; k)` with `k` neutral does not step to Σ at
all, so no bits exist to compare and nothing changes: two neutral vectors are
compared on their spines as today.

**Memo keys.** The gate's cross-head memo is keyed on `Rc` pointers and
already reports `conv_memo_hits = 0` on this workload (the same closed pairs
are re-spelled per site). A `BitRun` is a *value-level* key — `(elem pointer,
width, bits)` is a small, hashable, spelling-independent identity — so the
natural follow-on is a word-keyed entry in that memo. **Out of scope for
rounds 2 and 3**: it is a separate change with its own soundness surface
(`issues/value-cache-memo-in-arena.md`), and this line must be measurable
without it.

**What the sidecar will attribute.** Miss *counts* will not move: every refl
obligation the certificate raises is still a miss, and each still enters the
value domain. Their *seconds* collapse. The expected signature in
`<stem>.conv-miss.txt` is an unchanged `Id/Id` miss count against a much
smaller bucket time — the same signature the type-code quote fix produced
(14 682 misses unchanged, 8.62 → 0.62 s, `issues/function-ir-x86-proof-scaling`
log 2026-09-13). An implementer who sees the miss *count* change should stop:
that means a verdict changed shape, not a cost.

## 8. Oracle, fuel, and tests

**The differential oracle** (`crates/kernel/tests/eval_differential.rs`) is
the standing evidence, and it already has the precedent arm: `Agree` relates
`Val::NatRun` to `Term::Succ` by taking the run's virtual predecessor. The
`BitRun` arm is the same: relate it to `Term::Pair` by unpacking one bit —
`fst` against the term's `fst`, and the residual word against the term's
`snd`. Because unpacking rebuilds the `Vec` rule's own annotations (§3.3)
rather than the ones the term carried, the arm compares the element type and
the levels **through the existing `lazy_ty`**, which is Agree, not syntactic
equality; the `snd_ty` comparison descends into the `Vec`/Σ spelling. If a
seed shows the two spellings diverging where conversion would accept them,
the entry rule tightens rather than the oracle loosening: pack only at pairs
whose `snd_ty` is a `Vec` closure (§11.3).

Generator work the oracle needs: the well-typed term generator must produce
`Vec`-typed closed literals over a two-valued element type at widths that
straddle `WIDTH_CAP` (0, 1, 2, cap−1, cap, cap+1) and over neutral tails.
Seed-only failure reporting, per CLAUDE.md — a disagreeing word is exactly the
value that would fill a log 300 times.

**Property tests**, seed-only, in the `law!` style of
`crates/kernel/tests/subst_laws.rs`: pack∘unpack is the identity on values
that pack; unpack∘pack is convertible on values that pack; the transducer's
native loop agrees with iterating the probed table one bit at a time; a word
over-wide by one does not pack.

**Fuel.** Native steps charge fuel, one unit per bit consumed or produced (a
bulk `spend_n(width)`), plus the ordinary charge for the probe. The reason is
the invariant `probe.rs` states for its own probing — "a probe never
manufactures a verdict fuel would have refused" — read in the other direction:
charging *at most* what the structural path charges means nothing that
succeeds today fails tomorrow, and charging *something* proportional to the
data keeps `eval_steps` an interpretable measure and keeps a pathological
width from being free. The evaluator-step counts in the after column will
therefore fall by the compute factor and not to zero, which is the right
reading of the number.

*Amended 2026-11-14 (issue `native-word-fuel-per-word`):* a run charges
**one unit per word**, not per bit. A run is at most `BIT_RUN_WIDTH_CAP`
bits, so the charge is still proportional to the data (a wider vector is
one run per word, each charged) and still at most what the structural path
spends; what changed is the constant. Charged per bit, the accounting was
most of the steps of word-level code — a third of the token-kinds table's
check, half of a chain of additions — with no time behind it, so a closed
verdict over `u64` code ran out of fuel at a fraction of the work fuel
allows anything else. A literal's entry already charged one unit for the
same reason (DESIGN.md, "A vector literal is a term").

**Certgen controls unchanged.** The perturbed-library mutation controls and
the native x86 gates are not touched; a round that changes them has changed a
verdict.

## 9. Ordering and rounds

`docs/kernel-arena-terms-design.md` §1 settled the ordering question the issue
raised: `Val`/`VTy` already borrow the query region and reach syntax through
`TmClo`/`TyClo`, so a new `Val` variant is orthogonal to the term rewrite and
the value-arena slice does not block it. This line goes now; whichever term
representation lands later retypes one field.

**Round 2 — representation, conversion, oracle.** The `BitRun` variant, the
bit and enumerability predicates with their memo, pack/unpack, the merging
frame, the `Val` consumers (`shift.rs`, `TmView`, the eliminator arms), the
conversion fast paths of §7, the oracle arm and the property tests.

*Measurable alone*: yes, and §2's A3 row is why. The closed-refl families
spend ~59 steps/bit and ~9 misses/bit on the comparison alone, independent of
the operation, so round 2 alone should move `byte_page`, `byte_wrap`,
`stack_allowed`, `store_offset`, `write_literal`, `read_address` without any
fold being classified. If round 2 shows no movement on those rows, the
premise is wrong and the round stops there.

**Round 3 — the classes.** The transducer probe and its `FoldClass` variant,
the native iteration, the two consumer output modes and the scaled leaf, the
shape operations of §6 that come free with them, and the closed-`Fin` index.

**The bar, both rounds.** Whole-workload **item total ≤ 36.141 s** and
**`kernel_gate` ≤ 26.087 s** on a furnace instance of the same shape, same
recipe (release, `--features value-metrics`, `--kernel-workers 1`,
`reused_callee --callee leaf --arg 21 --arg 1`), with a fresh before column
measured on *that* instance in the same session — a copied before table
misranked two of three mechanisms once already
(`docs/call-memory-read-spelling-design.md@4acf2fe` §1). The chartered families are
**diagnosis, not the bar**: they say whether the mechanism fired.
**If the bar fails, STOP and report** — do not tune the workload, do not
widen the cap, do not add a case for the definition that did not classify.

`scripts/test` full, twice, for each round; `scripts/bench --check` against the
baseline, with the `--save`-before-apply-`--check` dance if it is run on
furnace (the committed baseline is desktop-recorded).

## 10. Draft for `crates/kernel/DESIGN.md`

To be applied by the round-2 implementer, after the *Acceleration policy*
paragraph and before the "Owed to ch. 07" note. Not yet applied.

> **Native bitvector values** (`issues/kernel-native-bitvector-values.md`,
> `docs/native-bitvector-values-design.md`). The second representation change
> of the runs kind. A `Vec^l(T; n)` whose element type `T` has exactly two
> canonical inhabitants with proof-irrelevant payloads — which is what a
> tier-0 two-constructor nullary inductive lowers to — has canonical values
> that are right-nested Σ-pairs of injections, one pair node and one
> injection per bit. `Val::BitRun` holds a closed prefix of such a chain as a
> machine word: an element type, a width, `u128` bits, and a tail, standing
> for the Σ-chain that unpacks from it one bit at a time with the annotations
> the `Vec` type rule itself produces. It is `Val::NatRun` for a different
> former: the same closed-prefix-over-a-tail shape, the same virtual
> predecessor on the way out, and the same generality — nothing in it names a
> library type or definition.
>
> Adequacy is bisimulation, in two parts. *Values mean the same*: a word
> unpacks to the pair the `Vec` rule builds, with the element type's own
> injections and their canonical payloads, so every consumer that matched on
> `Pair` sees what it saw before; a bit whose payload is not canonical does
> not pack. *Reduction is unchanged*: a fold over the width whose step is
> classified (`eval/probe.rs`) as a **bit transducer** — at every combination
> of closed head bits and of a finitely enumerable state, one application
> reduces to `cons(closed bit, ih(tails, closed state))` with the tails
> reached by projection paths of neutral probe variables — is iterated over
> the word instead of being taken one bit at a time. The neutral tails are
> the substitution property, as in the `Nat` classes: a probe value with no
> stuck case split on them was reached by a reduction that holds at every
> instantiation. The bits and the state are not an argument at all but a
> truth table, exhaustive because both types are finite. Consumers into
> `Nat`/`Bool` are the same machine with a different output algebra — a
> finite value, or a run endomorphism `ih ↦ q·ih + r`, which is the affine
> tree with a scale.
>
> Conversion compares two native words by their words, before Σ-η, and packs
> a structural side against a native one by the projections η would have
> performed. Native steps charge one fuel unit per word (originally per bit;
> see §8's amendment), which is strictly less than the structural path
> spent, so no verdict that fuel allowed becomes a refusal. What does not classify — an open `Fin` index, a
> recursion on a shift count, a state type above the cap — folds exactly as
> it does today.

## 11. Verification items

For the implementing agent's **first hour**. Each is a concrete probe or
test. **If one refutes the design, STOP and report before working around it.**

1. **`size_of::<Val>()` before and after** adding the variant (a
   `const _: () = assert!(…)` or a one-line test). If the `u128` variant grows
   the enum, fall back to `u64`/`WIDTH_CAP = 64` and record it — §3.4's choice
   is a preference, not a requirement.
2. **The bit criterion fires on the library's `Bool`.** A kernel test that
   whnfs the element type of `[Bool; 8]` as the elaborator emits it and
   asserts it is `Sum(unit-like, unit-like)`; and that `False`/`True` force to
   `Inl`/`Inr` with a canonical payload. If the payload is *not* canonical
   (say a glued definition that stays a neutral), nothing packs and §3.1's
   entry rule needs the witness-pointer variant instead — report before
   choosing.
3. **Unpack reproduces annotations the oracle accepts.** Pack a closed
   width-8 vector built by the elaborator, unpack it, and run `Agree` against
   the syntax-domain whnf of the same term. This is the one place §3.3's
   "the `Vec` rule's own annotations" claim can be wrong, and it is cheap to
   settle.
4. **The transducer probe on `bxor`, by hand, at width 2.** Assert the table
   is four entries and that the recursive call's arguments are
   `projection_path`-recognizable. Then the same for `add_bits`: eight
   entries, and the carry reaching `ih` *closed* — if `add_bits_next`'s match
   has not reduced, the probe sees a stuck case split and §4.4's claim about
   the pre-forced carry is wrong.
5. **The negative control stays negative.** `bitvec::set` classifies
   `Opaque`, and the suite's `set` proofs are unchanged.
6. **`toNat`'s step is not an affine tree** (§5), confirming the correction:
   a test asserting `classify_step` returns `Opaque` today and that the
   consumer mode is what changes it.
7. **Round 2 moves the A3 floor.** Re-run the §2 A3 probe after the
   conversion fast path: `from_bits(64, L).bits = L` should fall from 3 771
   steps to a small constant. If it does not, the fast path is not on the
   path the certificate takes, and the family rows will not move either.

## 12. What it assumes from elsewhere

- **`issues/kernel-acceleration-policy.md`** (closed) owns the rule this
  design obeys: representation changes with an adequacy argument, classified
  by evaluation, never by a definition's spelling.
- **`issues/succinct-inductive-values.md`** and
  **`issues/nat-run-algebra-primitives.md`** own the runs precedent — the
  `Val` constructor, the probe, the arena memo, and the substitution
  argument this design reuses verbatim for the tails.
- **`docs/wf-former-design.md`** §§1.2–1.3 and
  **`docs/inductive-tier0-lowering.md`** §3 own the two facts the canonical
  form rests on: `Vec` is a right-nested Σ, and a two-constructor nullary
  inductive is a sum of proof-irrelevant tags.
- **`docs/kernel-arena-terms-design.md`** §1 owns the ordering: the value
  domain already borrows the query region, so this does not wait.
- **`issues/value-cache-memo-in-arena.md`** owns the word-keyed conversion
  memo, deliberately left out of both rounds.
- **`issues/bitvec-ofnat-large-literals.md`** owns the inverse direction
  (`Nat` to bits), which this design does not touch.
- **`issues/function-ir-x86-proof-scaling.md`** owns the workload and the
  family table.

## 13. What implementing corrected

Round 2, 2026-09-13. Furnace instance `…gvb5vvpq` (the same one §1 was
measured on). Corrections are listed with the section each amends; the last
one is the round's verdict and is why round 2 did not land.

**§3.4 / §11.1 — the width cap is 64, not 128.** Measured: `size_of::<Val>()`
is **88 bytes with alignment 8** before the variant and after it. A `u128`
field would raise the enum's alignment to 16, and 88 is not a multiple of
16, so the enum would round to **96** — eight bytes on every value in the
machine to widen one variant. §11.1's own fallback rule applies: `u64`,
`BIT_RUN_WIDTH_CAP = 64`, which covers every operation in
`lib/std/arch/x86_64/x86_64.hthr` today. The widening argument §3.4 made for
128 is still real for round 3's `concat`/`zero_extend`; the answer there is
a second run over the first's tail, not a wider field.

**§3.1 — a run carries its element type's two injections, not just the
element type.** Unpacking has to produce the element type's *own* `Inl`/`Inr`
at their canonical payloads, and building those needs the evaluator: it has
to force the sum's halves and construct their `Triv`-nests. The consumers
that unpack — `value/shift.rs`, the conversion `TmView`, the `Fst`/`Snd`
arms — have no evaluator in hand. So the criterion's verdict is a value:
`BitTy { elem, zero, one }`, built once when the criterion is decided and
memoized on the element closure, and `Val::BitRun` holds a pointer to it.
This also keeps the variant small (a `Level`, a pointer, a width, a `u64`,
two closures) rather than carrying four type annotations per bit.

**§3.3 — a run stores its *tail's* length, not its own.** The unpacked
pair's `snd_ty` is `Vec(elem; pred)`, which needs a length term; deriving it
from the run's own length would mean forcing a `Nat` at every unpack.
Storing the tail's length instead makes the residual length
`Succ^{width-1}(tail_len)` — a `NatRun` built in O(1) with nothing forced —
which is what keeps unpacking pure and lets `value/shift.rs` and `TmView`
call it.

**§3.2 — the merging frame has no producer in round 2, so it is the
operation without its `Frame`.** Entry route 1 starts at a classified fold,
which is round 3's; route 3 is round 3's by construction. What landed is
`Val::bit_run_cons`, the merge step itself (one bit onto a run, capped),
which is what `Frame::BitRunTail` will call. Adding the frame with nothing
that pushes it would have been an untested enum variant.

**§7 — the entry condition is "at least one side canonical", and the other
side is walked by η's own projections.** The first implementation required
*both* sides to be `Pair`/`BitRun`, on the reasoning that packing a neutral
means δ-unfolding a spine the neutral-first guard decides on its spine. It
fired almost nowhere: the certificate's shape is a *computed* vector against
a literal, and the computed side is a glued projection. The rule that
actually holds the guard's ground is: two stuck spines are left alone, and
otherwise the non-canonical side is projected with the Σ's own annotations —
which is exactly the `fst`/`snd` the η arm was about to take, in the same
order, so it is not new δ.

**§3.1 — the criterion must be decided δ-transparently.** An element type
reached through the elaborator is an `El` of a glued code, so `force_ty`
alone leaves a neutral and the criterion never fires on the library's
`Bool`. `delta_whnf_ty` is right here and is not a δ-discipline change: the
verdict is a question about a *type*, decided once per element closure and
memoized, not a term comparison.

**§10 — the `DESIGN.md` paragraph was applied amended, not verbatim.** Two
changes: `u128` became `u64` (above), and the whole *Reduction is unchanged*
half was rewritten. §10's draft describes the transducer class — the probe,
the truth table, the consumer algebras — which is round 3's and is not in
the kernel. What the applied paragraph says instead is what is true of this
tree: nothing in the evaluator produces a word, entry is pack-on-demand at
conversion, and what does not meet the criterion is compared exactly as it
was. When round 3 lands, the missing half goes back in.

**§7 — no packed-word memo.** §7's "the packed prefix is memoized on the
value" is not implemented and was not needed: the walk's forces are already
memoized in the arena's term cache, so a second packing of the same chain is
a loop with no evaluation in it. It would be worth adding only if a profile
showed the loop itself.

**§2 and §11.7 — the A3 floor was misread, and this is the round's
verdict.** §2 reads A3's 3 771 evaluator steps at width 64 as "59 steps per
bit of Σ-η conversion", and §9 builds round 2's whole case on it: that a
third of every closed machine-word item is the comparison, so the
conversion fast path alone should move the closed-refl families. Measured
with the fast path in place, A3's steps fall from **3 771 to 3 481** — the
vector comparison is under **8%** of that item, not its floor. The rest of
A3's per-bit cost is *elaborating and checking a 64-element `Bool` literal*
(its 582 conversion misses at width 64 are ~9 per bit, one per list
element), which no kernel conversion rule touches.

The whole-workload measurement says the same thing. Cold cache, same recipe,
5 001 item rows, same instance and session:

| | items | total s | `kernel_gate` s | steps | misses |
| --- | --- | --- | --- | --- | --- |
| before | 5 001 | 99.202 | 70.834 | 52 390 787 | 361 706 |
| after | 5 001 | 99.821 | 71.395 | 51 909 608 | 361 706 |

Miss counts are **identical**, which is the signature §7 predicted and the
evidence that no verdict changed shape. Evaluator steps fall by **0.9%**,
and the fast path costs about what it saves. Per family (steps, before →
after): `store_offset` 772 000 → 653 392 (−15%), `read_address` 453 532 →
384 344 (−15%), `call_callee_local_outside` 528 256 → 449 184 (−15%),
`stack_allowed` 1 217 212 → 1 117 724 (−8%) — and `byte_page` 1 461 584,
`byte_wrap` 1 347 239, `write_literal` 455 664 **unchanged to the step**.

So the mechanism fires, is correct, and is worth 8–15% on the three families
whose items really do compare two vectors — but half the chartered rows
contain no vector-against-vector comparison at all. Their cost is the fold,
not the conversion. §9's bar is a whole-workload bound and it is not met;
round 2 stops here, as §9 says it must.

What this implies for round 3, stated so the next round does not inherit the
same misattribution: the prize is where §2's A1/A4 rows put it — 177 steps
per bit for `bxor` and 256 for `bitvec::add`, of which the conversion floor
is a small part — and the transducer class is not an accelerant on top of a
conversion win but the whole of it. The conversion fast path in this tree is
a correct prerequisite for round 3 (a fold that produces a word needs a
comparison that reads one), not a measurable change on its own.

---

Round 3, 2026-09-13, same instance. The transducer class, the producer, the
consumer modes and the shape operations. Corrections are listed with the
section each amends.

**§4.2 step 2 — a peeled argument's type is a `Vec` *in a unit-like Σ-context*,
not a `Vec`.** §4.2 says each domain of `M(Succ k)` "whnfs to a `Vec` at a
successor length". None of them does: the library's vectors arrive inside a
**record**, and a record is a one-constructor tier-0 inductive — a Σ-nest
whose other components are `Tag_D` spines
(`docs/inductive-tier0-lowering.md` §3). So `BitVec(Succ k)` whnfs to
`Σ(Tag). Σ(Vec(Bool; Succ k)). Unit`, and the class carries the **projection
path** to the vector (`eval/transduce.rs`'s `Slot`) for each peeled argument
and for its result. This is still the eliminator's own annotation and not a
definition's shape: the path is found by walking the *type*, and every
component it does not pass through must be the canonical inhabitant of a
unit-like type — the same criterion `bits.rs` decides for a bit's payload,
and proof-irrelevant for the same reason, which is what makes rebuilding the
wrapper reproduce the value rather than a merely convertible one. §4.2's own
`projection_path` idea survives intact for the *recursive* arguments: the
value the step hands `ih` is projected through the same wrapper and must be
the probe's own tail variable.

**§4.2 step 2 — "a `Vec` at a successor length" has to be read
δ-transparently.** `take_low`/`drop_low`/`concat` are indexed `BitVec(m + k)`,
and `m + k` is `nat::add` — a *definition* — applied to the width. At
`Succ k` it is a successor only after that definition unfolds. Reading the
length with `force` alone classifies all three as **carried**, which is to say
not at all; the shape operations of §6 were dark until this was fixed. As in
§13's earlier note about the element type, this is not a δ-discipline change:
the question is about the eliminator's annotation, asked once per class.

**§4.2 — the class is memoized on `(step, motive)`, and on their *syntax*.**
The argument modes come from the motive, so the step alone is not the
question; and the evaluator allocates a fresh closure cell at every
`Term::ElimNat` it evaluates, so an address key re-probes the same fold once
per occurrence. The key is the closures' body pointer and environment
identity, both of which the arena keeps alive for as long as the memo.

**§4.1/§5 — `pass` is decided before the result type is consulted.** The
design presents `pass` as one of the *word* output modes, alongside `cons`.
It is not: a step that hands the recursive result back untouched is one
whatever that result is, and the whole carry family —
`carry_bits`/`borrow_bits`, which fold a carry over two vectors and return a
`Bool` they never inspect — is exactly that shape. Asking "is the codomain a
vector?" first refuses all of them; `byte_wrap` (131 items of the
certificate) is `carry_add_bit`, and it did not move until the order was
swapped.

**§5 — the finite and scaled outputs admit no state argument.** A finite
output is tabulated by probing the step with a *constant* `ih` at each
enumerated value of its own type, and that pass cannot also observe where the
arguments went. A state whose transition is invisible cannot be tabulated, so
a step with one is declined rather than guessed at. Nothing in §5's list
needs one (the ones that look like they do — the carries — are `pass`,
above).

**§5 — the scaled output needs a closed base, or a coefficient of one.**
`toNat`'s fold is `ih ↦ q·ih + r` and the whole word's map is the
composition; applying it to the fold at the tail is `Q·base + R`, and a
`NatRun` can only spell that when `Q = 1` or `base` is a closed count.
Anything else is the multiplication of an *open* term, which the run
representation has no form for, and the fold declines. At a literal width the
base is `Zero` and the answer is one run literal, which is what §5 predicted.

**§5 — the finite output must keep the structural path's early exit.** §5
says `is_zero_bits`'s early exit at a differing low bit "disappears — both
become O(1)". The first implementation made it *worse*: it packed the whole
word and forced the fold at the tail before consulting the table, where the
structural path had stopped at the first set bit. The fix is in the machine,
not the class: a combination whose table row is constant in `ih` settles the
fold, so the bits are read one at a time and the walk stops at the first such
row (`Transducer::run_finite_short`). The fold at the tail is then never
built.

**§3.2 route 1 — `Frame::BitRunTail` is not needed and was not added.** The
producer builds its run with an **unforced** tail — the fold at the residual
width, as a projection closure — which is what makes a chain of shape
operations cost its last step and not its whole history. Nothing therefore
forces a tail into a position where a merge could happen, and a merging frame
would force exactly what the laziness exists to avoid. Round 2's
`Val::bit_run_cons` stays what it was: the operation, exercised by the
property tests. A width above the cap is the second run over the first's
tail that §13 predicted, and the packing walk consumes such a chain without
noticing it.

**§8 — the oracle arm is in, and is not reachable from the generator.** The
`BitRun`↔`Term::Pair` arm of `Agree` is added and is the `NatRun`↔`Succ` arm's
shape exactly: unpack one bit, and let the pair arm compare the annotations
through `lazy_ty`. It cannot fire from a random seed: `Agree` relates a value
`eval` produced to the rewriter's whnf, and `eval` produces a `BitRun` only
from a **classified fold**, which the well-typed generator does not build —
generating `Vec` literals over a two-valued element type, which §8 asks for,
exercises the *conversion* path, where no `Val` ever reaches the oracle. The
standing evidence for the producer is therefore the in-crate fold tests
(`eval/transduce.rs`'s `tests`, which run the eliminator on a run and read
the word back) and the certificate; the arm is insurance for the day a
generator does build one.

**§9 — the bar, measured, and not met.** Same instance, both columns cold
and back to back in **one** job, the before column the committed tree
(reversed patch), the after column this one:

| | items | total s | `kernel_gate` s | steps | misses |
| --- | --- | --- | --- | --- | --- |
| before | 5 001 | 100.067 | 71.540 | 51 909 608 | 361 706 |
| after | 5 001 | 100.347 | 71.789 | 48 797 992 | 361 706 |

The mechanism fires — 4 532 classified folds over the workload, every output
mode among them — and evaluator steps fall **6.0 %** with the conversion miss
count **identical**, which is the signature §7 predicted and the evidence
that no verdict changed shape. Per family (steps, before → after):
`byte_page` 1 461 584 → 726 116 (−50 %), `byte_wrap` 1 347 239 → 742 508
(−45 %), `stack_allowed` 1 117 724 → 663 444 (−41 %), `store_offset`
653 392 → 424 776 (−35 %), `write_literal` 455 664 → 228 192 (−50 %),
`read_address` 384 344 → 250 920 (−35 %). The unit probes at width 64
(evaluator steps): `bitvec::add` 13 914 → 9 444, `is_zero(bxor(x,x))`
10 755 → 4 941, `toNat` 4 540 → 2 322, `is_zero` of a literal 3 016 → 365,
`bxor` 10 099 → 8 742 — and A3, the literal floor, **3 481 → 3 481**, which
is the right reading of the rest: A1's residue is its three 64-element
`Bool` literals, not its fold.

**But the seconds are flat, and §9's bar is the seconds.** Item total is
+0.28 % and `kernel_gate` +0.35 %; the round does not meet the bar, and per
§9 it stops there rather than being tuned into it. The gap is smaller than
this instance's own run-to-run spread (three before columns on the same tree
came in at 100.067, 100.275 and, in round 2, 99.202), and a same-binary A/B
on a desktop — the mechanism switched off and on in two back-to-back runs of
one process image, which removes the rebuild from the comparison — reported
92.166 → 90.924 s total and 67.901 → 66.232 s gate, i.e. the other sign. The
honest statement is **flat**, not a win and not a regression, with the step
count down 6 % and the miss count unmoved.

**One family is worse, and it is the whole of the gap.** `read_literal` (32
items) goes 410 379 → 435 235 steps and **0.682 → 1.398 s** — +0.72 s, more
than the +0.28 s the whole workload moved; without it the after column is
0.44 s *under* the before one. The cause is not overhead but **eagerness**: a
classified `bxor` computes all 64 bits at once, where the structural
cons-chain computed only the bits its consumer forced — and this family's
consumer is a memory walk whose address comparison short-circuits at the
first differing bit, so it forced one. Packing two structural literal
arguments is what the family now pays. It cannot be fixed by making the
producer lazier: a `BitRun` is its whole width by construction. What it
points at is a design question this round did not have — *at what width
should a classified fold fire when its consumer is demand-driven?* — whose
cheap answers (fire only when every argument is already a word; fire in
fixed chunks) are both tuning, and §9 forbids that here. It is recorded for
the round that takes it up.

Everything else the round found is above; the tree is otherwise complete, the
suite is green twice, and the class is the one §4 specified.

Coordinator review of round 3, 2026-09-13, two corrections found reading the
diff and re-running the gates:

**§5 — the finite output's table is read by *replaying*, not by
substituting.** The first implementation tabulated a finite output by
applying the step again with a constant function in place of `ih`, once per
enumerated value of the result type. A constant function answers *every*
call, so a step that reads `ih(tails)` and then, in a branch on it, calls
`ih` at other arguments — `case(ih(tx, ty)) { False => ih(ty, tx), … }` —
would have tabulated as if the second call returned the first's value: a
fold that is not a function of `(bits, ih(tails))` at all, evaluated
wrongly. No library step has that shape, which is why nothing measured it,
and it is a soundness defect all the same. The probe now takes the
eliminations that follow the recursive call in the neutral-`ih` value and
replays them on the closed enumerated value with `ih` still neutral; a
hidden second call is then a stuck neutral, does not read back as an
enumerated value, and the step declines (`eval/transduce.rs`, with the
regression test `a_second_recursive_call_hidden_in_a_branch_declines`).

**§4.2 / §3.1 — two constant-factor changes made on a wrong diagnosis, kept
because they are right anyway.** The desktop `scripts/bench --check` flagged
`nat/step-once`, `nat/step-into-closed-body` and `nat/mul-normalize` at
1.26–1.29×. Two causes were fixed in turn — the `(step, motive)` memo was
hashed with SipHash on every opaque `Nat` fold's step (now the arena's
pointer hasher, and a fold whose motive is *written* `Nat` skips the lookup:
an annotation, not a spelling), and round 2's `ValueArena::bit_tys` was a
`typed_arena::Arena::new()` that allocates its first chunk in the
constructor of every per-query arena (now made lazily) — and the flag
survived both. The control that should have come first: the same bench on
the pre-K1 commit (8fc9ee8) reports the identical 1.26×. The constant is
the desktop's drift against the 2026-08-17 baseline
(`issues/kernel-bench-full-run-flags-drift.md`'s signature), and this line
did not cause it. Both changes stay: neither costs anything and each
removes a real per-step or per-arena cost, but the design records that the
bench verdict was not evidence about this tree, and that a constant-factor
flag gets a same-machine control on the parent commit before it gets a
diagnosis.
