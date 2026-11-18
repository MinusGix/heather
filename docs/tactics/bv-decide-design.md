# `bv_decide`: fixed-width claims by SAT, checked by the kernel

`by bv_decide()` proves an equation between words (`a = b` at `BitVec(n)`),
between Booleans (`p = q`), or a Boolean claim (`p = True`) whose atoms are
local words and Booleans. It is Lean's `bv_decide` design carried into
Heather: the bit-blaster and the LRAT checker are proved once; the reader,
the solver and the proof's layout are untrusted generators whose output the
kernel checks.

```
theorem add_comm8(x, y: u8): x + y = y + x { by bv_decide() }
theorem cont_word(c: u8): (word(c) & 0xC0).eq_bit(0x80) = (utf8::bit7(c) && !utf8::bit6(c)) { by bv_decide() }
```

A false claim fails with values that falsify it:
`bv_decide: the claim is false at x = 0, y = 128`.

## The pieces

| Piece | Where | Trusted? |
|---|---|---|
| `BVExpr`, `BVPred`, their `eval` | `lib/std/tactic/bitblast.hthr` | statement only |
| Bit-blaster to an and-inverter graph, Tseitin clauses, `BVPred::unsat_sound` | `lib/std/tactic/bitblast.hthr` | proved |
| The normalizer, `BVPred::norm_eval`, `BVPred::norm_unsat_sound` | `lib/std/tactic/bv_normalize.hthr` | proved |
| LRAT checker and the staged refutation lemmas (`Reaches`, `reaches_*`) | `lib/std/tactic/lrat.hthr` | proved |
| The `Sat(cs, vars)` request: CaDiCaL, the proof's layout as one term | `crates/elab/src/host/sat.rs`, `crates/sat` | no: the kernel checks the term |
| The reader, the layout of the atoms, the read-back | `lib/std/tactic/bv_decide.hthr` | no: an ordinary tactic |

## The proof the tactic builds

1. **Read.** The goal's sides are read into a `BVPred` over atoms, numbered in
   order of first appearance: each local word (with its width, read off its
   type) and each local Boolean. A definition the reader does not recognize
   is unfolded once and read again (`bv_unfolded`), so `utf8::bit7(c)` reads
   as `PBit(8, c, 7)` through `drop_low` and `head_bit`. Atoms are laid into
   one bit stream, words first at the sum of the widths before them, then
   Booleans, one bit each; `K` is the stream's length.
2. **Normalize.** `p.norm()` (below) is what is blasted: chains of one
   associative and commutative operation flattened, sorted and merged, so
   that `x + y = y + x` and `x - y + y = x` arrive as constants.
3. **Decide.** The tactic asks `sat(BVPred::clauses(p.norm(), K), K + 1)`. The host
   evaluates the clause term (closed: the predicate is a literal), runs
   CaDiCaL, and answers with a model or a refutation term
   `reaches_refutes(cs, …) : (v) → all_true(cs, v) = False`.
4. **Bridge.** `BVPred::norm_unsat_sound(p, K, refutation, L)` gives
   `p.eval(λ k => Succ(k).leb(K) && L(k)) = True` at the layout
   `L = lay_word(x, 0, lay_word(y, 8, …, lay_bool(b, 16, no_bits)))`.
   Each side of the claim is abstracted over the word atoms
   (`abstract_over`), and each atom is put back in place of its window by
   congruence (`layout_cong`, `layout_congr`), its window read back by a
   chain of `window_lay_past` steps ending in `window_lay_here`. A Boolean
   atom needs no read-back: its bit is `lay_bool`'s at a numeral, which
   evaluates. `layout_eq`, `layout_iff` or `layout_true` closes the goal.

The predicate's `eval` must meet the claim's own spelling under
conversion, so each constructor's `eval` is the library operation the
reader read it from (`BAdd` is `BitVec::add`, `PXor` is `Bool::xor`). An
operation read as a combination of others (`xor` as `¬(p ↔ q)`) does not
meet, and fails at the kernel; give it a constructor of its own.

## Normalizing first

`lib/std/tactic/bv_normalize.hthr` rewrites the predicate before it is
blasted, and proves once that the result means the same at every input
(`BVPred::norm_eval`), so nothing it does is trusted. A chain of `+`, `*`,
`&`, `|` or `bxor` (`AC`) is flattened (`AC::flat`, with `a - b` as
`a + -b`), its operands sorted by a structural order (`BVExpr::key`:
constants first, a negation just after what it negates), and neighbours
merged (`AC::merge`): constants folded for `+` and `*`, `x & x` and `x | x`
to `x`, `x bxor x` and `t + -t` cancelled, units dropped. The sort compares
anything it likes: a sort is a permutation, and the chain's value
(`AC::fold`) is invariant under permutations of an associative and
commutative operation. An equation whose sides normalize to one expression
(`BVExpr::same`) becomes `PConst(True)`, which blasts to a single clause
refuted in one step.

This is where sharing equal subcircuits pays off most: two spellings of one
word meet before any gate is built. Hash-consing every and gate instead
(issues/bv-decide-shared-subcircuits.md) was built and set aside: each
lookup and insertion in a `NatMap` table costs the kernel several hundred
steps while it builds the circuit inside a conversion, ten times the gate
itself, which put 64-bit circuits past one conversion's budget. A level of
a lookup reads the key's low bit as `Nat::low_bit`, a recursion two at a
time like `half` that the kernel runs on a numeral in a few steps (it was
`n - 2·⌊n/2⌋`, a halving, a product and a difference); that took between a
tenth and a third off each proof check in the probes.

A rule is a case of `AC::merge` (with its equation in `AC::merge_ok`) or of
`BVExpr::norm` (with its case in `BVExpr::norm_eval`).

## The refutation as one term

Every obligation in the refutation is `X = True` or `X = literal` by
`refl`, so each is one conversion, inside the kernel's per-conversion fuel.
The host cuts the solver's proof into stages (`refutation` in
`crates/elab/src/host/sat.rs`):

- **Pieces** (`reaches_piece`): the clause list as the tactic wrote it
  (`BVPred::clauses(p, K)`) is met against the host's spelling of it a
  piece of `PIECE` clauses at a time: `cs.take(n) = chunks` by `refl`, the
  rest left as `cs.drop(n)` for the next piece. Meeting a 64-bit adder's
  4193 clauses in one conversion passed the budget; each piece computes the
  list again, which is cheap next to comparing it.
- **Build** (`reaches_build`): the input clauses the proof uses, a run of
  consecutive ones at a time (at most `BUILD_PER`), inserted into the
  formula; every `BUILD_EVERY` runs, and after the last, the formula as a
  literal trie.
- **Drop** (`reaches_drop`): runs of input clauses no step names are never
  inserted. Dropping hypotheses is sound for a refutation.
- **Add** (`reaches_add`): the solver's steps, a chunk at a time, cut by the
  hinted literals they read (`STEP_PER`, 500: on a 64-bit adder's proof
  chunks of 800 passed the budget, since lookups deepen as the formula and
  the variables grow); every `EVERY` chunks the formula
  becomes a literal again (`reaches_add_at`), so a stage replays at most
  `EVERY` chunks of insertions.
- **Done** (`reaches_done`): the last chunk derives the empty clause.

Each stage's statement is read off the lemma instantiated at its
arguments, so a stage's type and the type its parent expects are the same
term; built any other way they are compared by evaluation, which is slow.

### Cost shape

- A step chunk's check is linear in the hinted literals it reads: each is
  a lookup of its variable in the assignment and each hint a lookup of a
  clause by id, both logarithmic. This dominates.
- Replaying an earlier chunk's insertions (`add_all`, no checking) is a
  small fraction of checking it, which is why literals are needed only
  every few chunks.
- A literal checkpoint costs about what inserting its new clauses costs;
  comparing the computed trie with the literal is cheap, since consecutive
  literals share every untouched subtree.
- Pruning a checkpoint to the clauses later steps still name
  (`reaches_keep`, `reaches_trim`) costs a lookup and an insertion per kept
  clause, which at thousands of live clauses is several times the budget;
  it is kept for experiments (`SAT_KEEP=1`) and off by default.
- The solver's proofs are long even for small claims: reassociating three
  4-bit additions takes about 5000 hints (CaDiCaL's options barely move it,
  `HEATHER_SAT_OPTIONS=name=value,…` to try more), and each hinted literal
  costs the kernel several hundred steps. So a claim's check time is the
  proof's length times that constant: a few seconds for chained byte
  arithmetic, tens of seconds for 64-bit `x + y = y + x`. The checker's
  constant (`lib/std/tactic/lrat.hthr`'s lookups through two tries) is the
  lever for every claim at once.
- Multiplication is hard for any SAT solver: blasted, 8-bit `x * y = y * x`
  is over a million hints. The normalizer decides it at any width before
  any solver runs; a claim it cannot close (`x * (y + z) = x * y + x * z`)
  is out of reach past a few bits. Multiplication by a constant is cheap.
- Claims the normalizer closes cost the reader and one tiny refutation:
  64-bit `x + y = y + x` or reassociating three words checks in about a
  tenth of a second.

`HEATHER_SAT_TRACE=1` prints the clause and step counts, each stage, and
the fraction of the budget each obligation needs (found by bisection, so
slow).

## What it reads

Words: `+ - *`, negation, `& | bxor`, `complement`, `<< >>` by a numeral,
numerals, `zero_extend`, `truncate`, `take_low`, `drop_low`,
`sign_extend`, `concat`. Booleans: `&& || !`, `xor`, `bool_eq`, `eq_bit`,
`unsigned_lt_bit`, `signed_lt_bit`, `bit_at` at a numeral, `head_bit`.
Atoms must be locals; anything else is unfolded, and refused when it
cannot be.

A claim is `a = b` between words, `p = q` between Booleans, `p = True`, or
`a < b`, `a <= b`, `a ≠ b` between words (`BVClaim`): `<` reads as
`unsigned_lt_bit`, `a <= b` as `!b.unsigned_lt_bit(a)`, `≠` as the negated
equation. The goal is one; so is every hypothesis the reader can take, and
a local it cannot read (a `Nat`, a claim over other types) is passed over,
which is sound since dropping a hypothesis only weakens what is refuted. The
predicate refuted is `¬h₁ ∨ … ∨ ¬hₖ ∨ goal` over one set of atoms, so a
counterexample names values that meet every hypothesis. The read-back is
the goal's, below `k` uses of `layout_imp`, each fed its hypothesis's proof
carried to the layout by `layout_*_hyp`, the converse of the goal's
bridge.

**Numbers of words** (2026-11-18). `a.toNat() < b.toNat()`, `<=`, `=` and
`≠`, either side a word's number or a numeral, and `Nat::leb` and
`Nat::same` of them as Booleans, read as a comparison of the two words'
numbers in a circuit wide enough for both (`PNatLe`, `PNatLt`, `PNatEq`,
bridged by `layout_nat_*`). `Succ(n)`, `n + 1` and `ofNat` at either arity are
read.

**Negations** come in both spellings a proof meets: `¬(a < b)` and
`a < b → False` (an arm's refuted test reads the second way). Each
comparison has its negated claim (`CNLt`, `CNLe`, `CNatNLt`, `CNatNLe`),
read as the flipped comparison where that is the same claim (`¬(a < b)` as
`b <= a`), with `layout_nlt`/`layout_nle`/`layout_nat_nlt`/`layout_nat_nle`
and their `_hyp` converses.

**A word chosen by an `if`** (2026-11-18). A program's verdict is often a
word that a test picks (`if c & 0xC0 = 0x80 { … 1 } else { 0 }`); the
reader does not read a `match`. When reading fails, `bv_decide` looks for
such a word: unfolding a word-typed term one definition at a time, as the
reader does (the host's `whnf` would go on into the test, where a word's
own representation is spelled out), to a `match` on a Boolean, inner calls
first. The goal is split on that test (`cases`, which abstracts it inside a
call's unfolding too, `goal_combinators::co_occurrences`, even under a word
operation the search does not unfold), and each case decided again with the
match now at a constructor, whose selected arm the reader reads. Splits
along a path are bounded at eight, and a case that fails says which test it
was a case of. `examples/utf8/utf8_check.hthr`'s `two_decides` relates the
decoder to the program's `utf8_two` this way, with no lemma restating the
program's tests as one Boolean.

**A word chosen by a test, without splitting** (2026-11-18). An
equation `x = k` whose `x` unfolds to a `match` on a Boolean test is read
as the statement `(c ∧ a = k) ∨ (¬c ∧ b = k)` (`SIte`), `a` and `b` the
arms, each read again, so nested `if`s become one predicate and one SAT
call instead of `2^k` cases. The arms are found by abstracting the match
over its test (the host's `Abstract` takes any term now, every occurrence
as written becoming the parameter) and taking that function at `True` and
`False` by β and ι alone (`Unfold` reduces a head that computes without a
definition): the transparent `whnf` gives up spelling an arm that is stuck
on a call that unfolds far, and goes on into a word's representation when
it does not. The bridge states the word as `c.select(a, b)`, which converts
with the program's `if` (both are one `match` on `c`), so no function of
the test enters the proof, and passes each part's predicate as held terms
(`layout_ite_p`): its verdict is then written as the statement's own and
the kernel meets the two without evaluating either. A claim's proof is held
too (`bv_held`), or a table of tests is one returned `Expr` past the host's
read budget. When this reading fails the split above is still tried.

Cost: `lib/_tests/std/tactic/bv_decide_tests.hthr`'s `table_*` (Unicode's
Table 3-7 over four bytes, five levels and two five-way conjunctions)
decide in a few seconds at `u8`. The same table over 64-bit words widened
from bytes is past one conversion: the tactic's clause list is computed by
evaluation once per piece (`reaches_piece`), and a 64-bit comparison's
circuit is eight times a byte's. Narrowing a comparison of zero-extended
words to the width that holds them would retire that.

**Statements joined by connectives** (2026-11-18). A goal or hypothesis
is a tree of `∧ ∨ ↔ ¬` and `False` over claims (`BVStmt`), read to the
Boolean tree of its claims' predicates (`&& || bool_eq !`, `False`), so a
loop's condition written as one Prop (`c & 0xC0 = 0x80 ∧ (b ≠ 0xE0 ∨ 0xA0
<= c)`) and its negation in the refused arm read as they stand. One
structurally recursive bridge (`BVCx::bridge`) carries a proof across each
connective in either direction with `layout_and`/`_or`/`_not`/`_iff_p`/
`_false` and their `_hyp` converses (lib/std/tactic/bitblast.hthr). `∨` and
`¬` as goals, and `∨`, `¬` and `↔` as hypotheses, take their parts' bridges
as functions, so a part nested under another is a λ whose binder the host
places under the enclosing part's (`assume(…, under)`); placed at the root
it is not in scope there. `¬P` reads only as a negation of a statement it
can read; `P → False` with `P` a claim keeps its claim reading.

## Open

- Non-local atoms (a field, a call the reader cannot unfold) could be
  abstracted as fresh words instead of refused. A Boolean call on both
  sides (`is_utf8(r)` beside the claim) is the common case: today the
  proof rewrites it away first.
- The split is per test, so `k` independent tests make `2^k` cases; an
  equation on a chosen word is read as `ite` now, the split remaining for
  the shapes that reading does not take (a chosen word inside a word
  operation).
- Comparisons of zero-extended words at the wide width: their circuits
  cost the width, and the clause list is computed in one conversion per
  piece. A normalizer rule narrowing them would let a byte table over
  64-bit parameters decide.
