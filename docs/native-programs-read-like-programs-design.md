# A native program reads like a program

Status: **scoped 2026-10-02; V1–V5 run (§4.1); S6, S1, S2 and S3 landed (part 3 after a design round: `Decide` carries its bit, `native-frontend-decided-matches`); S4 landed 2026-10-03.** Anchor issue:
`issues/native-programs-read-like-programs.md`. This round comes after step 2
of `docs/automatic-author-surface-design.md` (the stream filter) and before
step 3 (`issues/native-one-program-logic.md`, which waits on ITrees).

## 1. What this round does

`examples/x86-native/wc.hthr` is 320 lines:

- about 25 are the program: the state record, two byte predicates, the step
  and the bundle;
- about 30 are what the counts mean;
- the rest is proof and plumbing.

The program part spells byte tests as comparison chains, and every arm
rebuilds the whole state record. The proof copies the step (`wc_next`), moves
facts with hand `j` rewrites under `match … as λ` motives that restate whole
arms, and proves stdout through three rewrites under `three_fields_line`.

This round makes the file read like `wc` written in another language. Proofs
stay, but each is only as long as its idea. The round is library and frontend
work and needs no ITrees. Every example program migrates: `wc`, `wc_l`, `tr`,
`tr_s` and `tr_d`.

**Measure.** `wc.hthr` fits on a screen. Every fact in it is either one
per-byte case analysis or the one real invariant: words are runs, a library
lemma once. The other examples shrink the same way. The executables may
change: an equality node changes code, so this is not a byte-identical
refactor.

### 1.1 The target, as a sketch

Spellings marked `?` were decided in §5 (decided propositions, `s with { … }`); the sketch predates that and still shows Bool operators. Everything else follows from §3.

```
record WcState { lines: Nat, words: Nat, bytes: Nat, inside: Bool }

fn newline(b: BitVec(8)) → Bool { b ≟ '\n' }                       // ? §5.1
fn space(b: BitVec(8)) → Bool { b ≟ ' ' || ('\t' ≤? b && b ≤? '\r') }

fn wc_step(s: WcState, b: BitVec(8)) → WcState {
    match space(b) {
        True => s with { lines = s.lines + bit(newline(b)), bytes = s.bytes + 1, inside = False },   // ? §5.2
        False => s with { words = s.words + bit(!s.inside), bytes = s.bytes + 1, inside = True },
    }
}

// What the counts mean.
fn wc_lines(bytes: List<BitVec(8)>) → Nat { bytes.filter(newline).len() }
fn wc_words(bytes: List<BitVec(8)>) → Nat { bytes.split_by(space).filter(non_empty).len() }
fn wc_bytes(bytes: List<BitVec(8)>) → Nat { bytes.len() }
fn wc_out(bytes: List<BitVec(8)>) → List<BitVec(8)> { three_fields_line(wc_lines(bytes), wc_words(bytes), wc_bytes(bytes)) }

// Why: what one byte does to each count.
theorem lines_step(s: WcState, b: BitVec(8)): wc_step(s, b).lines = s.lines + bit(newline(b)) { split_all; all_goals { bv_omega } }
theorem bytes_step(s: WcState, b: BitVec(8)): wc_step(s, b).bytes = Succ(s.bytes) { split_all; all_goals { bv_omega } }
theorem words_step(s: WcState, b: BitVec(8)): wc_step(s, b).words = s.words + runs_start(space(b), s.inside) { split_all; all_goals { bv_omega } }
theorem inside_step(s: WcState, b: BitVec(8)): wc_step(s, b).inside = !space(b) { split_all; all_goals { refl } }

fn wc_program() → Filter<WcState>(counting(wc_step), WcState(0, 0, 0, False),
    [λ s => s.lines, λ s => s.words, λ s => s.bytes], Fields, wc_out) {
    Filter(fields_computes(counts_filtered(lines_step), counts_runs(words_step, inside_step), counts_len(bytes_step)))
}
```

## 2. What the probes found (2026-10-02)

Probe files are in `probes/ergo/`; byte-path costing is logged on
`issues/byte-vocabulary-for-native-programs.md`.

- **Per-byte facts are one line each.** Against wc's current step,
  `split_all; all_goals { bv_omega }` proves the lines, bytes and words facts,
  and `split_all; all_goals { refl }` proves the in-run flag. No `wc_next`
  copy and no `newline_is_space` lemma are needed: `split_all` specialises
  every occurrence of a comparison, so the step and the predicate in the
  statement are split consistently. Plain `omega` fails one case because
  `split_all`'s facts keep `toNat(ofNat(14))` as an atom
  (`issues/split-all-closed-tonat-literals.md`).
- **The CLI reads neither `init` nor `counts` from the bundle.** It restates
  them as zeros and as the state's leading Nat fields
  (`crates/cli/src/native/read_filter.rs`, `context`), so dropping the
  finish's repeated counts changes only how the finish is recognised.
- **Byte vocabulary.**
  - The frontend's only Bool producer is `unsigned_lt_bit`, and a literal
    must be literally `ofNat(w, k)`.
  - Helpers with literal-width parameters are expanded structurally, so
    `&&`, `||` and `!` (`lib/std/bool.hthr`) *should* already work. This is
    untested (V1).
  - There is no equality node in the IR and no SETE in the x86 model. CMP's
    `zf` is `is_zero_bits(sub)`, with no law relating it to equality.
  - `if P` is `match decide<P>()`, which the frontend refuses.
  - A `Numeral`/`CharLiteral` instance arrives as an unreduced projection.

## 3. Slices

Slices S1 and S2 are library-only and independent. S3 is the frontend and
lowering. S4 migrates the examples and is where the measure is read. S6 is
required (§4.1, V1); S5 rides along only if small.

### S1. Counting folds and stdout from count facts

Issues: `fold-count-lemmas`, `filter-computes-from-count-facts`.

- **Per-count lemmas next to `fold_bytes`** (`lib/function_ir_loop.hthr`):
  - `counts_filtered`: if `f(g(s, b)) = f(s) + bit(p(b))`, then
    `f(fold_bytes(g, bytes, s)) = f(s) + bytes.filter(p).len()`.
  - `counts_len`: if `f(g(s, b)) = Succ(f(s))`, then the fold adds
    `bytes.len()`.
  - `counts_runs`: if the count grows by `runs_start(sep(b), inside(s))` and
    the flag becomes `!sep(b)`, then from a state outside a run the fold
    counts `bytes.split_by(sep).filter(non_empty).len()`. This is wc's
    `inside_words` invariant, stated generically and proved once, by tactics
    where they reach.
- **`Finish` names positions, not functions.** `Quiet | Line | Fields`, where
  `Line` prints the first of the program's counts and `Fields` the first
  three. `finish_bytes` and `FinishFits` take `counts`. The CLI's
  `finish_written` matches a bare constructor.
- **`fields_computes` / `line_computes`.** From one fact per printed count
  (`spec_i(bytes) = f_i(fold_bytes(g, bytes, init))`), these build the
  `computes` field, with `spec` being the finish's line of the `spec_i`. This
  deletes `wc_prints` and `count_wc_input` from programs.

**Built 2026-10-02.** Amendments to the text above:
- The lemmas live in `lib/filter_program.hthr`, not `function_ir_loop`,
  because they use `omega`, which `function_ir_loop` must not import.
- `counts_filtered` states the count's growth as `+ Nat::of_bit(p(b))`.
- `counts_runs_from` is the from-outside instance an author calls.
- `Finish` lost its type parameter.
- `line_computes` and `fields_computes` take the counts after the printed
  ones (`rest`).
- The program's `spec` stays a named function; the CLI reads it by name.

Result: `wc.hthr` is 115 lines, down from 320. Its proofs are four per-byte
facts (`split_all`, then `omega` or `refl`) and three two-line count
theorems. `wc_l`'s proof is two theorems. Both executables match the host
tools; wc differs only at 0xA0 (`wc-words-no-break-space`). The mutation
controls moved to the new spellings: a `Quiet` finish for wc_l, and swapped
counts and a swapped spec for wc.

### S2. `List::split_by`

Issue: `list-split-by`. It goes in `lib/std/list.hthr`, with `non_empty` and
the lemmas `counts_runs` needs (the cons equations, and the count of pieces).
Its definition is the obvious recursion: `n` separators make `n + 1` pieces.

**Built with S1 (2026-10-02).** `List::split_by` goes through a non-recursive
`List::split_onto(cut, x, pieces)` (with `List::onto_first`), so a proof can
case on one element's cut without unfolding the recursion. Also added:
`List::non_empty` and `List::len_filter_cons`. The piece-count, append and
concat lemmas are not written yet; they stay on `list-split-by`.

### S3. Byte tests a reader knows

Issue: `byte-vocabulary-for-native-programs`. The shape depends on decision
§5.1. In both options:

- **An `Equal` node in FunctionIR.** It needs the Rust IR and its roughly 8
  certificate match sites, `lib/function_ir.hthr`, exec, and the x86 lowering
  arms in `function_ir_x86_lower.rs` and `structured_cert.rs`. Branches
  lower to `CMP` + `JE`/`JNE`, whose Jcc forms already decode; a
  materialised Bool uses a new SETE step form. The new law is
  `is_zero_bits(w, a.sub(b)) = a.eq_bit(b)`, plus an `eq_bit` zero-extend
  law for narrow operands. Equality as two comparisons is not kept: that is
  a defect, not a design.
- **`BitVec::eq_bit`** in `lib/std/bitvec.hthr`, with `toNat` lemmas so
  `bv_omega` reads it.
- **Literals at `BitVec(8)`.** `Numeral<BitVec(n)>` and
  `CharLiteral<BitVec(8)>` instances. The elaborator reduces a closed
  instance projection on a literal to `ofNat(w, k)` (preferred over a
  frontend recogniser, so the kernel term, `bv_omega` and the frontend all
  see one spelling).
- **Width-generic helpers.** The frontend instantiates an implicit `{n}`
  from literal arguments when expanding a helper (`structured.rs`
  `produce`), so `unsigned_le_bit` and `eq_bit` expand.

**Built, part 1 (2026-10-02): the library and the literals.**
- **`BitVec::eq_bit`** is structural over the width, with `eq_of_eq_bit`,
  `eq_bit_of_eq`, `ne_of_eq_bit` and `eq_bit_dec`, and `Decide<a = b>` at
  `BitVec` decides by it.
- **Orders.** `<` and `<=` at `BitVec` designate the unsigned orders.
- **Literals.**
  - `Numeral<BitVec(n)>` is in `bitvec`. `CharLiteral<BitVec(8)>` is in a new
    `lib/std/bitvec/byte.hthr`, so `bitvec` does not import `char` (test
    harnesses list their modules).
  - A literal's embedding at a resolved instance is read as the carrier's own
    construction (`reduced_embedding`, `crates/elab/src/literals.rs`): the
    projection unfolds to the field's body and stops at the next definition,
    and arguments that compute to a natural literal are computed.
  - A numeral or character argument waits for a later argument to fix its
    carrier (`unsigned_le(9, b)`), falling back to its own type first when
    the call stalls (`first_then(Nil, 3)`).
- **Operator carrier.** A character on the left of an operator is as flexible
  as a numeral.
- **Check.** `perf ab` (whole tree, calc_parser) moved no counter by more than
  0.1% and found no change in seconds.
- **Imports.** Byte literals need `import algebra; import char; import byte;`
  (`literal-classes-need-importing`).

**Built, part 2 (2026-10-02, fd95e486): the `Equal` node.** FunctionIR
`Equal`, x86 SETE, a fused CMP + JNE, and narrow operands compared
zero-extended. CMP's zero flag is equality (`zero_bits_sub`), with no borrow
law. `eq_bit` is a frontend producer. It was built by an agent from a brief;
its deviations are in the commit, and two follow-ups are filed
(`native-narrow-compare-fusion`, `filter-default-spells-program-names`).

**Part 3, the frontend reading decided propositions (2026-10-02, after a
design round).** The paused version reflected `match decide<P>()` through
the instance tree, and could not tie its expansion to the source: the source
branched on a decision whose instance matches on the comparison, and
case-of-case is not definitional. `issues/native-frontend-decided-matches.md`
weighed three ways out; the user chose (e), **a decision carries its bit**:

- `Decide<P>` is `{ dec, bit: Bool, reflects: Reflects(P, bit) }`, in `bool`
  (its bit is one). The BitVec instances' bits are `eq_bit` and
  `unsigned_lt_bit` (`a <= b` is `!b.unsigned_lt_bit(a)`); the connectives'
  are `&&`, `||` and `!`. Every other instance reads its bit off its `_dec`
  (`or_bit`, `or_bit_reflects`).
- An `if` without an evidence binder is `match decide_bit<P>() { True => …,
  False => … }`; `if h: P` is unchanged. At a resolved instance the
  elaborator reads `decide_bit<P>()` as the instance's bit
  (`reduced_decision`), so a step's term is a match on `b.eq_bit(10)` or on
  `x || y`, never on the dictionary.
- The frontend reads Bool `&&`, `||` and `!` matches as short-circuit
  branches, an operand at a time. One comparison's expansion is the source by
  `refl`; a connective's is by `split_all; all_goals { refl }`, since only
  Bools are split. A helper whose body branched on a connective is expanded
  in place, and a Bool it computes is tested as itself (`split_all` takes
  `head_bit(ofBool(x))` and `x` for different atoms).

Tests: `filter_step_generation` (`decided_*`: `tr -d` with `if b = '\n'`
and a negative control, `wc` with `b = ' ' ∨ ('\t' <= b ∧ b <= '\r')` in a
helper, `tr a-z A-Z` with `¬(b < 'a') ∧ b <= 'z'`).

### S4. Migrate the examples

Rewrite `wc`, `wc_l`, `tr`, `tr_s` and `tr_d` in the new style. Delete what
the library now owns. Check that the executables still match the host tools
(the existing `native_*` tests).

**Built 2026-10-03.** Byte tests are decided propositions everywhere: a step
branches with `if b = '\n'` (`wc_l`, `tr_s`, `tr_d`) or `if 'a' <= b ∧ b <=
'z'` (`tr`), and a predicate a specification passes to `filter` or
`split_by` is a decision's bit, `fn space(b) → Bool { decide_bit<b = ' ' ∨
('\t' <= b ∧ b <= '\r')>() }`. Lines: `wc` 115 → 84, `wc_l` 55 → 47, `tr`
39 → 36, `tr_s` 69 → 55, `tr_d` 49 → 35. Every proof left is one per-byte
case analysis (`split_all`, then `omega` or `refl`) or a library lemma's
call. What it took:

- **Library.** `fold_counts_filtered`, `fold_counts_len` and
  `fold_counts_runs` (replacing `counts_runs_from`) state a count folded
  from zero in the shape `line_computes`/`fields_computes` take, so a
  program's count theorems are arguments of its bundle. `quiet_computes`
  (over `emits_from`) gives a program that prints nothing after end of file
  its `computes` from one equation per byte, which deletes `tr_s`'s and
  `tr_d`'s hand inductions under `match … as λ` motives. `bitvec_omega`
  gains `equal_true`/`equal_false`.
- **`split_all`.** `eq_bit` is a comparison, with its Nat fact (`=`, or `≠`
  on the false side); a helper that is a comparison is split at the
  comparison and stops the search there, which also makes the bundle's
  `advances` default work for `decide_bit` predicates
  (`filter-default-spells-program-names`); and a comparison reached through
  a recursive definition at a constructor reads its operand off the
  constructor's encoding, so `Cons(b, rest).filter(kept)` and the other
  side's `kept(b)` are one split (it was a kernel refusal before: two
  splits of one comparison).
- **`omega`** splits a Nat `≠` by trichotomy, as it did an Int one.
- **Frontend.** A Bool helper whose body *is* a connective (a decision's
  bit) compiles as the connective's branches, each giving its outcome, so
  `match space(b)` costs no materialised operands (the eager form hit
  `RegisterPressure`). A Bool parameter or field is tested as itself in the
  source expansion, as a produced Bool already was: `split_all` takes
  `head_bit(0, ofBool(x))` and `x` for different atoms.

S5 (`s with { … }`) did not ride along: `wc_step` still rebuilds its record
in each arm.

### S5. Record update (rides along if small)

Issue: `record-update-syntax`. Parser and elaboration desugar to the
constructor over the old value's projections. The frontend already reads
that term. Refuse a dependent record whose later field mentions a replaced
one.

### S6. `split_all` reduces defined heads and states literal facts

Issues: `split-all-reduce-defined-heads`, `split-all-closed-tonat-literals`,
and `cons-nil-argument-inference`, which the S6 work ran into.

**Built 2026-10-02.** Changes are in `crates/elab/src/goal_combinators.rs`
and `constructor.rs`; the described behaviour is in `docs/goal-combinators.md`.

- **Defined heads.** `simplify_goal` replaces a call by the arm its match
  selects (`matched_at_constructor`), but only when the match ι-reduces to a
  value that the source can spell, with no eliminator at its head. Any
  eliminator counts as the match: `List`'s match is not a `Case`. A
  match's scrutinee is simplified too, so `!b && c` reduces once `b` is
  decided. A relation's head (`Le`) is never reduced, only its arguments;
  the new test caught `0 <= 1` computing to `True`.
- **Hypotheses.** A binder introduced after a split is restated by a typed
  `let` at its simplified type. A λ annotation does not work, because the
  binder keeps the expected domain. A hypothesis already in context is not
  revised (`split-all-revise-hypotheses`).
- **Literal facts.** A comparison against a closed `ofNat(w, k)` gets its
  Nat fact at `k`.
- **`Cons(Nil, xs)`.** `infer_ctor` defers a field it cannot infer, and
  `ctor_from_child` reads a non-indexed family's instance off a child
  argument. The original error stands when nothing determines the
  instance. Omega's certificates spell such atoms, so the leaf needed this.

Result on the probes: wc's step facts close with plain `omega`; wc_l written
with `&&` passes the bundle's default `advances`; the run-count case lemma
is `split_all` plus three facts (it was about 25 lines of motives). Two of
those facts are real lemmas; the third, `words(Cons(Nil, ps)) = words(ps)`, is
`refl` and waits on `split-all-through-recursive-definitions`.

## 4. Verification first (stop and report if one refutes the plan)

- **V1.** `&&`, `||` and `!` in a step reach the frontend. Rewrite wc_l's
  `newline` with `&&` and build it (`build-x86`, capped). If it is refused,
  S3 also adds Bool connectives to the frontend.
- **V2.** A generic `counts_runs` is provable at a reasonable size. Prove it
  first, against S2's `split_by`, before migrating anything.
- **V3.** The `Equal` law. `is_zero_bits(64, a.sub(b)) = a.eq_bit(b)` and its
  narrow form, by `bv_omega` or hand. Earlier notes found CMP-equality needs
  a borrow law; check whether `zf` avoids that.
- **V4.** Closed instance reduction. An elaborated `'\n' : BitVec(8)` arrives
  at the frontend as `ofNat(8, 10)`.
- **V5.** `Finish` by position. The CLI context module still restates the
  bundle's facts, and a wrong finish is refused at the program's source.

### 4.1 Results (2026-10-02)

None refutes the plan. Two amend it: V1 changes S3, and V1 and V2 add a
`split_all` fix. Probe files are in `probes/ergo/` (`v1_wc_l`, `t_v2_runs`,
`t_v3_zf`, `v4_tr`, `t_wc_a`).

- **V1, amended. `&&` reaches the frontend but cannot be lowered.**
  1. The Filter's `advances` default refused the step first: after splitting
     the comparison, `split_all` leaves `Bool::and(Bool::not(True), …)`
     unreduced, and omega cannot spell it
     (`issues/split-all-reduce-defined-heads.md`).
  2. With `advances` given by hand, the frontend accepted the step. The x86
     lowering then declined it:
     `RegisterPressure { live_temporaries: 2 }` at the step's continuation.
     `Bool::and` is expanded as a helper with both operands evaluated
     eagerly, and the filter step has no room for two live comparison
     results.

  **Amendment to S3:** connectives are control flow. The frontend turns
  `&&`, `||` and `!` (and the `Decide` instances for `∧`, `∨` and `¬`) into
  short-circuit branches, never materialised Bools. This is also what
  recognising a decide tree produces, so the decided-proposition route
  needs it anyway.

- **V2, holds.** The generic run-count lemma (`counts_runs` over a probe-local
  `split_by`) is about 50 lines. The per-byte case lemma had to be written
  with explicit motives, because `split_all` leaves
  `words(split_at(False, …))` unreduced (the same gap as in V1).
  `Cons(Nil, pieces)` needed `Nil<A>`
  (`issues/cons-nil-argument-inference.md`). wc's step meets both premises
  (`wc_step(s, b).words = s.words + runs_start(space(b), s.inside)`, and the
  flag) in one `split_all` line each.

  **Amendment:** S6 becomes "`split_all` reduces defined heads", taking in
  `split-all-reduce-defined-heads` beside the literal-facts fix. Without
  it, every connective-built predicate fails the bundle's own default.

- **V3, holds, and no borrow law is needed.** `zf_sub_same` gives
  `is_zero_bits(n, a.sub(a)) = True`, and `zf_sub_eq` gives that
  `is_zero_bits(n, a.sub(b)) = True` implies `a = b`, at any width, in about
  50 lines. They go through the iterated forms (`sub_bits_spec`,
  `iterate_increment_toNat`, `zero_bits_of_pos`) plus one new inverse,
  `increment_decrement`. The narrow form follows from `truncate_zero_extend`
  (zero-extend is injective). `BitVec::eq_dec` already exists, so
  `Decide<a = b>` at BitVec is an instance declaration.

- **V4, refuted as the code stands, as predicted.** With `Numeral<BitVec(8)>`
  and `CharLiteral<BitVec(8)>` instances, tr's `'a'` and `0x7b` elaborate,
  but the frontend refuses them ("source value must use a resolved pure
  operation"). The reduction goes after the dictionary projection in
  `elab_overloaded_num_check` (`crates/elab/src/lib.rs`), and in its
  char-literal twin (`literals.rs`): when the dictionary is a closed global
  instance whose field is a λ, emit the β-reduced field body.

  **Risk:** this changes every `Int` literal's elaborated term across the
  library, because `Numeral<Int>` takes the same path. That means module
  images rebuild, and possibly costs move. Measure it with
  `scripts/perf ab --source-patch` before landing; this is a counter
  change, not a design change.

- **V5, holds by reading.** `Finish` is consumed in three places:
  `filter_program` (`finish_bytes`, `FinishFits`, `filter_output`),
  `elf64_filter_finish` (`filter_prints`, whose `FilterShape` already
  carries `counts`), and the CLI context (`read_filter.rs`, where the
  restated finish and two `finish_bytes(…)` spellings gain the counts
  argument). `finish_written` already accepts a bare `Var` head.

## 5. Decisions for the user

### 5.1 Byte tests: Bool operations or decided propositions?

Two coherent options:

- **Bool operations.** `b.eq_bit('\n')`, `b.lt_bit(32)` (or short names:
  `b.is('\n')`, `'\t' ≤? b`), combined with `&&` and `||`. A predicate is a
  Bool function, which `filter` and `split_by` take directly. The frontend
  learns one new producer (`eq_bit`). Smallest; the spellings carry a
  suffix.
- **Decided propositions.** Write `if b = '\n' { … } else { … }`, which is
  already `match decide<b = '\n'>()`, with `∧`, `∨` and `¬` through the
  existing `Decide` instances. The frontend recognises `decide` of the
  BitVec comparison and equality instances, and of the connective
  instances, as Bool producers. Specs need a Bool from a decidable
  proposition for `filter` (a library `⌊P⌋`, i.e. `decide_pick(True,
  False)`). This reads most like the language (`=`, not `==`), but costs
  more: Decide for BitVec `=`, a frontend matcher for instance trees, and
  making the derived instances unfold for the kernel and `split_all`.

**Decided 2026-10-02 (user): decided propositions.** `if` already means decide in Heather, and
the reflection-through-decide-instances design exists for exactly this. If
its cost in V1 and V4 runs large, Bool operations are the fallback, and the
equality node is shared by both. The library `⌊P⌋` is `decide_bit<P>()` since part 3 (S3).

### 5.2 Record update spelling

`s with { f = e }`, `s.with(f := e)` (named arguments), or
`WcState(..s, f := e)`. **Decided 2026-10-02 (user): `s with { f = e }`.** It reads like the
other languages, and the parser's record-literal guard at `if` shows `{`
after an expression is already disambiguated.

## 6. Not in this round

- The effectful author surface (`while let Some(b) = read()`). It waits on
  ITrees (`native-one-program-logic`).
- argv, files and flags (`native-wc-as-a-command`).
- Formatting beyond `%7d` (`native-proven-formatting-api`).
- The 0xA0 word break (`wc-words-no-break-space`). It is a one-line spec
  choice; take it at S4 if the user wants it.
- Stdout stays the claim. Per-count facts are how a counting program proves
  it, not what it claims.
