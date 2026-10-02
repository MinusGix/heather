# A native program reads like a program

Status: **scoped 2026-10-02, not started.** Anchor issue:
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
lowering. S4 migrates the examples and is where the measure is read. S5 and
S6 ride along only if small.

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

### S2. `List::split_by`

Issue: `list-split-by`. It goes in `lib/std/list.hthr`, with `non_empty` and
the lemmas `counts_runs` needs (the cons equations, and the count of pieces).
Its definition is the obvious recursion: `n` separators make `n + 1` pieces.

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

### S4. Migrate the examples

Rewrite `wc`, `wc_l`, `tr`, `tr_s` and `tr_d` in the new style. Delete what
the library now owns. Check that the executables still match the host tools
(the existing `native_*` tests).

### S5. Record update (rides along if small)

Issue: `record-update-syntax`. Parser and elaboration desugar to the
constructor over the old value's projections. The frontend already reads
that term. Refuse a dependent record whose later field mentions a replaced
one.

### S6. `split_all` states literal facts (rides along)

Issue: `split-all-closed-tonat-literals`. Literal widths with `k < 2^w`
produce `14 <= toNat(byte)`.

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
equality node is shared by both.

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
