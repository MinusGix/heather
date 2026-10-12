# A native program, written as itself

Status: **landed 2026-10-01** (one round, three parts). Anchor issue:
`issues/automatic-author-surface.md`.

## 1. What was wrong

After the native-stack review (`docs/native-architecture-review.md`, R0–R7),
`examples/x86-native/wc.hthr` was 433 lines. About 70 were the program, about
100 the real argument (why the in-word flag counts words), and the remaining
~200 lines were bookkeeping that existed for two reasons:

- **The step had the loop generator's type.** `wc_body(needle, cursor, byte,
  s) → LoopStep<WcState>`. A fold never reads the needle or the cursor and
  always continues, so the program had to prove that it always continues
  (`wc_body_folds`) and to recover its next state from the `LoopStep`
  (`wc_step_is`), and every fold lemma carried a `j(sym(wc_step_is …))`
  transport. `wc_l.hthr` had the same three, and compared each byte with the
  needle register by a hand-written `byte_equal`.
- **Every obligation was proved by hand,** including "each count grows by at
  most one per byte", which is a case split followed by `omega` in every case.
  Each case split was spelled as a written motive restating the goal.

The aim, from the user: a program should read as the program, the language
should discharge the routine obligations, and when it can't, the author
should get the one goal left over, prove it, and carry on.

## 2. What changed

### 2.1 `split_all` splits what blocks the goal (`docs/goal-combinators.md`)

- **Records are not split.** A record is one case. Splitting `byte: BitVec(8)`
  into its bit vector broke the comparison search that followed.
- **Binders are introduced,** including a goal that a definition unfolds to a
  Π, such as `LoopFolds(region)`. A binder of a finite type is split as it is
  introduced.
- **Conjunctions** are proved one side at a time.
- **Any stuck match of a finite type** is split, not only one blocked on
  `unsigned_lt_bit`. The order of preference:
  1. a comparison, which carries its Nat fact for `omega`, including one
     behind a helper (`low(x) = x.unsigned_lt_bit(10)`);
  2. something deeper in the scrutinee, a projection, or the arguments of a
     call a definition unfolded to;
  3. the scrutinee itself, when it is a neutral the source can spell
     (`s.inside`).
- **The split specializes every occurrence.** The scrutinee is abstracted
  where the search found it, and also in each other position of the goal
  that reaches it through definitions (`wc_next(…, s)` beside a step that
  matched on `s.inside`). Before this, the second occurrence was split again
  with nothing linking the two splits.
- **Goals simplify uniformly:** through constructors, pairs and projections,
  with β for applied function literals (a count `λ s => s.lines`). An encoded
  goal (`El(⌜Id …⌝)`, reached through introduced binders) is decoded first.

Two defects in the old code were found and fixed. A comparison behind a
helper (`match low(x) {…}`) produced a term the kernel refused with a bare
`NotConvertible`. A nested match whose result occurred twice was split
inconsistently. Both are covered by tests in `crates/elab/tests/goal_combinators.rs`
and `bv_omega.rs`.

### 2.2 A step at its own type (`lib/function_ir_loop.hthr`, `lib/read_program.hthr`)

`fold_body<C>(step: C → BitVec(8) → C)` is the loop body
`λ needle cursor byte s => Continue(step(s, byte))`. The library proves its
two facts once:

- `fold_body_folds` (it always continues) is `refl`;
- `fold_body_fold` says its chunk fold is the plain left fold `fold_bytes`.

The bundles move to a module of their own, `read_program`. Their defaults run
tactics, whose certificates name `omega`, and the loop's semantics have no
need to import it. They now take a fold step and state their facts about
`fold_bytes`:

```heather
record CountProgram(step: Nat → BitVec(8) → Nat, spec: List<BitVec(8)> → Nat) {
    advances: (count: Nat) → (byte: BitVec(8)) → step(count, byte) <= Succ(count) := { split_all; all_goals { omega } },
    computes: (bytes: List<BitVec(8)>) → spec(bytes) = fold_bytes(step, bytes, 0),
}
```

`fold_bytes(step, Cons(b, r), s)` unfolds to `fold_bytes(step, r, step(s, b))`,
so the transports are gone.

On the generator side:

- The loop reflection accepts `fold_body<C>(g)` as the body.
- The loop generator reflects `g` itself: the state's fields are the first
  ports, the byte is next, and there is no needle port and no choice.
- The discriminator comes from the library's constant `loop_continues()`.
- The producer's context module restates the bundle's facts at the shapes
  the loop and the claims read, by projecting the bundle's fields.

The needle stays in the process, and the profile loads 0 into its register.
Removing it is a follow-up (`issues/fold-programs-carry-a-needle.md`).

Measured against the previous build:

- **`wc`** differs from the old executable in exactly one byte, the needle
  immediate (10 → 0).
- **`wc -l`** is 7 bytes smaller. Its step now compares each byte with the
  constants 10 and 11 instead of the needle register.

### 2.3 Fields with a default (`docs/named-arguments-design.md` §9)

A record field may be written `name: T := e`. A construction that leaves the
field out fills it by checking `e` against the field's type as that
construction instantiates it. §9.2's rule holds: a defaulted field has no
positional slot, so the other fields fill positionally in order. A named
argument (`advances := p`) or a full positional spelling overrides it.

§9.4's scoping question is answered as it says it must be for a tactic
default, a stored goal and not a spliced expression:

- The default's names resolve in the record's declaring scope.
- The default sees the goal and none of the construction's locals by name.

This round ran a default only where the construction had no local bindings,
which is where a program bundle is built (a parameterless `fn`). Since
2026-10-12 a default also runs under locals: the goal stays open in them, and
the check runs in the construction's context with each local renamed out of
reach, so a tactic default sees them as hypotheses
(docs/named-arguments-design.md §9.6).

When a default fails, the error is at the construction and names the goal it
did not prove, followed by the tactic's own report. For a step that grows by
two at a newline, that report is the residual case, with the comparison
outcomes as locals:

```
error: `advances` was left to its default, which did not prove `…` here: `omega` got stuck:
  … locals [__split_all_x0: Nat, __split_all_x1: BitVec, __split_case: unsigned_lt_bit(__split_all_x1, ofNat(10)) = False,
  __split_case_: unsigned_lt_bit(__split_all_x1, ofNat(11)) = True, __omega_negated_goal: Le(Succ(Succ(__split_all_x0)), Succ(__split_all_x0)) -> False] …;
  give it by name (`advances := …`)
```

That error is the curtain the user asked for. The default covers the common
case. When it fails, the author sees the case it left, writes that one field,
and the rest stays automatic.

## 3. The programs now

`wc_l.hthr` is 60 lines: the spec, the step, one induction, and the bundle
`CountProgram(count_lines_input)`.

`wc.hthr` is 297 lines. The program keeps the specification and the words
argument, which is the real proof. Gone are:

- `WcAdvances` and its two helper theorems;
- `wc_body_advances`, `wc_body_folds` and `wc_step_is`;
- `wc_region` and every `step_fold`/needle transport.

`wc_next_bytes` is `split_all; all_goals { refl }`.

## 4. What is still by hand, and why

- **Fold lemmas over a recursive specification**, such as `count_lines_fold`.
  `split_all` can split them, but δ-unfolding `wc_l(Cons(byte, rest))`
  leaves the raw recursor where `wc_l(rest)` was, which `omega` cannot spell.
  This needs equation-style unfolding that respells recursive calls:
  `issues/split-all-through-recursive-definitions.md`.
- **Lemmas that need a hypothesis split.** `split_all` splits the goal. For
  `newline_is_space` the facts are in a hypothesis, and in
  `wc_next_lines` some leaves need `refl` and others contradiction.
  Alternation between leaf tactics belongs to `tactic-composition-ergonomics`.
- **Byte vocabulary.** Steps still say `b.unsigned_lt_bit(BitVec::ofNat(10))`.
  `<` is Prop-valued, `==` is not Heather syntax, and no `Numeral<BitVec(n)>`
  instance exists; each choice touches what the frontend recognises:
  `issues/byte-vocabulary-for-native-programs.md`.
