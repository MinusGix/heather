# Goal combinators

`split_all` and `all_goals` separate finite case analysis from the proof used
at each resulting goal:

```text
theorem example(a, b: Bool): (a && b) = (b && a) {
    split_all;
    all_goals { refl }
}
```

A Heather counterpart, `by split_all(reflexivity())` from `lib/std/tactic/tactic.hthr`,
closes the same goals through the host's split requests
(docs/metaprogramming/host-elaboration-interface-design.md §16); it does not port the
word-comparison facts below. This combinator is what `split_all; all_goals`
means.

`split_all` inspects the elaborated local context and constructs nested matches
for every local whose type is a finite case domain: a non-recursive,
non-indexed inductive with more than one constructor. There is no implicit
branch-count limit: invoking it explicitly authorizes the finite proof tree its
locals describe. Recursive and indexed families are left alone, and so is a
record, which is one case: a `BitVec` stays a word, and a record's Bool field
is split where the goal matches on it (below). A match arm's own binders
(`#scrut`) are not locals to split. Payload fields are bound by the generated
match.

Then, at each leaf, the goal is taken apart until nothing finite is left
(docs/automatic-author-surface-design.md@4acf2fe §2.1):

- **a binder** — a goal `(x: A) → B`, or a definition that unfolds to one
  such as `LoopFolds(region)` — is introduced, and split at once when `A` is
  finite;
- **a conjunction** is proved one side at a time;
- **a stuck match** is split. A bounded search looks through application
  arguments, projections and transparent definition heads, and the arguments
  of a call a definition unfolds to, without entering unselected match arms.
  It prefers, in order: something deeper inside the scrutinee; a comparison
  (`BitVec::unsigned_lt_bit` or `BitVec::eq_bit`), the scrutinee itself or a
  helper the scrutinee unfolds to (`low(x)`, `newline(b) = decide_bit<b =
  '\n'>()`); and the scrutinee itself, when it is a neutral of a finite type
  that the source can spell (`s.inside`). Deeper first is what splits
  `eq_bit(match c { False => x, True => y }, 1)` at `c` before the
  comparison, which is then split at `x` and at `y`: cased on first, the
  comparison would be decided by the split under it. An operand a split has
  already decided is read as the arm it selects (`eq_bit(x, 1)`), so the
  occurrence the other side spells is the same split. A helper that is a
  comparison is split at the comparison, not at its call: the split then
  spells only names any scope can see (a bundle's default runs in the
  library's), and the search never unfolds past it into the comparison's
  bit-level fold. Each branch gets an equation stating the scrutinee's
  constructor. For a comparison, with `bitvec_omega` imported, it also
  supplies the corresponding Nat fact as an ordinary `have`, usable by both
  `omega` and `bv_omega`: an order for `unsigned_lt_bit`, and for `eq_bit` an
  equation or a `≠`, which `omega` splits by trichotomy. A closed literal
  operand is stated at its value (`14 <= byte.toNat()`, not
  `toNat(ofNat(14))`), so plain `omega` can compare the constants of two
  splits and close a case they rule out.

The split specializes every occurrence of what it splits. That includes an
occurrence the goal reaches only through a definition, such as
`wc_next(…, s)` beside a step that matched on `s.inside`; otherwise the two
would be split independently. A recursive definition at a constructor
(`Cons(b, rest).filter(kept)`) reaches its element through the
constructor's encoding, a projection out of a pair; a comparison's projected
operands are read off the pair (`b`), so the occurrence there and the one
the other side spells are one split. A scrutinee that is not a comparison
is read through the encoding too (`bit7(c1)` reached as `bit7` of the
list's head projection): the split then names the term the other side
spells, so the decoder's `cont_lead(c1, r)` and a side that says `bit7(c1)`
split as one (`lib/_tests/std/text/utf8_tests.hthr`). The search under one
stuck match is bounded at 1024 steps, which a four-byte sequence's third
continuation byte needs. The search for hidden occurrences reads a word
operation's operands without unfolding the operation (`pick(b, c).eq_bit(0)`
hides the test in `pick`). The `cases` request a Heather tactic makes
(`bv_decide`'s split) searches each side of an equation under its own
budget, so a side that unfolds far without the test does not spend the
search for the other. Between steps the goal is simplified alike
everywhere: computed matches, projections of pairs and applied function
literals are reduced, inside constructors too. So is a call of a definition
whose match the split decided: `Bool::and(False, b)` once a comparison is
known, `split_at(False, x, ps)` once `cut` is. Such a call is replaced by the
arm it selects, but only when the arm is a value that the source can spell,
with no match left at its head. A call whose match is still stuck, or a
library call such as `words(xs)` that unfolds to no deciding match, stays as
written. A relation's head (`Le(a, b)`) is never reduced, only its arguments.
A hypothesis introduced after a split is restated at its simplified type, as
the goal is, so a leaf reads both at one spelling. The usual composition
handles restoring steps:

```text
fn place(s, threshold, weight: BitVec(8)) → BitVec(8) {
    match s.unsigned_lt_bit(threshold) {
        True => s, False => s.sub(threshold).add(weight)
    }
}

theorem lowers(s: BitVec(8)):
    place(s, BitVec::ofNat(10), BitVec::ofNat(0)).toNat() <= s.toNat() {
    split_all;
    all_goals { bv_omega }
}
```

The splitter abstracts the exposed match into its motive, including below
`toNat`, and computes constructor cases before checking a leaf. It searches
again in each specialized branch, so nested comparisons are split as they
become visible. The leaf remains independent of the splitter: `refl` and other
checking expressions work too. A match the bounded search cannot expose
leaves the goal to the written leaf.

The splitter checks its own output, so that it never reports a split the
kernel then rejects (issues/split-all-nested-scrutinee-kernel-reject.md):

- **A case computation refutes is closed, not handed on.** A split is taken
  on what blocks the goal at the time; the scrutinee may compute all along
  (`zero().unsigned_lt_bit(zero())`), or a later split may decide an earlier
  one's. The case whose equation then relates two different constructors by
  computation is no case of the program, and its goal can be false (`1 =
  0`). At every step, before anything else, the innermost such equation
  closes the case with `absurd`.
- **Every goal it builds restates the one it stands for.** A split's motive
  at its scrutinee, and the simplified goal handed to a split or a leaf, must
  convert to the goal; a failure is reported as an internal error of the
  splitter, at the split, rather than surfacing as the kernel's verdict on
  the declaration. (A conversion that runs out of fuel is left to the
  kernel.)
- **A goal the split has proved is closed, not handed on.** An equation
  whose two sides the split and simplification made the same term closes
  with `refl`. The leaf is written for the cases still open, and a step
  that answers a value in some arms and recurs in others meets a leaf
  written for its recursions (`all_goals { hg }`, a hypothesis stating
  them) at its answers as `acc = acc`, which only `refl` proves. The sides
  are compared as terms: a goal that holds only by computation is still the
  leaf's.
- **A convoy keeps its equation.** `match h: c { … }` elaborates to a match
  on `c` whose motive is `λ z => (c = z) → T`, applied to `refl`; an arm
  that uses `h` (an obligation, a recursion's bound) is typed by it. Split
  at `c`, only the convoy's match moves to the split's `z`; its motive, arms
  and `refl` keep `c`, and the split's motive takes the case's equation `q
  : c = z` as a second binder, the convoy applied to `q` in place of `refl`.
  In each case the convoy then takes its arm with the case's equation, the
  type the arm was written at. Abstracted whole, the arm was handed an
  equation about `z` and the kernel refused the split
  (issues/split-all-convoy-equation.md).
- **A `refl` leaf is checked where it stands.** Elsewhere `refl` is a note
  for the gate, not a check; at a `split_all` leaf it is converted on the
  spot, and a leaf whose sides differ is refused with its goal and the case
  equations that led to it (`` `split_all` leaves the goal `0 = 1` in the case
  `unsigned_lt_bit(ofNat(0), ofNat(0)) = False` ``). Other leaves check
  themselves as they always do.
- **A failing leaf names its case.** A leaf that fails (`bv_omega`
  stuck) has the case it failed in added to its error, each test as the
  source would write it: `` in the `split_all` case `lo <= x`, `hi < x`,
  `hi < lo` ``. A comparison taken false reads as its converse, and a
  literal operand as its value.

Programs call programs, and take preconditions that are calls
(docs/tactics/program-proof-tactics-design.md §3 A):

- **A call nested in a call** (`clamp(clamp(x, lo, hi), lo, hi)`,
  `max(max(a, b), c)`) is split inside out. The inner call's test is found
  first, in the outer call's argument, and the split abstracts the inner
  call wherever it is spelled; the outer call is never unfolded around it
  (unfolded, its comparison reached the bit-level fold, with the inner call
  still standing inside). Once the inner call is a value, the outer call
  meets its own tests, possibly one an earlier split already decided
  (`x < lo` again, at `x`). That test is split again, and **the case that
  contradicts the earlier one is closed** by `absurd(trans(sym(h0), h1))`,
  so every leaf still sees only cases some run reaches.
- **A premise that is a call with tests** (`is_digit(c) = True → …`) is
  split before it is introduced: the split abstracts the whole `Π`, and each
  case introduces the premise at what that case makes of it. A case where
  it reads `False = True` is closed, as a refuted case equation is.
- **A hypothesis that is a call with tests** (`h: is_digit(c) = True`) is
  reverted into the goal at the root, before any case is taken, and is then
  split as a premise. Only equations the user wrote are reverted, and only
  when a split can take them apart; the original stays in context
  unchanged.
- **An equation of constructors a split leaves** (`Leaf(w).emits(p, names)
  = Some(c)` reads `Some(Out(Cons(w, p), names)) = Some(c)` in the case
  where the test passes) is injected and its local substituted before the
  leaf is reached: the split emits `subst(h, …)` for the innermost such
  hypothesis it introduced (`injected_hypothesis`), so the leaf's goal is
  `Within(p, Cons(w, p))`, not one about `c`. A hypothesis whose fields clash
  closes the case the same way
  (`issues/constructor-equations-in-context.md`).

What it does not do yet: revise a hypothesis that a split substitutes into
when the hypothesis has no test of its own to split (only the root reverts,
and only what it can split); and
unfold a recursive definition to a spelling a leaf can read. Unfolding
`wc_l(Cons(byte, rest))` leaves the raw recursor where `wc_l(rest)` was,
which `omega` cannot spell (issues/split-all-through-recursive-definitions.md).

`all_goals { body }` checks the same block independently at every leaf. With no
finite local it checks `body` once at the original goal. The initial surface
requires the pair in sequence inside a declaration body:

```text
split_all;
all_goals { omega }
```

This is proof-tree composition, not solver-state sharing. A solver may cache
work internally, but the combinator promises only that each branch receives
the same checking expression in its branch context.

The parser packages the pair as an unspellable checking form because the
number and constructors of the branches are known only after local types have
been elaborated. The elaborator expands it to ordinary `match` expressions;
the completed proof crosses the declaration's ordinary kernel gate. Neither
form adds a trusted rule or a new kernel term.

`all_goals` is intentionally named for the general operation rather than tied
to Omega. Other goal producers and more concise sequencing syntax can reuse it
later without teaching individual solvers about finite case analysis.

## `cases h`

`cases h;` takes apart a hypothesis that says what a call returned, along
the tests the call makes, and the rest of the block is every case that
survives (issues/cases-on-hypothesis-tactic.md):

```text
theorem pipe_stage(n, out: Nat, ran: pipe(n) = Some(out), k: (a: Nat) → st1(n) = Some(a) → Nat): Nat {
    cases ran as e1(a), e2(b);
    k(a, e1)
}
```

It is the inversion a proof writes by hand, one step at a time, each step
checked in the case the previous one made:

- `absurd(h)` when `h` now equates two constructors (`None = Some(c)`);
- `subst(h, rest)` when it equates one constructor's applications with a
  local in a field (`Some(x) = Some(c)`), which replaces `c` and ends the
  inversion;
- otherwise a case split on the test `h` is stuck on, of `Π(h). goal` as
  `split_all` splits a goal, applied to `h`: `(match e: test { C(x̄) => λ h
  => <next step>, … })(h)`. The test is found by `split_all`'s search for
  what blocks a goal, except that it takes the test **as the callee wrote
  it**: a pipeline stage `st1(n)` is split as `st1(n)`, not on the
  `n.leb(5)` inside it, which `split_all`'s deeper-first order would reach.
  In each case `h` is the reduct the test was found in with the test
  replaced, so a structural recursion's later call reads as the call
  (`yes.emits(…)`, not the kernel's copy of its eliminator) and is split
  and named in turn. The goal is refined where it mentions the test as the
  split spells it;
- the rest of the block, once `h` is stuck on nothing.

`as e1, e2(x, y)` names the splits' equations in the order they are taken
along a path, and the fields of a constructor with that many fields (the
`Some(a)` of a stage). Names also **bound** the inversion: `cases h as e1;`
takes one split and then only closes or substitutes, so `emitted:
(match region.scopes() { …, True => region.code(…) }) = Some(c)` stops at
`region.code(…) = Some(c)` for a lemma about `code` rather than taking
`code` apart too, and `cases emitted as one(c1);` on a `Then`'s emission
leaves `emitted` the rest's `rest.emits(c1.prog, …) = Some(c)`. Without
names, every split is taken until `h` is stuck on nothing, each with a
hidden name that `known` still finds. A hypothesis stuck on nothing at the
start is refused (`there is nothing to take apart`, with what `h` reads).
A hypothesis whose type a definition computes (a premise of
`t.EmitsRun(s, …)`) is read as the equation it decodes to.

So the proof is ordinary nested matches; the kernel checks it as it checks
the hand proof. A goal that mentions the test only through a definition
(`s.checks(…)` over the `apart` tested) keeps it: use the split's named
equation (`Bool::is_true_of_eq(apart)`). Probes:
`lib/_tests/std/tactic/cases_hypothesis_tests.hthr`; uses across
`lib/native/` (`Stmt::emits_extends`, `Stmt::emits_runs`,
`Stmt::checked_sound`, `StructuredRegion::faithful`).

## `decide`

`decide` is a leaf, not a goal producer: at a goal `P` with a `Decide<P>`
instance in scope it elaborates `bool::decide_yes(refl)`, so resolution picks
the instance and the kernel runs its decision to judge the `refl`
(`docs/tactics/reflection-through-decide-instances-design.md` §4). It composes with
the pair above like any other leaf:

```text
theorem every_bool(b: Bool): bool::Le(b, True) {
    split_all;
    all_goals { decide }
}
```

A false closed goal is refused by the kernel as `NotConvertible`, reported at
the `decide` with the instance named. The name gives way to anything the
writer bound under it; the library's `decide<P>()` keeps its meaning where it
is applied.
