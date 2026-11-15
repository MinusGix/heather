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
(docs/host-elaboration-interface-design.md §16); it does not port the
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
the other side spells are one split. Between steps the goal is simplified alike
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

What it does not do yet: split a hypothesis, or revise one already in
context when a split substitutes into it (only binders introduced after the
split are simplified, so state such a premise as a binder of the goal); and
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

## `decide`

`decide` is a leaf, not a goal producer: at a goal `P` with a `Decide<P>`
instance in scope it elaborates `bool::decide_yes(refl)`, so resolution picks
the instance and the kernel runs its decision to judge the `refl`
(`docs/reflection-through-decide-instances-design.md` §4). It composes with
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
