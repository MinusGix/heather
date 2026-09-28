# Goal combinators

`split_all` and `all_goals` separate finite case analysis from the proof used
at each resulting goal:

```text
theorem example(a, b: Bool): (a && b) = (b && a) {
    split_all;
    all_goals { refl }
}
```

`split_all` inspects the elaborated local context and constructs nested matches
for every local whose type is a non-recursive, non-indexed inductive. There is
no implicit branch-count limit: invoking it explicitly authorizes the finite
proof tree its locals describe. Recursive and indexed families are left alone.
Payload fields are bound by the generated match, although this first form does
not recursively inspect finite values introduced by those fields.

After splitting the locals, it also splits matches in the goal that are
blocked on `BitVec::unsigned_lt_bit`. It searches application arguments and
transparent definition heads with a bounded unfolding budget, without entering
unselected match arms. Each comparison branch gets an equation stating that
the comparison is `True` or `False`. With `bitvec_omega` imported, it also
supplies the corresponding Nat order as an ordinary `have`, usable by both
`omega` and `bv_omega`. The usual composition handles restoring steps:

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
checking expressions work too. A comparison the bounded search cannot expose
leaves the goal to the written leaf.

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
instance in scope it elaborates `logic::decide_yes(refl)`, so resolution picks
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
