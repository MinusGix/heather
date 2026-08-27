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
