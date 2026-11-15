# `have`: a block binding whose value is hidden

Status: implemented 2026-09-25. Anchor issue:
`issues/proof-let-substitution-cost.md`, whose 2026-09-25 log entries hold the
measurements this design rests on.

## 1. The problem, in one paragraph

A `let` is an alias (docs/language/let-and-blocks-design.md §2.2). Its value is one
`Rc` in the elaborated term, but the kernel gate re-checks a shared subterm
once per *path* to it. Module images and shifts under a binder also copy it
once per path. So a chain of `let`s in which each one mentions the previous
one several times costs the product of those counts. The unsplit
`read_print_after_read` took 186 s this way. Splitting it into lemmas fixed
it, because a lemma's body is opaque to its callers, so the expensive value
became a parameter. Binding four lets as β-redexes by hand fixed it better
(0.5 s against the split's 1.1 s). `have` is that β-redex, given a name.

## 2. Surface

```text
have x = e;
have x: T = e;
```

The grammar is `let`'s single-name form exactly: the annotation puts `e` in
checking position, and `no_eq` governs the annotation as for `let`
(docs/language/let-and-blocks-design.md §3). `have` may appear wherever a `let`
statement may, and the two interleave freely.

`have` is a contextual keyword. It is one only when an identifier follows it,
which is `let code x`'s device (docs/language/let-and-blocks-design.md §2.3). A value
named `have` still works everywhere, because `have x` was never an
expression: application is `f(x)`.

Not included, each for a stated reason:
- **`have { a, b } = e;`** A record pattern on an opaque value would bind
  projections of a variable. `let { a, b } = h` already does that when `h` is
  itself a `have`, so nothing is lost.
- **`have code x`.** Letbox is already a binder.
- **A `have` in a `meta fn` body.** The meta slice's statement loop is
  alias-only (`quote.rs`). It refuses `have` by name rather than treating it
  as a `let`, because silently treating it as a `let` would remove the one
  property the writer asked for.

## 3. Meaning

The rest of the block sees `x : T` and **not** its value. `x` is an ordinary
local binder. It shadows and is shadowed like a λ parameter, a goal raised
after it lists `x : T` with no body, and conversion never unfolds it. A proof
that needs `x ≡ e` must use `let`.

This is Lean's `have`/`let` split. The rule of thumb that the measurements
support is: use `have` for **certificate and lemma results**, i.e. values
whose head is a theorem application or a field of a parameter. They are
neutral anyway, so hiding them hides nothing a later conversion could have
used. Use `let` for **data that later proofs must see through** (`s1 =
w.after` in the print proof).

## 4. Lowering

`{ S⃗; have x: T = v; R⃗; r }` elaborates `S⃗` as before (aliases), then `v`
at `T`, then the remainder `{ R⃗; r }` in the context extended by the binder
`x : T`. It emits

```text
app(λ(x: T). b; l_T, l_B; x: T. B; v)
```

the kernel's fully annotated `App` (`term.rs`), with `b` the remainder's term
and `B` its type under `x`:

- **checking** at `E`, level `l`: `B = E↑1`, the expected type weakened past
  the new binder, and `l_B = l`. The remainder is checked, not inferred, so a
  `have` keeps a block checking-transparent (docs/language/let-and-blocks-design.md
  §4.4).
- **inference**: the remainder is inferred as `(b, B, l_B)`, and the block's
  type is `B[v/x]`.

The kernel checks `v` once and `b` once, with `x` a variable. Conversion
inside `b` compares `x`, not `v`. That is the whole cost argument.

`App` rather than `AppAt`: the unannotated form infers its function, and a
λ whose body is only checkable (a hole, a `refl`, a match under a motive)
does not infer.

Unannotated `have x = e` infers `e` exactly as `let x = e` does, including
the skeleton harvest from a λ right-hand side. The binder carries that
skeleton (`Cx::push_skel`), so implicit arguments of a `have`-bound function
still work. An annotation naming a class installs the dictionary binder just
as an annotated `let` does.

## 5. Where it plugs in

The three places that sequence statements now stop at the first `have` and
recurse on the rest: `statements::check_block`, `statements::infer_block`,
and the declaration body in `elab_decl_inner`, which now calls `check_block`.
`statements::elaborate` (aliases only) is kept for the statements before the
first `have`. The AST carries the difference as `Stmt::Let { opaque, .. }`
rather than as a new variant. Every walker (hole pre-count, lints, roles,
postfix-`?` lowering, `decreases` rewriting) already treats a `have` as a
binding, and under-counting holes is fatal (let-and-blocks §2.2). The sites
that *rebuild* a `let` carry the flag through. The module image encodes a
`have` as statement tag 3.

## 6. Not decided here

- **A diagnostic that suggests `have`.** It would compare the tree size of an
  item's term with its shared size and name the let with the largest
  multiplier (issue log, 2026-09-25). It is the other half of the issue's "a
  person should not have to find it by bisection".
- **A refusal that names the `have`.** When a conversion fails because a
  `have` hid a value, the error could say so. Today it reports the ordinary
  conversion failure, and the goal context lists `x` without a body.
- **The kernel typing memo on node identity**, for `let`s whose value is
  needed. It is a separate decision, and `have` does not depend on it.
