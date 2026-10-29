# Proof patterns: what costs, and what the language wants

The rules rounds kept rediscovering, checked against master on 2026-10-29
([[proof-patterns-audit-2026-10]] in issues/ has the probes and what was
retired). Each rule says why, so it can be dropped when the reason goes.
A rule that names an open issue is a workaround for that issue, not a
property of Heather.

## 1. Closed facts: evaluate once, in the kernel

- **State a closed verdict as `b = True` by `refl`.** The kernel evaluates
  `b` once. `b.IsTrue()` by `trivial` or `decide` costs about twice that,
  because the elaborator evaluates `b` too, and at native scale the gap is
  not a constant (cat FILE's allocation check passed 12 GiB as `trivial`,
  0.6M steps as `refl`): [[closed-verdict-evaluated-twice]].
- **Never compare two separately computed values by `refl`.** Conversion
  unfolds both sides in lockstep, a δ-step on each side per step. Small
  lists cost about three single evaluations; an allocation's `Homes = Homes`
  ran out of memory, and whole `MachineState` equalities run out of fuel.
  Decide equality with a Bool function and state `same(a, b) = True`.
- **A computed value is shared only by closure identity.** Two textual
  copies are two evaluations. Name a value once: a `let`, a record field a
  constructor computes (`Layout::of` holds the leaf pool), or
  `Option::some_get` around a compile. In evaluated Nat code write `q * 2`,
  not `q + q`.
- **Never run a loop at a constant fuel by conversion.** It runs out of
  fuel. Instantiate a generic lemma whose statement is syntactic instead.
- **Prove at a neutral parameter, instantiate at the literal.** A lookup at
  a literal width converts in lockstep (about 10k steps) where the same
  lemma at a variable width costs about 130. Stretches over an abstract
  label are elaborated once and cited with `refl` at each use.

## 2. Statements and proof shape

- **Split a long proof into stage theorems with written statements.** One
  theorem composing stages inline took 80 s and once ran out of memory; the
  same stages as five theorems took 0.2 s each. A proof whose state λ holds
  many lets makes every later let dearer (388 s, split to 27 s + 12 s).
- **Annotate a λ binder you match on when the expected type is computed.**
  The annotation is what the binder gets; unannotated, it gets the computed
  domain and the match spells its unfolding (20–170× kernel steps).
- **Put case analysis of a trace or other inductive in a small lemma over
  its own type**, not inside a recursion or under a computed binder.
- **State lemmas in the goal's spelling.** `x - y` against `x + -y` makes
  `rewrite` and generic-lemma matching convert, or fail before instance
  search (`hi + -lo`, not `hi - lo`, for a generic lemma at `Rat`).

## 3. omega

- **Give it what it cannot read yet:** a Nat `a - b` is an atom (add
  `Nat::sub_add_cancel`, [[omega-nat-truncated-subtraction]]); an
  `Exists`'s `.proof` is skipped
  (restate it with a typed `have`, [[omega-redex-typed-fact-ignored]]).
- **Over records and layouts at a literal program, prefer Nat step lemmas**
  (`Nat::le_trans`, `add_le_mono_l`) or a generic lemma over Nat variables.
  The kernel converts the atoms' definitions, and a field whose value
  computes is read as an opaque atom ([[omega-closed-field-value-atomised]]).
- **It reads every hypothesis in scope.** Keep its context small: put
  arithmetic in small lemmas, never `omega` inside a stretch or with `Rat`
  facts in scope. `omega(h, …)` names the load-bearing facts; whether it
  should read *only* those is [[omega-listed-facts-only]], an open decision.
- **It needs a checking position:** `let k: (T) = omega(…);`
  ([[checking-tactic-in-inference-position-diagnostic]]).
- **Linear arithmetic at `Rat`/`CReal` is `linarith`**, not `omega`, which
  unfolds Rat facts into Int cross products.
- **nat.hthr and int.hthr cannot import omega.** Facts about Nat and Int
  still live there; prove them by case splits and the order kit.

## 4. Matches and recursion

- The convoy `match h : obs(t)` refines the goal, including hypotheses
  taken as arrows after it. If unsure, take `(o) → obs(t) = o → …` and match
  on `o`.
- A recursion that varies another parameter returns a function
  (`(self fuel): (n: Nat) → …`), with the matched parameter first.
- The guard is the nearest `match` on a parameter: a self-call under a case
  split on another parameter is refused
  ([[recursion-guard-takes-nearest-parameter-match]]); split in a helper.
- A motive-less nested match on a `Cons` tail needs a written motive
  ([[nested-match-on-list-tail-motive]]).
- `absurd` needs a constructor clash; `False` goes by `false_elim`.
- Tier-2 laws through `Vis` are not provable with `=` (no funext): state
  them up to the tree's equivalence.

## 5. Names and syntax

Diagnosed by the elaborator and by design: `let p: (a = b) = …` needs the
parentheses; a parameter with a default is passed by name; declarations are
used after they are declared; records have unqualified names; `split`,
`match`, `fun`, `if` and `Type` are not binder names; `Zero` and `Succ` are
built in; identifiers are ASCII.

Not diagnosed well yet:

- A member's bare base name is its self-reference: inside `Prog::Sim`,
  `Sim()` is a recursive call. Reach the global as `<module>::Sim`
  (`prelude::cong` for the prelude,
  [[self-reference-hides-same-named-global]]).
- Inside a section or class body, `+` and `*` are the carrier's operations
  even at Nat operands: spell `Nat::add(a, b)`.
- A generic lemma whose explicit arguments don't mention the carrier needs
  it written (`sound_rel<Rat>(…)`, [[partial-type-application]]).
- An all-numeral relation (`0 < 1`) is at Nat: write `Rat::Lt(0, 1)`
  ([[all-numeral-relations-default-to-nat]]). Numerals at `BitVec` need
  `import algebra;`, characters at a byte `import char;`
  ([[literal-classes-need-importing]]).
- `[x] ++ ys` has no carrier: write `Cons(x, ys)` or `List::append`
  ([[list-literal-left-of-append]]). A statement may start with a literal
  (`[1, 2] = xs`); `[` opens a vector type only when `;` follows its
  element ([[statement-leading-list-literal-parse]]).
- Generated source: never `list::Nil` (bare `Nil` resolves by expected
  type), and Int numerals as `int::OfNat(k)`.

## 6. Before pushing lib/

- `heather check --cache --review <file>` on each touched module: plain
  `check` hides the review tier of lints, and some suite tests assert none
  fire.
- `scripts/fmt` on new or edited `.hthr` files.
- New surface syntax: `scripts/check-tree-sitter`, and new lexer symbols in
  tree-sitter-heather/syntax-inventory.json.

## 7. Measuring a proof's cost

- Use a fresh `--cache-dir` per run: a warm store, and an identical
  declaration earlier in the same process, answer from verdicts and make
  items look 10–50× cheaper.
- `--only module::Owner::name --timings f.tsv` probes one declaration over
  a replayed prefix; read the table with `scripts/timings`.
