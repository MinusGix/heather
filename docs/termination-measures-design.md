# Termination measures: `decreases e`

How a `fn` or `theorem` whose recursion the structural checker declines is
elaborated from a **`Nat` measure** (`issues/termination-measures.md`,
layer 1). The customers are Euclid's `gcd`, `merge` on two lists, and the
parser shape — a recursive call on a suffix some callee returned, decreasing
by that callee's lemma (layer 2, the separate-lemma route).

## 1. The idea: strong induction on a bound, spelled at the surface

```
fn f(x̄) -> T decreases e { body }
```

becomes, before any elaboration, the ordinary program

```
match Succ(e) as λ z => (x̄) -> nat::Lt(e, z) -> T {
    Zero        => λ x̄ h => match h {},
    Succ(k, ih) => λ x̄ h => body[ f(ȳ) ↦ ih(ȳ, nat::le_trans(Succ(e[ȳ]), e, k, obligation, h)) ],
}(x̄, nat::lt_succ_self(e))
```

and is checked against `T` like anything else (`crates/elab/src/measure.rs`,
`measure::lower`). Read it from the outside in — but note that the three
layers are now **named** rather than nested inline: `f#body` is the `Succ`
arm, `f#rec` the eliminator, `f` the application
(`docs/decreases-unfolding-design.md` §2, which amends this section and §5).
Nothing else changes: a `fn` is transparent, so closed arguments still
compute through the indirection.

- The recursor is on the bound `Succ(e)`, a `Nat`, so it is one `elim_Nat`
  and **closed arguments compute**: `gcd(12, 8) = 4` is `refl`, and the
  fuel-shaped `Zero` arm is unreachable by construction — `h : e < 0`
  reduces to `False`, and `match h {}` is its elimination.
- The motive quantifies every parameter and the bound hypothesis, so the
  `Succ` arm's ih is `Π x̄. e < k → T`: the value of `f` at any argument
  whose measure is below the bound. That is the induction hypothesis a
  well-founded recursion wants, and the written-motive `match` with the
  explicit-ih arm — both older than this round — is all it takes to bind it.
- Inside the arm the parameters are re-bound under their own names, so
  `body` reads exactly as written; only its self-calls are rewritten.
- A self-call `f(ȳ)` becomes the ih at `ȳ` with a proof that `e[ȳ] < k`. The
  arm has `h : e < Succ k`, which **is** `e <= k` by reduction (`Lt` is
  `Le ∘ Succ` and `Le(Succ a, Succ b) ⇝ Le(a, b)`), so `le_trans` from the
  call's own obligation `e[ȳ] < e` closes it. No lemma about the measure is
  ever needed beyond that one obligation per call.

Nothing here is trusted. The rewrite reads *names* — the declaration's own
for a self-call, the parameters' for `e[ȳ]` — and where a name misleads it
the emitted program fails to check: the ih's hypothesis is at the
elaborated measure, so a wrong obligation is refused where the call is
written, never accepted. The kernel checks the whole recursor afterwards.

## 2. Obligations: named holes, `omega` by default

Each recursive call, in source order, owes `e[ȳ] < e` under the name
`decN`. The writer discharges it with `on ?decN := …;` at the end of the
body, as any goal; where no `on` names it and the `omega` and `int` modules
are in scope, the obligation is `omega`. Where they are not, the hole is
reported as an ordinary unsolved goal with its statement.

The obligation is not raised at the call: it is lifted into a generated
declaration of its own, `f#obl_N`, which the body and both unfolding
companions reference (`docs/decreases-unfolding-design.md` §4). Nothing the
writer sees changes — the hole is still `?decN`, the `on` is still written at
the end of the body, and it travels to `f#obl_N` with its obligation.

An `omega` failure is reworded to name the obligation and the `on` that
would discharge it: "this recursive call must decrease the measure, and
`Succ(Succ(k)) < Succ(k)` was not proved automatically (…). Discharge it by
hand: `on ?dec1 := …;`". The negative controls in
`crates/elab/tests/termination_measures.rs` pin that message.

So that measure obligations — which are full of pattern successors — reach
`omega` at all, an **open** `Succ(t)` now reflects as `t + 1`
(`omega_cert.rs`, `nat_affine_syntax`). `nat::add(t, 1)` reduces to
`Succ(t)`, so a certificate stated over the sum checks at the goal.

## 3. Refinement: the obligation is stated at the pattern

The obligation a reader expects inside `match b { Succ(k) => gcd(…, mod(a,
Succ(k))) }` is `mod(a, Succ(k)) < Succ(k)`. The ih's hypothesis, though, is
at the *parameter* `b`, and a `match` does not refine the context — inside
the arm `b` is still `b`. Stated naively the obligation is
`mod(a, Succ(k)) < b`, which nothing can prove.

The rewrite therefore **convoys the refinement**: a `match` on a variable
the (already refined) measure mentions is given a hidden equation binding,
`match __dec_eqN: b { … }`, so each arm has `__dec_eqN : b = Succ(k)`. The
obligation is stated at the measure with every enclosing arm's pattern
substituted — `e_i = e_{i-1}[patᵢ/vᵢ]` — and transported back to the ih's
own statement through the equations, innermost first:

```
j(sym(__dec_eqᵢ), λ y _ => nat::Lt(e[ȳ], e_{i-1}[y/vᵢ]), acc)
```

turns a proof at `e_i` into one at `e_{i-1}`. Nested matches chain
(`n = Succ(k)`, `k = Succ(l)` give `l < Succ(Succ(l))`, which `omega`
closes), and a `match` whose scrutinee is not a variable, or whose pattern
has no expression form (`_`, a named field), refines nothing and sees the
measure as the enclosing arm did.

The equation binders and the wrapper's own binders are spelled `__dec_…`,
not `#`-hygienic names, on purpose: `omega` renders its certificates as
source text and re-parses them, and a context local it cannot spell is one
it cannot use. The names are unspellable by convention, not by the lexer.

## 4. What it composes with, and what it does not

- **Any body shape.** The rewrite walks every expression form and every
  block statement; a self-call under a nested `match`, a `let`, a lambda or
  a spill (`f(ȳ)(more)`) is rewritten in place. Named arguments on a
  self-call are refused, as the structural guard refuses them.
- **Implicit parameters** are quantified explicitly by the motive, so a
  self-call passes them: it must be `@`-marked, and a plain call meets a
  message saying so. `self` and solver parameters are refused for now — the
  recursion re-binds every parameter explicitly, and those two are filled
  another way.
- **A `theorem` by measure** works the same way: `even_or_odd_wf` recurses
  at `l` under two matches, and is the one shape course-of-values recursion
  would also reach; a measure reaches further (`halve_steps` at `mod`, or
  any lemma-fed descent).
- **Unfolding at open arguments is not definitional.** A recursive
  occurrence inside the unfolded body is the recursor at the bound's
  predecessor with a transported proof, not `f(ȳ)`, so a proof *about* a
  `decreases`-defined function by induction cannot rewrite `f(ȳ)` with its
  hypothesis. Every well-founded-recursion story owes an unfolding equation
  here; ours is generated — `f_unfold(x̄): f(x̄) = body`,
  `docs/decreases-unfolding-design.md`, which also says which body shapes the
  generator declines (a computed `match` scrutinee, a self-call under a `λ`).
- **Mutual recursion** (the showcase parser's three functions) is not this
  round: it needs declaration groups before a shared recursion, and has its
  own issue, `issues/mutual-recursion-declarations.md`.
- **The refined-return-type route** for layer 2 (`{rest | rest.len() <
  ts.len()}`) was not built; the lemma route covers the customer
  (`a_callee_postcondition_feeds_the_decrease`), and a refined return is a
  record whose proof field is exactly that lemma.

## 5. Where it lives

- `crates/syntax/src/ast.rs`, `parser.rs` — `Decl::decreases`, parsed after
  the result type (`fn f(…) -> T decreases e { … }`); the module image
  format carries it (magic bumped to `\x03`).
- `crates/elab/src/measure.rs` — the wrapper, the self-call rewrite, the
  refinement convoy, the obligation diagnostics, the lifted obligations, and
  the unfolding companions (`docs/decreases-unfolding-design.md`).
- `crates/elab/src/lib.rs`, `elab_measure_decl` — the hook: a declaration with
  a measure is replaced by the family of declarations that lowering names,
  each elaborated as an ordinary declaration; `ctor_fields_of` is the one
  question the syntactic generator asks back (what an arm binder is typed at,
  for a lifted obligation's parameters).
- `crates/elab/src/surface.rs`, `count_holes` — the obligation holes are
  counted into the declaration's goal reservation.
- `crates/elab/src/omega_cert.rs` — open successors as sums.
- `crates/elab/tests/termination_measures.rs` — acceptance for the lowering;
  `crates/elab/tests/decreases_unfolding.rs` for the companions.

No kernel change.
