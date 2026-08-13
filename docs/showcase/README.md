# The showcase pair: one program, written twice

Two spellings of the same program — a shell calculator whose compiler to an
RPN stack machine is *proved correct*, the project's thesis in miniature:

- **`idealized.hthr`** — the language we want. It does not check, and its job
  is to be argued with: a concrete surface for design critique, ahead of the
  issues (which lag the head — several constructs here have no owner yet).
- **`calc.hthr`** — the same program at the limit of what checks today
  (2026-08-13). Verify with:

  ```
  (ulimit -v 8388608 -t 120; \
   target/release/heather check -L lib/std docs/showcase/calc.hthr)
  ```

The method: every diff between the two files is either a **gap** (a feature
that doesn't exist, mapped below to its owner) or a **friction** (it exists
but cost too much argument). When a line of the idealized file starts
checking, a brick landed; re-derive the realized file toward it and shrink
the table. The idealized file is *not* a commitment — it is the current best
guess, revised freely as taste and design rounds move.

## What already matches

Worth saying first, because half the idealized file **is** the realized file:
inductives with fields and shared annotations, structural `match` recursion
with self-call IHs, nested patterns and `_` default arms, `+`/`*`/`++` via
designations (`*` at `Nat` is one line in the showcase itself), `calc`
equational chains, the empty proof block `{}`, implicit `{a, b}` theorem
binders, receiver members (`e.eval()` and `args.nth(1)` — `fn Expr::eval(self e: Expr)` checks today), honest
`Option` failure in the machine, and the whole *shape* of the correctness
statement. The demo theorem computes `2 + 3 * 4 = 14` by kernel reduction.

## The gap table

| Idealized construct | What's missing | Owner |
| --- | --- | --- |
| `theorem compile_pushes_eval(e, rest, s)` with plain parameters | varying arguments force the returned-function statement + over-applied IHs | `issues/ih-generalization.md` |
| `fn run(toks, s)` uncurried | same mechanism at `fn` level — the stack varies, so `run` curries it | `issues/ih-generalization.md` |
| calc steps that reassociate `++` silently | monoid laws as an ambient simp set the chain applies where they obviously fire | `issues/grind-port.md`, `issues/lemma-selection-and-search.md` |
| `:= compile_pushes_eval(l)` (endpoints fill the arguments) | unification-driven instantiation of a calc-step justification | `issues/elab-unifier-completeness.md` (nearest) |
| no `cong_run` anywhere | congruence inferred from the goal's shape | `issues/congruence-by-anti-unification.md` |
| `heather disprove '…'` at the shell | counterexample search before anyone pays for a proof | `issues/heather-disprove.md` |
| `[TPush(n)]`, `n :: s` list notation | list literals and cons as notation | no owner yet (nearest: `issues/notation-extensibility.md`) |
| `Result`, `?`-chaining, `.map` | prelude types and their chaining kit | `issues/prelude-option-and-friends.md` |
| `let b :: a :: s2 = s else { … }` | let-else (the one-non-absurd-branch match) | `issues/let-else-sugar.md` |
| `String`, `.chars()`, `[c, ..rest]`, `if c.is_digit()` guards | strings, slice patterns, match guards | no owner yet |
| `decreases ts.len()` on mutually recursive parsers | non-structural termination measures; mutual recursion; callee consumption postconditions | `issues/termination-measures.md` |
| `"{src} = {eval(e)}"` | string interpolation | no owner yet |
| `datarepr Nat = repr::BigNat` | runtime representation chosen per type, linked by certified refinement | `issues/datarepr-separation.md` |
| `derive instance Compile[Cpu] for eval` | the certifying generator at **tier-1 source types** — `eval` recurses over `Expr`, `run` over `List<Tok>`, exactly the generator's next staged feature | `issues/certifying-generator.md` |
| `Compile[Cpu]` as a class | the Compile typeclass and certificate coupling | `issues/compile-typeclass-design.md` |
| `runtime_fn main`, `IO`, `println` | the effects story and the kerneltime/runtime rim | `issues/effects-direction.md` |

## Frictions found while writing the realized file

Recorded here because "it checks" hides them:

1. **A parameter named `code` cannot be matched on.** `match code {` parses
   as the quotation form `code { … }` and dies with ``expected `}` to close
   the quote`` — a baffling message for an ordinary variable name. The
   realized file renamed the parameter to `toks`. Filed:
   `issues/match-scrutinee-named-code.md`.
2. **`++` is left-associative; `append`-based proofs are right-nested.**
   Swapping `append(a, append(b, c))` for `a ++ b ++ c` silently changed the
   term under an already-green proof to `(a ++ b) ++ c` and broke it — fixed
   by writing `a ++ (b ++ c)`. Nothing wrong, but nothing *said* anything
   either. **Resolved 2026-08-13**: `++` is right-associative now (the fixity
   table in `parser.rs` says why), and this file dropped the parens. The
   durable lesson stands: fixity is proof-relevant, so notation declarations
   should carry associativity visibly.
3. **The congruence tax.** One `cong_run` lemma is cheap, but it is the same
   `j(p, λ y q => …, refl)` shape every file writes per position
   (`list_algos` has five). This showcase's whole proof burden beyond the
   induction itself is congruence plumbing plus `append_assoc` shuffling —
   both rows in the table above.
4. **`calc` is already a big win.** The first draft used `trans` chains; the
   calc rewrite is the difference between a proof you re-derive and a proof
   you *read*. It landed with `surface-operators` and deserves to be the
   default idiom.

## Bookkeeping

The realized file is checked by hand (command above), not by the test suite —
so it can rot silently if the surface moves. If it earns keeping, wire it
into a test; until then, re-check it when showing it to anyone.

`mul` (and its `*` designation) belongs in `std/nat`, but moving it collides
with `crates/elab/tests/certgen.rs`'s own `fn mul` fixture, which elaborates
on top of the `ir_v1`+`nat` prelude and whose generated emissions are pinned
byte-for-byte under that name. Deferred until a round is touching those pins
anyway; the collision itself is a small argument in the module-scope story
(fixture programs and the library share one namespace).
