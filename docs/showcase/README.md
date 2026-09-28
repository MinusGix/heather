# The showcase pair: one program, written twice

Two spellings of the same program — a shell calculator whose compiler to an
RPN stack machine is *proved correct*, the project's thesis in miniature:

- **`idealized.hthr`** — the language we want. It does not check, and its job
  is to be argued with: a concrete surface for design critique, ahead of the
  issues (which lag the head — several constructs here have no owner yet).
- **`calc.hthr`** — the same program at the limit of what checks today
  (2026-08-13). Verify with:

  ```
  scripts/showcase check calc
  ```

Every file in this directory has a row in [`showcases.tsv`](showcases.tsv) —
its `-L` set, how it is gated, and what it is for — and `scripts/showcase`
reads it, so a check by hand is the name alone, with the `-L` set and the
`ulimit` discipline already right. `scripts/showcase list` prints the table.

The method: every diff between the two files is either a **gap** (a feature
that doesn't exist, mapped below to its owner) or a **friction** (it exists
but cost too much argument). When a line of the idealized file starts
checking, a brick landed; re-derive the realized file toward it and shrink
the table. The idealized file is *not* a commitment — it is the current best
guess, revised freely as taste and design rounds move.

## Checked token parser

[`calc_parser.hthr`](calc_parser.hthr) extends the realized calculator with
numbers, `+`, `*`, and parentheses. Multiplication binds more tightly than
addition; both operators associate to the right, as in the idealized parser.
It imports the existing `Expr`, evaluator, RPN compiler, and compiler proof
from `calc.hthr`. The grammar imports `parser`, the facade over
`lib/std/parser/`, for source-indexed cursors, consuming composition,
commitment and complete-input checking.
See [the parser library](../parser-library.md) for its contracts.

```text
expr   := factor [ '+' expr ]
factor := atom [ '*' factor ]
atom   := number | '(' expr ')'
```

```sh
scripts/showcase check calc_parser
```

There is no copy step, and there used to be one here: this file imports `calc`,
which sits beside it, and the loader searches the importing file's **own
directory first** (`resolve` in `crates/cli/src/loader.rs`). What the old
recipe was working around is `-L docs/showcase`, which puts this directory's
`parser_core.hthr` — the pre-library prototype — against `lib/std/parser`'s,
and a module in two search directories is refused rather than resolved by
precedence. The answer is to not pass that `-L`, which is what the manifest
records, rather than to move the files.

The public entry points are `parse(tokens)`, `calculate(tokens)`, and
`execute(tokens)`. For the tokens of `2 + 3 * 4`, they produce
`Ok(Plus(Lit(2), Times(Lit(3), Lit(4))))`, `Ok(14)`, and `Ok(Some([14]))`.
Parenthesizing the sum produces `Ok(Some([20]))`. Malformed input and tokens
left after a complete expression produce explicit `ParseError` values.

`parsed_compile_correct` proves for **every token list** that compiled RPN
execution agrees with direct evaluation after parsing, preserving errors.
`parse_sound` additionally proves that every successful parse has an independent
well-formed grammar derivation whose spelling is exactly the input and whose
meaning is the returned AST. Source-indexed cursors and checked consumption
provide recursive-call evidence. The proof-carrying recursive implementation
projects ordinary replies for public callers. See
[calculator grammar soundness](../calculator-grammar-soundness.md).
AST equations also check precedence, association, and nesting, including an
open numeric payload. Characters are no longer future work — `calc_text.hthr`
below is the same grammar over text, scannerless. General recognition
completeness, shell IO, and native compilation remain future work.

Both realized files are checked by
`crates/elab/tests/showcase_calculator.rs`, including controls that require the
kernel to reject wrong precedence, association, arithmetic, leftover-input
handling, and error priority. The smaller [`result_parser.hthr`](result_parser.hthr)
remains a standalone introduction to `?`. Check it with:

```sh
scripts/showcase check result_parser
```

## Scannerless text calculator

[`calc_text.hthr`](calc_text.hthr) is the same grammar over **characters**, so
`calculate("2 + 3 * 4")` runs the whole pipeline from a `String` to a checked
answer — the consumer `String` and `Char` were built for
(`../string-char-design.md`). Two things change when the source is text.

A numeral is a *run*, not a token: `Number` carries its digits, so `spelling`
is those characters and `meaning` is the decimal fold, and no `Nat`-to-decimal
rendering function or round-trip theorem appears anywhere. And whitespace is
carried *in the derivation* — each lexeme owns its trailing spaces, the whole
parse owns its leading ones, and `WellFormed` obliges every one of those
characters to be a space — so the span theorem still says the derivation spells
the input character for character. Nothing is skipped behind the proof's back.

```text
expr   := factor [ '+' spaces expr ]
factor := atom [ '*' spaces factor ]
atom   := digit+ spaces | '(' spaces expr ')' spaces
```

```sh
scripts/showcase check calc_text
```

It checks in 16 s at 0.3 GiB at width one (2026-09-22), its semantic image
publishes, so a warm recheck replays it in about a second and `--only` works,
and it is an ordinary row of the CLI showcase test. It was 343 s and 9.8 GiB
with an image refused as over budget until application annotations stopped
being written (`docs/app-by-head-type-design.md`); the history is in
`issues/showcase-harness.md` and `issues/check-only-no-stored-image.md`.

The entry points take a `String`: `parse`, `calculate`, `execute`.
`parse_sound` gives every accepted text a well-formed derivation that spells it
and means the returned AST, and `parsed_compile_correct` carries the compiler
agreement across. Fifteen `refl` equations run the pipeline on text, including
multi-digit numerals, spacing, and five error cases.

The derivation's theory is namespaced — `d.tier()`, `d.meaning()`,
`d.WellFormed()`, `d.spell(tail)`, `d.spelling()` — and the elementwise class
tests are `list`'s own `ds.all(is_digit)` and `ds.nonempty()`. The relations
handed to the library's `Certified` are records partially applied —
`Grammar(level)`, `RunSpec(cls)`, `OpRun(target)` — so their evidence is read
by name (`op.evidence.progress`, `run.span`) rather than by `.left.right` into
a conjunction.

The cap above is deliberate and the reason this file is **not yet** in
`crates/elab/tests/showcase_calculator.rs`: it needs more than 8 GiB cold,
which the suite's 6 GiB per-process rail refuses. The cost is not the grammar's
shape — a record token type costs 27× the conversion misses of an inductive one
in a controlled pair (`probes/str/p10.hthr`), which is
`issues/elaborator-canonical-type-spelling.md` reached from the type-argument
end, since `Cursor<Char>` and `List<Char>` instantiate the library at a record.
`issues/sequence-parser-source.md` owns the file and
`../sequence-parser-source-design.md` records the design.

## What already matches

Worth saying first, because half the idealized file **is** the realized file:
inductives with fields and shared annotations, structural `match` recursion
with self-call IHs, nested patterns and `_` default arms, `+`/`*`/`++` via
designations (all three from `std/algebra` since 2026-08-13 — `*` at `Nat` was
the showcase's own line until then), `calc` equational chains, the empty proof block `{}`, implicit `{a, b}` theorem
binders, receiver members (`e.eval()` and `args.nth(1)` — `fn Expr::eval(self e: Expr)` checks today), honest
`Option` failure in the machine, and the whole *shape* of the correctness
statement. The demo theorem computes `2 + 3 * 4 = 14` by kernel reduction.

## The gap table

| Idealized construct | What's missing | Owner |
| --- | --- | --- |
| `theorem compile_pushes_eval(e, rest, s)` with plain parameters | **landed 2026-09-05**: a varying parameter is generalized into the motive by the elaborator (`docs/ih-generalization-design.md`); the realized file still writes the old shape until `issues/uncurried-recursions-library-sweep.md` | closed |
| `fn run(toks, s)` uncurried | **landed 2026-09-05**, same mechanism at `fn` level | closed |
| calc steps that reassociate `++` silently | monoid laws as an ambient simp set the chain applies where they obviously fire | `issues/grind-port.md`, `issues/lemma-selection-and-search.md` |
| `:= compile_pushes_eval(l)` (endpoints fill the arguments) | unification-driven instantiation of a calc-step justification | `issues/elab-unifier-completeness.md` (nearest) |
| no `cong_run` anywhere | congruence inferred from the goal's shape | `issues/congruence-by-anti-unification.md` |
| `heather disprove '…'` at the shell | counterexample search before anyone pays for a proof | `issues/heather-disprove.md` |
| `n :: s` cons notation | finite construction is now `[TPush(n)]`; infix open-tail cons remains absent | `issues/notation-extensibility.md` |
| `Result`, `?`-chaining, `.map` | **landed 2026-09-14** via `import result;`, function/lambda-scoped propagation and explicit `Ok`; runnable parser and recursive collection in `result_parser.hthr` | `issues/result-propagation.md`; remaining Option chaining: `issues/prelude-option-and-friends.md` |
| `let b :: a :: s2 = s else { … }` | let-else (the one-non-absurd-branch match) | `issues/let-else-sugar.md` |
| `String`, `.chars()`, `[c, ..rest]`, `if c.is_digit()` guards | strings, slice patterns, match guards | no owner yet |
| `decreases ts.len()` on mutually recursive parsers | **realized 2026-09-15** in `calc_parser.hthr`: three adjacent proof-carrying recursive functions use checked consuming recognition for their decrease. Production composition constructs independent source-span derivations; the public parser projects ordinary results. Certificate ergonomics and group unfolding equations retain their own owners. | `issues/showcase-token-parser.md`, `issues/group-unfolding-equations.md`, `issues/omega-renders-member-by-base-name.md` |
| `"{src} = {eval(e)}"` | string interpolation | no owner yet |
| `datarepr Nat = repr::BigNat` | runtime representation chosen per type, linked by certified refinement | `issues/datarepr-separation.md` |
| `derive instance Compile[Cpu] for eval` | **half landed 2026-08-14**: tier-1 source types are in the generator's fragment (`docs/certgen-tier1-source-types-design.md` — an `eval`-shaped recursion over an `Expr`-shaped type generates a kernel-checked `Compile` instance end to end). Still missing here: the `derive` surface and the `Compile` class (their own row), and `run` — blocked by four independent certgen declines even after hand-monomorphization (probed 2026-08-15: tier-1 constructor fields at a *third* inductive — the binding one; recursive tier-1 results; non-`Nat`-field results like `Option<List<Nat>>`; the curried result), not only the parameterized-instantiation name gap | `issues/compile-typeclass-design.md`; `run`: `issues/datarepr-separation.md` |
| `Compile[Cpu]` as a class | the Compile typeclass and certificate coupling | `issues/compile-typeclass-design.md` |
| `runtime_fn main`, `IO`, `println` | the effects story and the kerneltime/runtime rim | `issues/effects-direction.md` |

## Frictions found while writing the realized file

Recorded here because "it checks" hides them:

1. **A parameter named `code` cannot be matched on.** `match code {` parses
   as the quotation form `code { … }` and dies with ``expected `}` to close
   the quote`` — a baffling message for an ordinary variable name. The
   realized file renamed the parameter to `toks`. Filed:
   `issues/match-scrutinee-named-code.md`. **Resolved 2026-08-16**: the
   quotation now stands down wherever the `{` belongs to the enclosing form
   rather than to the payload — the condition `no_record_lit` already marked
   for record literals — and `match code as λ z => T { … }` was found to be
   the same gap one form up. `match code { … }` and `match code as …` are
   ordinary matches on an ordinary variable; a quotation that really is the
   scrutinee is parenthesised, as a record literal there already was.
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

The realized calculator and its token parser are checked by the ordinary test
suite as of 2026-09-15 (`crates/elab/tests/showcase_calculator.rs`). The
idealized file remains a design sketch and is deliberately excluded.

**`mul` moved to `std/nat` on 2026-08-13** (`issues/std-nat-multiplication.md`),
with the lemma kit and the `CommMonoid<Nat>(mul)` instance the library wanted
anyway; `calc.hthr` dropped its own `mul` and its `*` row and takes both from
`std/algebra`. The deferral paragraph that stood here was **wrong about the
mechanism**, and the correction is the better datapoint: a module-local `fn`
*shadows* an imported one rather than colliding with it, so the byte-pinned
`fn mul` fixture in `crates/elab/tests/certgen.rs` would have gone on working,
silently meaning something other than what it read as. That is the module-scope
argument this paragraph was reaching for — fixture programs and the library
share one namespace, and the sharing resolves without a word. The fixture was
renamed `viaadd` for exactly that reason; the pins moved by name only.

## Finite-set client exploration

[`finite-sets-idealized.hthr`](finite-sets-idealized.hthr) is a separate
client-first design sketch for relational abstraction, ahead of an implementation.
It deliberately does not check and has no realized counterpart yet.
[Its design analysis](../finite-set-client-design.md) works backward from the
client to certificates, dependent membership transport, and proof opportunities.

For a smaller introduction and syntax critique, see
[three small transfer experiences](../three-small-transfer-experiences.md):
one set function, one positive-natural function, and one rejected/repaired
cardinality implementation. These are proposed examples, not checked programs.

## Writing your own thing with laws

[Mergeable summaries](your-own-thing-with-laws.md) walks through defining a
relation-indexed class, supplying two implementations, proving a reusable
repeated-delivery law, and reporting unfinished proof fields. The snippets are
illustrative and unverified. Exact obligation display is the baseline;
bounded counterexample search is an optional improvement.

## Realized Mergeable foundation

[`mergeable.hthr`](mergeable.hthr) is the checked manual counterpart to
[the user-authored law interface](your-own-thing-with-laws.md). Its library
closure and every showcase declaration run in `lib_setoid_mergeable`:

```console
furnace run -- scripts/test -p heather-elab --test lib_setoid_mergeable
```

[The implementation record](../manual-mergeable-round.md) contains the gap table,
explicit compatibility proof, and acceptance boundaries. The broader idealized
finite-set and subtype examples are still design sketches.

## Composed relational contexts

[`relational_contexts.hthr`](relational_contexts.hthr) constructs a certificate
for `known ++ (incoming ++ incoming)`, applies a local law beneath that whole
context, and states the extra evidence required by a surrounding observer.
It runs in `lib_setoid_mergeable`; [the round notes](../relational-context-round.md)
explain the proof rules and remaining automation work.

```sh
scripts/showcase check relational_contexts
```

## Bounded certificate-generation prototype

[`relational_generator_input.hthr`](relational_generator_input.hthr) is ordinary
client source for `scripts/relational-context-demo`. The driver can emit a checked
preservation definition, expose a missing observer contract, resume with supplied
evidence, or leave raw length unproved. [The generator round](../relational-generator-round.md)
documents the explicit request API and its source-level prototype boundary.

[`relational_generator_generated.hthr`](relational_generator_generated.hthr)
is the saved success output, including the generated `receive_generated`
certificate. It can be checked directly as an ordinary Heather module.

## One contextual rewrite

[`contextual_rewrite_input.hthr`](contextual_rewrite_input.hthr) contains a theorem
with a single goal hole. The source driver selects its proof parameter, recovers
the shared context, and fills the hole with a checked certificate application.
It is input to `scripts/relational-context-demo rewrite`, not a completed module
until the driver fills that hole. [The round notes](../contextual-rewrite-round.md)
cover partial occurrences, missing observer evidence, and the bounded fragment.

The [saved generated theorem](contextual_rewrite_generated.hthr) contains the
ordinary proof emitted by the driver and is independently checked.

## Relational congruence in a proof

[relational_proof.hthr](relational_proof.hthr) uses a supplied idempotence proof
inside `merge_twice` and discharges a missing observer certificate with an
ordinary `on` clause. See [the round notes](../proof-position-relational-congruence.md).
