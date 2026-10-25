# Which tests are worth having: tests versus theorems

Status: audit 2026-10-24, master 87348e3. Minus took the policy the same
day, with `lib/_tests` for probes (§4.5). Implemented since: the
whole-library gate and its lints (§4.1), the refusal helper (§4.4), and the
float, number, algebra and relation modules migrated (§6). The rest are filed
as issues (§7). Counts come from
`scripts/test-census`, a static read of every `#[test]` fn, so they are
approximate: a few percent of tests land in the wrong kind.

Minus's ask (2026-10-24): look over the testing apparatus. How much of it is
useful, and how much should just be theorems? Which patterns recur that the
tooling, the layout or the library itself should be designed for? His worry
is that we have drifted into testing for its own sake, because every language
PR gets tests even when what they check is a theorem.

`docs/testing-architecture-design.md` (#151) and early cutoff (#157) asked
what the suite *costs*. This note asks what it *buys*, and builds on their
numbers rather than re-measuring.

## 1. Short answer

The worry is right for **library** PRs and mostly wrong for **language** PRs,
but the two have one root cause.

- **Library PRs.** Most of their Rust tests restate the library. They check
  the module (which the library check would do), list its lemma names, prove
  `refl` examples, and restate its theorems at open arguments. A quarter of
  them are refusals that a `¬` theorem would say better. They exist because
  of how the suite is built. A library module is checked by the suite only
  if some Rust test `include_str!`s it, and nothing checks the library as a
  whole. So a new module *needs* a Rust test file just to be checked at all
  (§3.1).
- **Language PRs.** Their tests are mostly worth having. An elaborator
  feature needs positive cases, refusals that name their reason, and the
  axes of `docs/testing-generated-terms.md`. What is wrong is the *form*.
  About 1000 of the 2528 elab integration tests are a Heather program in a
  Rust string handed to `ok(…)`. The Rust adds nothing to such a test, and
  it costs editor support, formatting, renames and linking (§3.3).
- **Rust is the right home for about a third of the suite.** That third is
  kernel property and differential tests, cache and CLI behaviour, syntax,
  elab unit tests, cost counters, and refusals whose reason is the point.

The policy (§5) follows from one rule. **Write the claim in the language
whenever the language can state it.** A positive fact goes in a module. A
negative mathematical fact is a `¬` theorem. A program that should elaborate
goes in a `.hthr` file. Rust tests are for what Heather cannot say about
itself: what the checker refuses and why, what a term looks like, what
something costs, and how the tools behave.

## 2. What the suite is

`scripts/test-census` puts each `#[test]` fn in the first kind that fits:

| kind | what the test does |
|---|---|
| structural | asserts on Rust values: kernel terms, counters, lengths, images |
| refusal with reason | expects failure and checks the message or the error variant |
| accept + bare refusal | accepts some source and expects other source to fail, without checking why |
| bare refusal | only expects failure |
| accept lib/showcase file | only checks a `lib/` or `docs/showcase` file |
| accept only | only hands Heather source to something that must accept it |

At 87348e3 there are 3583 static `#[test]` fns. The suite's "~3700 passed"
also counts generated cases. By area:

| area | tests | accept only | accept file | accept + bare | bare refusal | refusal + reason | structural | other |
|---|---|---|---|---|---|---|---|---|
| elab: language features | 1958 | 936 | 1 | 39 | 112 | 601 | 200 | 69 |
| elab: library modules | 377 | 131 | 14 | 15 | 94 | 71 | 24 | 28 |
| elab: tactics | 131 | 68 | 0 | 0 | 0 | 27 | 14 | 22 |
| elab: native/os | 62 | 23 | 7 | 5 | 7 | 2 | 10 | 8 |
| elab unit (src) | 246 | 18 | 0 | 24 | 13 | 11 | 175 | 5 |
| kernel (tests + src) | 498 | 30 | 0 | 10 | 29 | 6 | 375 | 48 |
| syntax (tests + src) | 180 | 22 | 0 | 5 | 3 | 31 | 108 | 11 |
| cli, cache, export, lsp, numeral | 131 | 11 | 0 | 0 | 2 | 6 | 79 | 33 |
| **all** | **3583** | **1239** | **22** | **98** | **260** | **755** | **985** | **224** |

Three more numbers frame the rest of this note:

- **Test fns contain about 4000 `theorem`s. All of `lib/` has about 2900.**
  About 1200 of the test theorems are `{ refl }`. The suite holds more
  Heather proofs than the library does, in Rust strings.
- **105 test files hand-list library closures**: 891 `include_str!("…/lib/…")`
  lines, written in dependency order. Some carry ordering comments for the
  image cache's sake ("the byte model's modules come last, so the list up to
  `linux_x86_64_wp` stays the prefix other targets replay").
- **Pure-library PRs add Rust tests.** Over the last forty merges, the PRs
  that touched `lib/` and no compiler source still added test lines at
  between a sixth and a half of their library lines. Examples: #137 (Linux
  image), #128 (x86 memory on the byte model), #120 (byte memory), the
  float-arith round, #106, #110.

## 3. What the patterns are, kind by kind

### 3.1 "The module checks" (about 25 library tests)

`the_int_module_checks`, `the_bitvec_module_checks`,
`rationals_and_their_client_check`, and others like them. Each one
elaborates a module, sometimes with its showcase client.

**Why they exist.** No test checks the library as a whole. `heather check
lib/std` is something a round runs by hand. The suite checks a module only
if some Rust file lists it in a `MODULES` closure. The gap is real today:
**`lib/std/os/linux/elf64_load.hthr` is checked by nothing.** The B2 burn
(#156) removed the last test that listed it, and no library module imports
it. It still checks at 87348e3, but nothing would notice if it stopped. That
case shows the rule the suite actually runs on: a library module counts
only while a Rust test names it.

**Verdict.** These tests are redundant once a whole-library gate exists
(§4.1). Until then they are the gate, so keep them.

### 3.2 "The kit is there" (13 library tests)

`lib_std_rat::the_law_kit_is_there` builds `let law0 = Rat::same_refl; …`
over a 130-name list. Ten more files have the same test.

**What it checks.** That names the module declares are still declared. A
rename fails it, and so would any client that uses the name. A deletion
fails it too, though the deletion was deliberate. Nothing else can fail it.
It is a snapshot of the API, kept up by hand. Every new lemma means adding
the name in two places.

**Verdict.** Drop these. Where a name matters to a client, the showcase
client or an example (§3.4) uses it. That is a check with content.

### 3.3 Programs in Rust strings (about 1000 language tests, and most library tests)

```rust
#[test]
fn a_default_reads_the_receiver() {
    ok("
inductive Holder { Hold(n: Nat) }
fn Holder::count(self h: Holder) -> Nat { match h { Hold(n) => n } }
fn Holder::get(self h: Holder, extra: Nat := h.count()) -> Nat { extra }
theorem by_default(): Hold(4).get() = 4 { refl }
theorem by_name(): Hold(4).get(extra := 2) = 2 { refl }
");
}
```

The test is good: it pins elaborator behaviour, and every claim in it is a
theorem the checker decides. The only thing the Rust contributes is "this
must elaborate", and the language already says that by being a source file.
What the wrapper costs:

- No editor, LSP, tree-sitter or formatter support inside the string.
  `scripts/fmt` and `scripts/lib-paths --fix` do not reach it, so the
  lib-layout move (#145) hand-edited 1094 test lines.
- Each helper file grows its own `ok`, `bad`, `check`, `refused`, `elab_err`,
  `fails`, and the census has to rediscover what each one means.
- The program can't be imported, run with `--only`, timed with `--timings`,
  or exported.
- It links into a test binary. The families
  (`docs/elab-test-families-design.md`) contain that cost, but they don't
  remove it.

**Verdict.** Keep the content and change the form: a `.hthr` corpus checked
by one runner (§4.3). Migrate it lazily, when a file is touched anyway. This
is not urgent, but new tests of this shape should go to the corpus once it
exists.

### 3.4 Library facts written as tests (about 85 library tests)

Two shapes recur. `lib_std_float_arith.rs` has both side by side:

- **Computation examples** (`LITERAL`): `theorem third(): Rat::Same(val_or(
  one().div(three()), 99), Rat(1365, 4096)) { refl }`, forty of them. These
  are real theorems. They document behaviour, and they pin that evaluation
  does not get stuck. They should not live in a Rust string.
- **Restatements** (`OPEN`): `theorem add_ok(…): RoundsTo(…) {
  Finite::add_correct(a, b, mode) }`. Each restates a library theorem and
  proves it by citing that theorem. It fails only if the library statement
  changes. It is a statement pin, and it is worth something only for
  headline theorems whose statement is the contract, such as
  `add_correct`. For the rest it is a second copy.

**Verdict.** Ask whether a client would cite it. If yes, it is a library
theorem and goes in the module. Most of these are probes instead: they
check that the concept is pinned down right at particular values, and no
client would cite them. Those go in `lib/_tests` (§4.5), checked by the
library gate. Keep restatements only for headline contract theorems, in the
same place. Drop the rest.

### 3.5 Negative controls (about 260 bare refusals, plus most of the "accept + bare" tests)

This is where "should be a theorem" bites hardest. Negative controls are
necessary. Axis 4 of `docs/testing-generated-terms.md` is right that only a
negative control can tell a type from a quotient of it. But the library
tests write almost all of them as *a refused declaration*, and that is the
weakest way to state one. Across the library test files, refusal call sites
split roughly evenly between "`{ refl }` is refused" (definitional) and "this
term does not prove this statement", with about a tenth "this tactic fails".
Four kinds hide in there, and they want different homes:

**(a) A false mathematical claim. It should be a `¬` theorem.**
`lib_std_float.rs::the_zeros_are_same_but_not_equal` refuses
`Finite::zero(binary32(), False) = Finite::zero(binary32(), True) { refl }`.
That shows only that `refl` fails. The test would still pass if the zeros
*were* equal but not definitionally, or if a lemma name in it had been
renamed. The claim it stands for is a theorem:

```heather
theorem zeros_differ(): ¬(Finite::zero(binary32(), False) = Finite::zero(binary32(), True)) {
    λ h => {
        let signs: (bool::False = bool::True) = cong_fn(λ (f: Finite(binary32())) => f.neg, h);
        j(sym(signs), λ b _ => b.IsTrue(), trivial)
    }
}

// lib_std_creal.rs::same_is_not_identity refuses `ofRat(1/2) = ofRat(2/4) { refl }`.
theorem halves_differ(): ¬(CReal::ofRat(Rat(OfNat(1), 2)) = CReal::ofRat(Rat(OfNat(2), 4))) {
    λ h => {
        let nums: (Int::OfNat(1) = Int::OfNat(2)) = cong_fn(λ (x: CReal) => x.seq(0).num, h);
        omega(nums)
    }
}
```

Both check at 87348e3 (`heather check --cache -L lib/std`, `import list` for
`cong_fn`). A `¬` theorem is a positive check. It can't pass for the wrong
reason, it survives a stronger `refl` or tactic, it sits in the library next
to the law it guards, and clients can use it. The same goes for "a sequence
must be regular" (`¬ Regular(λ n => n)`), "the inverse needs a gap", "`<` is
strict", "a wrong sign is refused" and most `a_wrong_law_is_refused` cases.
For closed computations, the `¬` is decided by evaluation (`refl` on a
`Bool` decision, as in `[[asm-closed-facts-by-evaluation]]`).

**(b) A fact about definitional equality. It belongs in Rust, and only when
it guards something.**
`lib_std_itree.rs::right_identity_is_same_not_equal` refuses
`bind(t, Ret) = t { refl }`. With no funext, the propositional version is
independent, so no theorem can say it. The refusal is the only way to state
it. That is legitimate when it guards soundness or a documented design
choice (here, that `Same` and not `=` is the law). But many of these are
*incompleteness pins*. `nat_parity::the_kit_is_not_definitional_at_open_arguments`
refuses `n.add(n).half() = n { refl }`. That test fails the day the kernel
gets *better*, which turns an improvement into a red suite. Keep the ones
that guard something, and say what they guard. Drop the ones that only
describe today's limits.

**(c) The checker must refuse bad input. This is a language test.** A wrong
proof term, a missing hypothesis, an ill-formed instance. These are
elaborator and kernel tests even when they sit in a library file. They need
the reason pinned (§3.6), and they rarely belong to a library PR. Kernel
soundness is tested where the kernel is.

**(d) Mutation controls on generated or proved artifacts. These belong in
Rust.** In `linux_wp.rs`, the drain loop's exit proof is re-claimed as
"exit 1" and must be refused *by the kernel* (`assert_refused` pins
`NotConvertible`, and rules out an unbound name or a parse error). The same
goes for certgen mutants and the tabulate cross-check. These test that a
pipeline's output is really checked: that the proof is not vacuous. They
are worth keeping. Two notes:
- Where a theorem exists, it says more. `linux_x86_64_determinism` plus
  `drain_runs` proves outright that the program does not exit 1.
- A refusal of the *same proof term* at a changed statement is weak evidence
  of non-vacuity. It shows that this term doesn't prove that claim, not that
  the claim is false. The mutation is strong only where the change goes
  *through* the proof, as the exit-status edit does.

### 3.6 Bare refusals (about 260 tests, plus about 100 mixed)

A test that asserts only `is_err()` passes whenever elaboration fails for
*any* reason. A renamed lemma, a missing import or a parse error turns it
green-by-accident, and it stays green while testing nothing. `linux_wp.rs`'s
`assert_refused` is the antidote, and its doc comment says why: "the first
error is the kernel's or the checker's refusal, not a missing name or a
parse". Only that one file uses the idea.

**Verdict.** Every refusal names its reason: a message fragment, or at least
a refusal class (kernel, elaborator, resolution, parse) through a shared
helper (§4.4).

### 3.7 What is already right

- **Kernel tests** (`crates/kernel/tests`) are property and differential
  tests that cite the lemma of DeLaM ch. 05/06 they check
  (`ch05_06_lemmas.rs`, `docs/ch05-06-lemma-audit.md`). The kernel can't
  vouch for itself, so Rust is the right home. Their long-term replacement is
  theorems about the kernel model in Heather (`hih-kernel-model`, #155), not
  fewer tests.
- **`docs/testing-generated-terms.md`'s axes** are why language PRs have
  many tests. Each axis has caught a real defect. Keep them, and note
  axis 4's best form is a `≠` theorem where the type can state it.
- **The showcase manifest** (`docs/showcase/showcases.tsv`,
  `crates/cli/tests/showcase.rs`) is the model for §4.1. A file that isn't
  gated fails until it says how it is gated.
- **Refusals with reasons** (about 750), **structural tests** (about 1000),
  **CLI and cache behaviour**: these are what Rust tests are for.

## 4. What to design for

### 4.1 A whole-library gate

Implemented: `crates/cli/tests/library.rs`. One measurement shaped it: a
cold `heather check lib` in one process at width one takes about the whole
300 CPU-s rail, so the gate runs one `heather check` per folder of `lib/std`
and `lib/` (three at a time, one image store, single-flight builds); the
largest folder cold is under half the rail, and a warm run replays in
seconds. `elf64_load` stays: `docs/native-program-logic-design.md` §3 keeps
it for the native rebuild, so it is listed as a kept root with that reason.

The proposal as written:

Add one test that checks every module under `lib/` through the CLI with
`--cache` (as `showcase.rs` does per row), plus a lint that fails when a
`lib/` module is neither imported by another module nor named as a root.
Measured on `lib/std` at 87348e3 (one cloud box, default kernel width), a
warm run, which replays every module image, takes about a tenth of a cold
one. Cold is one elaboration of the library, which a fresh box's suite
already pays more than once (#151 §1). `lib/native`, `lib/lang` and
`lib/kernel_model` sit on top of `lib/std` as extra roots. With it in place:

- A library PR needs no Rust test to get checked. Its theorems are its
  tests, and §3.1's tests can go.
- An orphan like `elf64_load` is flagged the day its last importer goes.

### 4.2 Tests name imports, not closures

`support::library_for(&["rat"])` resolves imports through the loader
(`heather_cli::loader`, which the export sweep already uses), in place of a
hand-ordered `MODULES` list. The prefix key would become the root set, and
the image layer orders it. This removes the 891 hand-maintained lines and
the ordering comments. It also has an effect that #151 §2.2 wants: runtime
loading means a library edit no longer relinks every binary that
`include_str!`s the file.

### 4.3 A `.hthr` test corpus with inline expectations

Put programs that pin elaborator behaviour in `tests/hthr/<area>/*.hthr`,
checked by one runner. A declaration is expected to check unless an
expectation directive above it says otherwise:

```heather
// expect-error: lambda needs a function type
fn f() -> Nat { λ (x: Nat) => x }
```

The runner maps the checker's diagnostics (it already reports every one,
with spans) to declarations. Each annotated declaration must fail with a
matching first error, and every other declaration must pass. Precedents:
rustc's UI tests (`//~ ERROR`), Lean 4's `#guard_msgs`, and Idris 2's
`failing "msg"` blocks.

The in-language version is a `failing "fragment" { … }` block, which would
put refusals in the language itself. Its cost (Minus, 2026-10-24) is noise:
the common case, reading a theorem, gets refusals next to it. The answer is
to separate *where* a refusal lives from *what it is attached to*:

- **The block is legal anywhere, but by convention it lives in
  `lib/_tests`.** The library itself carries only `¬` theorems worth citing.
  A refusal sits next to a theorem only when it *is* the documentation (for
  example, that `≈` is deliberately not `=`).
- **The test names the theorem it guards**: `failing "msg" guards
  Rat::inv_mul { … }`. The LSP shows "2 negative controls" over `inv_mul`
  and jumps to them, so the theorem is still connected to its tests without
  them being next to it in the file.
- **Editors fold failing blocks by default, and doc output skips them**, for
  the few that stay inline.

Corpus first is cheaper and doesn't touch the language. If `guards` turns
out to be the only thing a block adds over a comment directive, the
directive can carry it (`// expect-error(guards Rat::inv_mul): …`) and the
language does not change.

### 4.4 Refusals carry a reason

Implemented: `support::assert_refused(e, name, src, Refusal::Kernel |
Refusal::Mismatch | Refusal::Says("…"))` in `crates/elab/tests/support`. It
also refuses an incidental slip (a parse error, an unbound name, an
unresolved import) unless `Says` asks for it by name. The census lists what
is left (`scripts/test-census --list bare_refusal`).

The proposal as written:

Add `support::refused(src, Reason::Kernel | Reason::Elab("fragment") | …)`,
generalising `linux_wp::assert_refused`. `check-elab-test-families.mjs`
already walks every elab test file, so it can also flag a bare `is_err()` or
`unwrap_err()` whose result goes unread, as a warning list to start with.

### 4.5 `lib/_tests`: theorems that are tests, not library

Minus (2026-10-24): some test theorems about very specific values don't
belong in the mainline library. They are probes that check the concept is
pinned down right in particular cases. They are still useful, even though a
better method would be nicer and isn't always available. So they get a tree
of their own, and the rule for which side a theorem goes on is: **would a
client cite it?** If yes, it is a library theorem, and ideally most tests
end up there. If not, it goes in `lib/_tests`:

- **Layout.** `lib/_tests` mirrors `lib/`, for example
  `lib/_tests/std/num/float/arith_tests.hthr`. Module names are stems and
  the loader searches every folder below `-L` (`docs/lib-layout-design.md`),
  so test modules take a distinct stem (`_tests` suffix) rather than their
  subject's name.
- **Content.** Probes at specific values (§3.4's computation examples), the
  headline contract restatements, refusals and later `failing` blocks
  (§4.3), and `¬` theorems that read better apart from the module.
- **Rules.** Nothing outside `lib/_tests` imports from it (a lint, beside the
  orphan lint of §4.1). The library gate checks each of its modules as a
  root. Its names never reach the library's namespace or the export.
- **Cost.** Opaque proofs don't invalidate dependents
  (`crates/cli/tests/check.rs`,
  `opaque_proof_edits_do_not_invalidate_dependent_module_images`), and
  nothing depends on a test module anyway, so the tree costs importers
  nothing.

`lib/_tests` holds library probes that need the library. `tests/hthr`
(§4.3) holds elaborator behaviour that mostly needs only the prelude. One
runner serves both.

### 4.6 Label incompleteness pins

A kind (b) refusal that pins a *limit* rather than a guarantee gets a
comment naming what it guards, or goes. A test that fails when the system
gets stronger should be a choice, not an accident.

## 5. Policy: what a PR adds

| the PR changes | add | do not add |
|---|---|---|
| **a library module** (`lib/` only) | Theorems in the module when a client would cite them. Probes at specific values and contract restatements in `lib/_tests`. `¬` theorems for false claims a reader might expect. A showcase client when the module is meant for clients. | A Rust test file. Specifically: a "module checks" test (once §4.1 lands), a kit list, `refl` examples in Rust strings, refusals of false claims. |
| **elaborator behaviour** (a feature, a lowering, a resolution rule) | Positive cases as `.hthr` (Rust `ok(…)` until §4.3 exists, grouped into one source per behaviour). Refusals with their reason. The generated-term axes. | Bare `is_err()`. A positive case per Rust fn when one source can hold several declarations. |
| **a tactic or automation** | Corpus cases for what it proves. Refusals with reasons for what it must not. Structural assertions when the route matters (which rule fired, what term was emitted). | A refusal that only shows the tactic failed on a false goal: that is a `¬` theorem, or nothing. |
| **the kernel** | Property and differential tests in Rust, citing the lemma. Later, theorems about the kernel model. | — |
| **a generator or pipeline** (certgen, compile-x86, export) | Mutation controls that go *through* the proof and are refused by the kernel. A determinism or uniqueness theorem where one exists. | A refusal of the same term at a changed statement presented as non-vacuity. |
| **cost** | Counter assertions (`scripts/timings` columns, `stats::`), never seconds. | — |
| **tooling** (CLI, cache, LSP, syntax) | Rust tests. | — |

When a negative control is needed, choose its form in this order:

1. **`¬` theorem**, when the claim is false and Heather can state it.
2. **A refusal with its reason**, when the point is the checker's behaviour
   or a definitional fact that guards something.
3. **A kernel-refused mutation**, when the point is that a generated or
   proved artifact is really checked.
4. **Bare refusal: never.**

## 6. Migration

Done so far: steps 1 and 2, and step 3 for the float modules
(`lib/std/num/float/`). Their four Rust files became four `lib/_tests`
modules of probes, one library theorem (`Finite::zeros_differ`), and one Rust
file of fifteen vacuity refusals, each refused as a checking mismatch or for
a named reason. The closed-value refusals went: a probe at the right value
already pins each wrong one, given that `Rat::Same` tells the two values
apart. A probe was added where none existed (`e2m1_carry_away`,
`e2m1_third_up`, `zero_zero_not_finite`).

Round two did step 3 for the number and algebra stack: `rat`, `creal`,
`int`, `ordered_field`, `semiring`, `order`, `relation`, and the `ring`
tactic's positive cases. Their eight Rust files held 72 tests and about 490
`theorem`s; now seven files hold 27 tests (refusals with reasons, `ring`'s
and the tactics' record-field checks, and one review-lint check), and eight
`lib/_tests` modules hold the probes. `lib_std_order.rs` went entirely: its one
refusal became a `¬` theorem. Kit lists went, the four client showcases moved
to the CLI tier of the showcase gate (so nothing checks a client twice), and
the false claims a reader might expect became `¬` theorems
(`half_not_equal`, `abs_not_identity`, `le_is_not_lt`, `identity_not_regular`,
`mul_le_mono_not_at_negative`, `constant_pullback_not_antisymmetric`).
Pinning reasons showed several refusals failing differently from what
their comments said. Four layer-down refusals (two semiring, two ordered
field) matched `Ring<A>` or `PseudoOrder<A>` inside an implicit-inference
error ("cannot infer the implicit arguments needed for …"), not the missing
instance their comments describe; they now pin the inference error, which
is what one layer down produces. A bare ordered-field "`≤` is not `<`"
refusal is a failed instance search, not a mismatch. And several vacuity
controls are refused by the kernel, not the elaborator: most of `CReal`'s
(its conversion leaves sequence comparisons to the kernel), and three whose
argument mismatches a parameter that mentions an implicit, which is an
elaborator gap
(`issues/implicit-argument-mismatch-reaches-kernel.md`).

Round three did step 3 for the remaining library families: the
interaction trees (`itree`, its traces and simulations, the coinductive
trees, their bridge and `Eutt`), `list`, `list_algos`, `bounded_list`,
`certified_lookup`, `tree`, `bitvec`, `string`, `utf8`, `memory`,
`location`, `nat`'s evidence rules and the kernel model's reduction. Their
probes are eighteen `lib/_tests` modules. `lib_list_algos.rs`,
`lib_std_certified_lookup.rs` and `lib_std_location.rs` went entirely; the
rest keep refusals with reasons, incompleteness pins (each labelled, §4.6),
mutation controls that need a proof to mutate, diagnostics that name a goal,
and the structural and cost tests (`list`'s literal lowering, `bitvec`'s
machine-width costs and depth budget). Three more client showcases
(`itree_client`, `itree_refinement_client`, `memory_client`) moved to the
CLI tier. The wrong values became `¬` theorems, told apart where the type
has no `Decide` instance by a function into `Nat` and `omega`
(`mirror_moves`, `overlap_does_not_read_back`, `le_is_not_be`,
`x80_is_two_bytes`, `refused_is_not_ok`). Pinning reasons found one
refusal passing for an incidental reason: `bitvec`'s "the value's bound is
not `trivial`" control wrote an unqualified `toNat`, so `<` had no meaning
at its carrier and the refusal never reached the claim. And a `decide`
refusal at a string goal spells the literal's kernel encoding
(`issues/decide-refusal-spells-string-literal-encoding.md`).
`lib_setoid_mergeable.rs` stays a Rust file: it tests the relational-context
generator through its Rust API and the elaborator's subtype and `calc`
routes, not the library's facts. Its eighteen bare refusals now name their
reasons.

`lib_algebra.rs` is the traits feature's corpus over the library rather
than a library test, so it waits for the `.hthr` corpus (§4.3); its
refusals already carry reasons.

In order of value per effort:

1. **The whole-library gate and the orphan lint** (§4.1). Small. Then decide
   `elf64_load`'s fate: delete it (the burn's residue) or give it an
   importer.
2. **The refusal helper and the bare-refusal warning list** (§4.4). Small.
   Then fix refusals file by file as they are touched.
3. **The library tests**, one module at a time. Move probes and
   restatements to `lib/_tests`, promote any a client would cite into the
   module, turn kind (a) refusals into `¬`
   theorems, drop kit lists and module-check tests. On the census, about 85
   computation and restatement tests, 13 kit tests, 25 module checks and most
   of the 94 bare refusals in the library area move into Heather or go. The
   library area's Rust test files shrink to what Rust is for: cost and route
   assertions, and kind (b)/(c)/(d) refusals.
4. **`library_for`** (§4.2). Medium. It touches the image keys, so the
   sentinel's exact lane should see one run of it.
5. **The `.hthr` corpus runner** (§4.3). Medium. Then migrate lazily.
6. **`failing … guards` blocks in the language**, living in `lib/_tests`
   by convention (§4.3). Decide after the corpus shows how often the
   directive is used, and whether a `guards` directive is enough.

None of this cuts elaboration work much. The suite's time is the tests' own
modules and the library prefix (#151 §1), and moving a program from a Rust
string into a `.hthr` file elaborates it just the same. What it cuts is Rust
test code, hand-kept lists, tests that can pass for the wrong reason, and
tests that fail when Heather improves. And it puts the library's facts in
the library.

## 7. Issues

- `issues/library-whole-check-gate.md`: §4.1, with `elf64_load`.
- `issues/refusal-tests-pin-their-reason.md`: §3.6, §4.4.
- `issues/library-tests-as-theorems.md`: §3.2–3.5, §4.5 (`lib/_tests`), step 3 of §6.
- `issues/hthr-test-corpus.md`: §3.3, §4.2, §4.3, the `failing` question.
