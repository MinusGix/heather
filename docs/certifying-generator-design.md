# The certifying generator: design sketch (v1)

Status: **design sketch, pre-implementation** (2026-08-01). Written before
the code, per repo discipline; when the implementing round lands, this file
becomes the specification it is checked against.

Tracking issue: `issues/certifying-generator.md`. Adjacent decisions live
where they are owned: the instance shape in
`docs/compile-typeclass-design.md` (a `CompileNat2(f)` record value, ∃-form
certificate), the IR and its proof idioms in `docs/ir-simulate-design.md`
(§13 notes 7–8 especially), the in-language endgame in
`issues/generators-in-the-language.md`, the runtime boundary in
`issues/datarepr-separation.md`.

The design principle, inherited from the issue and **protected against
every choice below**: the generator is untrusted because each output
carries its own certificate. It may be heuristic, incomplete, and wrong —
a bad emission is one whose certificate the kernel refuses, never an
unsound theorem. Consequently the generator is allowed to *decline*
(fragment checks are honest, not load-bearing), and no decision below is
ever justified by "the generator is careful here"; the kernel is the only
careful party.

---

## 1. What the generator is, concretely

Input: one spec function in the supported fragment (§3). Output: the
declarations a human wrote by hand in the milestone round —

1. the IR (`f_ir_body`, `f_prog`-shaped definitions),
2. a fuel-bound function (`f_bound`),
3. the invariant theorem (`f_runs`, the `add_rec_runs` shape),
4. the ∃-form certificate (`f_converges`),
5. the instance value (`f_instance : CompileNatK(f_spec)`), declaring the
   per-arity `CompileNatK` record first if the library lacks it

— such that the whole emission checks with `heather check` appended to the
IR library. The milestone instance is the worked example the generator
generalizes: `lib/ir_v1.hthr`'s cross-IR section is, deliberately, a
hand-run of this generator on `add` (the recursive-`Apply` transcription,
`add_rec_runs`, `add_rec_converges`), and the implementing round's first
acceptance item is reproducing it mechanically.

## 2. Decision: v1 is Rust emitting surface text

Three candidate homes, and the choice is the middle one:

- **The meta layer** (a Heather meta-function over boxed code) is the
  thesis' answer and stays the target, but it is blocked on machinery that
  does not exist: surface quotation, the modal surface
  (`issues/surface-syntax.md` round 2), and the `box_synthesis`-compliant
  elaboration of emitted code. `issues/generators-in-the-language.md` owns
  that ladder and its ch. 07 expressiveness reading. Nothing below
  pre-commits against it: the generator's *phases* (fragment check,
  transcription, bound synthesis, proof schema) are the same program in
  either language.
- **Rust emitting kernel terms** is how every existing generator works
  (tier lowerings, recursors, no-confusion, the container schemas). For
  *this* generator it is the wrong altitude: those artifacts are emitted
  *during elaboration of a declaration* that the surface cannot express
  (a recursor is not surface-statable), while everything the certifying
  generator emits is ordinary surface Heather — the milestone round wrote
  it by hand. Emitting kernel terms would mean hand-maintaining kernel-term
  proof schemas that duplicate what the elaborator already does better,
  and per `docs/testing-generated-terms.md`, generated kernel terms are
  exactly where five live defects hid.
- **Rust emitting surface text** (chosen): the generator is a certifying
  *transpiler*. Its output is a `.hthr` fragment checked by the full
  pipeline exactly as handwritten code is — parse, elaborate, kernel-check
  — so the trust story is the strongest available and the debugging story
  is "read the file it wrote". The CLI round
  (`issues/cli-check-diagnostics.md`) exists precisely so that a real
  Heather file can be checked outside a Rust test; this is its second
  consumer. And surface text is what the meta-layer version will emit
  semantically (code), so the migration is a re-homing, not a redesign.

Cost accepted with the choice: string-level codegen against a surface the
repo owns. Surface syntax changes can break the generator; the acceptance
tests (which `heather check` the output) catch that immediately, and the
emitters are kept schematic (one function per declaration form) so the fix
is local.

**Where the output lands.** There is no module system, so the emission
cannot be a sibling file importing the IR (`compile-typeclass-design` §3
already hit this). v1: the generator produces a text fragment; the harness
checks `lib/ir_v1.hthr` + fragment as one concatenated file. Generated
names are prefixed with the spec function's name (`mul_ir_body`,
`mul_runs`), and the generator refuses a name that collides. A generated
section committed into the library (the way `add`'s hand-run is) is a
by-hand decision, not something the generator does to the repo itself.

## 3. The v1 fragment

A function is in the fragment iff:

- **Signature**: `fn f(a1: Nat, …, ak: Nat) -> Nat`, `k ≥ 1`. `Nat` only —
  per-type embeddings are `datarepr`/`generators-in-the-language`
  territory, and `embed_nat` is the one embedding the library owns.
- **Body**: either non-recursive, or a single `match` on one declared
  parameter whose arms are built from: parameter references, arm-bound
  fields, `Zero`/`Succ` constructor applications, and **self-calls that
  are structural** on the matched parameter (the arm's field, passed in
  the matched position, other arguments unchanged — the same discipline
  `match-recursion` enforces, so anything the surface accepts as a
  recursive `fn` in this shape is already termination-checked).
- **Not in v1**: calls to other functions (even generated ones — bound and
  invariant composition is the designed v2 step, §8), nested `match`,
  `let`, non-`Nat` inductives, multiple results.

The fragment check is a plain syntactic predicate over the parsed surface
AST, and *declining is a supported answer* with a reason string. It is not
a soundness boundary: a bug that lets a non-fragment function through
produces an emission whose certificate fails to check, which the negative
controls (§6) demonstrate on purpose.

## 4. The transcription target: recursive `Apply`, not loops

The generator transcribes the source recursion structurally:

- the function body becomes a one-function `Prog` whose body `match`es the
  recursive parameter's slot (`LetMatch`, one arm per constructor),
- constructor applications become `LetCon` chains,
- the self-call becomes `LetCall 0` on the structurally smaller field with
  the other argument slots re-gathered,
- the result reference chain ends in `Ret`.

The theta-loop `add` in the library is the *better* IR — tail, cheaper
fuel profile — and is deliberately **not** the target. Reasons, in order:

- **The proof mirrors the source.** The invariant of a transcribed IR is
  proved by the same structural induction the spec function performs, arm
  by arm; each arm of the proof replays the arm's instruction chain and
  the self-call lands exactly on the induction hypothesis. A loop-form
  target needs an accumulator invariant (`add_loop_runs`'s generalized
  accumulator) that the source never mentions — invented per function,
  which is the opposite of schematic.
- **Optimization is a pass, certified by refinement.** The cross-IR round
  proved the design's answer end-to-end: the loop IR and the recursive IR
  are related by `RefinesOn` over the calling-convention family, and the
  proof certifies each side against the spec and glues with
  `eval_functional` — no relation between the executions. So the generator
  emits the naive IR with its schematic certificate, and a loopification
  pass (later, possibly hand-written per function for a while) refines it
  *without touching the generator*. `add_instance` vs `add_instance_loop`
  is already the demonstration that two instances for one spec coexist.

Two facts from the hand-run that the transcription schema must respect
(`ir-simulate-design` §13 notes 5, 8):

- `LetMatch` arms are **lexical**, so the transcribed arm's environment is
  `[fields…, matched-slot re-visible, other params…, caller's tail]` and
  every emitted `Ref` is a de-Bruijn *distance* computed against that
  layout. The generator maintains a compile-time slot map per arm; an
  off-by-one here is a `Stuck` certificate failure, not unsoundness.
- The self-call builds a **closed** environment (`LetCall` gathers
  argument slots; the callee sees only them), while the enclosing arm
  still sees the caller's tail underneath. This asymmetry is exactly why
  the invariant quantifies over the tail (§5).

## 5. The certificate schema

**Superseded 2026-08-02 by the v2 ∃-composition schema — see §8 item 1.**
This section describes v1's bounded schema as it landed and is kept because
its two findings (the depth fuel model, and the constants-outside bound
spelling) remain the correct account of *why* the ∃-form won: the bound
spelling below is exactly what fails to compose across a call boundary.

Per generated function, three statements, each schematic in the source:

1. **The bound.** Two `fn`s emitted alongside the IR:

   ```heather
   fn f_lvl(n: Nat) -> Nat {
       match n { Zero => Zero, Succ(k) => Succ(Succ(f_lvl(k))) }
   }
   fn f_bound(n: Nat) -> Nat { add(f_lvl(n), c0) }
   ```

   *(Amended 2026-08-02 by the implementing round — the sketch originally
   put `c0` at `f_bound`'s base case with `add(f_bound(k), c)` in the step
   and claimed that reduces at an open `k`. It does not: at an open `k`
   that spelling is δι-stuck and exposes **zero** leading `Succ`s, so the
   invariant's sub-chains cannot spend fuel in the inductive step and the
   proof's `refl` cannot close. The constant has to ride outside, the way
   the hand-run's `add(dbl(a), 2)` always had it: `add(x, c0)` at a
   literal `c0` is `c0` literal `Succ`s over `x` regardless of `x`.)*

   The per-level cost is exactly 2 (the `LetMatch` and the `LetCall`; the
   fragment's self-call arguments are variables, so no instruction ever
   precedes the call). `c0 = max(2 + |zero chain|, |post-call chain| + 1)`
   — the second operand because the post-call chain runs at the callee's
   fuel, which the recurrence pins to `f_bound(k)`. Fuel is a *depth*
   budget (`1 + max(sub-run, rest)` at branching instructions, since both
   run at the same decremented fuel), which makes the bound exact for
   recursion depth ≥ 1; nothing depends on exactness at 0 — unused fuel is
   free (`ir-simulate-design` §13 note 3), and `conv_loosen` absorbs
   slack.

2. **The invariant** (`f_runs`), the `add_rec_runs` shape: for all
   parameters and an arbitrary environment tail,

   ```
   eval(f_bound(a_r), f_prog())
       (VCons(embed_nat(a_1), … VCons(embed_nat(a_k), tail)), f_ir())
     = Out(VCons(embed_nat(f(a_1)…(a_k)), VNil))
   ```

   proved by induction on the recursive parameter `a_r` with the tail and
   the non-recursive parameters generalized in an explicit motive (the
   surface has this since the fuel-interface round; the generator emits
   the motive text). The tail quantification is forced, not stylistic:
   the self-call's environment is closed (tail = `VNil`), so a
   tail-fixed statement cannot be applied to its own induction hypothesis
   — the hand-run's exact finding. Each arm of the proof is conversion
   (the arm's chain replayed at literal instruction count) around one IH
   application; the base arm is pure conversion ending in `refl`.

3. **The export**: `f_converges` introduces the ∃-form via
   `converges_intro` at the computed bound, and `f_instance` packages
   `prog`/`entry`/`cert` as a `CompileNatK(f_spec)` value, with
   `f_spec` emitted as the curried spelling of `f` (the record's parameter
   is curried; the declared `fn` is not — same move as `add_spec`).
   `CompileNatK` for a new arity `K` is emitted on first need, the §3
   record with `K` argument slots.

What makes this schema credible rather than hopeful: every line of it has
a checked instance in `lib/ir_v1.hthr` today (`add_rec_body`,
`dbl`-as-bound, `add_rec_runs`, `add_rec_converges`, `add_instance`), and
the generator's job is precisely to re-derive that section from `add`'s
source text. Divergence between the two is a test failure with a diff.

## 6. Negative controls (`docs/testing-generated-terms.md`, applied)

The four axes, instantiated for this generator:

- **Literal and neutral**: fixtures check generated IRs at literal
  arguments (a `rec_two_three` analogue per function) *and* the invariant
  itself is the open-argument statement; both land in the acceptance
  harness.
- **Checking position**: the instance value is *checked against*
  `CompileNatK(f_spec)` — the record's `cert` field type is the checking
  position, and it is where a wrong-spec emission must die.
- **Negative controls, mutation-shaped**: the harness perturbs a known-good
  emission and asserts failure — (a) a `Ref` off by one (certificate
  refuses: `Stuck ≠ Out`), (b) the bound short by one (`OutOfFuel`), (c)
  the wrong constructor tag in an arm (wrong value), (d) an instance
  claiming a different spec function (`cert` field fails to check). These
  are cheap: each is one edit to the emitted text plus one expected
  failure.
- **Fragment honesty**: a function outside the fragment (a non-structural
  self-call; a non-`Nat` parameter) is declined with a reason, and — the
  soundness-story control — a *forced* emission for it (test-only hook)
  produces a certificate that fails to check rather than a wrong theorem.

## 7. Deliberately rejected, each with its reason

| Rejected | Why |
| --- | --- |
| Writing the generator in the meta layer now | blocked on surface quotation and the modal surface; owned by `generators-in-the-language`, whose ch. 07 reading is scheduled separately; the phases carry over unchanged (§2) |
| Emitting kernel terms | wrong altitude — every output is surface-statable, and the surface pipeline is the strongest checker available; kernel-term schemas are where generated-term defects historically hid (§2) |
| Theta-loop / optimized IR as the target | invariant stops mirroring the source (accumulator generalization is per-function invention); optimization belongs to refinement-certified passes, proven viable by the cross-IR round (§4) |
| Verifying the generator | the certificate architecture makes it pointless, and the issue's charter says to protect that property; effort goes to the schema, not to proofs about Rust |
| A `∀ fuel ≥ bound` certificate export | the ∃-form is the instance's field type (`compile-typeclass-design` §3); bounds stay private, `conv_loosen` bridges |
| General termination measures (lexicographic, well-founded) in the fragment | the surface's own recursion discipline is single-argument structural; the generator inherits it rather than outrunning it |
| Cross-function calls in v1 | bound and invariant composition through `find_fun` at callee indices > 0 is real design work (§8) and the milestone shape has no instance of it to check against |

## 8. Staged next (recorded so v1's cuts read as staging)

1. **Calls to generated functions** (`mul` via `add`). ~~The caller's bound
   composes the callee's.~~ **Landed 2026-08-02, and the bound does NOT
   compose — the whole certificate schema moved instead.** A caller's
   per-level cost contains the callee's bound at an *open* argument, and no
   reducing spelling exists for that sum (the §5 lvl/c0 trick stops at one
   function). So v2 retires §5's bounded schema wholesale: the invariant is
   stated in the ∃-form (`Converges`), proved by folding the
   **∃-composition kit** — `ret_conv` / `letcon_conv` / `letcall_conv` /
   `letmatch_conv`, proved once in `lib/ir_v1.hthr` — over the instruction
   chain. Each kit lemma takes its `gather`/`lookup` facts as equation
   premises (all `refl` on the concrete-spine environments) and glues
   sub-certificates by raising their hidden fuels to the sum via
   `fuel_monotone`. The self-call's certificate is the induction
   hypothesis; a foreign call's is the callee's invariant **re-derived
   inside the caller's program** (same proof text, program swapped), since
   a certificate is about one exact `Prog` term —
   `issues/prog-extension-lemma.md` is the general answer that retires the
   re-derivation. `Prog` is the ordered transitive closure of callees with
   the prefix property enforced (a DAG that breaks it is declined). Bound
   functions no longer exist; §5 items 1–2 describe the retired v1 schema
   and are kept for the record. Literal fuels survive only in the exactness
   fixtures, computed by a mini-evaluator in the generator. Uniformity
   bonus: zero arms and non-recursive bodies also go through the kit, so a
   call in *any* position is handled identically. The design reading of
   *why* this won — fuel is internal, `Converges` is the possibility
   modality proofs actually work in, and bounds in statements are
   compositional debt — is recorded where the fuel interface is owned:
   `docs/ir-simulate-design.md` §13 note 9.
2. **Other tier-0/1 inductives**: per-type `embed_T` (a derived artifact —
   `generators-in-the-language`'s natural first in-language target),
   `CompileTK` records per signature until bundled records exist.
   **Stage 1 landed 2026-08-12** (`docs/certgen-non-nat-embeddings-design.md`):
   a fragment fn's **result** type may be a tier-0 *enumeration* — non-
   recursive, unindexed, unparameterized, no constructor fields — with
   `{T}_gen_embed` emitted per type and `CompileNatK{T}` per signature.
   `lib/ir_v1.hthr` did not change at all: `Val` is untyped constructor trees,
   so `embed_nat` was already one instance of the scheme rather than a
   primitive. The widening is in-language (`lib/certgen_code.hthr`: four
   walker arms, three signature arms), per the frozen-walker rule, and
   `lib/certgen_cert.hthr` needed **zero** edits. Three stages remain, in the
   order that doc's §8 argues for: constructor **fields**, non-`Nat`
   **parameters** (blocked on `Term::Case`'s lowering, not on effort), and
   **tier-1** source types (whose `Converges` induction is over `T`, not over
   `Nat`, so it is a different `CertOut` shape).
   **Stage 2 (fields) was designed, implemented and deferred again on
   2026-08-13** — `docs/certgen-ctor-fields-design.md`. The re-probe that round
   was chartered to run says the elaboration cliff the non-`Nat` round cut it on
   is gone, and that what defers it now is the transcriber's **in-language
   evaluation** cost: generating a fixture whose body builds a two-field
   constructor exceeds `scripts/test`'s address-space rail, and the fragment
   cannot decline the expensive shapes honestly because `check_sig` accepts a
   declaration by its type. The design is worked out and was kernel-checked end
   to end for a one-field constructor before being reverted; it also carries
   cross-function composition at a non-`Nat` result (that doc's §5), which the
   non-`Nat` round had deferred to land with it. The lever is on
   `issues/certgen-harness-cost.md`.
3. **Loopification as a refinement-certified pass**, hand-run first on one
   generated function against its `add_instance_loop` analogue.
4. **The meta-layer re-homing**, when its prerequisites land. The
   expressiveness reading is now done (2026-08-02, verdict on
   `issues/generators-in-the-language.md`): the v1 fragment here coincides
   almost exactly with what `elim^Trm` can analyze — a fragment function's
   code is `elim_N` + constructors + variables, with no global references,
   which is precisely the shape the recursor does not go neutral on. So
   this generator is a faithful prototype of the in-language version's
   natural first scope, and the blockers that reading enumerates (opaque
   globals, no oracle, no code equality, no context computation) gate the
   *later* stages (§8 item 1's cross-function calls onward), not this one.
   **Landed 2026-08-11**
   (`docs/certgen-transcriber-in-language-design.md`), with one correction
   to the sentence above: "variables" overstated — `elim^Trm` *walks*
   variables but cannot *distinguish* them (the `tm_var` branch abstracts
   over the variable at layer v), so a fifth enumerable blocker gates this
   stage too, closed Rust-side by the marker convention (occurrences
   renamed to closed level-carrying redexes before boxing). Transcription
   moved in-language; the certificate fold stays here for the calculus
   reason that doc's §5 records.

## 9. Acceptance sketch — **landed 2026-08-02**, all five items

1. ✅ The generator is `crates/elab/src/certgen.rs` (a module in `elab`,
   which already owns the syntax dependency and the test harness's
   `Elaborator`), with the four phases as written: fragment check,
   transcription, bound synthesis, proof emission. Public API:
   `generate`, `generate_forced` (the §6 honesty hook), and
   `compile_record(k)` for the per-arity `CompileNatK` records. *Superseded
   2026-08-12* (`issues/retire-rust-transcriber.md` stage 2): the fragment
   check and transcription now live in `lib/certgen_code.hthr`, and the public
   API is `generate_in_language` + `compile_record(k)`; `generate` and
   `generate_forced` are deleted, the honesty hook replaced by the controls
   named in docs/certgen-transcriber-in-language-design.md §5's addendum.
2. ✅ The `add` emission checks against the library support prelude. The
   one divergence from the hand-run, documented here as required: the
   generator transcribes `add` *itself*, which recurses on its **second**
   parameter — so the generated `LetMatch` scrutinizes slot 1 and the
   call gathers `(a, k)` as distances `(1, 0)` — where the hand-run
   transcribed the swapped spec `λ a b. add(b, a)` (theta-loop calling
   convention) and matches slot 0, gathering `(0, 2)`. Same instruction
   chain, shifted slot map, and the generated certificate is about
   `add(a, b)` with no swap. Asserted structurally in the harness.
3. ✅ Three functions with no hand-written certificate: `dbl` (1-ary
   recursive, from the library), `seven` (non-recursive constant), and
   `third3` (3-ary recursive) — emissions check end-to-end, instance
   values included, `CompileNat1`/`CompileNat3` emitted on first need.
4. ✅ The §6 controls in `crates/elab/tests/certgen.rs`: four mutations
   (junk ref → `Stuck`, short bound → `OutOfFuel`, wrong tag, wrong spec
   function on the instance) all refuted; five decline shapes asserted
   with reasons; the forced-emission control (`tri`, a foreign call
   transcribed as a self-call) fails to check rather than proving
   anything.
5. ✅ Budget: the harness is ~16 CPU-s against the 300s rail (measured,
   header note). The support prelude is the library's declarations
   section plus `dbl`/`Converges`/`CompileNat2` sliced by parse span —
   generated code references only declarations, never a library theorem,
   so the harness never pays the full-file elaboration.

One design-level finding from the round, folded into §5 item 1: the fuel
bound's base constant must ride *outside* the recursive spelling
(`add(f_lvl(n), c0)`), or the bound is δι-stuck at an open argument and
the invariant's inductive step cannot spend fuel. The sketch had this
wrong; the hand-run always had it right.

## 10. Open questions

- **Invocation surface.** v1 is harness-driven (a test/CLI hook that reads
  a file, generates, checks). Whether the CLI grows a user-facing
  `heather generate` subcommand before the meta layer obsoletes it —
  decide when someone other than the harness wants it.
- **Emission determinism.** `issues/elaboration-determinism.md` will
  eventually want the generator deterministic for artifact keying; v1
  emits deterministically by construction (no maps iterated in
  nondeterministic order — enforce casually now, formally then).
- **Slot-map convention.** Whether the transcriber's environment layout is
  specified normatively here or read off the emitted `add` (acceptance
  item 2 forces them to agree); leaning: the code comments own the layout,
  this doc owns only the lexical/closed asymmetry it must respect.
  *(Corrected 2026-08-11: with two transcribers the layout is an
  **interface**, not a comment — `lib/certgen_code.hthr`'s header states the
  two conventions and their meeting point, and the byte-identical-emission
  cross-check is what enforces agreement.
  `docs/certgen-transcriber-in-language-design.md` §§4–5.)*
