---
title: Move mul into std/nat with a proper lemma kit
status: closed
labels: [library,traits]
created: 2026-08-13
updated: 2026-08-13
---

`lib/std/num/nat.hthr` stopped at `add`. `docs/showcase/calc.hthr` declared its own
`mul` and its own `designation * at Nat := mul` because of that, and
`docs/showcase/README.md` recorded the deferral: the library name was believed
to **collide** with `crates/elab/tests/certgen.rs`'s `fn mul` fixture, which
elaborates on top of the `ir_v1`+`nat` prelude and whose emissions are pinned
byte-for-byte under that name.

Scope: `mul` and a lemma kit paralleling `add`'s in `std/nat`, a
`CommMonoid<Nat>(mul)` instance and a `*` designation in `std/algebra`, the
showcase file reduced to the library's, and the fixture-name question settled
one way or the other.

## What it assumes from elsewhere

- **[[certifying-generator]]** owns the generator and its byte pins. Assumed
  here: only that the `IR_*` literals are a pin on the *generator's* layout and
  must not become a pin on library text.
- **[[surface-operators]]** / `docs/language/classes/operators-onto-classes-design.md` own the
  symbol ladder. Assumed here: only that a `designation` outranks a file's own
  same-named global, which is what makes the `*` row a real decision.

## Log

### 2026-08-13 — LANDED

**The collision is not one, and that is the round's first finding.** A
module-local `fn mul` *shadows* an imported one; it does not error. Checked
directly:

```
import nat;
fn mul(a: Nat, b: Nat) -> Nat { 7 }
theorem shadowed(): mul(3, 3) = 7 { refl }     // ok
```

So the fixtures would have kept working untouched. `docs/showcase/README.md`'s
deferral paragraph was wrong about the mechanism and is corrected in place. The
module-scope datapoint it wanted is still there, and sharper: fixture programs
and the library share one namespace, and the sharing is resolved *silently*.

The second half of the same probe is the reason the round did not simply leave
things alone — with `std/algebra` imported, `*` at `Nat` is **not** the local
`mul`:

```
import nat; import algebra;
fn mul(a: Nat, b: Nat) -> Nat { 7 }
theorem star_follows_scope(x: Nat): x * x = 7 { refl }   // NotConvertible
```

That is the ladder working as designed (designation, then the file's own name,
then the fallback) and it is already pinned by
`crates/elab/tests/operators_onto_classes.rs`. Recorded here because it means
one file can hold two meanings of the same spelling — `mul(x, y)` the local and
`x * y` the library's — which is exactly the reading confusion a shared name
buys.

**DECISION: (a), rename the fixture; `std/nat` owns `mul`.** Rejected (b), the
fixtures using the library's `mul`: the `IR_*` literals are a pin on the
transcriber's layout, and routing them through library text means any future
edit to `std/nat`'s `mul` — a different recursion argument, a tail-recursive
spelling — breaks generator pins for a reason that has nothing to do with the
generator. The two programs also *want* opposite spellings, which is the
clinching argument: the fixture's step is `add(a, mul(a, k))` because that is
the cross-function shape it exists to pin (and its zero arm spells `Zero`, not
`0`, deliberately), while the library's step must be `add(mul(a, k), a)` for
its lemma kit (below). Two different programs, so two different names.
Rejected the do-nothing option for the reading reason above: a byte pin named
`mul_gen_body` that is not about the library's `mul` is a trap.

The fixture is `viaadd`, after `certgen_nonnat.rs`'s `viafield`/`viaflag`
naming — it says what the fixture is *for* (a foreign call whose argument is
the self-call's result) and cannot be claimed by a future library. The pins
moved by name only: the closure is in dependency order (callees before self),
so `["add", "viaadd"]` keeps `add` at index 0 and the self-call at 1, and every
instruction, slot and arm is byte-identical to the `mul` pins.

**The spelling `std/nat`'s `mul` gets, and why.** `mul` recurses on its SECOND
argument like `add`, and the step is `add(mul(a, k), a)` — the recursive result
on the LEFT. Same reasoning `add`'s own comment gives for `Succ(add(a, k))`:
put the step's `add` on the argument `add` itself descends on, so the zero side
stays definitional. `mul(a, 0) ↝ Zero` and `add(x, 0) ↝ x` both reduce with no
lemma, and that one choice is what makes

- `mul_left_zero` a bare self-call (no `cong`), and
- the zero arm of `mul_add_distr` a `refl`.

Spelled `add(a, mul(a, k))` instead, every proof in the section pays an
`add_left_zero` rewrite it does not otherwise need.

The kit, in dependency order: `mul_left_zero`, `mul_left_one`,
`mul_succ_left` (`add_succ_left`'s counterpart, and the only proof over three
lines), `mul_add_distr`, `mul_assoc`, `mul_comm`. `mul_assoc` is an instance of
`mul_add_distr` rather than the other way round, so distributivity comes first.
All six checked on the first run.

`std/algebra` gains `instance CommMonoid<Nat>(mul)` and
`designation * at Nat := mul`. The instance is worth reading beside `add`'s for
the reversal: there `unit_r` is the free `refl` and `unit_l` the lemma; at `mul`
it is the other way round, and `unit_r` is filled by an **`add`** lemma —
`mul(x, 1)` reduces to `add(0, x)`, so `unit_r := add_left_zero`. Nothing about
the class's `unit: A` field had to bend to hold `1`: it is a plain value slot,
and `Monoid` hardcodes nothing about the unit beyond the two laws.

`docs/showcase/calc.hthr` drops its `mul` and its `*` row and takes both from
the library; re-checked by hand per its README (`heather check -L lib/std`,
ulimit-wrapped): ok. `docs/showcase/idealized.hthr` never declared `mul` — it
assumed `*` worked — so one more idealized-file line is now true, and the
README's "What already matches" no longer has to qualify `*` as
showcase-local.

**One test needed a real repair, and it is the round's best evidence that the
`*` row is a decision rather than a formality.**
`crates/elab/tests/operators_onto_classes.rs`'s
`a_symbol_with_no_rung_names_the_symbol` asserts that `x * y` at `Nat` refuses
by naming the symbol, on the stated premise that "its fallback name `mul` is
nowhere". With `std/nat` owning `mul` that premise is false in every module
that imports `nat` — the third rung finds it, the theorem becomes a real goal,
and the test's `?p` reports an unsolved hole instead. Repaired by giving that
one probe a harness (`without_nat`) that elaborates `bool`/`option`/`list` and
a one-row designation table but **not** `nat`; `Nat` is a kernel type and needs
no import, so the carrier, the diagnostic and both "where `*` does mean
something" assertions survive intact. The test now tests what it says.

Files: `lib/std/num/nat.hthr`, `lib/std/algebra/algebra.hthr`, `lib/certgen/certgen_code.hthr`
(`mul_transcribes` → `viaadd_transcribes`, a name and its comment; the theorem
pins markers and never mentions the fn), `crates/elab/tests/certgen.rs`,
`crates/elab/tests/certgen_emissions.rs`,
`crates/elab/tests/operators_onto_classes.rs`, `docs/showcase/calc.hthr`,
`docs/showcase/README.md`.

Verification: full `scripts/test` — **1495 passed, 0 failed, 0 ignored**, the
same count as before the round (nothing new was added; the operators test was
repaired in place, and the six new library theorems are covered by the
whole-closure acceptance `crates/elab/tests/lib_algebra.rs::the_library_checks`
plus every certgen binary's `nat` prelude). `scripts/bench --check`: 18
comparisons within thresholds. Both showcase files re-checked by hand.

Design docs that predate today (`docs/metaprogramming/opaque-globals-analysis-design.md`,
`docs/certgen-cert-expression-design.md@4acf2fe`, `docs/archive/certgen-transcriber-in-language-design.md`,
`docs/certgen-non-nat-embeddings-design.md@4acf2fe`, `docs/certgen-ctor-fields-design.md@4acf2fe`,
`docs/metaprogramming/fn-signature-reflection-design.md`, `docs/metaprogramming/analyzer-evaluation-design.md`)
call the fixture `mul` and are left alone: they are round records, and
rewriting them would falsify what those rounds saw. The forwarding note lives
where a reader arrives — `certgen.rs`'s `VIAADD` doc comment and
`certgen_code.hthr`'s theorem — and names this issue.

`lib/std/num/nat.hthr` is part of `crates/elab/benches/frontend`'s corpus, so that
workload's content grew by six theorems and a `fn`. Expected, not measured:
this round's issue is not performance.
