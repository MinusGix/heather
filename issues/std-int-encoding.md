---
title: "Int: the encoding choice, and the arithmetic/order kit it costs"
status: closed
labels: [stdlib,design,proofs,performance]
created: 2026-08-16
updated: 2026-09-09
---

**Status (2026-08-17): LANDED and closed** — `lib/std/int.hthr` exists, the
encoding below survived contact unchanged, and its prediction about `add` did not.
Read §"What landed" for both. The text between here and there is the pre-round
design and is kept as written.

There was no `Int`. This issue owns the encoding decision and the kit that
follows from it. It is deliberately **after** the `Nat` and `List` waves
([[std-api-waves]]): it is the first library file whose proof burden is not
three-line induction, so it is worth reaching with the order kit already in
hand.

## The encoding

Recommendation: **`inductive Int { OfNat(n: Nat), NegSucc(n: Nat) }`** — the
Lean encoding, reading `NegSucc(n)` as `-(n+1)`.

Why: every integer has exactly one representation, so structural equality *is*
equality, `absurd` and constructor no-confusion keep working unchanged, and no
quotient type is needed.

The rivals and why they lose:

- **Difference pairs `Nat × Nat` quotiented by `(a,b) ~ (c,d) ⟺ a+d = c+b`** —
  mathematically the prettiest, and it needs quotients, which do not exist
  ([[setoid-auto-lifting]] is the substitute and is a much larger commitment
  than an encoding choice).
- **Sign plus magnitude** (`Neg(Nat) | Zero | Pos(Nat)`, or a `Bool` sign
  field) — two representations of zero in the naive spelling, junk values, and
  every lemma pays for them.
- **Binary/two's complement** — a *runtime representation*, which is
  [[datarepr-separation]]'s business, not the spec type's. It should arrive as
  a `Compile` instance over the canonical form, not replace it.

## What it costs, which is the point

`Int::add` is a four-way split whose mixed-sign cases route through `Nat`'s
`sub` and a comparison, so `add_comm` and `add_assoc` are **not** three-line
inductions — they are case analyses with a `sub` lemma at the bottom of each.
That is why the file is worth writing:

1. It is the best available **realistic checking-speed workload** — proof
   volume from a real development shape rather than from a benchmark fixture.
2. It measures how much the absence of [[grind-port]] / an `omega` actually
   hurts, on the arithmetic where such a tactic earns its keep.
3. It cashes `Nat`'s `sub` kit, which [[nat-order-kit]] adds and which nothing
   else in the library currently stresses.

Under Prop-first the order story is *cheaper* here than it would have been:
one relation stated once, rather than a `leb`-shaped pair per sign case.

## Sketch of the kit

`neg`, `add`, `sub`, `mul`; `add_comm`/`add_assoc`/`add_zero`/`add_neg`
(making it the first `Group` instance the algebra module could carry — worth
checking whether `Group` should exist before this lands);
`mul_comm`/`mul_assoc`/`mul_one`/distributivity; `Le`/`Lt` and their kit;
`ofNat`/`toNat` and the embedding lemmas connecting them to the `Nat` kit.

## What it assumes from elsewhere

- **[[nat-order-kit]]** owns `Nat`'s order and `sub`. Assumed here: only that
  the `sub` cancellation lemmas exist, since the mixed-sign cases are stated
  in them.
- **[[datarepr-separation]]** owns runtime representations. Assumed here: only
  that a machine-integer representation is its business and not an argument
  about the spec encoding.
- **[[std-api-waves]]** owns sequencing. Assumed here: only that this comes
  after the `Nat`/`List` waves.

## What landed (2026-08-17)

`lib/std/int.hthr`, new, 1093 lines / 97 declarations (1 inductive, 13 `fn`, 75
`theorem`, 5 instances, 3 designations), plus
`crates/elab/tests/lib_std_int.rs` (four tests: the closure checks, the law kit is
present at open integers, the API computes and the operators/instances resolve in a
file that also imports `nat`, and a false equation at closed integers is refused).
`lib/std/algebra.hthr` gained a `Group` class and one generic theorem; see §Group.

**The encoding survived contact, unchanged.** `inductive Int { OfNat(n: Nat),
NegSucc(n: Nat) }`. Every reason this issue gave held up in the writing, and two
of them paid more than predicted: `absurd`-free refutation (a wrong-sign
hypothesis unfolds to `False`, so it *is* the proof, exactly as `nat`'s order kit
has it), and — the one nothing predicted — **`NegSucc(n)` is definitionally
`neg(OfNat(Succ(n)))`**, because `neg(OfNat(k))` is `negOfNat(k)`. That single
convertibility is what makes the sign cases of `mul` affordable: a stuck product
under a `negOfNat` needs no case analysis, `mul_neg_l`/`mul_neg_r` move the sign
out at an open payload, and the eight cases of `mul_assoc` are each two or three
rewrites onto `nat::mul_assoc`.

**The prediction about the operations did NOT survive, and that is the round's
main design datum.** §"What it costs" said `Int::add` is a four-way split whose
mixed cases route through `nat::sub` and a comparison, so `add_comm`/`add_assoc`
would be case analyses with a `sub` lemma at the bottom of each, and §"What it
assumes from elsewhere" made `nat`'s `sub` cancellation kit the assumption. Both
are wrong, and not because the encoding is wrong — because the *definition of
`add`* is a free choice the encoding does not force:

```heather
fn addNat(a: Int, n: Nat) -> Int { match n { Zero => a, Succ(k) => isucc(addNat(a, k)) } }
fn subNat(a: Int, n: Nat) -> Int { match n { Zero => a, Succ(k) => ipred(subNat(a, k)) } }
fn add(a, b: Int) -> Int { match b { OfNat(n) => addNat(a, n), NegSucc(n) => subNat(a, Succ(n)) } }
```

`add` is iterated `isucc`/`ipred`. It is extensionally the same function as Lean's
`subNatNat` spelling and it computes just as well at closed arguments, but the
proof burden is different in kind: **no truncated subtraction appears anywhere in
the file, and `nat::sub`'s cancellation kit is never used**. What replaces it is
four push lemmas — `add_isucc`, `add_ipred`, `isucc_add`, `ipred_add` — after
which `add_comm`, `add_assoc`, `neg_add` and distributivity are each a single
induction whose arms do no arithmetic of their own.

So the correction to record for anyone reading the recommendation later: the
encoding decision is settled and the *operation* decision is separate, was not
made here before, and is worth as much. The cost of the swap is that this file
does not cash `nat`'s `sub` kit — reason 3 of §"What it costs" is void — and
nothing else in the library cashes it either, which is now [[nat-arithmetic-kit]]'s
datum rather than this issue's claim.

**`Int` has no structural recursion of its own**, and that shaped the file more
than any language gap. It is a two-constructor *non-recursive* declaration whose
payloads are `Nat`s, so every proof by induction descends on a payload, and the
guard rightly refuses to call that a descent on the integer. The file therefore
states the induction principle once, as `int_ind` (two base cases — `OfNat(0)` and
`NegSucc(0)` — and two steps), and every law that needs induction is one
application of it. The alternative, two payload-keyed companion lemmas per law,
would have roughly doubled the declaration count. This is not a language gap and
is not filed as one; it is what an `Int` induction principle *is*, and it is worth
saying because a reader coming from `Nat` will expect `match a { … }` to carry an
IH and it never does.

### The kit, against §"Sketch of the kit"

Everything the sketch named, and the order kit is the part that came in cheaper
than expected (four cases, no arithmetic, six of transitivity's eight cases closed
by computation):

- `neg`, `negOfNat`, `toNat`, `isucc`, `ipred`, `add`, `sub`, `mul`, `Le`, `Lt`,
  `le_dec`, `int_ind`.
- group kit: `add_comm`, `add_assoc`, `add_zero`, `zero_add`, `add_neg`,
  `neg_add_self`, `neg_add`, `neg_neg`, `sub_self`, `sub_zero`, `neg_unique`.
- ring kit: `mul_comm`, `mul_assoc`, `mul_one`, `one_mul`, `mul_zero`, `zero_mul`,
  `mul_neg_l`, `mul_neg_r`, `mul_neg_one`, `mul_isucc`, `mul_ipred`,
  `mul_ofnat_succ`, `mul_add_distr`, `add_mul_distr`.
- order kit: `le_refl`, `le_trans`, `le_antisym`, `le_total`, `le_dec`,
  `le_of_not_le`, `lt_isucc_self`, `lt_irrefl`, `le_of_lt`, `le_isucc`, `le_ipred`,
  `le_neg`, `add_le_mono_r`, `add_le_mono_l`.
- embedding: `ofNat_add`, `ofNat_mul`, `ofNat_le_iff`, `ofNat_lt_iff`,
  `zero_le_ofNat`, `negsucc_le_ofNat`, `toNat_ofNat`, `ofNat_toNat`.
- instances: `CommMonoid<Int>(add)`, `CommMonoid<Int>(mul)`, `Group<Int>(add)`,
  `Default<Int>`, `Cmp<Int>`; designations `+`, `*`, `<=` at `Int`.

**Cut, and why:** `min`/`max` (they are `Cmp`'s `max_of` at this carrier and a
bespoke pair would need its own lattice kit for no new information); `lt_trans`
and a full strict kit (`Lt` is a definition, so its facts are `Le`'s read at
`isucc`, and three of them make the point); `le_mul_mono` (needs a `0 <= k`
hypothesis and is the first lemma here whose statement is *about* signs rather
than through them — the natural next item); anything division-shaped, which
[[std-api-waves]] excludes by name.

**Stalled, not worked around:** `instance(a, b: Int) Decide<Le(a, b)>`
([[instance-key-collides-across-modules]]). The file carries a comment where the
instance would be.

### Group

The issue asked whether `Group` should exist before this lands. **Yes**, and it is
written: `class Group<A>(op as ∙) extends Monoid<A>(op)` with `inv`, `inv_l`,
`inv_r` stated over the *inherited* `unit`, plus one generic consequence
(`op_inv_unique`) which `std/int`'s `neg_unique` instantiates by resolution with
nothing re-proved. `Int` under `add` is its first and only carrier — `Nat` and
`Bool` have no inverses under either operation and `append` has none at all — so
the class is one carrier wide, which is exactly the shape a chain member should
have when a new carrier earns it. The instance is three lines because the monoid
half comes from the canonical `CommMonoid<Int>(add)`; writing it again is refused
([[inherited-field-override-owes-conversion]]).

### Cost of checking, which was the other thing this round was for

Not a perf round, so no protocol and no numbers beyond the shape (CLAUDE.md).
`heather check lib/std/int.hthr` is ~1.4 s against ~0.85 s for its import closure
alone (`algebra`, which pulls in all of `lib/std`), so the file's own elaboration
and kernel checking is roughly half a second for ~90 declarations at this proof
density — the same order as `lib/std/list.hthr` and two orders below
`lib/ir_v1.hthr`. **No pathology to file.** The three things that might have cost
and did not: the eight-case `mul_assoc` (each case is shallow), the 51 written
motives (a motive is a type, not a search), and `int_ind`'s value-parameter motive
(instantiated once per use). `scripts/bench --check` is clean, as expected for a
round that does not touch the kernel.

## The ranking this round produced

1. **[[nested-match-on-field-binder-motive]]** (filed). A motive-less `match` on a
   constructor *field binder* gets a non-dependent motive, because tier-0 field
   binders are projection aliases and motive synthesis only abstracts a variable.
   Fourteen hand-written motives in this file are purely this, and it is the one
   defect that makes a *correct* proof fail — as an unlocalized kernel
   `NotConvertible`. Very likely the same fix as the list round's #1
   (`goal-motive-by-scrutinee-abstraction`, which is not in this worktree, so its
   count could not be updated — coordinator, please merge).
2. **[[motive-application-hides-hypothesis-type]]** (filed). An induction
   hypothesis's type inside `int_ind` is the motive *applied*, a β-redex, so
   implicit arguments cannot be read off it and `cong_int(isucc, ih)` is refused.
   Ten sites, each paying `@cong_int` with both endpoints restated. This is the tax
   on *having* to state your own induction principle, and it will hit every
   future carrier that is not a kernel type.
3. **[[instance-key-collides-across-modules]]** (filed). The only row of the kit
   that could not be written: `Decide` at `int::Le` is refused because `nat::Le`
   holds the key `Le`. Stalled per doctrine — renaming to `Le_int` would register
   the instance and would also cost the carrier its `<=`, which is `std/bool`'s
   existing dodge and the wrong direction.
4. **[[congruence-by-anti-unification]]**, fourth consecutive round, and by far
   its largest customer: 58 congruence applications and four congruence lemmas
   (`cong_int`, `cong_int_of`, `cong_ofnat`, `cong_negsucc`) that exist only to
   move an equation into an argument position. Twenty-three of the 58 additionally
   spell their endpoints because of item 2, so the two issues compound.
5. **[[inherited-field-override-owes-conversion]]** (filed). Cost minutes, not
   lines, and the working spelling is the nicer one — but the rule as written is
   unsatisfiable at a proof field in a proof-relevant theory, and the diagnostic
   leaks a "`refl` needs an expected type" from inside the agreement check.
6. **[[designation-of-lt-unparseable]]** (filed). One token: `designation <` reads
   as a type-parameter list. Consequence is that `<` at `Int` is unwritable in any
   file that also imports `nat`.

Two things that are *not* rankings, recorded because they are the round's
sequencing-relevant surprises:

- **The designations worked, and they retire a naming dodge.** `+`, `*` and `<=`
  all resolve by the operand's carrier, so this file could name its functions
  `add`, `mul`, `neg`, `Le`, `Lt` like a first-class carrier instead of taking
  `std/bool`'s `Le_bool`/`leb_bool` suffixing. What does *not* have an operator —
  every lemma name — is ambiguous by name in a file importing both modules and
  must be written `int::add_comm`, which is [[type-owned-namespaces]]'s case made
  concretely: the ambient namespace now holds two of everything arithmetic.
- **Six of the eight cases of `le_trans` are closed by computation**, and the
  order kit as a whole came in at about a third of the arithmetic kit's size. The
  Prop-first order (`docs/nat-order-design.md`) transfers to a new carrier with no
  new technique, which is the first evidence that it generalizes rather than
  fitting `Nat`.

## Log

- 2026-08-16: Filed out of the std-API design discussion, with the encoding
  recommendation recorded rather than left implicit — the point being that
  the choice is forced by "no quotients" plus "no junk values", so it can be
  settled now even though the round is not scheduled.
- 2026-08-17: LANDED: lib/std/int.hthr (1093 lines, 97 declarations) + crates/elab/tests/lib_std_int.rs (4 tests), and a Group class + op_inv_unique added to lib/std/algebra.hthr. The ENCODING survived contact unchanged, and the unpredicted reason it is cheap is that NegSucc(n) is definitionally neg(OfNat(Succ(n))), which is what makes mul's sign cases need no case analysis on a stuck product. The PREDICTION about the operations did NOT survive: add is iterated isucc/ipred rather than the four-way subNatNat split, so no truncated subtraction appears in the file at all and nat's sub cancellation kit is never cashed (reason 3 of the original cost argument is void). Int has no structural recursion of its own, so the file states int_ind once and every law that needs induction is one application of it. Group exists and Int is its only carrier. Checking cost: ~0.5 s of the file's own elaboration+kernel work on top of a 0.85 s import closure -- no pathology. Full narrative, the kit as written, what was cut, and the six-item ranking are in the body above.
- 2026-08-17: The round's one stalled row LANDED (2026-08-17): `instance(a, b: Int) Decide<Le(a, b)>` is in `lib/std/int.hthr` and the stall comment is out. [[instance-key-collides-across-modules]] carries the narrative.
- 2026-09-09: The original prediction has come true after all: `add` is now the four-way `subNatNat` split (issue [[int-arithmetic-over-nat-primitives]]), because iterated `isucc`/`ipred` cost the magnitude at closed arguments once the kernel could do Nat arithmetic on runs in one step. `subNatNat` is structural on its first argument with the second synchronized, so its cancellation is definitional; nat's `sub` kit is still never cashed.
