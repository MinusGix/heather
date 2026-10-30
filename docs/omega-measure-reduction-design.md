# Reducing a measure at a constructor pattern before `omega` reflects it

`issues/omega-measure-at-constructor-pattern.md`. The most common `decreases`
obligation there is — `fn drop1(xs: List<Nat>) -> Nat decreases list_len(xs)`
recursing on the tail — is refused, and every existing `decreases` test
discharges its constructor-pattern site by hand
(`docs/mutual-recursion-design.md` §7 records two of them).

The charter framed this as a **reducer/conversion gap**: the small-step
reducer stops at a stuck `elim_Wf` where conversion reaches
`Succ(list_len(t))`. §1 shows that is false — the reducer reaches the `Succ`
in six steps on the term that matters. What it does *not* reach is a
**spelling**, and that, not reduction, is what the implementation has to
solve. The fix is small and lives entirely in `omega`'s reflection.

## 1. What the probe shows

Instrumented `omega_cert::nat_term_source` and the atom fallback of
`nat_affine_syntax`, over the std modules (scratch test, hand-run and
removed). Skeletons below print term structure only; `Global(397)` is
`list_len`, `Global(396)` is `list::List::len`, `Global(542)` is `nat::add`.

### 1.1 The declaration is lowered twice, and the second message is the one you see

`elab_measure_decl` (`crates/elab/src/lib.rs`) first lowers with `lift = true`:
each site's obligation becomes a theorem of its own,
`drop1#obl_1(h: Nat, t: List<Nat>) : nat::Lt(list_len(t), list_len(Cons(h, t)))`
with body `omega` (`docs/termination-measures-design.md` §4). When the checker
refuses one, the declaration is re-lowered with `lift = false`, obligations
back at the calls. Both attempts fail here; the writer sees the **second**.

- **Lifted attempt — the real failure.** `h` and `t` are Π-bound variables, so
  `Cons(h, t)` is a `Term::Supf` and *both sides spell*. The atom probe fires
  on ``list_len(Cons(h, t))`` and ``list_len(t)``, interns them as two
  unrelated atoms, and `omega` reports no contradiction. The hand-written
  control reproduces it exactly:

  ```
  theorem at_ctor(h: Nat, xs: List<Nat>): nat::Lt(list_len(xs), list_len(Cons(h, xs))) { omega }
  // Omega's real shadow found no contradiction;
  //   atoms [list_len(Cons(h, xs)), list_len(xs)]; residual [0 <= list_len(Cons(h, xs))]
  ```

  while the same statement handed the successor form checks:
  `theorem reduced(xs: List<Nat>): nat::Lt(list_len(xs), Succ(list_len(xs))) { omega }`
  passes. **Reaching the `Succ` is sufficient.**

- **Un-lifted retry — the message that surfaces.** With the obligation back
  inside the arm, `t` is not a binder: §6.3 of
  `docs/inductive-tier1-wf-lowering.md` *aliases* a tier-1 arm's recursive
  binder to `nth^l(⟦List⟧; 1; cs'; ι_0)`. The probe's failing argument is

  ```
  App(App(ElimNat(Succ(Zero)); Var 2); Inl(Triv))   -- nth(…; cs'; ι_0)
    ⇝ … ⇝ Fst(Var 2)                                -- stuck: cs' is neutral
  ```

  so the whole left-hand side is `list_len(nth(…))`, whnf `ElimWf(Fst(Var 2))`
  — a genuine neutral. `display.rs` spells a `Supf` through `ctor_value` but
  has no case for a projection out of a neutral children tuple, so
  `nat_term_source` raises "Omega could not spell a natural expression". **That
  string is about the left-hand side `list_len(t)`, not about
  `list_len(Cons(h, t))`.**

### 1.2 There is no reducer/conversion gap

The earlier hand-run read the un-lifted retry's terms and compared them with
`tail_lt`'s (`crates/elab/tests/mutual_recursion.rs`), which is stated over a
*variable* `t`. Different terms. On the un-lifted term both the small-step
reducer and the value machine are stuck, and correctly so — `elim_Wf` on a
neutral scrutinee has no rule in `reduce.rs` (line 622) or `eval.rs`
(line 1427), and conversion cannot decide it either.

On the term that matters, `SemanticOracle::term_reducts` walks straight
through, and `whnf_term` agrees (value head `Succ`):

```
list_len(Cons(h, t))                                        δ list_len
  ⇝ App(App(Lam(Lam(ElimWf(Var 0))); …); Supf(…))          β, β
  ⇝ ElimWf(Supf(Inr(…); Pair(Var 1; Triv)))                 elim_Wf on Supf
  ⇝ App(App(Case(Inr(…)); Pair(Var 1; Triv)); Lam(ElimWf(…)))   tag Case
  ⇝ … ⇝ Succ(App(Lam(ElimWf(nth(…; Var 0))); Inl(Triv)))    6 steps, head Succ
```

`theorem step_len(h: Nat, xs: List<Nat>): list_len(Cons(h, xs)) = Succ(list_len(xs)) { refl }`
checks today, and so does the `.len()` spelling of it. The reflection is
handed a term whose head *is* a `Succ` after six δ/β/ι steps and interns it as
an opaque atom without ever asking.

### 1.3 The catch: the reduct does not spell, and its payload is not the atom

The trace above ends at a **weak** head normal form. The `Succ`'s payload is
the ih λ applied at the literal index, `(λi. elim_Wf(…; nth(…; cs; i))) ι_0`,
and `spell_term_source` returns `None` for it at *every* step of the trace.
Reducing it further reaches `ElimWf(Var 1)` — which is also what `list_len(t)`
itself whnfs to, and which does not spell either: `list_len(t)` spells only in
its **unreduced** form `App(App(Global(397); …); Var 1)`.

So "reduce the atom, then reflect the reduct" fails twice over: the payload
has no spelling at all, and even if it had one it would be `elim_Wf`-shaped
and would not intern as the same atom as the goal's left-hand side. Atoms are
interned **by their spelling** — `nat_affine_syntax` calls
`atoms.intern_by(|atom| atom.nat_source == nat_source, …)` — so a reduct that
respells is a *new* atom and closes nothing.

The two are convertible, though, and conversion is what bridges them. §2 is
built on that.

## 2. Option A — reduce to discover the shape, convert to recover the spelling

At the atom fallback of `nat_affine_syntax` (`crates/elab/src/omega_cert.rs`)
— the one chokepoint every `Nat` side of every goal and every local fact
passes through — a term that is about to become an opaque atom gets one more
question:

1. **Bounded whnf.** `SemanticOracle::whnf_term` under the
   `STUCK_SPELLING_STEPS` budget of `crates/elab/src/oracle.rs` (the budget
   that exists precisely for this hazard,
   `issues/elaborator-whnf-probes-on-computing-types.md`). Keep the reduct only
   when its head became **arithmetic** — `Succ`, `Zero`, a literal, or an
   `add`/`mul`/`div`/`mod` application. Any other head means reduction bought
   nothing; intern the original term unchanged and nothing moves.
2. **Reflect the reduct structurally**, by re-entering `nat_affine_syntax`,
   which already knows `Succ`, `nat::add`, `nat::mul`, `nat::div`, `nat::mod`.
3. **Re-spell each unspellable leaf by conversion against a candidate.** The
   candidates are generated from the *original* term, which does spell: it is a
   call `g(ā)` one of whose arguments is a constructor value `C(f̄)` (spelled
   by `ctor_value`, so its fields spell too). For each **recursive** field `fᵢ`
   of `C`, the candidate is `g(ā[C(f̄) ↦ fᵢ])`. Accept the first candidate that
   `SemanticOracle::convert_term` says is convertible with the leaf, and
   reflect *it* — spelled, and therefore interned as the atom the other side of
   the goal already has.

### 2.1 A leaf no candidate converts against gets one more reduction

A measure whose unfolding yields *two* successors — `Succ(Succ(size(t)))`, or
`2 * len + 1` written by recursion — leaves the first reduct's leaf at
`u ≡ Succ(size(t))`, which `size(t)` does not convert against. That leaf is
therefore given step 1–3 once more, under a small fixed depth (two), and under
the **same** candidates: they were built from the original term, and they are
the only spellings the rest of the goal shares. Past the depth the original
term is interned unchanged, exactly as when no candidate matched.

Worked, on the three reproducer shapes:

| original atom | whnf head | leaf(s) | candidate(s) accepted |
|---|---|---|---|
| `list_len(Cons(h, t))` | `Succ(u)` | `u` | `list_len(t)` |
| `Cons(h, t).len()` | `Succ(u)` | `u` | `t.len()` |
| `tnodes(Node(l, r))` | `Succ(nat::add(u₁, u₂))` | `u₁`, `u₂` | `tnodes(l)`, `tnodes(r)` |

and the goal becomes `list_len(t) < Succ(list_len(t))` over one shared atom,
which is `reduced` above — a certificate `omega` already produces.

- **Blast radius.** `omega_cert.rs` only. No kernel change, no reduction rule
  anywhere, no other elaborator `whnf` probe sees a different answer. This is
  not one of the 46 probes that issue audited; it is a new call on a path taken
  once per reflected side of an `omega` goal, after the spelling already
  succeeded.
- **Bounded twice over.** One `whnf_term` per atom under a fixed step budget,
  and at most `arity(C)` conversion calls per unspellable leaf. Nothing here is
  a search.
- **Metatheory obligation: none.** Reduction and the conversion test are both
  contained in the kernel's conversion, so the reflected form is convertible
  with the goal's by construction; the certificate is checked at the unreduced
  goal, which `tail_lt` already demonstrates by hand. The kernel re-checks the
  certificate as always, so a wrong candidate is a refusal, never a false
  theorem.
- **Cost.** One guarded branch plus the tests. The charter's expensive half —
  "close the reducer/conversion gap" — is not needed; §1.2 shows there is no
  gap.

## 3. Option B — synthesize the successor where the obligation is stated

The refined measure is built syntactically in
`crates/elab/src/measure.rs::Rewrite::refine` (`e_i = e_{i-1}[patᵢ/vᵢ]`,
`docs/termination-measures-design.md` §3): at the `Cons(h, t)` arm the
statement is the surface expression `list_len(Cons(h, t))`. Option B would
unfold the measure's own definition there and state the obligation at
`Succ(list_len(t))` instead.

Wrong shape for this problem:

- It has to unfold a **user `fn` at the surface**, matching the measure's body
  against the arm's pattern — a second, syntactic evaluator inside a pass whose
  whole discipline is that it only builds surface the writer could have
  written, and whose correctness is otherwise guaranteed by the checker
  refusing what it gets wrong.
- It covers `list_len(xs)` and little else. `xs.len()` is a one-line wrapper
  the reducer walks through in two steps; a measure through a helper (`tnodes`
  above), a two-argument measure (`xs.len() + ys.len()`, `merge`), and a
  non-structural measure (`nat::mod(a, Succ(k))`, `gcd`) each need another rule
  or get nothing.
- It restates the obligation at a form the writer did not write, so every
  existing by-hand `on ?decN := …` is now stated against a different goal.
- It does nothing for the identical failure outside `decreases`: `at_ctor` is
  an ordinary theorem whose proof is `omega`.

Option B is a worse special case of Option A, in a place that cannot see terms.

## 4. Verdict

**Take Option A.** The reduction the obligation needs is the kernel's own and
already reaches the `Succ`; what is missing is that the reflection never asks,
and that the reduct's payload has to be named by conversion rather than by
readback. Option B reimplements a fragment of reduction in the syntactic
lowering, covers one measure spelling, and leaves the non-`decreases`
occurrence of the same defect standing.

## 5. Atom identity

Interning is by spelling (`intern_by` on `nat_source`), and §2 step 3 is what
keeps that sound: a leaf is only ever replaced by a **candidate built from the
original spelled term**, so the string it interns under is one the rest of the
goal produces too. After `list_len(Cons(h, t))` becomes `Succ(list_len(t))`,
the inner spelling is the byte-identical `list_len(t)` the left-hand side
already interned, and the two share an atom.

The hazard is admitting a reduct whose spelling *moves* without buying
arithmetic: it would split one atom into two, or rename an atom that a
writer's `on ?decN := lemma(…)` is stated against. Hence the two guards —
keep the reduct only on an arithmetic head, and never intern a re-spelled
leaf that no candidate matched. `runs`'s `drop_eq(t, rest).len()` reduces to a
stuck `elim_Wf` on a neutral, buys nothing, and must intern exactly as it does
today.

Nothing in this round changes `AtomTable` or `intern_by`.

**Since 2026-09-27** (issues/omega-atoms-up-to-computation.md) a spelling is
no longer the whole of atom identity. A Nat atom whose spelling is new is
first evaluated under a small budget and, if it computes to a numeral, becomes
that constant (`of_bit(True)` is `1`); after this document's reduction it is
compared by bounded conversion against the table's atoms of the same head and
arity, and joins one it converts to (`f(append(Nil, Nil))` is `f(Nil)`). The
table still records the first spelling met, the certificate still spells each
occurrence as written, and the checker's conversion redoes the computation.
The hazard above is unchanged: nothing is re-spelled, so no atom is split or
renamed; a pair differing only in distinct variables is never asked.
Int-valued atoms get the same two questions
(issues/omega-int-atoms-up-to-computation.md): a global-headed atom whose
bounded weak head is `OfNat(n)` or `NegSucc(n)` with a numeral `n` is that
constant, and Int atoms of one head are compared at `int::Int`, elaborated
from its name only when a pair passes the syntactic gates.

## 6. Which hand discharges become removable

- **`tail_lt`** (`mutual_recursion.rs`, cited by all three showcase-parser
  members) — **removable**, and the customer: those sites are exactly
  `list_len(rest) < list_len(Cons(t, rest))`.
- **`merge`'s `succ_add_le` and both `on`s** (`termination_measures.rs`,
  `merge_with_two_obligations_at_a_sum_measure`) — **removable**. With both
  `Cons` measures reduced the obligations are `a + b < Succ(a) + Succ(b)` over
  the atoms `a = xt.len()`, `b = yt.len()`: linear, `omega`'s own arithmetic.
- **`runs`'s `drop_eq_le`** (`a_callee_postcondition_feeds_the_decrease`) —
  **a genuine lemma site.** The recursive call is on a suffix a *callee*
  returned; `drop_eq(t, rest)` is opaque under any reduction and the decrease
  is that callee's postcondition. Layer 2 of the measures issue owns this
  shape.
- **`gcd`'s `nat::mod_lt`** (`gcd_by_hand_obligation_computes_and_steps`) —
  **untouched.** The measure is the parameter `b`, refined to `Succ(k)` by the
  convoy; nothing is at a constructor *measure*, and
  `nat::mod(a, Succ(k)) < Succ(k)` is a fact about `mod`, not a reduction.
  Whether `omega`'s division atoms close it is a separate question and not a
  claim here.

The removable ones lose their hand discharge *and* gain a companion assertion
that the `on` is no longer needed, so a regression shows up as a refusal
rather than as dead scaffolding.

## 7. Negative controls

Per `docs/testing-generated-terms.md`, all four axes, all required:

1. **A non-decreasing measure at a constructor pattern is still refused, with
   the obligation named.** `Cons(h, t) => f(Cons(h, t))` reduces both sides to
   `Succ(list_len(t))`; `omega` finds no strict decrease and the message must
   still be §2-of-the-measures-doc's — "this recursive call must decrease the
   measure, and `…` was not proved automatically … Discharge it by hand: `on
   ?dec1 := …;`". Reduction must not turn a refusal into an acceptance, and
   must not lose the rewording.
2. **A genuinely opaque measure head still reflects as an atom under its own
   spelling.** `runs` is the live case; assert the atom label is
   `drop_eq(t, rest).len` and not a partially reduced form.
3. **An open element type.** Exercise the measure at `List<A>` with `A` a type
   variable, not only `List<Nat>`; a closed element type hid three of the five
   defects that document records.
4. **A neutral scrutinee alongside the literal one, in a checking position.**
   The obligation is closed inside a generated theorem, so `omega` is in
   checking position already; pair each `Cons(h, t)` site with one whose
   argument is a variable and assert *that* one is unchanged.

One more, specific to §1.1: with `drop1#obl_1` accepted, the `lift = false`
re-lowering must no longer run on the reproducer, so the arm-alias spelling
failure stays latent. Assert it.

## Filed separately

Two defects a coordinator can file on their own; neither blocks this round,
and neither is fixed by it.

- **A tier-1 arm's recursive binder has no spelling.** Inside a `match` arm,
  §6.3 of `docs/inductive-tier1-wf-lowering.md` aliases the recursive binder
  `t` to `nth^l(⟦D⟧; mᵢ; cs'; ι_t)`, which reduces to `Fst(cs')` on a neutral
  `cs'`. `spell_term_clean`/`spell_term_source`
  (`crates/elab/src/display.rs`) spell a `Supf` through `ctor_value` but have
  no case for a projection out of a neutral children tuple, so any route that
  has to *name* such a binder fails. It surfaces here as `omega`'s "could not
  spell a natural expression"; it is not an `omega` defect and it survives this
  round, merely unreached on these programs. A fix maps the projection back to
  the arm binder's surface name, which the elaborator knows when it builds the
  arm.
- **A refused lifted obligation reports the retry's error, not its own.**
  `elab_measure_decl` re-lowers with `lift = false` when the checker refuses
  `f#obl_N`, and the writer sees the second attempt's message. Here that turns
  "Omega's real shadow found no contradiction; atoms […]" — accurate and
  actionable — into "Omega could not spell a natural expression", which points
  at nothing the writer wrote. The first attempt's reason is already recorded
  (`unfold_refusals` keeps "the lifted `f#obl_1` was refused (…)"); the
  diagnostic should prefer it when both attempts fail.

Adjacent and already filed: the `.len()` measure renders as `t.len <
Cons(h, t).len` (`issues/omega-renders-member-by-base-name.md`), and the probe
shows `list::List::len(t)` respelling as `list_len(t)` after two δ/β steps —
worth that issue's attention, not this round's.

## Verdicts binding on implementation

1. The fix is **Option A**, in `crates/elab/src/omega_cert.rs` only. No kernel
   change, no new reduction rule, no change to any other elaborator `whnf`
   probe.
2. The reduction is `SemanticOracle::whnf_term` under the
   `STUCK_SPELLING_STEPS` budget, at the **atom fallback** of
   `nat_affine_syntax` — after the spelling already succeeded, never as a
   general "normalize before reflecting".
3. The reduct is kept **only when its head became arithmetic** (`Succ`, `Zero`,
   a literal, or `add`/`mul`/`div`/`mod`); otherwise the original term is
   interned unchanged.
4. An unspellable leaf of the reduct is named by **conversion against a
   candidate built from the original spelled term** — `g(ā[C(f̄) ↦ fᵢ])` for
   each recursive field `fᵢ` — and never by respelling the reduct. If no
   candidate converts, the original term is interned unchanged.
5. Atom identity stays spelling-keyed; `AtomTable` and `intern_by` do not
   change.
6. `tail_lt`, `succ_add_le` and `merge`'s two `on`s come out; `drop_eq_le` and
   `nat::mod_lt` stay, and the tests say which and why (§6).
7. §7's five controls all land, including the assertion that the `lift = false`
   retry is no longer reached on the reproducer.
8. Neither item under "Filed separately" is fixed here.

## 8. What implementing corrected

Five things, none of which changes a verdict.

- **§2.1 was implemented**, at depth two, and is exercised by a measure whose
  arm is `Succ(Succ(dlen(t)))`.
- **A leaf that is already arithmetic is decomposed where it stands, not
  reduced.** The branching measure `tnodes(Node(l, r))` whnfs to
  `Succ(nat::add(u₁, u₂))`, and reducing that leaf a second time — §2.1's
  route — unfolds `nat::add` into its eliminator and *loses* the head step 2
  is looking for. So step 3 tries, in order: the leaf's own spelling, each
  candidate, the leaf's arithmetic shape, and only then another reduction.
  Without this the two-leaf row of §2's table does not close.
- **Step 1 is gated on the shape §2 is about**, before any reduction: a call
  whose head is a global and one of whose arguments is a constructor value
  (a `Supf`, an injection, or a `Succ`/`Zero`). Every other atom — `list_len(t)`
  at a variable, `runs`'s `drop_eq(t, rest).len()` at a neutral — is interned
  exactly as before and pays nothing, which is §5's requirement reached one
  step earlier than §2 described it.
- **`oracle.rs` gained one method**, `whnf_term_bounded`: `whnf_term` under the
  `STUCK_SPELLING_STEPS` budget verdict 2 names, which the oracle did not
  expose. No existing probe changed, so verdict 1's "no change to any other
  elaborator `whnf` probe" holds; only its "`omega_cert.rs` only" is amended
  by this one addition.
- **§6–§7's new tests live in a file of their own**,
  `crates/elab/tests/omega_measure_reduction.rs`. Added to
  `termination_measures.rs` they took that binary past `scripts/test`'s
  per-child address-space cap under the parallel bound, and it was `SIGKILL`ed
  — an `INCOMPLETE` suite, not a failure. Two binaries, two peaks.

## 9. Neutral constructor arguments inside match arms

`issues/omega-inside-match-arms.md` extends step 3 to a constructor whose
payload or children tuple is neutral. `spelling::tuple_fields` reads literal
pairs as before; for a neutral tuple, it matches each field's projection path
against the context's typed aliases, ignoring projection annotations. A Wf
child alias is an `nth` application headed by Nat elimination: bounded whnf
exposes its projection path. The candidate retains the original alias term,
so its argument is a recursive child of this constructor with the correct
type, rather than an arbitrary local that happens to spell. Container fields
remain outside this reader's scope.

The constructor printer uses the same reader and interleaves payload and
recursive fields in declaration order. Alias spelling still checks shadowing.
Under a printed binder, alias terms are weakened to the printer's depth;
any reduction happens first in the alias's actual context. Generated binder
names avoid aliases as well as kernel binders.

Ordinary fact reflection now declines an unspellable fact and rolls back any
atoms it interned before the spelling failure. Other reflection errors still
propagate. The final stuck diagnostic lists the declined facts by name and
reason, while the relevance filter and certificate checker operate on the
remaining facts. No discarded fact contributes evidence to a certificate.

## 10. Record fields (2026-09-29)

`issues/omega-record-projection-atoms.md`. A closed record whose spine is not
dependent registers no projection definitions (`register_rec_projs`: they
would be all cost), so `s.words` elaborates to the inline walk
`fst(snd(snd(s)))` — entry 0 is the tag, field `j` is entry `j + 1`. The
speller had no case for it, so every field of such a record was "could not
spell a natural expression", and one in a fact in scope sank the call until
the fact-declining of §9. Four pieces, three in the speller:

- **A field read spells as `r.name`** (`Speller::field_read`,
  `crates/elab/src/display.rs`) when the receiver's type, read off its spine
  (`Elaborator::spine_type`: the head inferred, one Π instantiated per
  argument, the walk `app_domains` makes), is a record. Only receivers whose
  head is a variable, a global or another field read, and only at the
  context's own scope. Re-elaborating the spelling walks the same spine.
- **A record value spells as its constructor** (`ctor_value`): the checked
  pair carries the record's type, and the value is the one constructor's
  payload tuple itself.
- **In a source spelling only, a projection nothing else names spells as its
  bounded weak head** (`Speller::projection_reduct`): a field read off a
  record value after a `let` inlined it, or off a `match` on a literal in a
  motive's instance. The consumer re-elaborates and checks by conversion. A
  projection out of a neutral is its own weak head and still falls back.
- **In `omega`, a projection whose bounded weak head is arithmetic is
  reflected as that reduct** (`projection_reduct` at the top of
  `nat_affine_syntax_within`), by §2's rule: kept only on an arithmetic head
  whose leaves spell (`named_arithmetic_shape` with no candidates). So
  `(match False { … }).words` is `Succ(s.words)`, not an opaque atom, and
  `step_fold(…).bytes`, whose reduct is an eliminator, interns as before.
  `convertible_atom` (§5) compares a field read by its receiver along the
  same projection path, so `step_fold(wc_region(), …).lines` meets
  `step_fold(ReadonlyLoop(wc_body), …).lines`.

§5's hazard does not arise: no atom that spelled before is re-spelled. The
first three pieces give a spelling where there was none, and the fourth
reduces only projections out of values, whose spelling was either absent or
the reduct's own.

Not covered: an atom equal to another only by unfolding a *different* head
(`wc_words(bytes)` against `words_of(wc_split(bytes))`) stays two atoms, as
§5 has always said. `examples/x86-native/wc.hthr` states those two facts at
the specifications' names in typed `let`s. Its six Nat-only helper lemmas
are gone. The module costs a few times its old cold check, which is the
folds' certificates.

## 11. Defined propositions and calls that compute to constructors (2026-10-12)

`issues/omega-unfolds-defined-propositions.md`. The rationals client
(`lib/std/num/rat.hthr`) restated most goals and hypotheses with a typed `let`
before calling omega, because each was spelled through a definition. Five
pieces, all in `crates/elab/src/omega_cert.rs`:

- **A fact whose head is a defined proposition** (`h: Rat::zero() <= x`, a
  `Rat::Le`) is reflected as the relation it unfolds to
  (`unfolded_proposition`): the goal side's existing rule, unfolding the head
  one reduct at a time and stopping at the first relation it reads, then
  simplifying the arguments as a goal's are. A negation's domain gets the same
  question. The evidence is still the local's name, and the checker converts
  its type to the unfolded statement where the certificate uses it. Gated on an applied
  global that is not an inductive type, so data locals pay nothing.
- **A goal that unfolds to an equation** (`x ≈ y`, an `=` underneath) is
  decoded before it is simplified and read; the loop already took `<=`.
- **A global call whose bounded weak head is `Succ(…)`** (`Pos::val(p)` is
  `Succ(p.pred)`; `computed_successor`) and **an Int call whose weak head is
  `OfNat(e)`** (`Pos::int(p)`; `computed_of_nat`) are reflected as that
  arithmetic, by §2's rule: an arithmetic head and leaves that spell, or the
  term interns as before. This is a second route beside §2's, ungated by a
  constructor argument; a call stuck on a match (`bump(b, n)`) still interns.
- **A field of a call that unfolds to a constructor** (`p.mul(q).pred`,
  `(x + y).num`; `field_as_put`) is the expression put there: the receiver is
  unfolded only as far as the pair and the field projected without δ, since
  the weak head of the whole read unfolds the sum on into its recursor. Nat
  keeps it on §2's arithmetic rule; Int keeps it when it spells.
- **A factor that computes to a numeral** (`x.num * Rat::one().num`) scales,
  on both carriers, as an atom that computes to one is a constant.

Separately, a fact whose equation side is a β-redex (`Int::cong(λ (t: Int) =>
e * t, p)`) is simplified and retried when the first attempt cannot spell it,
instead of being skipped. Only that shape is retried.

§5's hazard is narrowed, not absent: an atom such as `Pos::val(p)` is now
re-spelled as `p.pred + 1`. Every occurrence takes the same route, goal and
facts alike, so no atom splits; what moves is that a fact stated over the
unfolded spelling now meets the call. The negative controls are in
`crates/elab/tests/omega_defined_propositions.rs`: a proposition stuck on a
match is still skipped, a false claim through a defined fact is refused, and a
stuck call stays an atom.

## 12. Fields of fields, and fields put as atoms (2026-10-26)

`issues/omega-nested-projection-of-call.md`. §11's `field_as_put` unfolded
one receiver and gave up when the projected field was itself a projection,
and the Nat side kept the field only on an arithmetic head. So
`R::at(n).inner.den.pred` (each field put by a call) stayed one atom, and so
did `P::of(n).pred`, whose field is put as the variable `n`: neither met the
goal's `n`. Two changes, both in `crates/elab/src/omega_cert.rs`:

- **A field that is again a field read is read on** (`field_as_put_within`),
  up to `FIELD_NESTING_DEPTH` receivers, each unfolded only as far as its pair
  and projected without δ, as before.
- **On `Nat`, a field put as an atom is that atom** (`projection_reduct`): a
  variable or an applied global that spells. A stuck eliminator put there
  still leaves the projection an atom. `Int` already kept any field that
  spells.

§5's hazard is as in §11: every occurrence of such a field takes the same
route, so no atom splits, and a field read off a neutral record (`q.den.pred`)
is untouched. Probes and controls: `lib/_tests/std/tactic/omega_tests.hthr`.

## 13. Conjunction facts at every depth (2026-10-29)

`issues/omega-nested-conjunction-facts.md`. A context fact `h: P ∧ Q` was
read only by the connective split, the fallback after reflection fails:
`omega::and_elim_false` binds both sides and re-enters as
`__omega_connective_branch`, which splits nothing further. So in
`h: a < b ∧ (b < c ∧ c < 5)` the inner conjunction was never read.

Now `local_facts` lists a conjunction as its conjuncts, recursively, each
under its projection path (`h.left`, `h.right.left`, `h.right.right`), with
the type `project_field` gives it. Every consumer of `local_facts` (Omega's
reflection, the relevance layers, CutSat, the connective and disequality
splits, `linarith`'s and `bv_omega`'s fact scans) sees the conjuncts as
ordinary facts. The certificate is source, so a used conjunct is cited by its
path and an unused one never reaches the kernel; a disjunction under a
conjunction (`h.right: A ∨ B`) is split like a top-level one. The `And` arm of
`split_connective` stays only for a fact whose projection declines.

## 14. Fields at closed arguments (2026-10-30)

`issues/omega-closed-field-value-atomised.md`. §10's `projection_reduct`
asks first for the read's bounded weak head, keeping it on a numeral or an
arithmetic shape. At a variable that head is stuck early and cheap; at
closed arguments (`Lay::of(3).size`, every layout at a literal program) it
evaluates the field itself, spends the budget, and the failure returned from
the function before §11–§12's read-as-put route was tried. Every field of the
call became its own atom, so `Lay::of(3).size` and `Lay::of(3).cap`, put as
`lay(3)` and `lay(3) + 4`, shared nothing.

A spent budget now skips only the shortcut. The field is then read as put:
the receiver unfolded as far as its pair, the field projected without δ, so
it is spelled and never evaluated, and its atoms are decided like any other
subterm's. A cheap field still takes the shortcut and arrives as its numeral.
A field put as an eliminator over the computation (`match lay(n) { … }`)
stays behind its projection, as §12 left it; probes and that control are in
`lib/_tests/std/tactic/omega_tests.hthr`.

## 15. Facts typed by a β-redex (2026-10-30)

`issues/omega-redex-typed-fact-ignored.md`. An `Exists`'s `.proof` is typed
`(λ k => P(k))(e.witness)`: the record's field type instantiated at the
witness, with the redex left in place. The display contracts it (PR #184),
so the report listed the fact as `a = add(e.witness, 2)`, but reflection
looks for a relation at the type's head, found an application of a λ, and
skipped the fact.

`push_conjuncts` now contracts the head redexes of a fact's `El` type
(`spelling::beta_head`, the unifier's contraction since PR #62) before the
conjunction check, so every consumer of `local_facts` sees the contractum and
a conjunction under the redex is split as in §13. Only the head is
contracted: a redex inside a relation's side is an atom like any other
subterm. The certificate still cites the fact by name; its declared type and
the contractum are β-convertible, so the kernel pays one β-step.
