# Reducing a measure at a constructor pattern before `omega` reflects it

`issues/omega-measure-at-constructor-pattern.md`. The most common `decreases`
obligation there is — `fn drop1(xs: List<Nat>) -> Nat decreases list_len(xs)`
recursing on the tail — is refused, and every existing `decreases` test
discharges its constructor-pattern site by hand
(`docs/language/recursion/mutual-recursion-design.md` §7 records two of them).

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
with body `omega` (`docs/language/recursion/termination-measures-design.md` §4). When the checker
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
  `docs/inductives/inductive-tier1-wf-lowering.md` *aliases* a tier-1 arm's recursive
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
`docs/language/recursion/termination-measures-design.md` §3): at the `Cons(h, t)` arm the
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
  §6.3 of `docs/inductives/inductive-tier1-wf-lowering.md` aliases the recursive binder
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

## 16. Truncated subtraction at Nat (2026-10-30)

`issues/omega-nat-truncated-subtraction.md`. A Nat `a - b` was one atom, so
`a - b + b = a` under `b <= a` had the model `a = b = 0, a - b = 1`, and every
round fed `Nat::sub_add_cancel` by hand. It is now split as Lean's `omega`
splits it: `omega::nat_sub_elim(a, b, …)` gives two branches, `b <= a` with
`(a - b) + b = a` and `a < b` with `a - b = 0`, bound as
`__omega_sub{k}_case` and `__omega_sub{k}_eq`, each closed by `omega` again.
The subtraction stays one atom; both cases now constrain it, so a linear
problem is enough in each. Nothing new is trusted: the split is a lemma in
`omega.hthr` and the branches are ordinary certificates.

`split_nat_subtraction` is the last fallback of the attempt that answers:
after CutSat finds a model and after the disequality and connective splits,
so a goal that closed before closes the same way, and not in a narrower
relevance layer, whose failure only widens. It looks for subtractions on the
sides of the relations `integral_sides` reads (stated, unfolded or negated,
through `Succ` and applied globals, never under a binder), newest fact
first, so the negated goal's subtractions are split before an old fact's.
A subtraction is settled once a case equation in scope names it, compared by
its spelling; the case equations are counted to name the next pair, and
past six of them nothing more is split — each split doubles the branches,
and a subtraction whose spelling did not round-trip would otherwise be split
forever. A refused control's report names the case its model lives in
(`__omega_sub0_case: Lt(a, b)` among the locals). Probes are in
`lib/_tests/std/tactic/omega_tests.hthr`.

## 17. Bool guards (2026-10-30)

`issues/omega-reads-bool-guards.md`. A fact `b.IsTrue()` was skipped
whatever `b` was, so every client of a Bool-guarded field
(`Finite::ok`, the x86 asm tables, FunctionIR evaluation) took the guard
apart with `is_true_and`/`leb_sound` before omega could see it
(`docs/language/matching/bool-guard-reflection-design.md` §3.2).

A **guard round** (`split_bool_guards` in `crates/elab/src/omega_cert.rs`)
now reads every guard in scope by its structure, with one `omega::guard_*`
rule (omega.hthr) per connective, each taking one connective off a guard
proved true (`h: b.IsTrue()`) or proved false (`h: (!b).IsTrue()`):

| guard | proved true | proved false |
|---|---|---|
| `a && b` | both (`guard_and`) | two cases, `!a` or `!b` (`guard_nand`) |
| `a \|\| b` | two cases (`guard_or`) | both negated (`guard_nor`) |
| `!a` | `a` proved false | `a` proved true (`guard_not_not`) |
| `n.leb(m)` | `n <= m` (`guard_leb`) | `m < n` (`guard_not_leb`) |
| `n.same(m)` | `n = m` (`guard_same`) | `n ≠ m` (`guard_not_same`) |
| `a.leb(b)` at `Int` | `a <= b` (`guard_int_leb`) | `b < a` (`guard_int_not_leb`) |
| `a.same(b)` at `Int` | `a = b` (`guard_int_same`) | `a ≠ b` (`guard_int_not_same`) |
| `a.unsigned_lt_bit(b)` at a word | `toNat(a) < toNat(b)` (`bitvec_omega::guard_lt`) | `toNat(b) <= toNat(a)` (`guard_not_lt`) |
| `a.unsigned_le_bit(b)` at a word | `toNat(a) <= toNat(b)` (`bitvec_omega::guard_le`) | `toNat(b) < toNat(a)` (`guard_not_le`) |
| `a.eq_bit(b)` at a word | `toNat(a) = toNat(b)` (`bitvec_omega::guard_eq`) | `toNat(a) ≠ toNat(b)` (`guard_not_eq`) |
| any other Bool `r` | `bit(r) = 1` (`guard_bit`) | `bit(r) = 0` (`guard_not_bit`) |

A fact `¬b.IsTrue()` is `b` proved false (`guard_negated`). The rules take
the guard's operands as implicits, so the certificate spells nothing: the
checker reads them off the evidence's type, and the parts reach the leaf
`omega` as the original subterms. Every guard in scope is taken apart in one
certificate, which ends in `omega` at each branch.

- **Definitions.** A guard whose head is a Bool definition
  (`F.canonical(mag, bexp)`) is unfolded one reduct at a time, as §11
  unfolds a defined proposition, to the first reduct with a connective at its
  head, through its `let`s. The unfolded statement is the type of an alias
  (`__omega_unfold{k}_{i}`) the caller binds before checking, whose value is
  the fact itself: the kernel converts the two where the rule uses it. An
  alias rather than a written type, because the reduct need not spell
  (`canonical`'s least-exponent test is a `match`), and rather than letting
  the unifier find the reduct, because it does not: asked for
  `(?a && ?b).IsTrue()` against `g(n, m).IsTrue()` it solved `?a := n`,
  `?b := m` and left the kernel to refuse it.
- **Atoms.** A Bool that is neither a connective nor a comparison, nor a
  definition that unfolds to one (`F.specials.reserves_top()`, a variable),
  is the atom `omega::bit(r)` (`1` when true, `0` when false): Nat
  arithmetic, so `r` and `!r` meet as `bit(r) = 1` against `bit(r) = 0`
  with no propositional atom kind and no case split per atom. The issue's
  open question resolves that way. A stuck `match` inside a guard is not
  read; its part is bound and left alone.
- **Rounds and settling.** A round is the first fallback of the attempt
  that answers, before the disequality, connective and subtraction splits,
  so a goal that closed before closes as it did; it is written only when
  some guard has a connective or a comparison to read (or two bare atoms
  might meet). The facts it reads are settled for the omegas inside it (a
  stack on the elaborator, `omega_settled_guards`, pushed while the
  certificate is checked); the parts it binds are `__omega_guard{k}_{i}`,
  never read again. What it leaves for the next round is bound as
  `__omega_open{k}_{i}` (`guard_open`): a part that needs a definition
  unfolded (an alias can only be made for a fact already in scope), and a
  disjunction past the round's budget of `GUARD_BRANCHES` branches — each
  `||` doubles the certificate's tail. A later round runs only where a
  branch fails without it, at most `GUARD_ROUND_LIMIT` deep.
- **Goals.** A goal `b.IsTrue()` that does not compute to a verdict is
  refuted from its negation (`guard_goal`), which the round reads as a fact;
  `¬b.IsTrue()` is assumed and refuted, as a negated relation is.

`Format::canonical_elim` (`lib/std/num/float/float.hthr`) is now
`omega(ok)` for its comparison conjuncts and `λ rt sp => omega(ok, rt, sp)`
for the reserved-top implication, the disjunction staying a `reflects_elim`;
`Finite::units_le_max` reads `g.ok` through `omega` instead of binding the
elim. Probes for each connective, a definition at the top and inside a
guard, a record's guard field, a guard goal, the next-round budget, and the
controls (a false claim naming the guard's parts, a guard over `parity(n)`
that no unfolding takes apart, a bare atom) are in
`lib/_tests/std/tactic/omega_tests.hthr`. The library's hand-written
decompositions in modules that do not import omega (the x86 asm tables,
FunctionIR evaluation) are left as they are.

## 18. Fields of a record constructed in place, and guards as equations (2026-10-31)

`issues/decreases-measure-record-field-unspelled.md`. A `decreases s.m`
measure at the self-call `f(CdState(s.m - 1, Cons(s.m, s.out)))` is the
read `fst(snd(pair(…)))`: the field off a record *value*. Three gaps stood
between it and the default `omega`, and the record-free control
(`decreases m` over two parameters) shared the third:

- **The speller had no case for it.** §10's `Speller::field_read` types its
  receiver off a spine, and a pair is no spine; `projection_reduct` takes a
  δ-transparent weak head, which goes past the field's value (`s.m - 1`)
  into `sub`'s eliminator. `Speller::value_field_read` (display.rs) now
  projects by syntax (`spelling::project_value`: every projection meets a
  pair, no reduction): for reading the read is spelled as written,
  `CdState(sub(s.m, 1), …).m`; for a source spelling it is the component
  itself, which re-elaborates to a term the read converts to by Σ-β.
- **`omega` reflected it as an atom with no spelling** — the same weak-head
  overshoot in `projection_reduct`, and `field_as_put` declines a receiver
  that is not a call. `field_as_put_within` now takes the syntactic
  component first, so the read is reflected as `s.m - 1` and §16's split
  applies.
- **The arm's equation was not a fact.** `match h: Nat::leb(s.m, 0)` binds
  `h: leb(s.m, 0) = False`, and §17's round read only `b.IsTrue()`. A Bool
  equation `b = True`/`b = False` is now a guard proved true/false
  (`guard_eq_true`/`guard_eq_false`, `bool_equation` in omega_cert.rs). For
  the *lifted* obligation (`docs/language/recursion/termination-measures-design.md` §4) to see
  it, `measure::arithmetic_fact` admits an arm equation at `True`/`False`
  beside `<`/`<=` facts, so `measure_local_evidence` quantifies it; its
  trial elaboration still decides whether the fact is used.

The repro checks with no `on`, lifted. Its unfolding companion stays
declined for §3 of the unfolding design's own reason (a `match` with an
equation binding). Probes, the false-claim control included, are in
`lib/_tests/std/tactic/omega_tests.hthr` (`guard_eq_*`,
`field_of_constructed_record`, `count_down`).

## 19. Comparisons and measures at Int (2026-11-06)

`issues/while-bool-condition-measure.md` and its Int follow-up. A `while`
over a Bool condition binds `c = True`, which §18 already reads; what a
loop over `Nat::same` or an `Int` comparison lacked was the comparison
itself, read as the atom `bit(c)`. §17's table gains `n.same(m)` and the
`Int` `leb`/`same` rows, each a lemma in `omega.hthr`.

An `Int` loop's measure is a Nat, usually `x.toNat()`, and that read was
an opaque atom. It is now split as §16 splits `a - b`:
`omega::int_to_nat_elim(x, …)` gives `0 <= x` with `OfNat(x.toNat()) = x`,
or `x < 0` with `x.toNat() = 0`, bound as `__omega_tonat{k}_case`/`_eq`.
`split_int_to_nat` runs right after `split_nat_subtraction`, under the
same settle-by-spelling rule and the same limit of six; its search enters
an `Int` constructor's payload, so a case equation `OfNat(x.toNat()) = x`
settles the read it names. Probes: `guard_int_*` and `to_nat_*` in
`lib/_tests/std/tactic/omega_tests.hthr`, `idrain`/`iclimb` in
`lib/_tests/std/core/imperative_statements_tests.hthr`.

## 20. `max` and `min` at Nat and Int (2026-11-09)

`issues/omega-reads-min-max.md`. `a.max(b)` was an opaque atom, so a goal
past two thresholds (`a <= c`, `b <= c` ⊢ `a.max(b) <= c`) had the model
`a = b = c = 0, max(a, b) = 1`, and every proof that picks an index past
two others cited `le_max_l`/`le_max_r` and `le_trans` by hand. Lean's
`omega` adds the defining facts per atom; here the read is split as §16
splits `a - b`, by the order of its arguments: `omega::nat_max_elim(a, b,
…)` gives `a <= b` with `a.max(b) = b`, or `b <= a` with `a.max(b) = a`
(`min` the other way round), bound as `__omega_mm{k}_case`/`_eq`. Each
case's facts imply the issue's `a <= m`, `b <= m`, `m = a ∨ m = b`, and a
split is already the shape the fallbacks take, so no disjunction is added
to the problem. The four lemmas (`nat_max_elim`, `nat_min_elim`,
`int_max_elim`, `int_min_elim`, `omega.hthr`) cite `max_eq_l`/`max_eq_r`
and `min_eq_l`/`min_eq_r` from `nat.hthr`/`int.hthr`; the certificate
never unfolds `Nat::max`'s recursion or `Int::max`'s `if`.

`split_max_min` runs after `split_int_to_nat`, under the same
settle-by-spelling rule and limit of six; its search enters applications
and an `Int` constructor's payload. Like the other splits it is only in
the attempt that answers and only after CutSat found a model, so a goal
that mentions no `max`/`min` gets no new atom, branch or certificate step.
A read whose arguments omega cannot spell (an `Exists` witness projected
out of a section's dictionary, as in `Converges::mul`) is not reached
either; that is the fact reader's limit, not the split's. Probes:
`max_*`, `le_min_bare`, `min_add_max`, `int_m*_*` and the refused controls
`max_le_left`/`int_min_ge_left` in `lib/_tests/std/tactic/omega_tests.hthr`.

## 21. Fields of a call put as reads, and applied function fields (2026-11-10)

`issues/omega-field-of-record-valued-call.md`,
`issues/omega-applied-field-atom.md`. Two gaps, both met building
`issues/address-interval-sets.md`:

- **A field of a call put as a read off a neutral** (`s.take(k).base`, with
  `Span::take(s, k) = Span(s.base, …)`) stayed one atom. §12's
  `field_as_put_within` read the field on when it was itself a field read,
  and declined when that read's receiver was no call (`s`). Such a read is
  now the result: it unfolds no further and is the atom the goal's other
  mentions of `s.base` intern as. `projection_reduct` keeps a field put as a
  field read or an applied one. The fallback splits search their facts
  through the same reading (`nat_subtractions`, `int_to_nats`,
  `max_min_reads`), so the `min` in `s.take(k).len` and the `-` in
  `s.drop(k).len` are split as if written; before, they were found only in
  the written form, and the read form was reflected with a `min` atom no
  case equation named. The searches now return owned terms.
- **A function-valued field applied** (`nb.number(a)`) had no spelling:
  `call_parts` recognises a projection whose spine is exactly instantiation
  and receiver, and an inline projection head is no call at all.
  `Speller::applied_field` spells the field read, then the arguments, when
  the spine's innermost head is a projection and each argument meets an
  explicit arrow of the field's declared (surface) type. An implicit binder,
  or a type the declaration names through an alias, declines, since the
  spelling must re-elaborate to the same spine. Every receiver spells, a
  call included; that first needed a section's bare `f<A>` (how a
  zero-argument section function spells) to elaborate with its dictionary
  filled where nothing is expected
  (`issues/applied-field-source-spelling-level-mismatch.md`). Diagnostics
  spell the same way, so mismatch notes that used to fall through to the
  kernel for want of a spelling are now reported where they were recorded.

§5's hazard: every occurrence of such a field takes the same route, goal and
facts alike, so no atom splits; what moves is that `s.take(k).base` now
meets `s.base`. Probes and refused controls (`call_field_false`,
`field_call_apart`) are in `lib/_tests/std/tactic/omega_tests.hthr`.

## 22. Opening what the search is given (2026-11-14)

`issues/omega-opens-closed-terms.md`, `issues/bv-omega-hypothesis-word-bound.md`.
The linked SHA-256's agreement proofs bound a `let … = refl` before nearly
every arithmetic step, each one restating a term so `omega` would read it as
arithmetic. Each such binding is a shape the reflection now opens itself,
before the search, and each opening is bounded:

- **A word's range.** Every atom `toNat(w)` at a literal width `n` brings
  `toNat(w) < 2^n` (`bitvec::BitVec::toNat_lt_pow`), whether it is met in
  the goal or only in a fact. It is stated beside the facts, as a division
  atom's bounds are, so it never widens what a relevance layer reads. A
  width that is not a literal brings nothing, and the range is skipped
  where the lemma is not in scope. `bv_omega`'s inner `omega` calls inherit
  this, which is what its side condition over a word met only in a fact
  (`j < mn` with `mn` nowhere else) lacked.
- **A closed call computes to its numeral** under
  `NUMERAL_COMPUTATION_STEPS` (a few thousand). A call stuck on a local
  stops long before it, so only a computation that keeps going pays it.
  `u64::ofNat(0).toNat()` needs a few hundred steps, which the earlier
  256-step probe did not give it.
- **`a * Succ(b)` is `a * b + a`**, by `mul`'s definition (it recurses on
  its right), so an induction hypothesis about `a * b` meets the step's
  goal. A literal factor was already a scale.
- **A call is named at the parts of its arguments.** §2 named a reduct's
  leaves against the call at the fields of an argument that *is* a
  constructor. The candidates are now also the fields of an argument that
  *computes* to one (`ending(z, l)` is `Cons(0x80, zero_bytes(z) ++ …)`), and,
  two calls deep, an argument's own candidates (`spelled(Cons(w, rest))`
  names `spelled(rest)`). `computed_successor` uses them, and a leaf that
  computes to successors is peeled (up to sixteen) without spending the
  depth until what is left converts to a candidate or spells:
  `spelled(Cons(w, rest)).len()` is four successors of
  `spelled(rest).len()`.
- **A base case that is a parameter or a numeral** is a reduct §2 keeps:
  `x.doubled(0)` is `x`. A literal argument (`NatLit`) now passes §2's
  gate, as `Zero` did.
- **A definition followed to its arithmetic.** The weak head of
  `be_value([b0, b1, b2, b3])` is past the arithmetic, since `+` itself
  unfolds to its eliminator. When the weak head names nothing, the head
  reducts are walked (`Unfold::ArithmeticBody`, 256 reducts) for the first
  whose head is `+`, `*`, `div`, `mod` or a successor and whose leaves are
  named. A leaf that is a β-redex (a fold's step function applied to its
  accumulator) is contracted at no cost to the depth. The operations the
  reader reads, splits or keeps as atoms on purpose (`+`, `*`, `pow`, `-`,
  `div`, `mod`, `min`, `max`) are never unfolded this way, and a power keeps
  the probe's small evaluation budget: `closed_power` stays the gate on
  what the kernel is asked to evaluate (`omega_wide_constants`'s
  `costly_power` control).

What a bound stops is named in the failure report, after the residual:
`left as atoms by a bound [`…` did not compute within 4096 steps]`, or
`… reached no arithmetic within 256 unfolding steps`. That is the line to
read before binding a `refl` by hand: it says which term to state, and
which budget a library change would have to move.

Probes and refused controls are in `lib/_tests/std/tactic/omega_tests.hthr`
("Terms opened before the search") and
`lib/_tests/std/tactic/bitvec_omega_tests.hthr` ("Every word's range").
Each opening is also reached by the kernel's conversion when it checks the
certificate, which spells the original term and converts it at the
normalized row: the cost of `docs/proof-patterns.md` §3 (records at a literal program) applies,
so the budgets above stay small.

## 23. A word's comparison bit as the comparison (2026-11-16)

`issues/omega-if-bit-word-comparison.md`. An `if larger: x < y` over words
binds `larger` only in a branch that names it; a branch that does not keeps
the test as the bit's equation, `unsigned_lt_bit(x, y) = True`. §18 read
that equation as a guard and §17 kept the bit as the atom `bit(r)`,
unrelated to `toNat(x)` and `toNat(y)`, so `omega` got stuck where
`bv_omega` (which reads the test off the context itself) did not. The
guard round now reads the three word tests, `unsigned_lt_bit`,
`unsigned_le_bit` and `eq_bit`, as the comparison of their operands'
values, by the `bitvec_omega::guard_*` rules in §17's table. The rules
live in `bitvec_omega.hthr`, not `omega.hthr`, which does not import
`bitvec`; where `bitvec_omega` is not loaded, such a bit stays an atom, as
before. A Bool equation is also read either way round (`True = b` as
`sym(h)`). Probes, a wrong-way control among them, are in
`lib/_tests/std/tactic/bitvec_omega_tests.hthr` ("`omega` reads a word's
comparison bit"); `examples/sort/sort.hthr`'s `insert_at_inserts` states
its `ab` and `ba` by `omega`.

## 24. A measure through an `if` (2026-11-24)

`issues/while-decrease-through-branches.md`. A `while` whose measure is
assigned in each arm of an `if` (or set to an `if`), and a recursive call
at an `if`-valued argument, owe `m(if c { a } else { b }) < m(x)`. Neither
search splits the match: `omega` reads `m(if …)` as an atom unrelated to
`m(x)`, and `bv_omega` takes the word apart only through arithmetic. The
closer (`Checking::elab_measure_search` beside the `CLOSER` arm,
`crates/elab/src/checking.rs`) now falls back, once both searches have
failed and only where `split_all`'s search finds a stuck match in the goal,
to `split_all`'s stuck-match step with the searches alone at each leaf
(`measure::CLOSER_LEAF`): each arm gets its test's equation, and over
words its Nat reading, so `left = 5` gives `toNat(left) = 5` beside the
arm's `0 < toNat(left)`. Lean's `decreasing_tactic` splits the same way. A
split whose leaves fail leaves the searches' first refusal as the
diagnosis, so `Obligations::explain` and the loop's rewording read it as
before. The fallback costs only an obligation that would otherwise be
refused.

A recursive call's arguments are substituted into the measure as written,
and an `if` there infers its type from an arm: `(if n = 7 { 0 } else { n -
1 }).toNat()` read `0` as a `Nat`, and `toNat` was no method of it. An
argument that is a match or a block (an `if` once the body is rewritten,
its scrutinee bound first) is now ascribed at its parameter's type
(`measure::typed_arguments`). Probes and a control whose one arm keeps the
measure are in `lib/_tests/std/core/imperative_statements_tests.hthr`
(Nat) and `lib/_tests/std/tactic/bitvec_omega_tests.hthr` (words).

## 25. `x % n` and `x / n` by a divisor that is not a literal (2026-11-24)

`issues/omega-nonliteral-div-mod-facts.md`. At a literal divisor `c` a Nat
`x % c` and `x / c` are read through a quotient atom with its division
bounds (`NatMod`/`NatDiv`); at any other divisor both were opaque atoms, so
`x % n <= x`, `x % n < n` under `0 < n` and `x / n <= x` had models. They
are now split as §16 splits `a - b`, by the divisor's two cases:
`omega::nat_divmod_elim(x, n, …)` gives `n = 0` with `x % n = x` and
`x / n = 0`, or `0 < n` with `x % n < n`, `x % n <= x` and `x / n <= x`; both
with the link `x / n * n + x % n = x`, which holds at every divisor. It is bound as
`__omega_dm{k}_case`, `_mod`, `_div`/`_mod_le`, `_div_le` and `_link`. The
reads stay atoms; the product `x / n * n` is one atom more, so the link
serves a goal that spells that product (`x / n * n <= x`,
`x < x / n * n + n` under `0 < n`) and nothing that needs it multiplied out.
A `0 < n`, `n ≠ 0` or `if h: 0 < n` in scope refutes the zero branch at once,
so no guard has to choose a plain fact over the split. The lemma cites
`Nat::mod_lt`, `Nat::div_mul_add_mod`, `Nat::mod_zero`/`div_zero` and the
two laws added beside them in `nat.hthr`, `Nat::mod_le` and `Nat::div_le`
(any divisor); the certificate never unfolds `divmod`.

This is the word side's idea (`docs/tactics/bv-omega-design.md` §3.1, its
`d <= 0 ∨ r < d` disjunctions) one level down, written as `omega`'s own
splits are rather than as hypotheses: `bv_omega` states facts as source
before it calls `omega`, while `omega` reflects the context it is given, so
its facts enter where its other fallbacks do. `split_nat_division` is the
last of them, after `split_max_min`, in the attempt that answers only and
after CutSat found a model. A goal that closes without the facts never pays
for them, and the extra hypotheses never widen a relevance layer: they exist
only inside the branches, each a fresh `omega`. Reads are found as §16 finds
subtractions (the sides `integral_sides` reads, through `Succ`, applied
globals and fields as put, never under a binder, newest fact first), and a
read whose divisor spells as an integer literal is left to the reflection's
own facts. A pair, compared by the spelling of its dividend and divisor, is
settled once a `_mod` fact in scope names it; past six such facts nothing
more is split. A refused goal over `p` open pairs runs `2^p` leaves, each a
small linear problem (a few milliseconds for two pairs).

Left: over a divisor that is not a literal the link is linear only in the
product atom. What follows from the link and the bounds as they stand
closes (`x < x / n * n + n` under `0 < n`), but a goal that needs the
product multiplied out, such as `x / n * 2 <= x` under `2 <= n` (which scales
`x / n` by a bound on `n`), or `x / n` compared across two divisors, is
nonlinear and stays out of reach: `nlinarith` territory
(docs/tactics/nonlinear-arithmetic-design.md). Probes (`div_open_*`)
and refused controls (`x % n < n` with nothing known, `x / n < x`,
`x % n < x`, `x / n * n = x`) are in `lib/_tests/std/tactic/omega_tests.hthr`.

## 26. Definitions at open arguments, and what has no spelling (2026-11-24)

`issues/arithmetic-definition-opaque-at-open-arguments.md` (item 1),
`issues/omega-unspellable-local-in-scope.md`. Both met naming the distance
between two slots of the word map, `fn WordMap::dist(a, b: Nat) → Nat {
(b + 4 - a) % 4 }`.

- **A definition at open arguments.** §2's gate let a call through only
  where an argument is a constructor or a literal, so `dist(j, s)` was an
  atom and `omega` found a model with `dist(j, s) = 0`. A call at open
  arguments is now walked a few head reducts (`Unfold::OpenArithmetic`: the
  δ step and the β steps instantiating its parameters) for a body built
  from `+`, `*`, `-`, `div`, `mod`, successors and literals over the call's
  own arguments alone, and read as that body (`open_arithmetic_body`). A
  body that calls further definitions is not opened: `CReal::bound(x)`, a
  quotient of `x.at(0)`'s fields, is a quantity `creal`'s facts are stated
  about, and opened it no longer met them. A recursive definition is stuck
  on its `match` long before an arithmetic head, so it stays an atom and
  pays only the short walk; a word's `toNat` is never walked. The subtraction
  split (§16) looks through the same opening, so `b + 4 - a` inside
  `dist` is split as a written one is. The certificate still spells
  `dist(a, b)`; the checker converts it by the same δ step.
- **A generated binder.** A nested pattern binds its variable under a
  generated name (`#p1`) that the written `q` aliases, and a fact's type
  mentions the binder. Spelled raw, the certificate did not parse
  ("unexpected character '#'"). A certificate that fails so is built once
  more with every generated binder named `__omega_hidden_N`, as a shadowed
  one is named (`source_context_naming`); such a binder is still not read
  as a fact itself. Only on that failure: a generated binder is also a
  structure's instance dictionary, and named it hides the operations
  `ring`, `linarith` and `omega` read by their plain spelling (`difference`
  and `creal` failed that way when every call named them).
- **A term with no spelling that a `let` names.** `let jj = reached.witness`,
  where `reached` is bound to a call one of whose arguments the speller
  cannot write, left `jj.toNat()` without a spelling, and the goal with it
  ("could not spell a natural expression"). Where the plain spelling fails,
  the term is spelled again with every subterm that is a visible `let`'s
  value written as the `let`'s name (`spell_term_source_aliased`); the
  name reads back to the same term where the certificate is parsed. Asked
  only after the plain spelling failed. A term neither names is still a
  refusal, and the refusal now quotes it and says to bind it.

Probes and controls: `lib/_tests/std/tactic/omega_tests.hthr` ("Definitions
at open arguments": a recursive definition stays an atom, a false claim
about the body is refused; "Locals with no spelling").

## 27. A written `omega` lifted, and where an inline call's cost goes (2026-11-24)

`issues/runtime-hash-map-spec.md` reported one inline `omega` in
`WordMap::adds_next`'s nested `λ` taking minutes, against milliseconds for
the same facts as a lemma, and `docs/proof-patterns.md` §3 made "keep its
context small" a rule users must follow. Reproduced on the current tree,
the gap is not of that order: each of the two arithmetic steps of
`adds_next` written inline, with the facts it reads, cost a small constant
factor over its lemma plus the lemma's call. What dominates, inline or not,
is the certificate: a slot distance `(s + 4 - j) % 4` is a truncated
subtraction (§16, a split) under a remainder by four (a quotient atom),
and the real shadow fails on integrality, so each leaf is a CutSat
refutation, a case analysis spelled over every atom of the leaf. The lemma
over bare numbers is seconds too; the context adds atoms and facts to every
leaf, which widens every row and lengthens the case analysis.

Two things changed:

- **A written `omega` lifts its proof** into a proved slot of the
  declaration, as `bv_omega` does (docs/tactics/bv-omega-design.md §6;
  where the slot's context or statement does not check on its own, as for
  a `λ r f => omega` whose binder types the coinductive goal's checking
  direction supplied, `lift_proved` keeps that proof inline; and a
  `simp_only` discharger, which is tried per side condition and
  kernel-checked in the goal world, is elaborated in a generated scope, so
  an `omega` in it stays inline):
  the gate checks the certificate once, as its own item in the
  declaration's context, and the body holds a reference. The certificate
  is no longer substituted along with the body under each enclosing
  binder and `let`. A call inside a certificate or a generated proof stays
  inline. `count_tactic_slots` reserves one more slot per `omega`; a proved
  slot records its tactic, so an open goal shows `inside := omega`.
- **Nothing else about the search.** A split on a quotient that the real
  shadow pins within a few values (`0 <= (x + 4 - y) / 4 <= 1`), tried
  before CutSat, made a lone distance lemma cheaper, but the branches
  multiply with the number of remainders (each branch is a full `omega`
  again), and the word map's lemmas over five remainders got several times
  slower. It was withdrawn.

Measured with `scripts/perf ab` on `word_map_laws.hthr` against the tree
before this round (cold, width 1, the module's arithmetic rewritten with
it): the proofs whose `omega` sits in a deep context gated in a fraction of
their time (`shift_move`, `shift_skip`), the module's gate and total fell
by a quarter or so, and local substitution nodes by a tenth over the whole
check, imports included; the distance lemmas themselves did not move. A
distance step moved inline (`step_before_back` into `adds_next`) cost more
than the lemma and its call: the context still widens the certificate.

What the context still changes besides width: the subtraction split
(§16) takes the facts newest first, up to `SUB_SPLIT_LIMIT`, whatever atoms
they share with the goal. Two of the word map's one-off distance steps,
written inline in a context of `ShiftInv`'s distances, spent the splits on
facts over other slots and got stuck; as lemmas over bare numbers they
close. A split ordered by connection to the goal (the relevance layers'
reach) would let them move inline.

Left, in the order the measurements point at: the split order above;
rows sized by the atoms the
refutation used rather than every atom reflected (`issues/bv-omega-check-cost.md`
cost 1, now `omega`'s own), and a cheaper certificate for a CutSat leaf.
Whether a narrowed call reads only its listed facts
(`issues/omega-listed-facts-only.md`) is a separate lever on the same
width: it would shrink a leaf's atoms to what the call names.
