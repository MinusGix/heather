# Positive values: a type, a hypothesis, or a binder

Status: design proposal, 2026-10-10; route and spelling chosen the same day
(§7). Round 1 landed (§9), and the `positivity` tactic (§10); the probes in
§3 were run against master at f2deb85, before either. Tracking issue:
[positivity-evidence](../issues/positivity-evidence.md).

The question: should `lib/std/pos.hthr`'s `Pos` exist at all? The three
answers on the table were:

1. **A general modifier.** `Pos<A>` for any carrier with an order and a
   zero, holding `h: 0 < val` beside the value instead of the shifted `pred`.
2. **No type.** Theorems take `h: 0 < x`. The noise is real, but it says
   that discharging positivity should be easy, not that a type is needed.
3. **A bundled type with inferred evidence.** `Pos<Nat>` is a `Nat` plus
   `h: 0 < val := <search the context>`, so a plain `Nat` can be passed where
   a `Pos` is wanted and its positivity is found. It is closer to typeclass
   inference than to coercion.

The recommendation (§6) is option 3's surface built on option 2's
semantics. `Pos<Nat>` should be **binder sugar** that expands to a `Nat` and
an inferred hypothesis, not a type with a constructor. That gets the
readability and the "pass a Nat, find the proof" behaviour with no wrapping
and no coercion. Every option needs the same missing piece, a search that
can discharge `0 < x` from more than an exact local, so that gets built
first.

## 1. What `Pos` is today, and what it buys

```heather
record Pos { pred: Nat }                 // stands for pred + 1
fn Pos::val(self p: Pos) → Nat { Succ(p.pred) }
fn Pos::mul(self p, q: Pos) → Pos { Pos(p.pred * q.pred + p.pred + q.pred) }
```

Its users are `Rat`'s denominator, the two cancellation lemmas
`Int::mul_cancel_pos_r` and `Int::mul_le_cancel_pos_r`, and the rationals
showcase and test. Nothing in the native libraries uses it.

What the shifted representation buys:

- **No proof field.** Two `Pos` are equal exactly when their numbers are, and
  nothing ever compares proofs.
- **Positivity is definitional.** `OfNat(1) <= p.int()` is `trivial`, because
  `p.int()` is `OfNat(Succ(p.pred))`.
- **A zero denominator cannot be written.**

What it costs:

- **The literal lies.** `Pos(1)` is two. `Rat(OfNat(1), Pos(1))` is ½ in the
  test suite. Every reader has to do that subtraction.
- **Its operations are not the ambient ones.** `p.mul(q).val() = p.val() *
  q.val()` is a theorem (`Pos::mul_val`), not computation. Omega reads neither
  `val` nor `mul`, so `pos.hthr` restates goals over the predecessors before
  asking. Every further operation (`add`, `pow`, `min`) needs its own shifted
  formula and its own `*_val` bridge.
- **It cannot hold a positive that is computed elsewhere.** `bytes.len()`,
  `p.toNat()` and `ten_pow(i)` are positive by a lemma, not by a `Succ` at the
  head. Getting a `Pos` out of them means subtracting one and proving that
  the subtraction round-trips.
- **It only works for `Nat`.** The regular-reals probe wants positive
  rationals (ε), and a shift does not exist there.

## 2. What call sites actually need

Positivity is already spelled as a hypothesis almost everywhere. In
2026-10-10's `lib/` there are about fifty binders shaped `name: 0 < x`,
mostly in the native libraries (`elf64_command`, `elf64_format_width`,
`elf64_read_filter`, `field_line`) and in `nat.hthr`'s division lemmas. Their
call sites supply the proof in one of three ways:

| How the proof arrives | Examples |
| --- | --- |
| (a) A local hypothesis, passed by name | `Nat::mod_lt(x, p, positive)`, `n.mod_lt(a, pa)` |
| (b) Computation, because the term has a `Succ` or literal head | `dividend.mod_lt(Succ(divisor_pred), trivial)` |
| (c) A lemma about a computed term | `Nat::mod_lt(m, p, ten_pow_pos(Succ(i)))`, `r.mod_lt(c * 8, p8)`, `nonzero_word(p, facts.right.left)` |

A `Pos` type helps with (b) and with nothing else. It cannot reach (c)
unless every producer returns `Pos`, and (a) is a hypothesis that already
exists. A search that tried locals, computation and registered lemmas would
cover all three.

## 3. What discharge exists today (probed)

`h: P := infer` is the only solver. At a goal that is not a class it
consults the derived table, then the **locals in scope, compared by
conversion** (`crates/elab/src/resolve.rs`, step 1), then gives up with "not
a class". The instance registry is never consulted for a bare proposition.

Probes, with `theorem uses(n: Nat, h: 0 < n := infer): 0 < n { h }`:

| Caller | Result |
| --- | --- |
| local `p: 0 < n` | ok |
| local `p: 1 <= n` (convertible: `Lt` is `Le(Succ(·), ·)`) | ok |
| `let p = f.left` from `f: (0 < n) ∧ …` | ok (let aliases are scope) |
| `f: (0 < n) ∧ …` with no `let` | **no**: a conjunct is not a local |
| `uses(Succ(k))`, `uses(5)` | **no**, though the goal reduces to `True` |
| `uses(n + 1)` with `0 < n` in scope | **no** |
| `uses(a * b)` with `0 < a`, `0 < b` in scope | **no** |

Neighbouring mechanisms:

- **Parameter defaults** (`b: Nat := 0`, or `h: P := omega`) did not parse
  when this was written. They landed 2026-10-12
  (`docs/named-arguments-design.md` §9.6): a tactic default runs at the call
  over the caller's hypotheses.
- **Record-field defaults** landed (`h: 0 < v := trivial` or `:= omega`,
  `docs/automatic-author-surface-design.md` §2.3). They only run where the
  construction has no local bindings; under a local, `P(Succ(k))` is refused
  and asks for `h` by name (`issues/field-defaults-under-locals.md`).
- **Solver binders in function types** do not parse
  (`(n: Nat) → (h: 0 < n := infer) → Nat`).
- **A `Fact<P>` class as a workaround** (Lean's `Fact` or `NeZero` shape)
  half-works. `instance(k: Nat) Fact<Nat::Lt(0, Succ(k))>` resolves
  `Fact<0 < Succ(k)>` and `Fact<0 < 5>`. A second rule (`Fact<0 < a * b>`
  requires two `Fact`s) is refused, because instances key on (class,
  carrier head) and both rules have head `Nat::Lt`. A plain local `0 < n` is
  not a `Fact`, so the case that matters most still fails. That is the same
  friction Lean's `NeZero` has.
- **`>` is not an operator** (`docs/comparison-operators.md`). It is spelled
  `0 < x`.

Two diagnostic nits came out of the probes: the failure prints the
parameter's written type (`<(0, n)`), not the instantiated goal (`0 < 5`),
and it uses the prefix spelling, not the infix one.

So "grab it from context if it can, which I think we can already do" is
half true: an exact local, yes; anything derived, no.

## 4. The options, costed

| | Shifted `Pos` (today) | Refinement record `Pos<A>` (option 1) | Hypotheses only (option 2) | Bundled, inferred (option 3 as stated) |
| --- | --- | --- | --- | --- |
| Signature reads | `p: Pos` | `p: Pos<Nat>` | `n: Nat, h: 0 < n` | `n: Pos<Nat>` |
| Runtime value | `pred` | value + proof | value | value + proof |
| `val(p * q)` | a theorem | `p.val * q.val`, by computation | n/a, it is `a * b` | by computation |
| Equality | number equality | compares proofs | number equality | compares proofs |
| Passing a `Nat` | build `Pos(n - 1)` | build `Pos(n, proof)` | pass it, plus a proof | pass it, the proof is searched |
| New machinery | none | none (record), or squash | the search | the search **and** coercion insertion |
| Carriers | `Nat` only | any `A` with `0` and `<` designated | any | any |

Notes on the rows:

- **Equality with a proof field.** `Nat::Le` computes to `True` or `False`
  on constructors, so its proofs are unique. That is provable by induction,
  but the lemma is not in `lib/` yet. On closed values it is definitional
  already, because `True` has η. The other route is a squashed field,
  `∥0 < val∥`, which is definitionally irrelevant. Getting a relevant
  `0 < val` back out of it for omega then needs the decidable-unsquash
  bridge, which is open (`issues/sprop-inductives-and-squash-bridges.md`).
- **Option 1 needs no new class.** `0` and `<` are designations, and those
  already exist at `Nat` and `Int`. `Rat`'s strict order is
  `issues/rational-order-completion.md`. A dedicated `Zero` class would only
  be needed if `0` had to be named generically outside a designation, and
  nothing here needs that.
- **Option 3's extra cost is the coercion.** Passing a `Nat` where `Pos<Nat>`
  is expected means the elaborator inserts `Pos(n, ?)` on a type mismatch.
  That only works where the expected type is already known. Heather has no
  insertion point for that today, and
  `docs/three-small-transfer-experiences.md` §2 deliberately limited the same
  idea to the result boundary of a function. The reverse direction (reading
  a `Pos` where a `Nat` is wanted) is a second coercion, or an explicit
  `.val` everywhere.

## 5. The observation: one engine under every option

Options 2 and 3 discharge the same goal, `0 < x` in the caller's context,
and option 1 does too whenever a `Pos` is built from a computed value.
The only difference is where the obligation appears: as a parameter, as a
constructor field, or at a coercion. Whichever surface is chosen, the work
that removes the noise is the search.

## 6. Recommendation

### A. Make `:= infer` discharge positivity (needed by every option)

Grow `infer` at a non-class proposition goal by two sources, after the
locals and before failure:

1. **Computation.** If the goal reduces to `True` within a small fuel, the
   answer is `trivial`. That covers (b): `0 < Succ(k)`, `0 < 5`, and the
   `Le` goals that close on numerals.
2. **Evidence rules.** These are registered lemmas whose conclusion is a
   proposition, used by backchaining with each premise resolved by the same
   search, so locals come first. Positivity rules are keyed by the head of
   the positive term (`mul`, `add`, `pow`, `len`, `fact`), and that key
   removes the one-rule-per-`Lt` collision the `Fact` probe hit. This covers
   (c): `0 < a * b` from `0 < a` and `0 < b`, `0 < ten_pow(i)`, `0 < n.fact()`.

The spelling for registering a rule is open. One candidate reuses
`instance(a, b: Nat) 0 < a * b := Nat::mul_pos`. The keying, decrease
discipline, kernel-gated trial and trace are the ones the class resolver
already has (`docs/traits-layer2-design.md`). One possible third source is
looking through `∧` projections of locals, so `facts.right.left` needs no
`let`. That one is optional: it is cheap, but it widens what "in scope"
means.

Not proposed: **omega inside `infer`.** `infer` runs at every call site of
every solver parameter, invisibly, and omega is the most expensive thing per
goal in the library (`issues/omega-per-goal-elaboration-cost.md`). Omega
belongs where an author chose it:

- **At a call site**, by name: `mod_lt(x, p, positive := omega)`.
- **At a declaration**, as a parameter default: `h: 0 < n := omega`
  (`docs/named-arguments-design.md` §9.6, landed 2026-10-12). It shares
  record fields' machinery. The author who writes it has chosen omega's cost
  for every caller.
- **Later, a `positivity` tactic** that composes the evidence rules and hands
  linear leftovers to omega, usable as `h: 0 < n := positivity`. Whether the
  rules live in `infer` (as above) or only in that tactic is open (§7).

### B. `Pos<A>` as binder sugar, not a type

```heather
theorem Nat::mod_lt(self n: Nat, divisor: Pos<Nat>): n.mod(divisor) < divisor
// elaborates as
theorem Nat::mod_lt(self n, divisor: Nat, divisor_pos: 0 < divisor := infer): …
```

- **Parameters.** `x: Pos<A>` expands to `x: A, x_pos: 0 < x := infer`.
  Inside, `x` is an `A` and `x_pos` is a local, so positivity flows to
  callees through (A). A caller passes a plain `A` and the proof is found,
  which is option 3's behaviour with no coercion, because nothing is ever
  wrapped. The named argument `divisor_pos := …` overrides it.
- **Results.** `fn ten_pow(i: Nat) → Pos<Nat>` returns a `Nat` and gives the
  function a theorem `ten_pow::pos(i): 0 < ten_pow(i)`, registered as an
  evidence rule. The name is deterministic and owned by the function, not a
  hygienic minted name in the shared namespace. The body's positivity is an
  obligation discharged by (A), or left as a resumable goal, as field
  defaults already do. This is what turns (c) into (a):
  `ten_pow_pos(Succ(i))` disappears from call sites.

  Function-owned names exist as of 2026-10-11
  ([function-owned-members](../issues/function-owned-members.md)): a `fn`
  owns members as a type does, and `theorem ten_pow::pos` declares one,
  reached by qualification. Letting a `fn` own members is useful beyond
  positivity, since many theorems are about one function rather than about
  its result type. `ten_pow::pos` is the safe spelling. `ten_pow.pos` would
  collide with receiver dispatch, which resolves `f.m` by the type of `f`,
  here a function type; written anyway, it is refused with the qualified
  spelling named.
- **Record fields.** `den: Pos<Nat>` expands to `den: Nat, den_pos: 0 < den`,
  plus a rule `0 < r.den` from `r.den_pos`. `Rat` becomes
  `{ num: Int, den: Pos<Nat> }`, reading exactly as it does today, but the
  denominator is the number itself.
- **Carriers.** Any `A` with `0` and `<` designated works, which is option 1's
  generality without a type former.

Costs, as shapes:

- **Elaboration.** The sugar is a desugaring. The search runs only on solver
  parameters, which are opt-in per binder, so it adds no route to ordinary
  inference. Each extra source is bounded: computation by fuel, rules by the
  resolver's depth cap. Every candidate is kernel-checked at the goal before
  it is taken, as today.
- **Kernel and certificates.** One proof argument per call. It is a variable,
  `trivial`, or a short application of rule lemmas, all small next to the
  terms around them. The shifted `Pos` has no proof argument, but pays in
  `*_val` bridge theorems and restated omega goals instead.
- **Native compilation.** Nothing changes today. The compiled fragment is
  `BitVec(64)` only and refuses solver parameters
  (`crates/elab/src/function_ir_source.rs`, `reflect`), and `Pos` and `Rat`
  are not compiled. In the long run the sugar leaves the runtime value a
  plain word, with the proof parameter for `Compile` to erase. A shifted
  representation would put an increment on every `val` and make
  `pred = 2^64 - 1` an overflow edge. The native libraries' positivity
  hypotheses are the largest existing customer of (A).

What the sugar does not reach is a position with no binder: a function
domain (`Pos<Nat> → Rat`, the shape of Bishop-style regular sequences and of
CoRN's `Qpos`-indexed approximations) and a container element
(`List<Pos<Nat>>`). Those need a real refinement type: a record with a
squashed or relevant field, plus expected-type packing at known positions.
That is option 3 in full, and it should wait for the regular-reals probe to
ask for it.

### C. Retire the shifted representation

Once B exists, migrate `Rat` to `den: Pos<Nat>`. The cancellation lemmas
take `p: Pos<Int>` (sugar) or `h: 0 < p`. Then delete `Pos { pred }`. The
migration is mechanical, and most of `pos.hthr` (`mul_val`, `mul_int`, the
restated omega goals) goes away rather than being ported. Until then,
`Pos` stays as `Rat`'s private implementation detail and gets no new users.

### Prior art, briefly

Mathlib has `ℕ+` as a subtype with coercions, but most of its theorems take
`(hn : 0 < n)`, and the type-level positivity it does need (`ZMod n`,
`Fin n`) goes through the `NeZero n` class, which is inference. F* and Liquid
Haskell get the "pass a nat, the refinement is checked" experience from
built-in refinement subtyping with an SMT solver as the engine. Heather has
neither, and B gets most of that surface from the resolver it already has.
CoRN's `Qpos` is the function-domain case B deliberately leaves to a later
type.

## 7. Decisions

Taken by Minus, 2026-10-10:

1. **Route: B on top of A.** Sugar over search; no `Fact`-style class.
2. **Spelling: `n: Pos<Nat>`.** A property that is not worth a name is an
   ordinary proof parameter, so there is no general `where` form.
3. **`h := omega` should parse** as a parameter default (§6 A), and a
   dedicated positivity tactic is wanted eventually.
4. **Result facts are named under the function** (`ten_pow::pos`) rather
   than minted, which needs function-owned members (§6 B).

Then, the same day:

5. **Rules live in `infer`**, not only in the tactic, so a `Pos<Nat>`
   parameter works with no default written.

Settled by the round-1 implementation (§9): a hand-written rule is spelled
`evidence theorem`.

Still open: **whether `infer` looks through `∧` projections of locals.**

## 8. Rounds this implies, in order

1. `infer` at proposition goals: computation to `True`, and evidence rules
   with head-of-term keys if open question 1 puts them there. Fix the two
   diagnostic nits from §3 in the same round.
2. Parameter defaults with a stored goal (`h: 0 < n := omega`), sharing the
   record-field machinery (`issues/field-defaults-under-locals.md`).
3. Function-owned members (`theorem ten_pow::pos`).
4. `Pos<A>` binder sugar for parameters, then results (with `f::pos`), then
   record fields.
5. Migrate `Rat` and the cancellation lemmas, and delete the shifted `Pos`.
6. A `positivity` tactic.
7. A refinement *type* for function domains and containers, when the
   regular-reals probe needs one.

Each round has an issue: [infer-proposition-evidence](../issues/infer-proposition-evidence.md)
(round 1), [named-arguments](../issues/named-arguments.md) (parameter
defaults), [function-owned-members](../issues/function-owned-members.md),
[pos-binder-sugar](../issues/pos-binder-sugar.md),
[retire-shifted-pos](../issues/retire-shifted-pos.md),
[positivity-tactic](../issues/positivity-tactic.md) and
[positive-refinement-type](../issues/positive-refinement-type.md).

Owners elsewhere:
[setoid-auto-lifting](../issues/setoid-auto-lifting.md) and
[subtype-transfer-and-evidence](../issues/subtype-transfer-and-evidence.md)
own lifting operations and comparing evidence policies for real subtypes,
which round 7 would feed.
[field-defaults-under-locals](../issues/field-defaults-under-locals.md) owns
the stored-goal machinery that parameter defaults would share.
[implicit-logical-assumptions](../issues/implicit-logical-assumptions.md)
owns `assuming`/`using`, whose `infer` precedence (explicit, local,
derivation, scope providers) round 1 extends and must not reorder.

## 9. As landed: round 1 (2026-10-10)

`:= infer` at a goal that is not a class now tries, after the derived table,
the locals and the upcast pass:

1. **Computation.** `trivial` is proposed when the kernel accepts it at the
   goal within a small fuel (`COMPUTE_FUEL` in `crates/elab/src/resolve.rs`).
   `0 < 5`, `0 < Succ(k)` and `0 < k + 1` close this way; `0 < 0` does not.
2. **Evidence rules.** A rule is a theorem marked `evidence`:

   ```heather
   evidence theorem Nat::mul_pos({a, b: Nat}, pa: 0 < a := infer, pb: 0 < b := infer): 0 < a * b {
       (1).mul_le_mono(a, 1, b, pa, pb)
   }
   ```

   Every parameter must be one search can fill: `{…}` values are solved by
   unifying the conclusion with the goal, and premises are `:= infer`. A rule
   is therefore tried exactly as an instance is, by elaborating its bare name
   against the goal (`build_candidate`), so its premises recurse through the
   same search with the caller's locals first. It is also an ordinary
   theorem: `Nat::mul_pos()` searches every premise, `Nat::mul_pos(pb := q)`
   names one.

Rules are keyed by the qualified name of the conclusion's relation
(`nat::Nat::Lt`), read off the checked statement, and listed in canonical
order. Each records the head of every relation argument (a global, `Zero`,
`Succ`, or a variable), which prefilters candidates; the kernel-checked
trial decides. Several rules about one relation coexist.

**Termination** is Paterson's condition, as for instances
(`docs/traits-layer2-design.md` §6), checked on the elaborated statement:
each premise has fewer symbols than the conclusion and mentions no binder
more often. A premise that would grow the goal is refused at the
declaration.

**Persistence.** A rule is a module event (`DeltaEvent::Evidence`), so it
reaches importers and survives semantic-image replay. The image format's
magic was bumped, since `Decl` gained `is_evidence`.

**Trace.** New keys: `computed`, `rules`, `no-rule`. A failed proposition
goal is now displayed as the call instantiated it, `Lt(0, mul(a, b))`, not as
the callee's written `<(0, n)`. It is spelled rather than decoded, because
decoding reduces `0 < 0` to `False`. Operator notation in it is
[diagnostic-operator-resugaring](../issues/diagnostic-operator-resugaring.md)'s.

**Library.** `nat.hthr` registers `Nat::mul_pos`, `Nat::add_pos_l` and
`Nat::add_pos_r`. No existing signature changed: a `0 < d` parameter only
benefits once it is written `:= infer`, which is a positional-arity change
for its callers and belongs with the `Pos<A>` sugar.

Tests: `crates/elab/tests/lib_std_evidence.rs`.

## 10. As landed: the `positivity` tactic (round 6, 2026-10-11)

`positivity` is a tactic term, written where a proof of a proposition is
expected (`{ positivity }`, `needs(a * b, positivity)`, a `let` with its
statement written). It runs the search `:= infer` runs at that goal
(`Elaborator::positivity`, `crates/elab/src/resolve.rs`), with one more
source at every proposition subgoal:

1. Locals up to conversion, then computation to `True`, then the evidence
   rules, exactly as §9. Each is one kernel trial.
2. **Omega**, only where all of those failed at that subgoal. Rule
   premises recurse through the same search, so omega runs at the
   *leaves* the rules leave over, not at the goal: `0 < a * b` with
   `2 <= a` and `5 <= b` in scope is `Nat::mul_pos` with an omega proof of
   each factor. Omega alone treats `a * b` as an opaque atom and is stuck
   on that goal.

Why it is cheap:

- **The cheap sources always run first.** A goal a local, a computation or
  a rule closes runs no omega at all (`a_local_computation_or_rule_needs_no_omega`
  asserts the count).
- **Omega's calls are bounded.** A run remembers the subgoals omega was
  stuck on and does not try them again, so a failing run costs at most one
  omega call per distinct subgoal. A successful leaf is not memoized: its
  proof may name an atom-list slot a rejected rule took back with it.
- **A rejected attempt leaves nothing.** A rule or an omega call that does
  not end in the proof gives back its dependency edges, checking notes,
  named atom lists, warnings and Omega reports (`SearchMark`).
- **Rules skip goals headed by a local.** A goal argument whose head is a
  local can only meet a rule binder, since a local has no definition to
  unfold, so a rule about `a * b` is not tried at `0 < b`. This prefilter
  is shared with plain `:= infer`, where it only removes trials that fail.
- **Omega's own certificate runs with plain `infer`.** The flag that turns
  the omega source on is taken down for the duration of the call.

Without `import omega;` the tactic still runs steps 1, and the trace says
omega was not tried. A failure prints the whole search, with one line per
omega call (omega's verdict, not its report; `omega` written at the goal
gives the report).

Not in this round:

- **`h: 0 < n := positivity` as a parameter default** needed parameter
  defaults, which are [named-arguments](../issues/named-arguments.md)'s
  (§8 round 2). They landed 2026-10-12, and this default works.
- **Goals other than a relation.** `positivity` accepts any proposition and
  is only as good as the rules about it: there are rules about `Nat::Lt`
  and nothing else yet, so `e ≠ 0` and goals over `Int` are omega's alone
  for now (`Nat`'s `0 <= e` computes to `True`). New rules extend the tactic and
  `infer` together, with no change here.
- **`∧` projections of locals** (§7, still open) would reach the tactic
  through the shared search if `infer` takes them.

Tests: `crates/elab/tests/positivity_tactic.rs` (in the `omega` family,
which already builds the omega prefix).
