# Optimizer rules as theorems about words

A proposal for how the optimizer's rules and its `learn` search are written,
shared and read. It extends `optimizer-design.md` §4 ("an optimization is a
theorem"), which sketched a `rule` prefix before the rules existed, and
replaces that section's spelling with one that covers what the rules became.
Nothing here is built yet except the probe in §5. Minus agreed the surface,
the report and the direction on 2026-11-16 (§11).
The work is tracked in `issues/optimizer-rules-as-theorems.md`.

## 1. What writing a rule costs today

A rule (`lib/native/function_ir/function_ir_rules.hthr`) is three pieces
written by hand, and the same rule is then spelled a fourth time in the
search:

```heather
// 1. The clause, over node constructors and ids.
fn within_add(o, l, r, a, b, c, d: Nat) → Clause {
    Clause([Is(Add(64, o, l, r)), Within(l, a, b), Within(r, c, d)], Within(o, a + c, b + d))
}
// 2. Its soundness, over a valuation and a tuple of premises (`held.right.left.right`).
theorem within_add_sound(o, l, r, a, b, c, d: Nat, fits: (b + d).leb(word_top()) = True): within_add(o, l, r, a, b, c, d).Sound() { … }
// 3. Its line of `rules()`, unpacking the numbers three times.
Rule::when(λ n => (num(n, 4) + num(n, 6)).leb(word_top()),
    λ n => within_add(num(n, 0), num(n, 1), num(n, 2), num(n, 3), num(n, 4), num(n, 5), num(n, 6)),
    λ n ok => within_add_sound(num(n, 0), num(n, 1), num(n, 2), num(n, 3), num(n, 4), num(n, 5), num(n, 6), ok)),
// 4. In function_ir_learn, the recogniser: by the rule's place in the table, numbers in the clause's order.
True => Passed([], seen.learn(o, Range(a.low + b.low, a.high + b.high), [l, r], Derive(4, [o, l, r, a.low, a.high, b.low, b.high]))),
```

What is wrong with that, in the order it hurts:

- **It does not read as what it says.** The rule is "a sum that cannot wrap
  lies within the sums of its parts' bounds". The clause says it in ids:
  `o`, `l`, `r` are numbers naming words, the reader has to hold which
  argument of `Add` is the output, and `Is`, `Within`, `AtMost` are the
  replayer's bookkeeping showing through.
- **The proof is mostly plumbing.** Each soundness proof introduces a
  valuation, walks a right-nested conjunction, rewrites by each node's
  equation, and only then proves something about words.
- **A side condition is a Boolean function of a list of numbers**, with the
  proposition it decides recovered by hand (`leb_below`).
- **A rule is named by its place in a list.** `Derive(44, …)` in a plan, in
  `learn` and in the probes. A user's module cannot add one.
- **`learn` restates every rule.** A mistake in the order of a `Derive`'s
  numbers is found as a replay refusal.

## 2. The proposal in one picture

**A rule is an ordinary theorem about words. The author never writes a
node, an id, a valuation, a clause or a guard.** The `rule` prefix reads the
theorem's statement and produces all four pieces of §1 from it.

The rules above and their neighbours, as they would be written (spelling of
the fact forms is §4's; operators are `u64`'s own):

```heather
rule theorem add_zero({w: Nat}, x: BitVec(w)): x + 0 = x

rule theorem within_add(l, r: u64, {a, b, c, d: Nat},
    left: l.within(a, b), right: r.within(c, d), fits: b + d ≤ u64::top()):
    (l + r).within(a + c, b + d)

rule theorem narrow_back(s: u64, {n, high: Nat}, small: s.within(0, high), fits: high < 2 ^ n):
    s.resize(n).resize(64) = s

rule theorem below_yes(l, r: u64, {a, b: Nat}, left: l.within(0, a), right: r.within(b, u64::top()), apart: a < b):
    l.below(r) = 1

rule theorem order_set(l, r: u64, below: l.below(r) = 1): l.nat() + 1 ≤ r.nat()

rule theorem join_shift(f: Buffer, i, a: u64, {n, sh, c: Nat}, joined: a = f.join(i, n) << sh):
    a << c = f.join(i, n) << (sh + c)

rule theorem join_word(f: Buffer, i: u64):
    f.join(i, 4) = f.word(i).swap_bytes().resize(64)
```

Each of these is a statement a reader of the library would write anyway, and
several already exist there. Rule 44 (two byte swaps cancel across a widen
and a narrow) stops being a rule of its own:

```heather
rule theorem BitVec::byte_swap_byte_swap(…): w.byte_swap(k).byte_swap(k) = w     // already in bitvec_bytes
rule theorem BitVec::resize_round_trip(…, fits: n ≤ m, …): a.resize(m).resize(n) = a   // already in bitvec_resize
```

The search applies the second, then the first. That is §4's "a library's
theorems are its clients' optimizations" from `optimizer-design.md`, and it
is why the statement form matters more than the sugar: the person who knows
a type's algebra tags its theorems in the type's own file.

## 3. How a statement is read

The prefix is a declaration-prefix generator written in Heather
(`docs/metaprogramming/value-definitions-design.md`), reading the theorem's
type as code (`fn-signature-reflection-design.md`). It classifies each
binder by its type and each hypothesis by what it mentions.

| In the statement | Becomes |
|---|---|
| A binder of a word type (`BitVec(w)`, `u64`, `u32`) | An id of the clause, at that width |
| A binder `f: Buffer` | A buffer's number |
| A binder of `Nat` | A literal: a number of the instance |
| A term built from the IR's operators over those (`l + r`, `x.resize(n)`, `f.word(i)`) | A node premise for each operator, with a fresh id for what it writes |
| A hypothesis that mentions only literals (`b + d ≤ u64::top()`) | A guard, decided by evaluation where the rule is applied |
| A hypothesis that mentions a word or a buffer | A fact premise: it has to be one of the fact forms of §4 |
| The conclusion `term = variable`, `= literal`, `= one operator` | `Move`, `Const`, or that node writing the left side's id |
| The conclusion `term = deeper term` | The inner operators are nodes the plan puts first (as the word load does), the outermost the conclusion |
| The conclusion a fact form of a term | That fact about the term's id |

The operators it knows are a table from a library function to a node
constructor (`BitVec::add` to `Add`, `BitVec::resize` to `Resize`, …), a
registered value like any other, so a target that adds a node adds a row.

A statement the generator cannot read is refused where it is declared, in
the statement's words: "the hypothesis `small` mentions the word `s` and is
not a fact the optimizer keeps (it keeps: a range, an order between two
words, …)", or "`x.popcount()` is not an operator of the IR". A theorem can
always be proved without being a rule, so nothing is lost by a refusal.

Some of today's rules have nothing left to say in this form, which is a
sign the form is right. `move_move` is `x = x`. `load_again` is "two reads
of `f.byte(i)` are one word", which is one term written twice. Both are
what the replayer's `Again` step (the same computation over the same
operands) is for, and the generator can say so.

## 4. Conditions, with no `when`

`optimizer-design.md` §4 named three kinds of condition by who answers
them. A separate `when` clause would cover only the first and would grow a
second language for conditions. Reading the hypotheses by what they mention
covers all of them with the one language there already is:

- **On the instance's literals.** A hypothesis over `Nat` binders alone.
  The generator asks for its `Decide` instance (`lib/std/core/bool.hthr`),
  uses the instance's bit as the guard and `decide_true` to hand the proof
  to the theorem. Anything decidable is a condition: a comparison, a
  conjunction, `n.divides(64)`, a membership in a table.
- **A certificate.** A literal that appears in no premise is supplied by
  the search. `order_join`'s `u` and `v` are that today. So "something more
  complex" than a comparison is a hypothesis `check(witness, …) = True`
  for any function, with the witness a literal the search finds and the
  kernel only checks. A linear-arithmetic step with its multipliers, or a
  path through a graph of orders, is one rule this way (§9.3).
- **On values.** A hypothesis about a word: a fact premise, found among the
  facts, and where it is not there, asked for (`optimizer-design.md` §5,
  facts on demand).
- **On the buffers.** A term `f.byte(i)`, `f.word(i)`, `f.join(i, n)`: a
  memory fact, which the replayer keeps until something may store.

**Fact forms.** The facts the replayer keeps (`Fact` in
`function_ir_replay.hthr`) get a spelling each, as a method on the word
they are about, so that a hypothesis is recognised by its head:

| Fact | Written | Meaning |
|---|---|---|
| `Within(x, a, b)` | `x.within(a, b)` | `a ≤ x.nat() ∧ x.nat() ≤ b` |
| `AtMost(x, m, y, n)` | `x.nat() + m ≤ y.nat() + n` | as written |
| `Low(x, y, sh)` | `x.low_byte() = (y >> sh).low_byte()` | as written |
| `Loaded(BufferLoad(x, f, i))` | `x = f.byte(i)` | the byte now at `i` |
| `Joined(x, f, i, n, sh)` | `x = f.join(i, n) << sh` | `n` bytes from `i`, joined |
| `Split(w, a, b, c, d)` | `w.bytes() = [a.low_byte(), …]` | a word's bytes are four low bytes |

`f: Buffer` stands for the bytes of buffer `f` as they are when the rule is
applied, which is what `Buffers()` at a number is in a clause's soundness.

## 5. Soundness is generated, and it is still required

A `Rule` carries its proof, so an unproved rule cannot enter a table. That
stays. What changes is who writes the part of the proof that is not about
words. From the theorem the generator writes the clause's `Sound` proof,
and it is the same three moves every time: read the words at the valuation,
rewrite the conclusion by each node premise's equation, hand the fact
premises (and the guard through `decide_true`) to the theorem.

`lib/_tests/native/function_ir/function_ir_rule_words_tests.hthr` checks
that this works for four of today's rules of different kinds (an equation,
a range with a guard, a chain of four nodes, a memory fact): each is stated
as a theorem about words with no node in it, and today's clause is proved
sound from it by exactly those moves, in two or three lines. The word
theorems came out shorter than the proofs they replace, because the
plumbing left.

For the author's own proof, the statement being about words means the
ordinary tactics apply: `simp` with `BitVec`'s default set, `omega` once
ranges are naturals. Most range and order rules should close by one call,
and the algebraic ones by naming a lemma.

One loosening worth having later: a **candidate** rule, stated and not
proved, which the search may use to report what it would gain and which no
certificate accepts. It tells you whether a rule is worth proving.

## 6. Tables: registered, named, in sets

- **`rule theorem` registers** the rule (`register def`, `registered(Rule)`,
  `docs/metaprogramming/registered-values-design.md`). The table a
  compilation uses is the registered rules of the program's import closure,
  so a user's module adds rules by declaring them.
- **A plan names a rule by its key** (`name_of(within_add)`), and the
  replayer looks it up in the table it is given. `replay_sound` already
  holds for any table of sound rules, so nothing proved changes. Whether
  the certificate carries keys or places in the closure's key order is a
  cost question for the build.
- **Sets**, as `simp` has (`SimpSet`): a target's set (what its
  instructions do cheaply), a default set, and a constant-time set that
  leaves out every rule whose result depends on data. A compilation names
  the sets it uses.
- **`rule_check`**, as `simp_check`: two rules that undo each other at
  equal cost, a rule no test function fires, a rule another subsumes.

## 7. Learn

`learn` is untrusted, so the question is only effort and reach. It is two
things today, and they want different treatment.

**Finding instances of rules.** Most of `Seen::pass` is: a node arrives,
look up what made its operands and what is known of them, check a guard,
propose `Derive(k, numbers)`. The generator has the premises as patterns,
so one matcher does this for every rule: it starts from the premise that
writes the id just passed, follows operand ids through `seen.made` (the
index it needs is already there), finds fact premises in the walk's
ranges, orders and loads, evaluates the guard, and proposes the instance
with its numbers in the clause's order by construction. A user's rule
fires without the user reading `learn`.

What the matcher needs beyond the statement is small and optional:

- **A direction.** An equation is applied left to right where the right
  side is cheaper by the cost the search already uses, so most rules need
  nothing. A rule can say `rule(always)` or `rule(never_alone)`.
- **A bound** for facts that chain (a range gives a range), which the walk
  has by being one pass.

**Strategies.** The word store (grouping four stores, `Paid`, `Four`), the
word load, guards from tests and `Again` are not one rule's instance. They
become registered **learners**: a record with a pass over the walk's state
and a node, run in a stated order, beside the matcher. A user can add one,
and it is outside what is trusted like the rest of the search.

### 7.1 What a learner can promise

A learner needs no proof to be safe: the replayer refuses a wrong plan. A
proof is still worth having where it says something a user would otherwise
find out by a refusal or a slow compile. None is required; a learner that
has one registers it beside itself, and the report (§8) and `rule_check`
show which it has.

| Property | Statement | What it buys |
|---|---|---|
| **Accepted** | Every plan it proposes replays: `replay(facts, learner(seen, node))` is never `None` | A refusal can no longer come from this learner. For the matcher this is one theorem for every rule: it proposes an instance only where the premises are among the facts and the guard is true. The first to prove |
| **No dearer** | The nodes out cost no more than the nodes in, by the search's cost | The optimizer never makes this function worse through this learner |
| **Bounded** | The plan is at most a stated multiple of the nodes it read | What the kernel pays to replay is linear in the function, whatever the function |
| **Settled** | Run on its own output it proposes nothing | No reason to run the pipeline twice. Checkable on the library's functions where a proof is awkward |
| **Finds it** | On a stated shape it fires: "four byte stores in a row into one buffer, of the four low bytes of one word's shifts, become a word store" | The optimization is part of the library's contract, and a change that loses it fails a theorem and not a benchmark |
| **Monotone** | With more facts it proposes no less | Adding a rule or a domain cannot lose an optimization |

"Accepted" and "Bounded" are about the learner and the replayer and are
provable now. "Finds it" is the one a reader cares about, and today it is
stated only at examples, as the probes that evaluate a search on one
function. The general statement needs the shape as a predicate on a list of
nodes, which the rule's own premises (§3) already are for a single rule.

## 8. Reading what the optimizer did

The same statements serve as the report. A plan step and a refusal print
in the rule's own words, with the instance's words named as the source
names them where there is a name:

```
i + 4 within 4 ..= 60          by within_add   (i within 0 ..= 56, 4 within 4 ..= 4)
(i + 4) below len = 1          by ordered_below (i + 4 + 1 ≤ len)
join(block, i, 4)              = word(block, i).swap_bytes().resize(64)   by join_word
not applied: narrow_back at t9: needs `s within 0 ..= 255`, known `s within 0 ..= 4095`
```

`compile-x86 --explain-optimizer` printing that per function is the
optimizer's `simp_show`. A page listing every registered rule with its
statement is generated from the same data.

## 9. Bolder options

These go further than the syntax. Each stands alone, and each is a choice.

### 9.1 Domains: an analysis is one registered thing

Rules 2 to 6, 16 to 18 and 39 are one abstract interpretation: a range for
each operator from its operands' ranges. As rules they have three limits
that no spelling removes:

- **A rule cannot say what holds where two paths meet.** After a
  conditional the range of a word is the hull of its range on each arm.
  That is a property of ranges, not of any node.
- **A rule cannot say what holds around a loop.** "The counter stays below
  the length" is a fact that holds at the head because it held on entry and
  the body keeps it. This is the loop law with the counter's range, which
  the word load and the word store both stop at today.
- **The search repeats the rules.** `learn` computes `a.low + b.low` to
  know what to propose, and the rule computes it again to be checked.

A **domain** is what is known of one word, with the operations those three
need, and one theorem for each:

```heather
record Domain<A> {
    Holds: A → u64 → Type,                    // what an element says of a word
    top: A,                                   // nothing known
    meet: A → A → A,                          // both of two things known
    join: A → A → A,                          // what holds on either of two paths
    below: A → A → Bool,                      // `a` says at least what `b` does
    of: Node → (Nat → A) → A,                 // of the word a node writes, from its operands'
    from_test: Node → Bool → (Nat → A) → List<Learned<A>>,   // of a test's operands, from its bit
}

class Domain::Sound<A>(d: Domain<A>) {
    top_holds: (x: u64) → d.Holds(d.top, x),
    meet_holds, join_holds, below_holds: …,
    of_holds: (node: Node, known: Nat → A, values: Valuation()) →
        NodeHolds(values, node) → ((id: Nat) → d.Holds(known(id), values(64, id))) →
        d.Holds(d.of(node, known), values(64, node.writes())),
    from_test_holds: …,
}

register def ranges: Domain<Range> = …;       // today's `Range`, `Range::meet`, and rules 2–18, 39 as `of`
```

The author does not write `of` by cases over node constructors. The cases
are the `rule theorem`s whose conclusion is the domain's fact and whose
conclusion's numbers are computed from the premises' (`within_add` is one:
`a + c` and `b + d` come from the premises). The generator groups those by
the operator they are about and writes `of`, with `of_holds` from their
proofs. So a domain is declared by naming its lattice, and filled by rules
written as in §2.

What the replayer does with a registered domain:

- **At a node**: one step, "know what the domains say", which evaluates
  `of` once and adds the fact. It replaces a `Derive` per node and the
  search's copy of the arithmetic.
- **After a conditional**: the facts are the `join` of the arms', where
  today they are forgotten.
- **At a loop**: the plan names an element for each word the loop writes
  (the search's guess). The replayer runs the body's nodes once from those
  elements and checks the result is `below` them. `join_holds` and
  `below_holds` make that an induction proved once, for every domain.
- **A request** (`optimizer-design.md` §5: "is this index below that
  length?") is answered by asking each domain.

Other domains of the same shape, each a page: **known bits** (a mask of
bits known zero and one known set, which decides `x & m = x` and alignment),
**nonzero**, **a multiple of** (strides), **the low byte of** (today's
`Low`). A DSL or a backend registers its own: "a valid index into this
table", "a normalised float". Two domains inform each other through rules
between their facts, which are ordinary `rule theorem`s (`sum_within_low`
is one from a range to an order).

What a domain of this shape cannot hold is a fact about two words (an
order, §9.3) or about two runs (that a value does not depend on a secret).
The first is a relational domain with the same operations over a different
carrier. The second is not a property of a valuation and is out of scope
here.

### 9.2 Open fact forms

`Fact` is a closed inductive with seven constructors and `Facts` a record
with a field for each. A user's domain cannot add a kind. Making a fact a
registered form (its meaning over a valuation and the buffers, its
equality, whether a store forgets it) with the facts keyed by form opens
that. It touches the replayer's proved core and what a lookup costs the
kernel, so it comes after the surface, and only if 9.1 shows the demand.

### 9.3 Orders are a graph, and one rule with a certificate

An order fact is `x + m ≤ y + n` with `x` and `y` words read as naturals
and `m`, `n` literals. Subtract and it says `x − y ≤ n − m`: one word is at
most another plus a constant. Draw each as an edge from `x` to `y` with
that constant as its weight. A range joins the same picture through one
extra vertex for zero: `x.within(a, b)` is an edge each way between `x` and
zero.

```
        ≤ −1            ≤ −4             ≤ 0
   i ─────────▶ end   i+4 ◀──────── i    end ─────────▶ len
   (i < end)          (i+4 is i plus 4,   (end ≤ len)
                       no wrap)
```

Then:

- **Two edges that meet compose**, weights added: `i − end ≤ −1` and
  `end − len ≤ 0` give `i − len ≤ −1`. That is `order_join` (rule 24).
- **"Is `i + 4 ≤ len` known?" is a shortest path**: is there a path from
  `i` to `len` whose weights sum to at most `−4`.
- **A cycle of negative weight is a contradiction**, so the code reached
  under those facts is dead. Nothing finds that today.

What `learn` does now is keep a list of orders and, when a new one
arrives, join it with every one it knows that it meets
(`Seen::knowing`, `known_joined`), each join a `Derive(24, …)` in the plan,
under a cap on how many it keeps. So it pays for every pair whether or not
anything asks, it loses chains past the cap, and the plan carries a step
for each pair.

As a graph: the walk records only the edges that are created (a test's
bit, a sum that cannot wrap, a range). When something asks (a comparison
to decide, a bound for a load), it finds a shortest path, and the plan
gets **one** step whose numbers are the path. The rule behind it is one
theorem, by induction on the path:

```heather
rule theorem order_path(path: Path, wanted: Order, enough: path.weight() ≤ wanted.weight()):
    path.Holds() → wanted.Holds()
```

Here the path is §4's certificate: literals the search supplies and the
kernel checks by adding weights. Of today's order rules, the ones that
create an edge stay as written (20, 21, 25 to 28), and the ones that
compose or convert (24, 34, 35 and the range-to-order pair) are this one.

Abstract interpretation calls this the zone domain. It is the relational
domain §9.1 points to, with `join` the edgewise maximum. The same shape
with a multiplier on each edge is linear arithmetic by a Farkas
certificate, for `2 * i + 1 ≤ n` (`cutsat`'s certificate is the precedent
in the library).

### 9.4 Saturation for the equations

With rules as equations and the matcher generic, the search for the
equational rules is equality saturation: put the function's terms in an
e-graph, apply every rule in both directions until nothing new appears or
a budget ends, extract the cheapest term for each word the function still
needs, and emit the rewrites that reach it as the plan. It removes the
phase-ordering problem (a rule that only pays after another fires) and
the per-rule direction of §7.

The library has the graph (`lib/std/data/egraph.hthr`, built for `grind`):
classes closed under congruence, `union` with a justification of any
type, `ematch` for a pattern's instances up to the classes, and `explain`,
which folds the one path between two members of a class through a
client's algebra. Here the operator is a node constructor at a width, the
justification is a rule's instance, and the algebra `explain` folds into is
plan steps: a given edge is a `Derive`, a congruence is `Again`. So the
plan comes out of the module as it stands. What is to write:

- **Extraction**: the cheapest member of each class by the search's cost,
  bottom up, with sharing counted once.
- **A schedule and a budget**: which rules to match each round, and when
  to stop, since some rules (commutativity, associativity) grow the graph
  without end.
- **Conditions**: a rule with a fact premise reads it from the class. A
  class carries what each domain knows of it (§9.1), joined when classes
  meet, which is the e-class analysis of the egg design.

The kernel replays only the chosen chain, so the graph is untrusted and
its own soundness theorems are not needed here.

### 9.5 Rules found by machine

`optimizer-design.md` §4 already leaves this door open. With statements as
theorems about words and a `bv`-style decision for small ones, a tool can
enumerate small terms, keep pairs that agree on test inputs as candidate
rules (§5), measure what each gains on the library's own functions, and
prove the ones that pay.

## 10. Build order

Each step lands alone and leaves the optimizer producing the same code.

1. **Fact forms and operator table** as library definitions (§3, §4), and
   the generated soundness as a tactic (`rule_sound`), used by hand on
   today's clauses. No language change.
2. **`rule theorem`**: the generator, registering by name; port rules 0 to
   44; plans name rules by key; `rules()` goes. `load_again` and
   `move_move` go to `Again`.
3. **The matcher** in `learn`, with "Accepted" (§7.1) proved for it, the
   single-rule recognisers ported onto it and the strategies as registered
   learners.
4. **The report** (§8) and `rule_check`.
5. **Saturation** (§9.4) for the equation rules, on the library's e-graph.
6. **Domains** (§9.1), ranges first, then facts where paths meet and the
   loop check.
7. **Open fact forms** (§9.2), then the order graph (§9.3) as the first
   relational one, tagged library theorems replacing composite rules, and
   rules found by machine (§9.5).

## 11. Decided

Minus, 2026-11-16:

- **The surface** of §2 to §4: a plain theorem about words under a `rule`
  prefix, hypotheses read by what they mention, no `when`. The fact
  spellings of §4 stand ("decent enough if a bit odd").
- **The report** of §8 is wanted.
- **Learners are encouraged to carry correctness properties**, none
  required (§7.1 is the list offered in answer).
- **Saturation: yes**, on the e-graph work the library has, since the
  rules will be many.
- **Open fact forms are valuable**, for stranger backends and properties.
- Domains and the order graph: sketched further at his request (§9.1,
  §9.3), not yet ruled on. Rules found by machine: liked, later.

## 12. What is built

Steps 1 and the generator of step 2.

- **`rule_sound`** (`lib/native/function_ir/function_ir_rule_sound.hthr`):
  a clause's soundness from a theorem about words. It reads each premise
  at the valuation, rewrites the rest by the equation of each node premise
  and hands the fact premises to the theorem. `given` passes proofs of the
  theorem's guards.
- **`rule theorem`** (`function_ir_rule.hthr`): the theorem is published as
  written, and beside it `name_rule: Rule`, the clause the statement stands
  for with its guard and its soundness. Read today: binders of `Nat` and
  `BitVec(w)`, the IR's operators (written as methods or as operators, so
  `x + 0`), equations, `Range(a, b).Holds(x)`, orders over `toNat()`, and
  guards through their `Decide` instance.
- **A rule's numbers** are its binders in the order written, then the word
  each operator writes, outermost first. A plan's `Derive` gives them in
  that order.
- **A term written twice is one node**: the sum in a hypothesis and in
  the conclusion of `sum_tested_low` is one `Add`. Terms are compared as
  written, not by conversion.
- **A hypothesis about a word the theorem binds** (`a = 0` for a binder
  `a`) is a premise kept as a fact; one about a term (`l.below(r) = 1`) is
  the term's node and what it is.
- **Ported**: 31 of the 45 rules of `function_ir_rules.hthr` are
  `rule theorem`s: x + 0, the ranges, the comparisons both ways, the
  one-bit or, the orders and their join, the sums that do not wrap, and the
  swap cancellation. `rules()` lists each `name_rule` in its old place.
- **Not ported**: the fourteen that need what the reader does not read
  yet. The joins and the split of a word (29 to 33, 40 to 43) and
  `load_again` (19) speak of a buffer's bytes; `move_move` (1) and
  `within_move` (3) have no operator, since a move is equality of words.
- **Plans still name a rule by its place** and give its numbers in order,
  in `Derive` and in `Know`. Porting a rule reorders its numbers, so every
  plan that names it changes with it. That is the cost step 3 removes: the
  matcher finds the numbers from the statement.

Where the build differs from the sections above, for now:

| The doc writes | Built |
|---|---|
| `swap_twice::rule` | `swap_twice_rule`: a member cannot attach to a theorem |
| `x.within(a, b)` | `Range(a, b).Holds(x)`, the library's existing statement |
| `x.nat()` | `x.toNat()` |
| `f: Buffer` and the memory facts (`Loaded`, `Joined`, `Low`, `Split`) | not read yet |
| registered by name, plans name rules by key | not yet: a generator cannot publish a `register def`. That needs a new declaration form in the tactic host, an elaborator change |
