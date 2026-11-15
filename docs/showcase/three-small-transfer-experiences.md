# Three small experiences: meaningful objects, ordinary code

Status: UX and surface design sketch, 2026-09-04. All finite-set/subtype syntax
below is proposed, not runnable Heather. No syntax freeze or implementation is
claimed. [Client-first design owner](../../issues/finite-set-client-design.md).

The teaching sequence is: write a useful function, see a condition handled,
then understand a rejected implementation. The user-facing vocabulary is
"same set", "stays positive", and "different answers". Setoids, relators, and
certificates belong in the expandable explanation until the user needs them.

## 1. A function that works on sets

**What the user wants:** add the successor of each number to a finite set.

```heather
fn add_neighbors(xs: FiniteSet<Nat>) → FiniteSet<Nat> {
    xs.union(xs.map(λ x => x + 1))
}
```

This is the entire initial example. `FiniteSet<Nat>` is the identity-element
specialization of a library semantic interface; it does not mean "the default
relation of every list". `union` and `map` are methods of that interface. No
`within` block, global redefinition of equality, or extra derive line appears.

Introduce two values next:

```heather
let s = finite_set([1, 2]);
let t = finite_set([2, 1, 1]);

// s ≈ t: these describe the same set.
// add_neighbors(s) ≈ add_neighbors(t): both describe {1, 2, 3}.
```

`finite_set` takes a list as an input format. It makes no promise to sort,
remove duplicates, or preserve a particular representation. `{1, 2, 3}` in
the comment is mathematical notation, not a second literal syntax proposal.

**The explanation:** "Order and repeated entries do not change a set.
Your function uses operations that preserve this meaning, so it gives the
same set whichever representation it receives."

**Normal successful feedback:** a quiet success. The user can ask to explain
the generated guarantee, or inspect it in declaration information:

```text
add_neighbors preserves set equality.

If xs and ys describe the same set,
add_neighbors(xs) and add_neighbors(ys) describe the same set.

Established using: union, map, and compatibility of x ↦ x + 1.
```

The description does not claim equal list storage or function identity.
The mathematics exposed on request is:

```text
∀ xs ys, SetEq(xs,ys) → SetEq(add_neighbors(xs),add_neighbors(ys))
```

At the next level, a calculation should accept replacing `xs.union(xs)` by
`xs` inside `add_neighbors`, using the generated certificate. The first lesson
does not need to teach that tactic or its syntax.

### The only hidden work

1. The explicit `FiniteSet` interface selects its semantic relation and rules.
2. The lambda respects Nat identity; this is ordinary equality congruence.
3. The finite-set map rule proves compatibility of the map expression.
4. The union rule composes that result into the function certificate.

The class/semantic view supplies rule selection, not an unproved guarantee.
Generic `map(f)` over a nontrivial element relation may need a real hypothesis
about f. No such hypothesis may be silently added to a caller's contract.

## 2. A result that stays positive

**What the user wants:** double a positive natural and retain the positive type.

```heather
type PositiveNat = { x: Nat | x > 0 };

fn twice(x: PositiveNat) → PositiveNat {
    x.value + x.value
}
```

This sketch keeps `.value` explicit. It introduces only one convenience at
the function boundary: an expected subtype result can be constructed from
an ambient value after its condition is proved. Avoid simultaneously proposing
implicit projections, inherited arithmetic operators, and subtype construction.
If desired, `x + x` can later become a shorter spelling through ordinary
certified subtype addition; it is not necessary for this experience.

**The explanation:** "The input is a natural number with evidence that it is
positive. The declared result type asks Heather to check that doubling it
stays positive. Once that fact is proved, Heather constructs the result."

**Normal successful feedback:** quiet success, with an expandable explanation:

```text
Result satisfies PositiveNat.

Condition established:
    x.value + x.value > 0
From:
    x is a PositiveNat
```

For the initial implementation, a registered arithmetic lemma can solve this.
It does not require a universal theorem prover or a new arithmetic solver.

**If automation lacks the lemma:** show a proof task at the return expression:

```text
To return this expression as PositiveNat, establish:
    x.value + x.value > 0

The input carries positive-value evidence.
Proving this condition lets Heather construct the PositiveNat result.
```

The user can supply a local proof or register a general closure lemma. A code
action may offer an explicit result constructor with a reporting hole in its
evidence field. That remains a failing declaration until the evidence checks;
it is not a successful program containing an assumed theorem.

### Evidence policy must be explicit in the design

This proposed subset form is for a *condition*, with squashed evidence:

```text
PositiveNat corresponds to a record with
    value : Nat
    valid : ∥value > 0∥
```

This is a tentative policy for this subset constructor, not a change to
ordinary proof-relevant records or all dependent pairs. A user who wants to
compute from the particular witness uses an ordinary relevant record/Σ.
Explain the restriction when a witness-consuming operation is attempted.

The lowered result is schematically:

```text
value := x.value + x.value
valid := squash_map(x.valid, positivity_of_double(x.value))
```

Here `positivity_of_double(n)` is an ordinary function
`n > 0 → n + n > 0`. Squashed evidence is not unsquashed into a relevant
local proof. The pending goal in the actual context is squashed, or generation
can instead ask for this sufficient ordinary closure lemma. Diagnostics must
distinguish those two routes when displaying exact proof goals.

Existing `BoundedList` already uses this pattern: relevant contents and a
squashed fit condition, reconstructed using `squash_map`. This proposal brings
that library pattern to expected-result elaboration.

The [first checked subtype customer](positive-subtype-round.md) now demonstrates
explicit construction, closure evidence, and inherited algebraic laws using an
ordinary relevant record and value-based comparison. The squashed subset
syntax and expected-result construction proposed here remain separate next
steps.

The negative control is `fn bad(x: PositiveNat) → PositiveNat { 0 }`:
it must fail. There is no inserted runtime test or newly assumed premise.

## 3. An implementation that counts the wrong thing

**What the user wants:** implement cardinality using the current list backend.
This is explicitly the implementer's view, one step below ordinary client use.

```heather
fn cardinality(xs: FiniteSet<Nat>) → Nat {
    xs.representation.len()
}
```

`representation` is illustrative backend access in that implementation context,
not a proposed ordinary client method. Here it is a list that may contain
duplicates. Access alone is legal; using it in a semantic operation owes a
compatibility proof. Inspecting representation internally is not automatically
an error: for example, reversing a list before forming another set can be valid.

**The normal feedback when generation cannot finish:**

```text
cardinality has not been shown to give equal results for equivalent sets.

Required:
    equivalent input sets → equal Nat results
```

The expanded view shows the exact compatibility proposition and local context.
This does not claim the implementation is wrong. An optional fuel-bounded
counterexample search can try to provide a stronger explanation; no such search
is required to make the normal diagnostic useful.

**The feedback when a counterexample is validated:**

```text
cardinality gives different answers for the same set.

Representations:        [1, 2]       [2, 1, 1]
Set represented:       {1, 2}       {1, 2}
Your result:           2            3

List length counts repeated entries. Set cardinality counts each element once.

Possible repair: count a duplicate-free enumeration instead.
```

The proof obligation being refuted is exact:

```text
∀ xs ys, SetEq(xs,ys) → len(xs.representation) = len(ys.representation)
```

The word "cardinality" is not what imposes this requirement. The semantic input
interface and ordinary Nat output select set equality and Nat identity. A
function named `foo` with the same body owes the same condition.

If generation only gets stuck, say "could not establish representation
independence" and show the goal. Do not display the stronger refutation without
checking the example and the premise that the two representations agree.

**One possible repaired implementation:**

```heather
fn cardinality(xs: FiniteSet<Nat>) → Nat {
    xs.distinct_elements().len()
}
```

This API is also proposed. `distinct_elements()` returns a certified enumeration
view, not an ordinary list promised equal by identity; its `.len()` observation
is Nat-valued. Its important contract is:

- The enumeration contains exactly the represented members, once each.
- Enumeration order may depend on the representation.
- Length is nevertheless independent of that order.

Do not certify `distinct_elements` as preserving *list identity*: an enumeration
of `{1,2}` may be `[1,2]` or `[2,1]`. Its result interface uses permutation,
or an explicit enumeration package with the corresponding relational rule.
Length respects that relation, so the composition is certified. This is a
useful demonstration that intermediate relations can differ from both the
input relation and the final equality.

For Nat, duplicate removal can use its equality decider. For general elements,
the repair exposes an appropriate decider or another certified enumeration
capability. It does not impose decidability on every finite-set operation.

The tool suggests a repair; it does not silently change the definition.
Performance expectations and implementation choice belong to the author.

## 4. The surface choices these examples suggest

| Choice | Candidate for these experiences | Reason |
| --- | --- | --- |
| Name of the set object | `FiniteSet<Nat>` | Names the mathematical object before introducing its representation |
| Equality spelling | Local/interface `≈`, identity `=` | Makes the first distinction visible without changing existing equality |
| Selecting relations | Registered semantic interfaces and explicit constraints | No guessing from a raw carrier or a function's name |
| Starting a compatibility check | Automatic at a declaration explicitly using a semantic interface | Keeps these small definitions ordinary-looking |
| Subtype projection | Explicit `.value` initially | Avoids adding coercion inference to this design experiment |
| Subtype construction | Expected-result adaptation, with a proof obligation | The return type says what needs to be established |
| Evidence in the subset form | Squashed condition, provisionally | Matches its intended value-only observation policy |
| Successful proofs | Quiet; explanation available on request | Keeps routine evidence out of the main programming flow |
| Failed proofs | Exact goal, reason/status, capability unlocked, repair when known | Gives the next useful action without changing the program |

These choices are a hypothesis to test with the manual counterpart. In
particular, semantic interfaces and expected-result adaptation are new surface
behavior. Current `A → B` typing alone neither implies nor checks arbitrary
relational compatibility.

Automatic compatibility is scoped to a library interface explicitly opted
into this discipline. Its declaration checker emits an ordinary raw definition
and a separate kernel-checked certificate. Consumers of the semantic interface
use both. An uncertified raw function never gains semantic eligibility merely
by matching the underlying carrier type. Raw representative-level programming
remains available by writing the representative carrier explicitly.

The implementation can start with explicit derivation requests and constructors
as the fully visible fallback; the ideal snippet is the acceptance target for
the narrower automatic entry point. There is no general policy of running an
unbounded generator over every Heather definition.

## 5. Small implementation probes, in order

1. Manually define raw list/set semantics and the compatibility proof for the
   exact `add_neighbors` body. Then derive that certificate compositionally.
2. Manually define a record with a squashed positive condition and implement
   `twice` via `squash_map`. Then elaborate the expected-result form to it.
3. State and refute the raw-length compatibility claim at the displayed Nat
   example. Then demonstrate the repaired composite with a duplicate-free
   enumeration related by permutation, without claiming identical lists.

For each probe record the ideal source, checked expansion, exact assumptions,
generated artifacts, normal success display, and the failed-obligation display.
The manual implementation is the semantic oracle; the snippets above are not
tests that have already passed. No compilation was needed for this design round.

Work ownership: [setoid generation](../../issues/setoid-auto-lifting.md),
[subtype evidence](../../issues/subtype-transfer-and-evidence.md),
[counterexamples](../../issues/heather-disprove.md), and
[proof-opportunity diagnostics](../../issues/ai-facing-tooling.md).


Continue with [writing your own thing with laws](your-own-thing-with-laws.md)
to see how an author defines the interface that clients consume.
