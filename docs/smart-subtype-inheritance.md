# Choosing what a subtype inherits

Design sketch; the automatic behavior below is not implemented. The
[positive-natural round](positive-subtype-round.md) supplies the checked manual
expansion for the first case.

For a new user: a subtype gives you values with an extra guarantee. Reusing an
existing function can mean accepting those values as inputs, promising that
its output has the guarantee too, or both. Heather should help prove the
promise the author chose.

## Choose the result, infer its obligations

These are candidate target signatures, not new declaration syntax:

| Ambient function | Requested target | Additional work |
| --- | --- | --- |
| Natural addition | PositiveNat × PositiveNat → PositiveNat | Prove the sum positive; existing closure lemma suffices. |
| Natural addition | PositiveNat × Nat → PositiveNat | The same closure lemma suffices. |
| Natural subtraction | PositiveNat × PositiveNat → Nat | Project the inputs; leave the result alone. |
| Natural subtraction | PositiveNat × PositiveNat → PositiveNat | Prove the difference positive; positivity of both inputs does not suffice. |

Natural subtraction here is truncated at zero. For the last signature,
`y.value < x.value` is a useful condition under which the result is positive.
That conditional wrapper is a different API from total positive subtraction.
The generator must prove the condition sufficient before using it.

The carrier `Nat` alone does not tell us the purpose of a result. A count,
index, distance, or remainder can legitimately be zero even when some inputs
are positive. Preserve ambient results by default when suggesting adaptations;
an explicit target signature or an opted-in structure can request strengthening.
For example, asking to implement a semigroup fixes its operation's result to
the carrier. It still leaves a closure obligation to discharge.

## Three small experiences

**Reuse a function on my inputs.** Select the argument positions to adapt and
retain the source result type. The wrapper uses the registered projection.
Mixed signatures are useful: there is no requirement to replace every
occurrence of the ambient carrier. Ordinary user code can retain explicit
`.value`; generated wrapper code performs these projections locally.

**Keep this result in my subtype.** Request the stronger result explicitly.
The generator constructs the ambient result and asks for its invariant under
the available input assumptions. Registered closure lemmas may solve it. If
they do not, leave a named proof goal in the generated definition, just as
the manual `?valid` field does today. Failure does not mean the operation is
impossible, nor does it silently acquire a new caller requirement.

**Offer me a conditional version.** As a separate discovery action, show a
candidate function signature with an additional premise, and its checked
implementation when available. The author can adopt that API explicitly.
Do not export it under the signature of the failed unconditional request.
The direct obligation `P(f(x.value))` is always a starting point; a useful
condition such as `y.value < x.value` needs mathematical simplification or a
registered lemma. Bounded search need not find a weakest condition.

## Theorems follow the chosen operation

An ambient theorem quantified over all naturals can be instantiated at the
projected values. Its hypotheses remain obligations; subtype evidence may
discharge some of them. This alone does not change an existential witness
into a subtype value, or turn a theorem about an ambient operation into a law
of a different operation.

For a selected lifted operation, its projection theorem connects the two
expressions. Positive addition's associativity then follows from natural
addition's associativity, using the value-based relation. The comparison
does not identify the record's stored evidence.

Conditional operations require extra care: every intermediate application in
a law needs its own domain evidence. A partially available operation does not
provide the total operation required by `Semigroup`. Prefer a conditional
theorem with explicit hypotheses when that is what was proved. In particular,
adding premises must not make an unavailable monoid unit appear to exist.

## First generator boundary

Start with an explicit lift request naming a source operation, target signature,
and representation interface. The interface provides the ambient type,
projection, invariant, and constructor with its evidence policy. Do not infer
this interface from fields merely being named `value` and `valid`.

The preferred entry point is a Heather metaprogram receiving explicitly named
or quoted source code and the requested target. Naming the source gives the
metaprogram a concrete function to inspect and attempt to lift. It emits ordinary
checked definitions and proofs; the exact invocation syntax and code-inspection
API remain to be designed.

Later, theorem discovery could invoke the same transfer machinery when a user
tries to apply an ambient theorem to subtype values. The desired experience is
that even an unfamiliar Nat theorem becomes usable with only its necessary
remaining conditions exposed. Finding the theorem and selecting a suitable
adaptation are additional steps; an explicit operation lift alone does not
provide that experience. Keep this as a discovery-layer target.

The first supported case is a homogeneous binary operation on an ordinary
record with relevant invariant evidence, matching `positive_add`. Generate
the wrapper and its projection theorem. Try explicitly registered closure
evidence, and retain ordinary resumable goals when it is missing. Check the
generated artifacts before making a completed lift available. Law transfer,
conditional API suggestions, mixed signatures, and automatic discovery are
subsequent layers over that explicit request.

The projection theorem is proved by computation for the checked positive
record. A more general representation interface may need a supplied
constructor/projection law; its computation behavior must not be assumed.
Squashed invariants need a separate evidence-preserving construction path.

Regression targets for the first generator are successful positive addition,
its projection theorem, a resumable missing closure goal, rejection of an
incorrect closure proof, and refusal to complete a zero-valued positive
constant without evidence. Later signature-selection tests should distinguish
ambient and strengthened results, and total and conditional APIs.

Tracked by [subtype transfer](../issues/subtype-transfer-and-evidence.md) and
[the generator](../issues/setoid-auto-lifting.md). This design does not require
global implicit coercions or automatic export of all ambient declarations.
