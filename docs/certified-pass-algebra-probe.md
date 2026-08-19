# Certified passes as algebras: the first probe

Date: 2026-08-18

## Question

Can a transformation be packaged as a structural algebra plus one
constructor-local preservation law per clause, with one generic induction
proving the whole pass sound?

This is the first concrete test of `case-algebra-definitions` rung 4. It is a
probe, not a declaration-form or generator design. Everything here is written
as ordinary Heather records and functions.

## The interface

For `Tree<A>`, a pass is a `TreeAlg<A, Tree<A>>`. Its law record is indexed by
both an arbitrary relation and the algebra:

```heather
record TreePassLaws<A>(R: Tree<A> -> Tree<A> -> Type,
                       alg: TreeAlg<A, Tree<A>>) {
    leaf: (value: A) -> R(Leaf(value), alg.leaf(value)),
    node: (left, left_r: Tree<A>) -> R(left, left_r) ->
          (right, right_r: Tree<A>) -> R(right, right_r) ->
          R(Node(left, right), alg.node(left_r, right_r)),
}
```

`CertifiedTreePass<A>(R)` couples the algebra to those laws.
`tree_pass_sound` is the only induction: at `Node` it recursively obtains the
two relation witnesses and hands them to the pass's one Node obligation.

This division is load-bearing. A pass author never writes the traversal proof;
the generic theorem knows no fact specific to the pass or to `R`.

## Concrete acceptance: mirror preserves size

`mirror_alg` swaps the two recursive results at every Node. Its output is not
equal to its input, so the certificate cannot collapse to a rebuild theorem.
The chosen relation is

```heather
TreeSameSize(source)(result) := tree_size(result) = tree_size(source)
```

The Leaf law is reflexivity. The Node law consumes both induction hypotheses
and `add_comm`; those are exactly the local mathematical facts required by the
swap. `tree_mirror_size` is then one call to `tree_pass_sound`.

The acceptance varies an open leaf type and a neutral tree. A closed example
also computes to a visibly mirrored tree. The mutation replaces the Node
clause by `left`, dropping the right branch; returning the left induction
hypothesis at the Node law is kernel-refused as `NotConvertible`.

## IR-scale acceptance and the repaired boundary

The same interface was written first for the real eight-constructor `Ir`:

- `IrAlg<M>` replaced every recursive field by `M`;
- `IrAlgLaws(R, alg)` carried one local relational law per constructor;
- `ir_fold_sound` recursively assembled `R(ir, ir_fold(alg, ir))`;
- the intended pass rewrote each constructed tag `n` to `add(0, n)`, a real
  open-term syntax change certified locally by `sym(add_left_zero(n))`.

The first kernel run rejected `ir_fold_sound` with `OutOfFuel`. Three narrower
probes gave the same result:

1. naming the induction family behind a definition, following the successful
   `Refines` term-size boundary;
2. specializing the arbitrary relation to plain equality;
3. declaring the induction as a `theorem` rather than a `fn`.

The nondependent `Ir` fold itself checked. A kernel-boundary probe then found
that the refusal was not the induction's mathematical cost: one fallback
record projection checked the local `laws` value at two equivalent spellings.
Γ stored the component-respelled declaration binder, but the projection's
`Fst`/`Snd` annotations rebuilt the inline Σ record. Conversion consequently
walked the whole `Ir`/`Wf` encoding behind every affected field type.

The repair is emission-side and leaves the kernel untouched. Fallback record
projections still traverse the inline Σ for structural reads, but their
emitted component annotations pass through the same deep respeller used when
declaration binders are closed. The projection now synthesizes the spelling Γ
already stores. The arbitrary-relation `IrAlgLaws`/`ir_fold_sound` checks at
ordinary fuel, as does the intended tag-normalizing pass. Replacing its
`add(0,n)` clause by `Succ(n)` cannot reuse the law record and is refused as
`NotConvertible`. `issues/ir-pass-dependent-fold-fuel.md` records the
measurements and rejected kernel shortcuts.

## Verdict

The core value claim passes at the first nontrivial scale:

- a pass is an ordinary first-class algebra;
- its certificate is an ordinary record of local laws;
- the pass and certificate are coupled by dependent record fields;
- one relation-polymorphic induction supplies the global theorem;
- a bad clause is rejected at its local obligation.

The same claim now passes at Heather's actual IR scale. This still does not by
itself justify pass syntax or a `Cases`/`Alg`/`Elim` generator: the next honest
IR step is a genuinely semantics-changing pass whose local laws establish an
execution refinement rather than equality. Until that lands, “certified
optimizer passes” is a mechanically validated architecture, not a shipped
compiler capability.

Initial Tree probe: suite 1923 -> 1925, 0 failed. IR boundary repair: suite
1925 -> 1926, 0 failed; `scripts/bench --check`: 106 comparisons within
thresholds.

## Semantic control: extending missing arms

The next probe changes execution rather than merely syntax. Its algebra
replaces every `NoArm` tail with `Arm(Ret(RNil), NoArm)`: the first tag beyond
each previously complete arm chain can now take an empty-return fallback.
Existing successful matches retain their selected bodies, while some formerly
stuck programs become successful. The result is therefore not propositionally
equal to the source and the proof cannot pass through IR equality.

Plain direct-execution refinement is not compositional for this IR. `Arm` and
`NoArm` are both stuck when evaluated as instructions, so that relation says
nothing about the behavior `LetMatch` observes through `pick_arm`. The probe's
local relation consequently carries two observations:

- successful direct evaluation is preserved at the same fuel; and
- successful evaluation after selecting any tag is preserved at the same
  fuel.

The `Arm` law routes tag zero through the body's direct hypothesis and a
successor tag through the tail's selection hypothesis. The `NoArm` law is
allowed to add the default because selection from the source cannot have
succeeded. `LetMatch` consumes both observations; the remaining instruction
laws consume direct hypotheses. `LoopIter` needs a fuel induction because its
continue case re-enters itself, but no larger fuel bound is required.

One generic `ir_fold_sound` call produces the two-observation certificate, and
its direct field closes the ordinary existential convergence refinement. A
closed computation confirms that the transformed missing-arm program now
returns `VNil`. Replacing existing arm bodies with the default cannot reuse the
law record and is kernel-refused as `NotConvertible`.

This one-slot extension pays rung 4's semantic acceptance. It also identifies
a requirement for any generated pass interface: the relation offered to
constructor laws must include the inductive's eliminator-specific observations,
not only execution of the datatype value in isolation. The next honest
optimization target is constant-match fusion; generation can remain deferred
until that exercise shows whether these observation records have a stable
reusable shape.
