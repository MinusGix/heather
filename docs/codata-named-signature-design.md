# Codata: the named signature and the checked spelling

Status: implemented, 2026-10-22 (`crates/elab/src/codata.rs`,
`crates/elab/src/gendefs.rs`). Issue: `issues/codata-named-signature.md`.
It changes how `docs/codata-elaborator-design.md` ("codata §n") and
`docs/codata-indexed-design.md` ("indexed §n") spell their terms, not what
they mean: every lowering, rule and test there is unchanged.

---

## 1. The problem: the signature is spelled out at every use

`⟦D<ā>(v̄, ī)⟧` is an `M` whose signature (shape, positions, child index;
indexed §3) was written inline at every occurrence, and every constructor,
`match` and corecursive close carries that type several times over: in the
`corec`'s carrier, in each pair's component types, in each injection's sum.
A declaration whose fields mention another codata type (`Bisim` over
`CoTree`, two trees per index) nests one inline signature inside the next.
The terms the kernel was handed were nearly all annotation, and the
elaborator's own whnf and conversion paid for every copy: the cost of a
proof like `Bisim::refl` grew with the product of the nested signatures'
sizes rather than with the proof.

Inductives already avoid this: each declaration's code is a generated
definition (`D#tycode_fn`), and instances are spelled as a reference to it.
Codata now does the same, plus one rewrite the inductives do not need (§5).

## 2. The named signature

At declaration time the elaborator builds the inline signature once, over
`tycode_fn_telescope`'s all-`Ty 0` telescope `tel` plus the index binder
`i : I` (`Unit` when unindexed), and names its three parts:

```
D#mshape : Π tel. Π (i : I). Ty ls
D#mpos   : Π tel. Π i. Π (s : El(D#mshape tel i)). Ty lp
D#mnext  : Π tel. Π i s. Π (p : El(D#mpos tel i s)). I      (indexed only)
```

An instance at that profile (every type argument at level zero with a code)
is then

```
M(I; i. El(D#mshape ā i); i s. El(D#mpos ā i s); i s p. D#mnext ā i s p)(⟨ī⟩)
```

with `next` the unit triviality when unindexed. Nothing else about the
lowering moves: the bodies are exactly the inline pieces, so one δ step
gives back what codata §2 and indexed §3 wrote, and the kernel checks each
definition like any generated one. Registration is best-effort (a refusal
leaves the declaration inline, as for every generated definition), and an
instance outside the profile keeps the inline spelling.

The three definitions are pushed in order, and each push moves every
earlier-built term's global indices by one; the pieces built before a push
are shifted into the frame they are used in. That is the only subtlety, and
the kernel refuses a mistake there (the statement and the body stop
agreeing).

Module images carry the three `GenDef` keys (codec bytes 16–18), so an
importing module spells the instances the same way.

## 3. Structural readers unfold first

The elaborator's own readers take the shape apart: a constructor's label,
`match`'s branches, the spine an `inj`/`absurd`/declared equation walks.
They now read a named instance by **unfolding the reference** (the gendef's
body, one λ peeled per argument, then substituted), never by whnf of the
whole type. `MParts::read` keeps both forms: the named one for the terms it
emits, the unfolded one (`shape_inline`, `pos_inline`) for the spines it
walks. `tag_of` finds the declaration from the reference's key directly.

## 4. The instance matcher learns `M`

`Holes::ty`, which finds an inductive instance's arguments by matching
against its template, had no `M` arm, so an inductive with a codata field
(`Obs<R>(E)`, whose children are `CoTree<R>(E)`) never got its `tycode_fn`
reference and was spelled inline too, with the codata signature inside. The
arm matches levels, then index type, shape, positions and `next`
structurally, then the index term.

## 5. The checked spelling

The lowering writes every node annotated (`Pair` with both component
types, `Inl`/`Inr` with the sum, `Fst`/`Snd`/`App` with their types),
because its readers take those apart. Once a term is finished, nothing
reads the annotations but the kernel, and the kernel's checked forms
(`PairAt`, `InlAt`, `InrAt` with no type; `FstAt`, `SndAt`, `AppAt`) need
none in the positions where it already knows the type. So the three entry
points (a constructor, `match`, a corecursive close) hand back `slim(t)`:

- an intro in a **checking** position loses its annotation;
- a projection or application is spelled `fst@`/`snd@`/`app@` only when its
  receiver **infers** after slimming (a bare `pair@` does not, so
  `fst(pair@…)` stays annotated with the receiver checked);
- an application with a λ head stays annotated;
- the checking positions are the kernel's own (`typing.rs`): pair
  components, injection payloads, λ bodies under a checked λ, case branches,
  `J`'s base, `corec`'s step and seed (its signature is kept whole).

Every other node is kept whole, so the rewrite cannot change what a term
means, only how much of it is annotation. The kernel rechecks every
declaration, and a mistake here is a rejection (`NotInferable`), which is
how the receiver rule was found.

## 6. Cost

`Bisim::refl` and `Bisim::sym` over `CoTree` dropped by more than an
order of magnitude; what remains is the elaborator's own work, proportional
to the declaration, with the signatures counted once each as references.

## 7. Testing

The codata and indexed codata tests are unchanged and pass (they run every
declaration through the kernel, and their image round trips now carry the
named keys). `crates/elab/tests/lib_std_coitree.rs` adds a goal display
over a named instance (`b : Bisim<R>(E, t, spin(E))`), and the library
itself is the workload the names exist for.
