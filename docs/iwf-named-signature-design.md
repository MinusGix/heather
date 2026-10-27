# `IWf` families: the named signature

Status: implemented, 2026-10-26 (`crates/elab/src/iwf_family.rs`,
`crates/elab/src/gendefs.rs`). Issues:
`issues/mutual-group-recursion-gate-cost.md`,
`issues/indexed-family-recursion-gate-cost.md`. It changes how
`docs/iwf-former-design.md` §8 and `docs/mutual-inductive-design.md` spell
their terms, not what they mean. It is the `IWf` analogue of
`docs/codata-named-signature-design.md`.

## 1. The problem: the signature is spelled out at every use

`⟦D<ā>(m)⟧ = IWf(I; S; x. n; x. o; x i. c)(m)`, and the three index
functions are case trees over the shape: `n` and `o` have a branch per
constructor, and `c` is a convoy whose motive repeats `n`, so the
signature is Θ(k²) for `k` constructors. A mutual group of `m` members has
Θ(m) constructors in one family. Every occurrence of the family wrote the
whole signature out: every member wrapper's statement, every type in a
recursion's step, and every level of the step's case tree, whose convoy
motive spells the step telescope (`cs`'s type, and the ih's, whose `dnth`
carries the children's family several times). The kernel judged each copy,
the elaborator built each one, and the group's gate grew about as m³.

## 2. The named signature

At declaration time the elaborator builds the inline signature once, over
`tycode_fn_telescope`'s all-`Ty 0` telescope `tel`, and names its parts:

```
D#iarity : Π tel. Π(x : S). Nat
D#iout   : Π tel. Π(x : S). I
D#ichild : Π tel. Π(x : S)(i : Fin(D#iarity tel x)). I
D#idnth  : Π tel. Π(a : S)(cs : DVec(D#iarity tel a; k. IWf(…)(D#ichild tel a k)))
                  (i : Fin(D#iarity tel a)). IWf(…)(D#ichild tel a i)
```

An instance at that profile is

```
IWf(I; S; x. D#iarity ā x; x. D#iout ā x; x i. D#ichild ā x i)(m)
```

with the shape and the index type spelled as before. The bodies are exactly
the inline pieces, so one δ gives back what was written before, and the
kernel checks each definition once, as a generated one. `D#idnth`'s body is
`dnth` at the named signature: `match` spells the ih type of its step
telescope with it (`iwf_match_telescope`), so the convoy motive at each
level of the case tree is a handful of references plus the user's motive.
The kernel's own telescope (`iwf_step_telescope`) and β are unchanged; the
step's annotated type converts with it by δ.

Registration is best-effort, as for every generated definition (a refusal
leaves the family inline), and covers non-infinitary `IWf` families without
value parameters. An instance outside the profile (a type argument above
`Ty 0`, or one with no code) keeps the inline signature. The four pushes
move earlier-built pieces' global indices by one each, which the
registration shifts for, as `register_m_sig` does. Module images carry the
keys (codec bytes 19–22).

Registration runs inside the declaration's attempt, after the index type's
code (`I#icode`) was pushed, and builds index values: constructor values of
the index type, whose `sup_f` slots and children annotations name that
type's shape and arity definitions. The attempt shares those annotations
across its values (`DeclAttempt::wf_slot_annotations`,
`children_annotations`), and they are keyed by the Ψ scope
(`lowering_scope`) as well as the type and Γ's length: keyed without it, an
annotation minted before the push named every global one too close, and the
kernel refused `D#iout` for any family indexed by a recursive type, which
then stayed inline without a word.

## 3. Readers

Nothing in the elaborator takes `n`, `o` or `c` apart: arms are built from
the declaration's own index expressions, and inversion reduces goals by
whnf, which unfolds the definitions. The signature components are compared
and copied whole (unification, readback, codes), and two instances of one
family at one profile are spelled alike.

## 4. Cost

The m-member ring (`inductive/mutual-recursion`) went from about m^2.3 at
small m and cubic beyond 16, to about m^1.8. Typed syntax
(`inductive/typed-syntax`, a family indexed by a judgment type) is now
about linear in the constructors in `size` and in the whole file: the
signature it judged at every `IWf(…)` (half its gate before) is three
references, checked once in the definitions, which the declaration now pays
for. What remains is the shape
spine itself: the step's case tree is a comb of depth Θ(m), each level's
motive holds the label as a chain of `inr`s of that depth, and each arm's
conversion evaluates the definitions at its label down the same chain. Wide
sums are balanced since PR #214 (`issues/wide-inductive-balanced-sum.md`),
which makes both logarithmic. Two costs per arm were left
(`issues/iwf-shape-spine-comb-depth.md`), both from two spellings of one
type. Every mention lowered the shape and the index type afresh, so the
instances shared no node and the kernel compared them node by node; they are
now one allocation per family (`Elaborator::share_iwf_part`). And the
recursion's motive names the member index type by its registered code,
`El(D#members#tycode)`, where `D#iout` returns the inline sum, so the case
tree converted the two at every node, a Γ one binder longer each time; the
kernel now keeps a conversion of two sides that read nothing of Γ apart from
Γ (`ClosedSide` in `typing.rs`). The recursion's gate is about linear in the
members. What still grows is each member's own statement, which judges the
inline signature again in its own gate
(`issues/iwf-member-statement-signature-per-gate.md`).
