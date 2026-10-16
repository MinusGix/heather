# Theorem witnesses compute: sealed proofs, unsealed where they are eliminated

Status: landed 2026-10-16. Owner: `issues/theorem-witness-unfolding.md`
(option D). Tests: `crates/kernel/tests/sealed.rs` (both machines, the
checking position, the negative controls), `crates/elab/tests/slice_replay.rs`
(the edit firewall, in a module and across a module image),
`crates/cache/tests/end_to_end.rs` (the verdict store),
`crates/elab/tests/lib_std_creal.rs::witnesses_compute` and the `creal`
showcase (the client).

## 1. What a client sees

A `theorem` is still an opaque global: its Ψ binding has no body, its
interface hash leaves the proof out, and nothing compares or unfolds it. What
changed is that a theorem whose statement **carries data** keeps its proof
*sealed* beside the binding, and an elimination stuck on the theorem opens
it:

```heather
theorem zero_below_one(): CReal::zero() < CReal::one() { … }
theorem one_gap(): zero_below_one().witness = 2 { refl }   // computes
```

No keyword changes. The author of a proof does not guess whether anyone will
compute with it; the client that projects a witness or matches on a branch
is the one that opens it, and the opening is recorded against that client.

## 2. Which proofs are kept

Keeping every proof costs peak memory (the issue's probe: +10–31% over the
corpus), and almost none of it can ever matter: no elimination is usefully
stuck on a proof of an equation, a negation or a bound that reduces to
`True`. `crates/elab/src/sealing.rs` keeps a proof only when the statement,
under its parameters, reduces to a former with a component a client could
compute with:

- **no data:** `Id`, `SEq`, `SEmpty`, `Squash`, `Unit`, `Empty`;
- **what its parts carry:** `Π` (its codomain: `∀ n. ∃ m. …` is a modulus),
  `Σ` (either side), `Vec` (its element);
- **data:** `Nat`, universes, `Sum`, `W`, `Wf`, `Fin`, codes, opaque types;
- **a stuck decoding** `El(t)`: data only when `t`'s head is a variable (a
  type parameter could be instantiated at anything); a recursion into
  `Type` stuck on an open argument (`n <= m`) is a family of propositions.

The test walks the statement in the value domain, entering `Π` and `Σ`
under fresh variables, with one fuel budget and a bound on the formers it
visits; nothing is spelled and no definition body is copied. It is a
function of the statement and the definitions before it, so it is fixed by
the interfaces, which §4 relies on.

**Unknown means opaque.** A statement the walk cannot settle keeps its
proof out, which is what every theorem was before. The other default looked
like a memory cost only, but a kept proof is *run* wherever an elimination
is stuck on it, and the statements too big to classify are the ones whose
proofs are expensive to run. `CodeResident` over a generated program's bytes
(a conjunction per byte) decided it: classifying it by spelling ran the wc
certificate build out of memory.

## 3. Where the kernel opens a proof

Ψ carries the proofs in a side table, `GlobalCtx::sealed` (persistent
chunks, like the bindings; `prefix` and `extend` keep it aligned). Bindings
are unchanged, so every structural comparison of Ψ bindings — slice replay's
"same contribution", the module image's dependency prefix — is unchanged.

A proof is opened only at an elimination whose scrutinee's head is the
sealed theorem (`Elim::unseals`: projections, `Case`, the `Nat`/`W`/`Wf`/`J`
recursors and `ElimEmpty`/`ElimSquash`; never an application, `transp`, or
the code and box eliminators):

- **syntax reducer** (`reduce.rs::step_scrut`): the scrutinee spine
  `u a⃗` becomes `proof[a⃗]` and reduction continues;
- **value machine** (`eval.rs::Eval::unseal`): the neutral `u a⃗` is glued to
  the proof applied to `a⃗` exactly as a definition's neutral is, so the
  elimination being pushed extends a pending unfolding. Until then the
  neutral carried no unfolding, so `u 2 ≡ u 2` and `u 2 ≡ u 3` are decided
  on the spine and no proof is run;
- **conversion's δ stage** (`conv.rs::delta_head_in`): a sealed head counts
  as unfoldable only under an eliminator.

Layer c, `Defs::opaque`, and the Ψ-free entry points never open anything.

## 4. Recording, and the firewall

`heather_kernel::unseal` records, per thread and in nested frames, the
absolute Ψ indices of the proofs opened. The value machine records a proof
when its glue is **forced** (`ValueArena::mark_sealed`), not when it is
glued: a comparison decided on the spine opened nothing. Every consumer that
reuses a judgment consults the record:

- **The verdict store** (`KernelGate::accepted(…, unsealed)`): a verdict
  that opened a proof is not stored. A check that opened none took the same
  path whatever the sealed proofs are, because which theorems carry one is
  fixed by their statements (§2), so its key stays sound.
- **The kernel pool** carries each deferred check's record back to the join
  (`pool::Outcome::unsealed`), and a serial replay of a pooled verdict
  re-reports it (`unseal::observe`).
- **Slices** (`ItemSlice::unsealed`): each declaration's whole pass —
  elaboration and gate — is recorded. A theorem's proof edit leaves the
  prefix exact as before, and additionally marks that theorem's index
  *changed*; a later slice that opened a changed index is elaborated, every
  other slice still replays.
- **Module images** (`HTHMOD` 13) store the module's own sealed proofs and
  copies of the dependency proofs it opened. Whole-image replay refuses with
  `ModuleReplayError::OpenedProofChanged` when an opened dependency proof
  differs (an ordinary miss: the CLI falls to the slice path, which
  re-elaborates exactly the openers).

So the acceptance holds by construction: editing a proof nobody opened
replays every later declaration; editing an opened one re-checks the
declarations that opened it, and only those.

## 5. What it costs

On today's corpus outside `creal`, no declaration opens a proof, so
evaluation counters move only by the classification walk (a fraction of a
percent). Memory is the kept proofs. The native libraries are where that
shows: their run triples (`LinuxRuns`, `Runs`, the fetched-steps facts)
carry their end state and trace, so they are kept, and the wc certificate
build holds a few hundred of them at peak — a peak RSS increase on the
order of a tenth there, against about a fifth for keeping every proof.
Nothing computes with those witnesses today (clients consume a run through
`runs_elim`/`runs_into`); [[sealed-proof-memory]] owns making the cost
proportional to what is opened.

## 6. Not done here

- **Lazy proofs** ([[sealed-proof-memory]]). Kept proofs live in memory for
  the run.
- **Deciders.** `le_dec`, `or_pick` and the other deciders are `fn`s by a
  rule written when a theorem never unfolded (docs/nat-order-design.md,
  docs/decide-class-design.md). A decision's statement carries data, so as
  theorems they would now be kept and opened where matched on. This round
  leaves them as they are: nothing needs the change, and whether every place
  a decision is used is an elimination (rather than, say, a comparison of
  two decisions) has not been checked.
