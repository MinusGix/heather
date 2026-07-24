---
title: Write down the extended ch. 04 rules for our six formers
status: open
labels: [kernel,delam,metatheory,docs]
created: 2026-07-24
updated: 2026-07-24
---

DeLaM ch. 04 has no `Id`, `Σ`, `Unit`, `Empty`, `+` or `W`. We added all
six ([[kernel-v1-extensions]]) and implemented them in the kernel, but
their *declarative* rules — the ch. 04-style judgments, as opposed to the
algorithm in `conv.rs` — exist nowhere except implicitly in `typing.rs`
and in our heads.

Surfaced by [[metatheory-ch07-pass]] (see
`docs/metatheory-ch07-extensions.md` §7): ch. 07 instantiates its generic
equivalence *twice*, once with ch. 04's declarative equivalence and once
with ch. 06's algorithmic convertibility, and the two instantiations
together are what give soundness *and* completeness of the checker
against a specification. We only have the second. Today that is fine —
the pass established the LR cases go through — but it means we are
claiming `conv.rs` is sound and complete with respect to a spec we never
wrote down.

## Deliverable

A standalone document (`docs/delam-extensions.md` or similar — *not* an
edit to `docs/delam/*.tex`, which are the paper's own chapters and should
stay pristine), written to be liftable into a paper or blog post of our
own restating our extensions to DeLaM. So: self-contained, in the
paper's notation and rule style, with a short prose framing of what
DeLaM is and what we added and why.

Per former: formation, introduction, elimination, β, and η where it
exists, plus the code-recursor branch (the `G_A` telescope) — the
telescopes are already spelled out on `Branches` in
`crates/kernel/src/term.rs` and live once in `rec.rs`. Mostly
transcription from `typing.rs`/`reduce.rs`; the two that are *not*
mechanical, and the reason this issue exists at all, are the genuine new
rules rather than congruences:

- **Σ η / surjective pairing**: `Γ ⊢ p ≈ ⟨fst p, snd p⟩ : Σ(x:S).T @ l⊔l'`
- **Unit η**: `Γ ⊢ t ≈ t' : Unit @ 0` for any well-typed `t, t'`

Without those two on the declarative side, escape from the `Σ` and `Unit`
logical-relation cases has nothing to land on.

Worth stating alongside the rules, since they are the interesting content
and are already argued in the ch. 07 note: the `refl`-endpoints-by-
conversion invariant that keeps propositional equality at `□` exactly as
fine as the code recursor's observation (also in `crates/kernel/DESIGN.md`),
and `W`'s infinitary Kripke `NfEqW`.

## When

Parked, low priority. It becomes load-bearing when either (a) the Coq
formalization of DeLaM is far enough along to extend — this doc is the
natural input to that, and the rules should be written in a shape that
transcribes cleanly; or (b) a completeness question about the checker
comes up, rather than the soundness we currently lean on. Doing it also
front-loads the work for any *further* extensions past these six, which
is the actual motivation: the marginal cost of the seventh former drops a
lot once the six are written down properly.
