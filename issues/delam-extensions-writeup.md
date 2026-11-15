---
title: Write down the extended ch. 04 rules for our six formers
status: closed
labels: [kernel,delam,metatheory,docs]
created: 2026-07-24
updated: 2026-08-06
---

DeLaM ch. 04 has no `Id`, `Σ`, `Unit`, `Empty`, `+` or `W`. We added all
six ([[kernel-v1-extensions]]) and implemented them in the kernel, but
their *declarative* rules — the ch. 04-style judgments, as opposed to the
algorithm in `conv.rs` — exist nowhere except implicitly in `typing.rs`
and in our heads.

Surfaced by [[metatheory-ch07-pass]] (see
`docs/kernel/metatheory-ch07-extensions.md` §7): ch. 07 instantiates its generic
equivalence *twice*, once with ch. 04's declarative equivalence and once
with ch. 06's algorithmic convertibility, and the two instantiations
together are what give soundness *and* completeness of the checker
against a specification. We only have the second. Today that is fine —
the pass established the LR cases go through — but it means we are
claiming `conv.rs` is sound and complete with respect to a spec we never
wrote down.

## Deliverable

A standalone document (`docs/kernel/delam-extensions.md` or similar — *not* an
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

## Log

- 2026-07-31: The definitions round wrote its declarative rules already: docs/kernel/metatheory-ch07-extensions.md Part IV sections 23-25 give the bodied-binding grammar, the wf-def rule, delta with the argument for why transparency must be layer-indexed, and the delta-lazy conversion order. They live in the ch. 07 document only because this document does not exist yet -- when it is written, sections 23-25 move here as its definitions section, and the seventh extension is already paid for. ([[simulate-conversion-cost]])
- 2026-08-06: LANDED (2026-08-06, managed round): docs/kernel/delam-extensions.md (~1050 lines) — DeLaM in one page, the six formers each with formation/encoding/intro/elim/β/η-or-why-not/congruences/code-recursor branches, the code-recursor β schema with all 22 extension branches tabulated (§10), the two genuinely new rules argued (§11: Σ surjective pairing — a syntactic-equivalence obligation invisible to the LR; Unit proof irrelevance — escape from a law, not from structure; plus a third argued point: both η rules must sit under ⊨ i comp, the same coherence argument that layer-indexes δ), the refl-endpoints invariant (§12), W's infinitary NfEqW (§13), and definitions restated from ch. 07 §§23–25 (§14; pointer added there). Eleven spec-vs-implementation divergence candidates recorded in §16. The issue's 'Unit η @ 0' was stale: conv.rs:1186 fires η at any level, matching the level-indexed statement — resolved in doc §7.0, no decision needed. TWO FINDS FILED: [[recursor-elim-call-level-mismatch]] — rec.rs declares elim branches' scrutinee recursive call at the motive's level while reduce.rs supplies it at the scrutinee's, verified at source (rec.rs:1934 vs reduce.rs:1541), inherited from a ch. 04 typo in t_elimN, latent only because no live motive distinguishes the levels; and [[kernel-doc-comments-stale]]. Deliberately out of scope, stated in doc §0/§17: the ch. 06 side (whnf/neutral grammars and algorithmic convertibility for the six) and explicit code-recursor congruences (ch. 04 omits them too; a follow-up if the Coq formalization needs them). CLOSING: the ch. 04 deliverable is the whole of this issue; the ch. 06 side, if wanted, is a new issue when something needs it.
