---
title: Compute with a theorem's witness without making the author choose fn
status: open
labels: [kernel,elaboration,design,reals,cache]
created: 2026-10-16
updated: 2026-10-16
---

A `theorem` is opaque: its proof is kernel-checked, then dropped, and every
later reference is a neutral (`crates/elab/src/lib.rs`, the definition story
at the top of the file). So a witness inside an `∃` that a theorem proves,
or the branch of an `∨` it picks, never evaluates. `Exists` is a record and
the library has no `Prop`, so the witness *is* data. Opacity is the only
thing hiding it.

The regular Cauchy reals hit this first ([[regular-cauchy-reals]],
docs/regular-cauchy-reals-round.md "Computation"). A `≈` proof's start
index, a `<` proof's gap and `lt_cotrans`'s branch are what a client
computes with: an inverse reads the gap, and a limit reads moduli. The
round's workaround is to write every such proof as a `fn`, and to turn
`Rat::archimedean`/`archimedean_inv` into `fn`s. The rational-order round
had claimed those witnesses computed; they did not, because a `theorem`
never unfolds. The workaround makes the *author* decide, at definition time,
whether anyone will ever compute with a proof. That is the client's
question, not the author's.

## What opacity buys, and must keep buying

1. **The edit firewall.** Editing a theorem's proof leaves its Ψ binding and
   its interface hash unchanged, so every later declaration replays
   (docs/declaration-slice-replay-design.md, "The structural-equality
   test"). A `fn` body edit re-elaborates everything after it.
2. **Conversion never enters a proof.** No comparison unfolds a `ring` or
   `omega` certificate. `sym(refl)` does not reduce to `refl`
   (docs/decreases-unfolding-design.md §3), and that is relied on.
3. **Proof stability.** A client can depend only on a theorem's statement,
   so its proof can be rewritten freely. Computing with a witness gives up
   exactly this for that client. That is inherent to computing with it, and
   it should be visible at the client.

Making theorems transparent everywhere would give up all three for every
declaration in order to serve the few that compute.

## Options

- **A. `fn` (today).** It works, but the keyword lies: these are proofs. The
  author has to guess.
- **B. Transparent marker** (Coq's `Defined` against `Qed`): something like
  `theorem … computes`, which keeps the body. It is honest naming at almost
  no cost (a flag on `DeclKind::Theorem` deciding `body`). But it is still
  the author's guess, and it still opens the firewall for every dependent.
- **C. Use-site unfolding, explicit** (Agda's `opaque`/`unfolding`, Lean's
  `unseal … in`). Theorems keep their bodies *sealed*: stored, but out of
  the interface hash. A declaration that wants to compute names them,
  `unfolding zero_below_one`, or wraps an expression, `reveal(e)`. It can be
  done with no kernel change. The elaborator mints a transparent shadow
  `T#open` per revealed theorem, whose body references the shadows of the
  theorems it uses, minted lazily so that `ofRat_lt → archimedean_inv`
  reaches through. The revealing declaration's check key includes the
  shadows' bodies. Everyone else keeps the firewall.
- **D. Use-site unfolding, implicit** (closest to "ask for the witness and
  compute from it"). The kernel δ-unfolds a sealed theorem only when it is
  the head of a stuck elimination, a projection or a `match` scrutinee, and
  reports the bodies it unfolded. The cache folds those bodies' hashes into
  that one declaration's check key. With this, `zero_below_one().witness =
  1 { refl }` just works, and no keyword changes. The risks are the
  elaborator, not the kernel. Its whnf would now run proofs wherever a type
  mentions `T(…).witness`, which is the computed-types cost seen in
  `Straight` ([[elab-whnf-copies-straight-continuations]]). It also accepts
  strictly more, which can move timings.

## Recommendation

D's semantics with C's predictability as the fallback. In Heather a
`theorem` and a `fn` are already the same kind of thing (there is no
`Prop`), and the only difference is an unfolding policy. The policy should
be decided where the unfolding happens, and recorded where it happened, not
fixed at the definition.

Sequence:

1. **Measure first.** On a full library check, count stuck eliminations
   whose head is a theorem global, at the elaborator and at the kernel. If
   they are rare outside `creal`, D's elaborator risk is small. If they are
   common, start with C.
2. **Keep theorem bodies.** Images and slices drop them today
   (docs/declaration-slice-replay-design.md, "The same contribution"), so
   measure the size of keeping them sealed.
3. **Implement the unfolding with dependency recording.** Either the
   elimination-driven δ (D) or the shadow minting (C), with the unfolded
   bodies recorded in the declaration's check key.
4. **Turn `creal`'s data-carrying `fn`s and `Rat::archimedean*` back into
   `theorem`s.** Make the showcase's `add_zero_start` and `one_gap`, and
   `lib_std_creal.rs::witnesses_compute`, pass unchanged.

Acceptance: those tests pass with the proofs written as `theorem`s. Editing
the body of a theorem that nobody unfolds still replays every later
declaration. Editing the body of a revealed theorem re-checks exactly the
declarations that unfolded it.

## What it assumes from elsewhere

- **[[stuck-on-opaque-theorem-diagnostic]]** owns telling the writer that a
  theorem blocked a reduction. That is useful whichever option lands.
- **[[declaration-slice-replay]]** owns the replay firewall. Assumed here:
  only that the check key of an item may include extra hashes the item
  reports.

## Log

- 2026-10-16: Measured the upper bound on step 1 with a probe compiler where every `theorem` keeps its body (one line in `crates/elab/src/lib.rs`'s binding: `DeclKind::Theorem` takes `Some(term)`). It was run with `scripts/perf ab --corpus full --only '' --samples 2` against HEAD, plus `rat_client` and `creal_client` (cloud box, loadavg ~2.6 on 4 CPUs).

  - **Evaluation counters:** within ±0.1% on every corpus file (omega, nat, int, list, bitvec, algebra, calc_parser, ir_v1, function_ir, x86_64, the reused_callee certificate, rat_client, creal_client). The conversion counters (`conv_misses`, `conv_not_convertible`, memo and shortcut hits) are identical. With every theorem transparent, existing proofs almost never unfold one, so D's elaborator risk on today's library is negligible.
  - **Memory:** max RSS rises 10–31% (x86_64 +21%, the certificate +22%, creal_client +31%), because Ψ now retains every proof term. This, not unfolding, is the cost to design around.
  - **Seconds:** mostly inside the spread. `list` and `calc_parser` separated at about +20–28%, which is plausibly allocation from the retained bodies, on a loaded box with two samples. This is not a quotable result.
  - With bodies kept, `creal` written with `theorem`s in place of its data-carrying `fn`s checks, and the showcase's `add_zero_start`/`one_gap` evaluate by `refl`.

  Consequence for the plan: D is cheap at conversion. What remains is (a) retaining bodies without a 10–30% memory tax (lazily from the image or disk, or only for theorems whose statement carries data), and (b) recording which theorem bodies a declaration actually unfolded, at the kernel *and* in the elaborator's whnf, so the check key and slice replay depend on exactly those. On today's library that set is almost always empty, so the edit firewall would hold in practice. The probe patch is not committed.
- 2026-10-16: Landed option D (docs/theorem-witness-unfolding-design.md). A theorem whose statement carries data (a witness, a branch, a number, a function returning one; `crates/elab/src/sealing.rs`) keeps its proof sealed beside its opaque binding in `GlobalCtx::sealed`; bindings and interface hashes are unchanged. Both kernel machines and conversion's δ stage open a sealed proof only under a stuck elimination (projection, match, recursor), never under an application. `heather_kernel::unseal` records which proofs a check opened, at force time in the value machine, so a comparison decided on the spine opens nothing. The verdict store keeps no verdict that opened a proof; slices record what each declaration's pass opened and re-elaborate exactly those after the proof changes; module images (`HTHMOD` 13) carry the module's sealed proofs and the dependency proofs it opened, and whole-image replay misses (`OpenedProofChanged`) when one changed. `creal`'s 23 stopgap `fn`s, `Rat::archimedean(_inv)` and the showcase's `zero_below_one` are theorems again; `add_zero_start`, `one_gap` and `witnesses_compute` pass unchanged.

    - **Acceptance:** `slice_replay.rs` checks the firewall both ways (an unopened sealed proof edit re-elaborates 1 item, an opened one exactly it and its opener) and across a module image; `end_to_end.rs` checks a warm run re-gates only the opener (and fails with the store's guard removed).
    - **Cost** (`scripts/perf ab --base origin/master --whole-tree`, loaded box, counters only): outside `creal` nothing is opened anywhere in the corpus; the classification adds a weak-head probe per theorem (eval counters +0.2–0.6%), with no body rescopes once a decoded statement is answered from its value. Peak RSS within a few percent, against the keep-all probe's +10–31%.
    - Two tests moved by design: `check_reports_mismatch`'s stuck-projection fixture is an axiom now (a theorem's witness computes), and the Nat-suite golden hash moved because Ψ's printed form gained the `sealed` list.
    - Not done, owing nothing: loading kept proofs lazily from the image (not needed at today's sizes), and turning the `fn` deciders back into theorems (design note §6).
