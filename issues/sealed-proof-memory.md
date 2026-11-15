---
title: Make kept theorem proofs cost memory only when opened
status: closed
labels: [kernel,cache,memory]
created: 2026-10-16
updated: 2026-10-17
---

A theorem whose statement carries data keeps its proof sealed beside its
opaque binding ([[theorem-witness-unfolding]],
docs/kernel/theorem-witness-unfolding-design.md). Every kept proof lives in Ψ
for the whole run, whether or not anything opens it.

Measured when it landed (2026-10-16, cloud box, one run each): the wc
certificate build (`build-x86 examples/x86-native/wc.hthr wc_command`)
keeps 338 proofs, almost all native run triples (`LinuxRuns`, `Runs`,
fetched-steps facts, the stat/filter/cursor pieces), and its peak RSS
rises by roughly a tenth over master. Nothing opens any of them: clients
consume a run through `runs_elim`/`runs_into`. Elsewhere in the corpus the
increase is a few percent.

Options, cheapest first:

- **Lazy from the image.** A warm run decodes kept proofs eagerly from
  module images (`module_image.rs`'s sealed table). Keeping the encoded
  bytes and decoding on the first unsealing makes a warm run pay only for
  what it opens. A cold run still holds the proofs it elaborated.
- **Spill on a cold run.** After the module's image is written, replace
  each kept proof with a handle into that image.
- **Narrow the policy.** Keep a proof only if its statement's data is
  reachable without a `Runs`-like family. This is a heuristic about today's
  library, and it brings back the author-side guess the issue removed.

Acceptance: the wc certificate build's peak RSS within noise of the opaque
baseline, with `creal`'s witnesses still computing.

## Log

- 2026-10-17: Done: **lazy from the image.** Ψ keeps each sealed proof as a `term::SealedProof`: a term, or a `ProofSource` loaded on first use and kept from then on (`stats::sealed_loads` counts loads). A module image's reader decodes each kept proof once to validate it, drops the term, and keeps the proof's encoded bytes (`module_image::ImageProof`); `is_sealed` asks without loading, only an unsealing loads, re-encoding an image copies the bytes unloaded, and the replay's "did this proof change" comparisons compare encodings instead of decoding (`module_image::same_proof`). `shift_univ_psi` now shifts a proof when it is first needed instead of every proof at each universe telescope. The image format is unchanged.

  Measured (cloud box, peak RSS of `build-x86 examples/x86-native/wc.hthr wc_command` warm over its own images, one release binary per side, warm runs repeated): master 4433/4429 MB, this change 3660/3660 MB, the commit before sealing (5cc5d6b) 3625 MB, so warm is within 1% of the opaque baseline (master was about +22% warm). No proof is loaded in that build. Cold runs are unchanged: master 4385, this change 4393, opaque 4014 MB, since a cold run holds the proofs it elaborated. Residue (cold runs, value-machine glue loading before a spine decision): [[sealed-proof-cold-and-glue]].
