---
title: Keep sealed proofs unloaded on a cold run and through value-machine glue
status: open
labels: [kernel,cache,memory]
created: 2026-10-17
updated: 2026-10-17
---

Two places a kept theorem proof still costs memory without being opened,
left by [[sealed-proof-memory]] (which made proofs read from a module image
load on first use).

- **Cold run.** A module elaborated in this run keeps its proofs as terms
  for the whole run. Its image is written right after it checks; swapping
  each kept proof for an `ImageProof` over the bytes just encoded would make
  a cold run pay what a warm one does. Only worth it if other references to
  the proof term (the elaborator's own tables) let it be freed; check that
  first. The wc certificate build cold is still roughly a tenth above the
  pre-sealing peak.
- **Value-machine glue.** `Eval::unseal` takes the proof term when it glues
  it, so an elimination stuck on a sealed theorem loads a lazy proof even
  when conversion then decides on the spine and never forces the glue (it is
  not recorded as opened). Deferring the term to glue force would need a
  closure kind that loads on force. Nothing in today's corpus loads this way
  (the wc warm build loads none), so this is a note, not a cost.
