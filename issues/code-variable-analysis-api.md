---
title: The right API for variable-obscured code analysis: markers are staged substitution
status: open
labels: [metaprogramming,kernel,delam,design]
created: 2026-08-11
updated: 2026-08-11
---

Research direction from the transcriber round's user review (2026-08-11). tm_var's opacity is LOAD-BEARING metatheory, not a gap: if a recursor branch could observe which variable it received, eliminating code and then substituting into it would disagree with substituting first — the recursor's stability under the substitution calculus depends on variables being handled uniformly, and layer v exists to make exactly that abstraction (ch. 04 ll. 1204-1207). A kernel 'fix' exposing variable identity would damage the equational theory. Do not schedule one.

The principled endpoint instead: **marking IS a substitution** (rename variables to closed terms), and substitution is already in the calculus. When surface delayed substitution ($u[x := t], surface-v0 finding 2) and meta-layer re-entry exist, the elaborator's Rust marker pass becomes expressible in-language and the 'elaborator emits extra data' oddity dissolves into an ordinary staged operation. That is the API answer: not annotations, an operation.

**The hazard to watch: marker forgeability.** Today airtight — elaborated fragment bodies contain no App at all (verified 2026-08-11, certgen-transcriber-in-language-design sec. 9). When the fragment grows genuine applications (higher-order code), 'identity lambda applied to a numeral' stops being unambiguous. Misreads stay SAFE (refused certificate) but become a completeness annoyance. Constraint discovered this round: a reserved-global marker head does not work — the head's sub-elimination goes neutral and stalls the walk rather than being read. The marker must stay analyzable AND become unforgeable before the fragment includes application; no design yet.

Also homed here: the constant-motive ladder. Constancy is forced today (recursive results at extended contexts cannot be strengthened without delayed substitution) and fits analysis-into-data naturally; transformation passes (_(rebuild), motive Code(g' |- T) tracking the branch context) arrive WITH delayed substitution, and scrutinee-indexed motives (intrinsically verified analyzers) sit behind dependent code types (see in-language-certificate-emission route 3).
