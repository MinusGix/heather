---
title: The right API for variable-obscured code analysis: markers are staged substitution
status: open
labels: [metaprogramming,kernel,delam,design]
area: kernel
created: 2026-08-11
updated: 2026-08-11
---

Research direction from the transcriber round's user review (2026-08-11). tm_var's opacity is LOAD-BEARING metatheory, not a gap: if a recursor branch could observe which variable it received, eliminating code and then substituting into it would disagree with substituting first — the recursor's stability under the substitution calculus depends on variables being handled uniformly, and layer v exists to make exactly that abstraction (ch. 04 ll. 1204-1207). A kernel 'fix' exposing variable identity would damage the equational theory. Do not schedule one.

The principled endpoint instead: **marking IS a substitution** (rename variables to closed terms), and substitution is already in the calculus. When surface delayed substitution ($u[x := t], surface-v0 finding 2) and meta-layer re-entry exist, the elaborator's Rust marker pass becomes expressible in-language and the 'elaborator emits extra data' oddity dissolves into an ordinary staged operation. That is the API answer: not annotations, an operation.

**The hazard to watch: marker forgeability.** Today airtight — elaborated fragment bodies contain no App at all (verified 2026-08-11, certgen-transcriber-in-language-design sec. 9). When the fragment grows genuine applications (higher-order code), 'identity lambda applied to a numeral' stops being unambiguous. Misreads stay SAFE (refused certificate) but become a completeness annoyance. Constraint discovered this round: a reserved-global marker head does not work — the head's sub-elimination goes neutral and stalls the walk rather than being read. The marker must stay analyzable AND become unforgeable before the fragment includes application; no design yet.

Also homed here: the constant-motive ladder. Constancy is forced today (recursive results at extended contexts cannot be strengthened without delayed substitution) and fits analysis-into-data naturally; transformation passes (_(rebuild), motive Code(g' |- T) tracking the branch context) arrive WITH delayed substitution, and scrutinee-indexed motives (intrinsically verified analyzers) sit behind dependent code types (see in-language-certificate-emission route 3).

## Log

- 2026-08-11: User notes (2026-08-11): transformation passes are affirmed as PRACTICALLY CORE ('that's a core thing to be able to do to code') — raises the priority of the delayed-substitution/context-tracking-motive rung above 'someday'. And on forgeability: the user floats UNFORGEABLE THINGS as a possible fundamental language feature (generative/nominal tokens — 'Rust-style lifetimes sortof want a similar thing'), explicitly not to be planned as a generalist feature now; parked here because an unforgeable marker head is exactly what the forgeability hazard wants and a branded token is the shape that survives analysis where a reserved global goes neutral.
- 2026-08-11: Finding from the certificate discussion (2026-08-11) that weakens route 3's customer list and softens this issue's endpoint: the marker seam only needs substitution by CLOSED terms, and closed-substituend substitution is eagerly performable — an admissible operation on code, not a new former. So surface $u[x := t] for closed t can land as elaborator-performed sugar with a clean name: no pending substitutions, no ch. 05 edit, no conversion subtlety. The in-language marking future is therefore CHEAPER than 'delayed substitution' suggested; full CMTT machinery remains needed only for open substituends (dependent motives territory), and may never fire.
- 2026-08-14: The tier-0-parameters stage (docs/certgen-tier0-params-design.md@4acf2fe) landed WITHOUT this issue's substitution rung, correcting the non-Nat design's forecast that it would want closed-term substitution: the tier-1 round's marker conventions (accessor chains by lambda-arity, arm headers, scrutinee replacement) covered the Case tree whole, and payload-free arms need no accessor at all. The rung's live customers are now fielded tier-0 parameters (the Fst(Snd^j ·)-over-branch-binder coordinate that round deferred) and the transformation-pass ladder above.
