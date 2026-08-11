---
title: Certificate emission in-language: the Psi-staging route, and its two rivals
status: open
labels: [compiler,metaprogramming,kernel,design,delam]
created: 2026-08-11
updated: 2026-08-11
---

Research direction from the transcriber round's user review (2026-08-11), sharpening certgen-transcriber-in-language-design sec. 5's 'two futures' into three routes with a lean.

**What is unstatable today, precisely:** a code type whose statement mentions the transcriber's own output — Code(. |- Converges($prog, $env, $body, $out)) where those are meta-level LOCALS holding computed Ir/Prog values (ordinary first-order inductive data; it is only their address that is wrong — a meta fn's scope, not Psi). Code types index only by globals (the map round's correction 1, ch. 04 CAPP). So in-language we can compute the program but not state the theorem about it; proof-text emission stays Rust.

**Route 1 — Psi-staging (the lean).** The restriction is 'globals only', and the emitted text ALREADY declares the prog/Ir as definitions. So stage: elaborate those declarations first (they become Psi globals), then a layer-m builder states Code(. |- Converges(prog^delta, ...)) legally and folds the existential kit IN CODE by recursion over the Ir value. Kernel-side this looks ready — eliminators are layer-generic (typing.rs 518-583) so Ir-recursion at layer m should check, and Code/box formation is meta-only anyway (typing.rs 630/657, verified 2026-08-11), which is where the builder lives. Missing is SURFACE: ordinary match/recursion in a meta body (meta-body-statement-loop territory) and staged elaboration order (a generator that emits declarations, then emits code referencing them). Crucially this KEEPS the certifying trust story: every output individually kernel-checked, the generator free to be wrong. Verification items for whoever opens this: (a) elim over a lowered (Wf) inductive at Layer::Meta actually checks; (b) a quote payload may reference the just-minted prog^delta at the needed layers; (c) the kit lemmas are quotable at their statement types.

**Route 2 — the fold as a lemma.** One Converges-by-induction-over-Ir theorem with well-formedness hypotheses; generated certificates become applications; prog-extension-lemma retires with it. Flips CERTIFYING into VERIFIED: extending the fragment then extends a proof rather than a heuristic. Cheaper per output (the ~9s double-j kit folds stop being re-derived), costlier per feature. A charter decision on certifying-generator, not a technical default.

**Route 3 — dependent code types over meta data.** Meta-level Pi over terms indexing code — the calculus currently has no form of it at all. Heaviest, metatheory-grade; also the route that gives analyzers scrutinee-indexed motives (code-variable-analysis-api's far rung). File the kernel round only if routes 1-2 both prove insufficient.

Related: certifying-generator (owner of the staged list), prog-extension-lemma (retired by route 2, orthogonal to route 1), meta-body-statement-loop (route 1's surface prerequisite).
