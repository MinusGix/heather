---
title: The u^δ rule rescopes a binding's Δ and type once per occurrence: what is left of shift_global after the lazy bodies
status: open
labels: [kernel,conversion,performance]
created: 2026-09-18
updated: 2026-09-18
---

The `u^δ` / `U^δ` conversion rule rescopes the binding's declared Δ and its type into the ambient Ψ **once per occurrence** (`conv.rs`, counted by `global_ref_rescopes`), and since [[refl-theorem-step-cost]] made definition *bodies* lazy that is the whole of what `shift_global` still costs: 38.2 M of the showcase's 47 M remaining rescoped nodes, over 4.77 M occurrences, in a cold width-one `heather check docs/showcase/calc_parser.hthr` (2026-09-18). The heaviest items after that round are exactly the ones with no body unfolds at all: `parser_primitives::complete_post` 6.74 M nodes at 929,580 refs, `calc_parser::Grammar` 2.23 M at 209,370 refs and no unfolds, `parser_contracts::Certified` 1.96 M at 94,025, `calc_parser::close_body` 2.57 M at 528,714.

Unlike a body, this rescoping *is* cacheable as it stands: it is `shift_global(v + 1)` of a **binding's** ctx and type — a function of the index and the ambient Ψ alone, not of the occurrence or of the δ that occurrence carries, which is exactly the argument `reduce::BodyCache` already rests on. So the first candidate is a second slot in that cache (or a sibling of it) keyed by `GlobalVar`, owned beside the Ψ it belongs to and rebuilt when a telescope push changes Ψ. The second candidate is the same trick the bodies got: compare the substitutions without materializing the declared context at all, since only its length and entry types are read. Measure before choosing; the memo is the cheap one and the round should say what it bought. Related: [[refl-theorem-step-cost]], [[simulate-conversion-cost]].
