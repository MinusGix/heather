---
title: Projecting a theorem-valued record field exhausts memory
status: open
labels: [elaborator,defect]
created: 2026-08-15
updated: 2026-08-15
---

Found in the datarepr v1 round (2026-08-15, docs/datarepr-design.md §1.4 as-landed note 7): projecting a theorem-valued field off an assembled record VALUE (e.g. `ListTok().Cons_abs`) exhausts memory and dies on the ulimit — a user-reachable SIGABRT, not a slow check. The datarepr elaboration works around it by reaching through the generated namespace (`Repr_N::Cons_abs()`), which is why nothing in the landed tests hits it. Repro shape: any record with a proof-valued field, assemble a value, project the proof field. Likely a conversion/unfolding blowup where the projection forces the whole record value; worth a minimized repro before any fix. Related: [[datarepr-separation]].

## Log

- 2026-08-15: Promoted from workaround to DESIGN CONSTRAINT by docs/obligation-records-design.md §1.3: every obligation's proof is declared in the owner's NAMESPACE and the assembled record value is consumed whole or not at all — no path the new surface introduces projects a theorem field off a value. It is also now a PREREQUISITE for something wanted: repr-access-spellings' dot-shaped reference form, and any future reading of 'BinC.Succ_inv' as an expression rather than as a slot key, are blocked until this is fixed.
- 2026-08-15: Priority raised by user verdict on the obligation-records design (2026-08-15): this is a temporary performance bug and it does not get to hold designs back — the design round had bent its access-spelling reasoning around it (docs/obligation-records-design.md §1.3/§3), and the user ruled that if the right answer is blocked by a bug, the bug gets fixed sooner instead. repr-access-spellings should design assuming this is fixed; a fix round moves up the queue.
- 2026-08-15: The obligation-records round shipped without designing around this (2026-08-15). docs/obligation-records-design.md §1.3 was rewritten per the methodology verdict: the namespace rule now stands on its own three merits — the statement is source text before it is a term (which is what lets a '?' and the listing print something a human can read), laws must be reachable before the record value they are fields of exists, and one name per obligation is what the provenance/listing machinery keys on — and this bug is named as a bug to be fixed, with the note that the rule would be the rule anyway once it is. So nothing landed this round depends on the bug staying unfixed, and nothing landed this round is a workaround for it. Still unfixed, still user-reachable, still blocking repr-access-spellings' dot-shaped reference form.
