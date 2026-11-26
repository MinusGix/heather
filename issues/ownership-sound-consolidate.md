---
title: Consolidate the ownership soundness proof: CSt::Wf, clauses grouped by what they read, sound.hthr split into modules
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-26
updated: 2026-11-26
---

The coordinating session's item 3 for `claude/ownership-checker-sound`: before the body induction, the soundness proof gets its shape. No interface statement changes here (`verdict.hthr`, `SafeAt` and the checker are untouched); this is the proof's own organisation.

## Plan

- **`CSt::Wf(s)`**: the clauses that speak of the checker's state alone (`one`, `words`, `held`, `vents`, `chain`, `wpar`, `nbase`, and any other mentioning neither run, heap nor meaning) become one record over `s`, kept by each checker transition through a lemma about the checker alone. The join's meet needs exactly this.
- **The rest grouped by what each clause reads**:
  - the object table against the heap (`apart`, `inheap`, `owned`, `young`, `bare`, `made`, `frame`, `grows`, `stays`);
  - the cells against the table (`refs`, `own`, `uni`, `args`, `href`);
  - the places at the run's words (`excl`, `cfit`, `sib`);
  - `sim`.
  Each group gets its transport lemmas once (same heap; same environment at the levels read; one block longer; one cell changed), and the builders call them. `Inv::heap_rest`/`heap_rest_ws` is one such lemma already. Regroup where a clause reads more than its group's indices, and say so.
- **Split `sound.hthr` into modules** along its sections: selections and the lens lemmas; the invariant and its entry; the builders; the stages per statement kind; `Like`; the return; the call. `sound.hthr` is left stating and proving the theorem. Run `scripts/lib-closures --fix`; tests mirror under `lib/_tests/lang/ownership/`.
- If the grouping costs more than it removes (builders, lines, check time before and after), stop and report rather than push through.

## Log

- 2026-11-26 (tenth session): the first piece, forced by P5. `root` is an index of `Inv` and `Stepped`, no longer a field: builders ending in `j(…)` hid it from conversion, and the results' binding needs the pre-call roots after P4. It was a script over 14 constructor calls and the type mentions (8f348f4). `Inv::fresh` is now heap growth then `Inv::bind_fresh` over `Inv::heap_rest_ws` (af72f67). Nothing else of the plan is started.
