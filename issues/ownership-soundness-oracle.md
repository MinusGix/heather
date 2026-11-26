---
title: Ownership: SafeAt evaluated, and a search over small programs for a checked program that breaks it
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-26
updated: 2026-11-26
---

`check_sound` is being proved stage by stage, and the proof has been the way defects in the checker and its interface are found: about twenty so far, each met where the proof happened to arrive (`Ret([x, x])`, a moved parameter answered twice, a result's code, a forward atom, an atom that is a view). The checker, the run and the meaning are all functions, so the theorem's statement can be *evaluated* at closed instances. This issue builds that: an executable reading of `SafeAt` and a search over small programs for a checked program that breaks it. Design note §24.

## What it is

- **Deciders at closed data** for each clause `SafeAt` concludes (the run is not stuck; `ReadAll`; `Written`; `Heap::Frame`; `Heap::Kept`; `Value::Views`; the owning results apart; the results coded) and for what a verdict owes at closed arguments (`Owes::Due`). Each is a `Bool` function beside the `Type`-valued clause; a clause's decider is proved to refute it where it answers `False` only when a counterexample needs that to be believed (a finding is confirmed by hand as a `¬` theorem or a refusal probe, so an unproved decider cannot produce a false alarm that lands).
- **A generator** of small programs over the real `Func`/`Sig`/`Prog` types: bodies up to a size over every statement kind (joins and `Jump` included, which the proof has not reached), signatures over every mode and origin, one or two functions and a primitive, values over a word, a record of two words and a short sequence. Enumerated, not sampled, up to the size that runs in the budget; then sampled beyond it.
- **The search**: for each program the checker accepts and each small argument list and world at which what it owes holds, evaluate the run and the meaning and every clause. A checked program that fails a clause is a finding.
- **Calibration by mutation**: each defect already found and fixed (design note §23, the checker issue's log) is put back as a mutant of the checker, and the search must find it. A mutant it misses is a hole in the generator, fixed before the search's silence is trusted.

## Rules

- It reads `checker.hthr`, `run.hthr`, `body.hthr`, `verdict.hthr`; it does not edit them (the soundness session owns them). Findings go to the coordinating session with the smallest program, and are filed here.
- It lives where a tool lives: the deciders in a module of their own under `lib/lang/ownership/`, the generator and the search wherever they run fastest (Heather on the untrusted evaluator, or a Rust driver over it), per `docs/test-value-audit.md`. Say which and why, and the rate reached.
- It follows the interface as the soundness branch changes it: a new `SafeAt` clause gets its decider.

## Done when

Every known defect is found as a mutant, the search runs in the PR lane within a stated budget, and the count of programs enumerated and checked at each size is logged, with every finding either fixed by the soundness session or recorded as a decision.
