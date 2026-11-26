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

## Handoff

**Where it is.** The pieces:
- `lib/lang/ownership/oracle.hthr` holds the deciders: one `Bool` per `SafeAt` clause, `Owes::holds_b` for `Due`, and `Lendable::b` (syntactic apartness, which implies `Sel::Apart`, so it only under-tries). It also writes a program as numbers (`enc_*`).
- `lib/lang/ownership/oracle_search.hthr` holds the environment, the generator, the program (the function under test `0`, the catalogue `cat()` at 1–7, the primitive `len` at 8), the world unfolded `depth()` deep, and the stream `search_stream(fl, np, k, ka, kb, lo, n)`.
- `scripts/ownership-oracle` runs `search`, `calibrate`, `calibrate --claims` and `mutants`.
- `lib/_tests/lang/ownership/oracle_tests.hthr` is the PR lane's share: the deciders on hand-made breaking programs, `Lendable` on aliasing, and the search at its smallest size by the kernel, one parameter list a theorem.

**How it works, and why so.**
- Heather on the untrusted evaluator, through `heather eval`. It reads the real checker, run and meaning, and startup is about 1 s on cached images.
- A mutant is a copy of `checker.hthr` with one replacement, placed beside a copy of `oracle_search.hthr` in `target/ownership-oracle/<name>/`. A module beside its importer is found first.
- The generator is directed by the checker's own pass:
  - A prefix is kept only where `Stmt::verdict` accepts its last statement. The pass refuses a prefix whatever follows, so this loses nothing.
  - Joins are items, their arms generated and met by `CSt::joined`.
  - Each `Ret` is filtered at the prefix's state, then the whole function is re-checked by `check`.
  - So every function offered is accepted.
- Statement candidates are chosen by code: words for `Op`, `Fresh` and indices; a write's value of the place's code; call arguments of the parameters' codes.
- The precondition is maximal: `pres_b(g, args)` holds where the arguments are coded and `g`'s verdict is due there, recursively. `CheckSound`'s "every argument list" premise then holds by construction.
- The world is the meanings unfolded `depth()` deep. An instance is tried only where one more unfolding changes nothing at its arguments (`gen_pinned`).
- Fuels tried are 0, 1, 2 and 5.

**What the choices hide.**
- *The precondition* `Coded ∧ Due` is the strongest the theorem allows. It hides exactly the inputs at which some residual fails, which are outside `check_sound`'s scope, so that is correct.
- *`Lendable.apart`* is decided syntactically: other blocks, or a common prefix and then two selections `Sel::apart` finds apart. That implies the semantic `Sel::Apart`, so the search tries a subset of the inputs the theorem covers. Degenerate apart inputs are not tried yet: selections that are semantically apart because one reads a constant, which the proof sessions tripped on.
- *Whole checked programs only.* A defect that needs an ill-formed signature in the table, with a well-behaved callee behind it, is outside this search and belongs to the proof (the coordinator's note).
- *The world*: `Prog::Coded` holds of the one primitive (`len` answers a word).

**Next, in order.**
1. Whatever calibration missed (the log's table) is a generator hole: fix it first.
2. Generated callees in place of the catalogue (signatures over every mode and origin, two-owning-result callees), and `Call(0, …)` of itself.
3. Measured functions: `need` as the smallest the `RMeasure` residuals allow, and the `CNeed` clause exercised.
4. Words of a width (`WBits`), two-step places beyond the one window-then-element, `Bytes`/`[A; n]` instances.
5. A faster generator. Most of a run is generation, and the statement menu is still mostly refused by `code_ok`/`verdict`.
6. The PR lane's budget stated in `scripts/test` terms (the kernel probes are seconds). The deep run is `scripts/ownership-oracle search --np 2 --k 2 --flags 15`.

**Traps.**
- Never fold a lazy accumulator over a long stream on the untrusted machine. The thunk chain made it give up on nesting depth and fall back to the kernel's evaluator, which ran out of fuel or memory. Emit a `List<Nat>` stream and sum it in the driver.
- A mutant that changes `Body::verdict`'s `Do` case must also change the copy of that condition in `gen_next` (the `between` mutant does).
- `count_funcs` and the `search_*` terms take the flag bits as the driver's `--flags`: 1 calls, 2 joins, 4 `Jump`, 8 signatures fixed first (arms may return).
- `Gen::`-style namespaces need a declared type. Free functions here are `gen_*`.

## Log

- 2026-11-26 (first session): deciders, generator, driver, PR probes. Rates on 4 cores, for the checker as merged at 1e9103b:
  - (≤1 parameter, ≤1 statement, straight line): 1,134 checked programs in 5.5 s, 207/s.
  - (≤1, ≤2, straight line): 47,870 programs, 168k inputs tried, 146k owed, 101k with the verdict held. 118 s, 407/s. No findings.
  - (≤1, ≤1, every flag): 3,639 programs in 43 s.
  - Calibration against the checker merged with §23.21 is in the table below.
