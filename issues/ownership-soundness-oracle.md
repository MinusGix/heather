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

**Paused** (2026-11-26) at the repository owner's request. Nothing is thrown away: the deciders and the generator are meant to evaluate a restated invariant along runs before it is proved over. That case is the last section below.

### What exists

- `lib/lang/ownership/oracle.hthr`: the deciders.
  - A `Bool` beside each clause of `SafeAt`. The premises are `Value::read_all_b`, `Dyn::coded` and `Lendable::b`. The conclusions are not stuck, `Done` from the need, `ReadAll` of the answer, `Value::written_b`, `Heap::frame_b` (the lens equation), `Heap::kept_b`, `Value::views_b`, `Value::owned_apart_b` and the results coded.
  - `Owes::holds_b` decides what a verdict owes.
  - `Prog::verdict_b` answers the first clause broken, as a `Clause`.
  - `enc_*` writes a program as numbers for the driver.
  - It is generic over the environment, which supplies `Dyn` equality.
- `lib/lang/ownership/oracle_search.hthr`: the environment and the search.
  - The environment is a word, `Pt` (a record held as an object), `QPt` (the same record, plain) and a list of words with windows.
  - The program is the function under test `0`, the catalogue `cat()` at 1–7 (read views of an element and a window, writes of an element and a field, a list taken and given back, a fresh list, a field read) and the primitive `len` at 8.
  - The world is the meanings unfolded `depth()` deep (`world`). An instance is tried only where one more unfolding changes nothing (`gen_pinned`).
  - The precondition is `pres_b` (below). The generator is `gen_funcs`. Inputs are every argument list over `heap0()` (`gen_values`).
  - `search_stream(fl, np, k, ka, kb, lo, n)` is the search; `search_found` is the same counted, for the kernel.
- `lib/_tests/lang/ownership/oracle_tests.hthr` is the PR lane's share, a few seconds in the kernel:
  - the deciders on hand-made breaking programs;
  - `Lendable::b` on aliasing it must exclude and allow;
  - the search over every function of at most one parameter and a lone `Ret`, one parameter list a theorem.
- `scripts/ownership-oracle`: the driver. It needs the release binary (`cargo build --release -p heather-cli --bin heather`). Every `heather` run is capped (`--limits dev,cpu=3000`).
  - `search --np N --k K --flags F [--ka A --kb B] [--mutant NAME] [--cap C]` searches parameter lists of at most N, bodies of at most K items (a join is one item), and prints each finding's program decoded. Flag bits: 1 calls, 2 joins, 4 `Jump`, 8 signatures fixed first (so an arm may return). `--ka`/`--kb` bound a join's yes and no arm.
  - `calibrate [--only NAME]` runs each mutant at `SIZES`, cheapest first, and prints the table row where it is first found.
  - `calibrate --claims` checks that each `CLAIMS` copy accepts exactly the programs the checker does.
  - `mutants` lists both.
  - A mutant is a copy of `checker.hthr` with one replacement (sometimes also one in the copy of `oracle_search.hthr`), in `target/ownership-oracle/<name>/` beside a copy of the search module. A module beside its importer is found first, so the checked-in checker is never edited. The driver refuses a replacement that does not occur exactly once, which is how a moved checker shows.

### How the generator works

- **Directed by the checker's own pass.** A prefix is kept only where `Stmt::verdict` accepts its last statement (`gen_next` mirrors `Body::verdict`'s `Do` case). The pass refuses a prefix whatever follows, so nothing it would accept is lost.
- **Joins are items.** Each arm is generated from `s.arm()`, its leaf verdict taken, and the two met by `CSt::joined`.
- **Leaves.** Each `Ret` is filtered at the prefix's state (`gen_leaf_ok`). Unfixed signatures read their results off the `Ret`, with the origins its roles allow and some they do not, so a mutant may accept them. The whole function is then re-checked by `check`. So every function offered is accepted.
- **Candidates by code.** Words go to `Op`, `Fresh` and indices; a write's value has the place's code; call arguments have the parameters' codes.

### Rates (4 cores)

- (≤1 parameter, ≤1 statement, straight line): about 1,100 programs in 5.5 s.
- (≤1, ≤2, straight line): 47,870 programs and 168k inputs in 118 s, about 400 programs/s. No findings, against the checker at 1e9103b.
- (≤1, ≤1, flags 15): 3,639 programs in 43 s.
- (2, 1, flags 0): 19,300 programs.
- Generation dominates. The instances (owed, `Due`, the run at fuels 0, 1, 2 and 5, every clause) cost less.

### What each choice hides

- *The precondition*, `pres_b(g, args)` = the arguments coded and `g`'s verdict due there (recursively through `RPre`, depth-bounded), is the strongest the theorem allows. `CheckSound`'s premise "every argument list" then holds by construction. It hides exactly the inputs at which some residual fails, which are outside the theorem's scope, so it is correct. A recursion deeper than `depth()` counts as not owed, which only tries less.
- *`Lendable.apart`* is decided syntactically: other blocks, or a common prefix then two selections `Sel::apart` finds apart. That implies `Sel::Apart`, so the search tries a subset of what the theorem covers. Degenerate apart inputs are not tried: selections apart because one reads a constant, which the proof sessions tripped on.
- *Whole checked programs only.* A defect needing an ill-formed signature in the table with a well-behaved callee behind it is the proof's, not this search's.
- *The world* satisfies `Prog::Coded` (`len` answers a word). Every function is unmeasured, so `need` and the `CNeed` clause are not exercised. The `Going` histories are free (`reaches` is `True`).
- *The catalogue is fixed.* Callee behaviours outside it (two owning results, forward atoms, views of written parameters) are reached only through the function under test's own `Ret`.

### Calibration, as far as it got (checker merged at a68f936, with §23.21)

| mutant | found at (params, items, flags) | programs at that size | findings | first |
|---|---|---|---|---|
| fresh_twice | (1, 0, 0) | 20 | 16 | OwnedApart: `fn (a0: Pt take) → (Pt param 0, Pt param 0) { ret [a0, a0] }` |
| fresh_is_param | (1, 0, 0) | 20 | 16 | Views: `fn (a0: Pt take) → (Pt fresh) { ret [a0] }` |
| param_names_other | (2, 1, 0) | 19,300 | 17,528 | Views: `fn (a0: N take, a1: L take) → (N fresh, L param 1) { fresh L(a0 × a0); ret [a0, l0] }` |
| twice_param | (1, 0, 0) | 20 | 16 | OwnedApart: as fresh_twice |
| sig_ok_own | not found through (1, 2, 0); stopped during (2, 1, 15) | | | |
| the other 25 (`mutants` lists them) | not run | | | |

Before the merge, `fresh_twice` was found at (1, 1, 0), by `fresh L(a0 × a0); ret [l0, l0]` breaking `FreshApart`.

### Not done

1. The rest of the calibration: 25 mutants not run, `sig_ok_own` unresolved. `sig_ok_own` may be a generator hole: unfixed signatures are read off the `Ret`, so an ill-formed own signature is offered only where the `Ret` yields one. Check which programs it needs before trusting a miss.
2. The three newest mutants (`call_atoms_plain`, `sig_ok_read_param`, `sig_ok_telescope`) are in the list and not run.
3. The `AcOwn` claim (`calibrate --claims`, `returns_param_acown`) is not run.
4. The run against the current checker at the larger sizes (`search --np 2 --k 2 --flags 15`), and findings, if any, confirmed by hand as refusal probes or `¬` theorems before they are reported.
5. The PR lane's budget. Only the kernel probes are in the gate. A stated `scripts/test` budget for a small `search` run is not set.
6. Generated callees, `Call(0, …)`, measured functions (`need` least by the `RMeasure` residuals), `WBits` words, more two-step places, the `Bytes`/`[A; n]` instances, and degenerate apart inputs.
7. A faster generator (most candidates are still refused by `code_ok`/`verdict`).

### Evaluating a predicate along a run, not only `SafeAt` at the end

The pieces are all here; what is missing is a run that stops at each statement.
- `Body::run` is in continuation form: `Stmt::run(…, m, k)` hands the next machine to `k`.
- The checker's state after each statement is what `gen_next` computes (`Stmt::verdict(…).st`).
- The meaning's environment after it is `Stmt::eval(…, env, λ e => e)`.

So a predicate `P(CSt, Env, Mach) → Bool`, for instance a decidable reading of `Inv` or `Sim`, can be checked after every statement by walking the generated body's items with all three side by side:
- the checker state from `gen_next`;
- the meaning's environment by `Stmt::eval`;
- the machine by one `Stmt::run` with `k = λ m => Done(Answer(Nil, m.heap, m.io))`, reading `m` back out (or a copy of `Stmt::run` answering the machine).

A join steps into the arm its test picks, from `s.arm()`, then `CSt::joined` and the push of the yielded cells. A call is one step at the caller's level. This walk is a new function beside `gen_try`; the generator, the inputs, the precondition and the encoding are unchanged. The predicate's decider needs the same environment parts the clauses did: `eq`, and the syntactic apartness for anything `Sel::Apart`-valued. A finding would then name the first statement after which the predicate fails, which is where its stage lemma would be false.

### Traps

- **A fold with a lazy accumulator over a long stream** builds a thunk chain. The untrusted machine then gives up on nesting depth and falls back to the kernel's evaluator, which runs out of fuel or memory. Emit a `List<Nat>` stream and let the driver sum it (`search_stream`).
- **A mutant that changes `Body::verdict`'s `Do` condition** must make the same change in `gen_next`'s copy (the `between` mutant does), or pruning refuses what the mutant accepts.
- **Namespaces.** `Name::f` needs a declared type `Name`; the search's free functions are `gen_*`. Free functions are declared before use; members are not ordered.
- **`heather eval`'s answer** is read on the untrusted machine only if it can run it. `HEATHER_READ_TRACE=1` says which evaluator ran and why.
- **The kernel probes** each fit the kernel's budget only one parameter list at a time.

## Log

- 2026-11-26 (first session): deciders, generator, driver, PR probes. Rates on 4 cores, for the checker as merged at 1e9103b:
  - (≤1 parameter, ≤1 statement, straight line): 1,134 checked programs in 5.5 s, 207/s.
  - (≤1, ≤2, straight line): 47,870 programs, 168k inputs tried, 146k owed, 101k with the verdict held. 118 s, 407/s. No findings.
  - (≤1, ≤1, every flag): 3,639 programs in 43 s.
  - Calibration against the checker merged with §23.21: the Handoff's table. Paused at the owner's request with 4 of 30 mutants found, 1 unresolved and 25 not run.
