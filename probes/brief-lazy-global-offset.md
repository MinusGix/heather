# Round brief: lazy global offset in the value machine

Owning issue: `issues/refl-theorem-step-cost.md` (read its 2026-09-18 log
entry first; it holds the numbers and the fix candidate). Branch:
`claude/lazy-global-offset`. Coordinator commits; you do not.

## The defect

`Defs::body` (`crates/kernel/src/reduce.rs`) rescopes a definition's body
into the ambient Ψ with `shift_global(v + 1)`, memoized in a `BodyCache`
that `typing::check_term` creates per gate call. Every gate call therefore
re-copies every definition it unfolds; a closed refl theorem over the
certified parser walks 2.8–6.5 M nodes doing it and the showcase's root
module 105 M (16.8 s of its 18.5 s gate). The shift amount differs for the
same binding in every later Ψ, so a cross-item cache cannot help.

## The change

Stop shifting on the evaluation path. A syntactic closure (`TmClo::Syn`,
`TyClo` — `crates/kernel/src/value.rs`) carries a global-index offset
`gshift: u32`; `Eval::global_tm` (`crates/kernel/src/eval.rs`, ~1372)
evaluates the **unshifted** body under offset `v + 1` instead of asking
`Defs::body` for a copy. Wherever syntax inside a closure becomes a value or
a lookup that names a global, the offset is applied:

- `Term::GlobalTm` / `Type::GlobalTy` → `Head::Global { var: var + gshift }`
  and the body lookup by the ambient index;
- `CtxBase::Var(g)` and `SubstTail::Wk { ctx_var }` / `Empty { base }` when
  they are read off syntax under a closure;
- anything else `ShiftGlobal` touches — audit `impl Mapper for ShiftGlobal`
  in `crates/kernel/src/subst.rs` (~996) for the complete list; every hook
  there that changes something is a site.

The rewriter path keeps the eager shift: `reduce.rs:391`
(`step_term_delta`'s δ), typing's cold `whnf`, and `Eval::whnf_ty_syntax`
(Δ stays syntactic by design). `Defs::body` stays for them; add an
unshifted accessor beside it for the machine.

Adequacy is one equation, `eval(shift_global(k, t), ρ) = eval(t, ρ) at
offset k`; the design doc states it and the differential oracle
(`crates/kernel/tests`, eval against reduce) is the test.

## Three traps — design around them, do not discover them

1. **Closure identity must include the offset.** `CloId` (`value.rs` ~935,
   ~1011) keys the conversion verdict memo (`conv.rs` ~1204) and the
   transducer cache (`value.rs` ~775). Two closures over the same body and
   environment at different offsets denote different things. Same for every
   `ptr_eq`/`==` reflexivity shortcut on closures (`DESIGN.md` §"Shared
   syntax and scoped closure identity are reflexivity"; `conv/dom/values.rs`
   ~1263–1306): the scope pair is load-bearing there already; the offset
   joins it.
2. **Boxes carry raw syntax.** `Val::BoxTy`/`Val::BoxTm` (`eval.rs` ~1110)
   hold syntax with no environment, and box comparison is syntactic. A box
   formed from an unshifted body under offset `k` must be shifted eagerly at
   formation (`shift_global(k)` on the boxed code, once). Boxes are small;
   say so and measure it with the counter.
3. **Every syntax-to-value site that names a global.** Miss one and the
   result is a wrong index, which the kernel may accept (a different
   binding of the same type) rather than reject. The design doc lists the
   sites from the `ShiftGlobal` audit, and a debug assertion or a
   differential test covers each: the existing kernel differential oracle
   plus a new fixture whose definitions reference *other* definitions at
   several Ψ depths (so an unshifted index would resolve to the wrong
   binding and be detectably ill-typed).

## Protocol

1. **Design first**: `docs/lazy-global-offset-design.md`. Sections: the
   defect and datum; the offset's semantics; the site list from the
   `ShiftGlobal` audit with each site's treatment; closure identity; boxes;
   what stays on the eager path and why; the adequacy equation and where it
   is recorded (`docs/ch05-06-lemma-audit.md` machine-adequacy row gains a
   sentence, no new row); tests; acceptance. Keep it under ~250 lines.
   Report the design (stop and return) before implementing if any site's
   treatment is unclear or a trap turns out worse than stated; otherwise
   continue.
2. **Implement** on the branch. Match the surrounding style by hand; **never
   run `cargo fmt`**. Kernel stays at zero dependencies and no `unsafe`.
3. **Inner loop**: `(ulimit -v 8388608 -t 300; target/release/heather check
   -L lib/std -L lib/std/parser --cache --cache-dir <scratch> --kernel-workers 1
   --only calc_parser::parentheses --timings f.tsv docs/showcase/calc_parser.hthr)`
   after one plain `--cache` publish of the file into that scratch cache
   dir (republish after every rebuild; `--accept-stale-images` is the fast
   lane). Read with `scripts/timings f.tsv calc_parser::parentheses
   --columns "total ms,gate ms,misses,queries,steps,rescope,unfolds,refs"`.
   Build (`cargo build --release -p heather-cli`) **before** entering a
   `ulimit` cap (mold needs address space). Never run `heather` uncapped.
4. **Tests**: `scripts/test --fast` for the inner loop (never bare `cargo
   test`); the round's final verification is the plain full `scripts/test`,
   run in the background while you write up. Read the `== suite: N passed
   … ==` line; `INCOMPLETE` means a binary died, not a smaller green suite.
5. **Snapshot** at the end: `scripts/perf snapshot --corpus quick --label
   "lazy global offset"` with a plain release build (no
   `CARGO_PROFILE_RELEASE_DEBUG`; it inflated a snapshot's seconds by 15 %
   on 2026-09-18). Then `scripts/perf report`.
6. **Bookkeeping**: log the result on `issues/refl-theorem-step-cost.md`
   via `scripts/issue log refl-theorem-step-cost` (numbers there, not in
   docs); close it only if acceptance holds. Update `crates/kernel/DESIGN.md`
   (the δ-glueing bullet) in one paragraph.

## Acceptance

- `shift_global_nodes` on the showcase root module falls from 105 M to the
  rewriter path's remainder (report the number; expect well under 10 M), and
  `calc_parser::parentheses` from 6.5 M to near zero; `misses`, `queries`,
  `steps` **unchanged to the unit** on every item (this is a representation
  change, not a semantic one — a moved count is a defect).
- Showcase cold check materially faster in the snapshot (the datum says
  ~15 s of 52 s is at stake; report what moved, do not promise the number).
- Kernel suite, differential oracle, certgen controls, `scripts/bench
  --check` green; the full `scripts/test` green.
- No new kernel dependency, no `unsafe`, no `cargo fmt`.

## Reading list, in order

1. `issues/refl-theorem-step-cost.md` (2026-09-18 entry).
2. `crates/kernel/src/reduce.rs` 90–165 (`Defs`, `BodyCache`).
3. `crates/kernel/src/eval.rs` `global_tm` (~1372) and the closure
   constructors; `crates/kernel/src/value.rs` `TmClo`/`TyClo`/`CloId`/`Head`.
4. `crates/kernel/src/subst.rs` `impl Mapper for ShiftGlobal` (~996) — the
   site list.
5. `crates/kernel/DESIGN.md` §Algorithms (δ glueing; shared syntax and
   scoped closure identity) and `docs/nbe-conversion-design.md` §3 (locals
   are the only environment-based namespace; levels/globals syntactic — the
   decision this round amends for globals, offset-only) and §7 (no readback).
6. `CLAUDE.md` (test and ulimit discipline).

Report back with: the design doc path, the counter before/after on the two
gates above, the suite line, the snapshot's corpus table, and anything you
left undone.
