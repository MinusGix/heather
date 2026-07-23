# Heather — working notes for Claude

- **Run tests only via `scripts/test`** (wraps `cargo test` in `ulimit -v/-t`
  plus a thread cap). Never run bare `cargo test`: a runaway test or a
  Debug-formatted kernel term can OOM the whole machine, not just the process.
- `Debug` on kernel `Term`/`Type`/`Level` etc. is **budget-bounded**
  (`crates/kernel/src/fmt.rs`: ≤512 nodes, ≤64 depth, `…` elision), so an
  accidental `{:?}` is safe and prints compact syntax. Keep it that way: any
  new recursive kernel type gets a `node()`-gated manual impl, never a
  derived `Debug`. In property tests still prefer seed-only failures (the
  `law!` macro in `crates/kernel/tests/subst_laws.rs`) — bounded output is
  for humans debugging one case, not 300 failing seeds.
- Issue tracker: `scripts/issue` over `issues/*.md` (see `issues/README.md`).
- Type-theory source of truth: `docs/delam/04–06`; `docs/delam/README.md`
  explains which chapters are implementation-relevant (01–03 are a
  simplified warm-up system, not the target).
- Kernel design decisions: `crates/kernel/DESIGN.md`.
