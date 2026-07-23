# Heather — working notes for Claude

- **Run tests only via `scripts/test`** (wraps `cargo test` in `ulimit -v/-t`
  plus a thread cap). Never run bare `cargo test`: a runaway test or a
  Debug-formatted kernel term can OOM the whole machine, not just the process.
- **Never `Debug`-format or `assert_eq!` kernel `Term`/`Type` values** in
  tests or error paths — the failure message is built in RAM first and
  substituted terms can be enormous. Compare with `==` and report seeds/ids
  only (see the `law!` macro in `crates/kernel/tests/subst_laws.rs`).
- Issue tracker: `scripts/issue` over `issues/*.md` (see `issues/README.md`).
- Type-theory source of truth: `docs/delam/04–06`; `docs/delam/README.md`
  explains which chapters are implementation-relevant (01–03 are a
  simplified warm-up system, not the target).
- Kernel design decisions: `crates/kernel/DESIGN.md`.
