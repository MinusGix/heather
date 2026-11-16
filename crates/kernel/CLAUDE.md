# `crates/kernel` — the kernel

- Design decisions: `crates/kernel/DESIGN.md`.
- The unit tests are `scripts/test -p heather-kernel-lib --lib`.
- `Debug` on kernel `Term`/`Type`/`Level` etc. is **budget-bounded**
  (`crates/kernel/src/fmt.rs`: ≤512 nodes, ≤64 depth, `…` elision), so an
  accidental `{:?}` is safe. Keep it that way: any new recursive kernel type
  gets a `node()`-gated manual impl, never a derived `Debug`. Property tests
  still report seeds only (the `law!` macro in
  `crates/kernel/tests/subst_laws.rs`).
- `scripts/test --long` (own target dir) runs every slow kernel self-check
  every time (`crates/kernel/src/checks.rs`; they are off by default, and
  `HEATHER_KERNEL_SELF_CHECKS=sampled` or `full` turns them on for one
  `heather` run) — a sweep for rounds touching the kernel's traversals or bounds
  memo, not a gate.
