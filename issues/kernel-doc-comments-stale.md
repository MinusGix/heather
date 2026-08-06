---
title: Stale kernel doc comments: Branches binder counts, '45 branches', a layer-c gate that no longer exists
status: closed
labels: [kernel,docs]
created: 2026-08-06
updated: 2026-08-06
---

Filed from the [[delam-extensions-writeup]] audit (`docs/delam-extensions.md`
§16.11): comment drift, not rule or code defects.

## Log

- 2026-08-06: Landed alongside [[recursor-elim-call-level-mismatch]]: the
  `Unit`/`Empty`/`⟨⟩`/`t_elimE` telescopes in `term.rs` and `rec.rs` now
  carry the level binders the level-indexing round added, "45 branches"
  reads 52 in `conv.rs`/`typing.rs`/`benches/.../code.rs` (and "22
  branches" in `tests/typing.rs`, "45-branch" in `scripts/test`), and the
  layer-c gate wording is gone from `SEq`, `SEmpty`, `SRefl`, `Transp`,
  `ElimSEmpty` and `Vec` — the gates it described are covered by
  `tests/vec_fin.rs::layer_c_accepts_vec_and_fin` and `tests/seq_codes.rs`.
  CLOSING.
