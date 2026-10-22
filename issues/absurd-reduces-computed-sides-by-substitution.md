---
title: absurd reduces a computed equation side by substitution to find its constructor
status: open
labels: [elaboration,performance]
area: language
created: 2026-10-22
updated: 2026-10-22
---

`absurd(h)` (and `inj`, through the same `Elaborator::equation`,
`crates/elab/src/inductive.rs`) reads both sides of `h`'s equation as
constructors. It gets them with `whnf_tm`, and `SemanticOracle::whnf_term`
answers a constructor with sub-structure (anything but the Nat/universe/unit
leaves it special-cases) by the substitution reducer at full fuel. When a side
is a *computation* rather than a constructor spelled out, that redoes the
whole computation by `apply_local`, copying every intermediate term.

Workload: `crates/elab/tests/fixtures/linux_wp_drain.hthr`'s `drain_pass`.
The empty read's jump branch was `λ no => absurd(no)`, with
`no : condition_holds(E, <flags after TEST RAX,RAX over the answered machine
state>) = False`. Reducing that flag spelled the answered state, the block's
execution and the 64-bit `is_zero_bits` by substitution: about 90 CPU-s of
the item's 111 (gdb samples: `build_absurd` → `equation` → `whnf_tm` →
`reduce::whnf_term_delta`), against a kernel gate of about 17 s. Citing a
lemma for the flag (`trans(sym(drain_none_zero()), no)`, the form the other
two answers already used) makes the equation's sides `True` and `False` as
written, and the item 22 s with identical kernel steps. That fixture change
is in (2026-10-22, [[linux-wp-cold-rail]]); the elaborator cost is not.

## Levers

- **Ask conversion, not the reducer, when the side's constructor has no
  fields.** For each nullary constructor of the equation's inductive, convert
  the side against it in the value domain (what the kernel will do anyway);
  on a hit, spell the side as that constructor. Sound because the kernel
  re-checks `J` against the proof's type, and the spelling is a convertible
  one. Covers every `Bool`/flag/enum `absurd`, the common case.
- **A term readback beside the type readback** (`crates/elab/src/readback.rs`,
  [[elab-whnf-copies-straight-continuations]] lever 1): read the value's top
  constructor layer back. Not node-for-node with the reducer today: a
  `PairAt`/`InlAt` value drops its `ty` annotation (`Val::Pair { ann: None }`),
  so the readback cannot always respell what the reducer would, and the
  elaborator anchors on spellings (`docs/nbe-conversion-design.md` §7).

Acceptance: `drain_pass` written with the bare `absurd(no)` elaborates in
about its gate's time.
