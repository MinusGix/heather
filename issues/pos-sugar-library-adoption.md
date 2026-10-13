---
title: Adopt Pos<Nat> on the library's 0 < d parameters
status: open
labels: [stdlib,ergonomics]
created: 2026-10-13
updated: 2026-10-13
---

Adopt the `Pos<A>` binder sugar ([[pos-binder-sugar]]) on the library's
existing positivity hypotheses, so their callers stop passing proofs the
search can find.

Candidates, found by `grep -n ': 0 < ' lib`: `Nat::mod_lt` and `nat.hthr`'s
division lemmas (`div_mul_parts`, `div_div`, `mod_mul_mod`,
`div_mod_eq_mod_div`, `div_split`), and the native libraries' binders
(`elf64_command`, `elf64_format_width`, `elf64_read_filter`, `field_line`).
`ten_pow` (`lib/elf64_format_width.hthr`) becomes `→ Pos<Nat>` with
`on ?pos := ten_pow_positive(i);`, replacing `ten_pow_pos` with
`ten_pow::pos`, which is the call-site case (c) of
docs/positivity-evidence-design.md §2 turning into a rule.

Cost: each migrated signature changes its callers' positional arity (the fact
moves from a positional slot to a searched one), so every call site that
passed it positionally is rewritten, to nothing where the search finds it or
to `name_pos := …` where it does not. `mod_lt` alone has about fifty uses.
The native libraries' changes rebuild their certificates, so run the full
suite.

## What it assumes from elsewhere

- **[[pos-binder-sugar]]** owns the sugar. Assumed here: a parameter's fact is
  named `x_pos` and searched by `:= infer`.
- **[[retire-shifted-pos]]** owns `Rat` and the cancellation lemmas, which
  are not in scope here.
