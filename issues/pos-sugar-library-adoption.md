---
title: Adopt Pos<Nat> on the library's 0 < d parameters
status: open
labels: [stdlib,ergonomics]
area: mathematics
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
docs/library/positivity-evidence-design.md §2 turning into a rule.

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

## Log

- 2026-10-13: everything above but `elf64_command` adopted
  (docs/library/positivity-evidence-design.md §12 says what each call site became).
  `elf64_read_filter`'s binders are `0 < bytes.len()`, which bind no
  variable, so the sugar does not apply. Left open for `elf64_command`'s
  `n: Nat, nonzero: 0 < n` binders, held back while the native triples work
  rewrites that file; migrate them once it lands.
- 2026-11-05: gardener: cites a file it shares with [[native-proven-formatting-api]] (`lib/elf64_format_width.hthr`); [[positive-refinement-type]] (`docs/library/positivity-evidence-design.md`); [[positivity-evidence]] (`docs/library/positivity-evidence-design.md`).
