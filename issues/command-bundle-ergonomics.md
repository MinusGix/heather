---
title: A command bundle that states its columns once
status: open
labels: [native,surface-syntax,ergonomics]
created: 2026-10-07
updated: 2026-10-07
---

The end of `wc.hthr` (`:75-91`) carries bookkeeping a reader has to check by
hand:

```heather
fn wc_command() → Command<WcState>(counting(wc_step), WcState(0, 0, 0, False), [λ s => s.lines, λ s => s.words, λ s => s.bytes],
    wc_columns(), [True, True, False, True]) {
    …
    Command(counting_columns(wc_step, zero, wc_columns(), λ input => ⟨lines(input), ⟨words(input), ⟨bytes(input), ⟨bytes(input), trivial⟩⟩⟩⟩))
}
```

- **Counts twice.** `counts` lists the projections, and each `Column`
  repeats one. `Command` needs `counts` for `advances` and `columns` for
  meaning; nothing ties them. The counts could be derived from the columns.
- **A column's count is any function `C → Nat`, but the machine needs a
  field.** The producer recovers the field by evaluating each count at a
  probe state whose field `k` holds `k + 1` (`read_command.rs:239-268`). A
  typed field reference (a derivable `NatFields<C>`, or a projection section
  from [[field-projection-sections]]) would make it structural.
- **`default` is positional.** `[True, True, False, True]` means "l, w, c"
  only if you count. A set of letters, or a flag on each `Column`.
- **The proof is a nested tuple ending in `trivial`,** because `ColumnsMean`
  is a recursive `Type` over a list (`filter_program.hthr:68`). An `All<P>`
  type with list-literal introduction would read `[lines, words, bytes, bytes]`.
- **`zero` and the `refl`s** (each count is zero at `init`, `init` is not
  inside a run) are closed computations a default could discharge.

## What it assumes from elsewhere

- **[[native-wc-as-a-command]]** owns `Command` as built. Assumed here: only
  that its fields may change shape while the claim stays the same.
