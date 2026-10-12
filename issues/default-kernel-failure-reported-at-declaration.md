---
title: Report a default's kernel-only failure at the call, not the declaration
status: open
labels: [frontend,elaboration,defaults,diagnostics]
created: 2026-10-12
updated: 2026-10-12
---

A default whose failure only the kernel sees is reported at the
declaration, where the default's syntax is, rather than at the call or
construction that left it out. `refl` is the usual case, because the
elaborator leaves its endpoints to the gate:

```heather
fn f(n: Nat, h: n = Zero := refl) -> Nat { n }
fn g() -> Nat { f(1) }   // reported at `refl` in `f`, as a kernel error
```

A failure during elaboration (an `omega` leaf, a type mismatch) is
reported at the call, naming the parameter or field and the way out
(`h := …`). Both kinds are about the call site's instantiation, so both
should be reported there.

This was the second gap logged on [[field-defaults-under-locals]], which
closed when defaults began running under locals; parameter defaults
(docs/named-arguments-design.md §9.6) share it.

## Direction

Check a default's elaborated term against the instantiated goal before
it leaves the marker (a conversion check of `refl`'s endpoints, or the
kernel's judgment on the closed-over goal), and map a failure to the
marker's span with the same message the elaboration failure gets.
