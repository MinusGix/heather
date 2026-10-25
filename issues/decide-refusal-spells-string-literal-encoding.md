---
title: A decide refusal at a string goal spells the literal's encoding
status: open
labels: [elaborator,diagnostics]
area: language
created: 2026-10-25
updated: 2026-10-25
---

Found while giving the string refusals their reasons
([[library-tests-as-theorems]], round 3). `decide` at a goal it has no closed
decision for names the resolved goal, and at a string literal that name is
the literal's kernel encoding, not its source spelling:

```heather
import logic; import bool; import nat; import list; import char; import string;
theorem bad(s: String): s = "hi" { decide }
```

is refused with `the kernel rejected `bad`: NotConvertible. `decide` resolved
`Decide<s = String(Cons(fst[0,0](El[0](«Σ[0,0](«sEq»[0](«Nat»; 14; 14)). …`
to `string::String::Decide#Eq`, whose decision here is not `Inl` …`. The same
refusal at `List<Nat>` (`theorem bad(xs: List<Nat>): xs = Cons(1, Nil) {
decide }`) spells the goal as written, so the gap is the character literal's
encoding (a `Char` carries its `scalar` witness) reaching the goal printer
without a surface spelling.

The refusal is right; only the message is unreadable. A fix would spell the
goal from the elaborated surface term, or render a `Char`/`String` value as
its literal. `crates/elab/tests/lib_std_string.rs`'s
`decide_proves_only_closed_true_goals` pins the reason, not the spelling, so
it keeps passing either way; tighten it to the goal text once fixed.
