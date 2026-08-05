---
title: Option/Result/List in the prelude, with helpers and chaining
status: open
labels: [frontend,stdlib,elaboration,design]
created: 2026-07-31
updated: 2026-08-01
---

From the first real library file ([[ir-simulate-design]], lib/ir_v1.hthr):
the file declares `OptVal { NoneV, SomeV(v) }` by hand, monomorphic,
because there is nothing to import — every file is a whole program, so a
generic `Option<A>` written in one file helps no other file. The
declaration is trivially writable today (`inductive Opt<A> { None, Some(A) }`
elaborates — polymorphism round); what's missing is a HOME and the
helpers.

Three layers, separable:

1. **Prelude residency.** `Elaborator::with_prelude` already seeds Nat and
   friends; `Option<A>`, `Result<T, E>`, `List<A>` (and their basic fns:
   map, and_then, unwrap_or, append, nth) can live there long before a
   module system exists. This is the cheap 90%.
2. **Chaining ergonomics.** ir_v1's `gather` is the motivating shape:
   two nested `NoneV => NoneV` matches per element, pure propagation
   noise. Rust's `?` (or a `let SomeV(v) = e else ...`/bind sugar) would
   collapse it. This is elaborator sugar — expression-level CPS into
   match chains, no kernel anything — but it wants design care in an
   expression language with no early return (what does `?` scope to: the
   fn body? the enclosing block?).
3. **Dedicated Option syntax** (`T?` etc.): tempting, deliberately NOT
   leaned toward here — it is still an inductive at the end of the day,
   and the value is in layers 1–2; syntax can come later if usage says so.

Adjacent, not owned here: a real module/import story (this issue's layer 1
is exactly the stopgap that defers it); [[map-tabulate-convergence]] if
List/Vec helpers grow bridging lemmas.

## Log

- 2026-08-01: The fuel_monotone round widens layer 1's shopping list beyond
  containers: `lib/ir_v1.hthr` now locally defines a Nat ORDER kit —
  `leb`, `Le` (`fn Le(n: Nat, m: Nat) -> Type { leb(n)(m) = True }`, the
  named proposition the kit is now stated over), `sub`, `le_add`
  (`Le(n, m) -> add(n, sub(m)(n)) = m`),
  `add_left_zero`, `add_succ_left`, `sub_zero` — because the prelude has no
  order on Nat, plus two monomorphic explicit-f congruences (`cong_nat`,
  `cong_nat_val`). The congruence copies are the sharp datum: the prelude's
  own comment scopes `cong_succ` to Nat because "a general cong needs its
  function argument explicit" — but an explicit-f `cong<A, B>(f: A -> B,
  {a}, {b}, p): f(a) = f(b)` looks definable since the polymorphism round,
  and would have replaced both copies. Candidates for prelude residency:
  the general cong (try it first), then leb/le_add and the add/sub lemmas.

- 2026-08-05: Layer 1 is satisfied by [[modules]] instead of
  `with_prelude` seeding, as that issue's design intended:
  `lib/std/nat.hthr` (the whole order kit plus `cong_nat`),
  `lib/std/option.hthr` (generic `Option<A>`: map, and_then, unwrap_or),
  `lib/std/list.hthr` (`List<A>`: append, map, nth) — written in Heather,
  imported with `import nat;` etc. This issue stays open for layer 2
  (`?`-chaining; still the motivating `gather` shape) and the layer-3
  non-decision. The general-`cong` datum above is untouched and still the
  first thing a residency round should try — its home is now `lib/std`,
  not the Rust prelude.
