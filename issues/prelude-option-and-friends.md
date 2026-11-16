---
title: Option/Result/List in the prelude, with helpers and chaining
status: open
labels: [frontend,stdlib,elaboration,design]
area: language
created: 2026-07-31
updated: 2026-11-01
---

From the first real library file ([[ir-simulate-design]], lib/certgen/ir_v1.hthr):
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
  containers: `lib/certgen/ir_v1.hthr` now locally defines a Nat ORDER kit —
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
  `lib/std/num/nat.hthr` (the whole order kit plus `cong_nat`),
  `lib/std/core/option.hthr` (generic `Option<A>`: map, and_then, unwrap_or),
  `lib/std/data/list.hthr` (`List<A>`: append, map, nth) — written in Heather,
  imported with `import nat;` etc. This issue stays open for layer 2
  (`?`-chaining; still the motivating `gather` shape) and the layer-3
  non-decision. The general-`cong` datum above is untouched and still the
  first thing a residency round should try — its home is now `lib/std`,
  not the Rust prelude.
- 2026-08-07: 2026-08-07, advanced by the traits library-adoption round ([[traits]]). The
shopping list this issue kept is shorter by four:

- **The general `cong`** this log flagged in 2026-08-01 as "the first thing a
  residency round should try" turns out to have landed already, in the *Rust*
  prelude (`crates/elab/src/prelude.hthr`), with its function argument
  implicit and solved by anti-unification. `lib/std/num/nat.hthr`'s `cong_nat`
  and `lib/lang/list_algos.hthr`'s `cong_cons`/`cong_append_l` are therefore
  survivals, not necessities; retiring them is a separate small round (each
  is a *name* other files call, so it is a rename with referents).
- `lib/std/num/nat.hthr` gains `add_assoc` and `add_comm` — the two laws any
  algebraic client needs first, and both three-liners over the two moving
  lemmas that were already here.
- `lib/std/core/bool.hthr` finally has the `not`/`and`/`or` kit its own header
  asked for, with associativity/unit/commutativity for both operations and a
  decided order (`leb_bool`, `leb_bool_refl`).
- `lib/std/data/list.hthr` gains `cong_cons`, `append_nil`, `append_assoc`, moved
  in from `lib/lang/list_algos.hthr` (which imports them and is unchanged in what
  it proves).

Coverage note, filed here because it is a fact about this issue's layer 1 and
not about traits: before this round `lib/std/data/list.hthr`, `lib/std/core/option.hthr`
and `lib/lang/list_algos.hthr` had **no automated coverage** — only `nat` and
`bool` were checked, incidentally, by `crates/elab/tests/ir_v1.rs`. The
closure is now checked by `crates/elab/tests/lib_algebra.rs` and
`crates/elab/tests/lib_list_algos.rs` (0.8s).

Layer 2 (`?`-chaining, the `gather` shape) is untouched and remains this
issue's open scope.
- 2026-08-13: Verdict from the showcase critique (2026-08-13) on implicit Ok-wrapping (moving `Ok` out of every arm of a Result-returning body): NOT global T -> Result<T,_> coercion — it makes the elaborated term diverge from the written term (which is what refl unfolds, diagnostics print, and theorems are stated over; diagnostics-name-the-written-form is this wound already), and coercion in checking position is ambiguous exactly when T is itself a Result (the nested-Result footgun). The acceptable middle if the pattern proves common: an opt-in per-fn marker (try-fn shape) where the body checks at T, `?` marks failure, and wrapping is declared at the one declaration site. Rides with whatever [[effects-direction]] decides for Result-as-effect; wire the two when either moves.
- 2026-08-13: Also filed off the same critique: [[inline-enum-types]] — per-signature anonymous enums so narrow error types are cheap to declare; the `?` embedding story there is From-style and lands in this issue's chaining kit if taken.
- 2026-08-16: Residency landed for `True` (2026-08-16, [[true-prop-trivial-hypotheses]] half 1). It does NOT live in `lib/std` and it is not a declaration: `True` is the kernel's `Unit^0` claimed as a surface type name in the elaborator (crates/elab/src/inductive.rs `lower_named`), with `trivial` its canonical inhabitant (crates/elab/src/lib.rs, alongside `refl`/`FZ`) — i.e. always in scope for the same reason `Nat` is, with no import. The reason is forced rather than chosen: `crates/elab/src/prelude.hthr` is surface source, and the surface has no spelling for kernel `Unit`, so a prelude-source `True` was not writable; and the whole point of `True := Unit` is η-as-proof-irrelevance, which a one-constructor `inductive True` in `lib/std` would not have. Shadowing follows the `FZ` rule in both namespaces: a declared `True` type wins, a local `trivial` wins, and `Bool`'s `True` **constructor** is untouched (a constructor is not a type name), pinned by crates/elab/tests/true_prop.rs. Nothing is owed here.
- 2026-08-16: Layer 1's shopping list for `Nat`/`List` API content now has its own owner: [[std-api-waves]] holds the wave sequencing, with [[std-logic-module]], [[nat-order-kit]], [[decide-class]] and [[std-int-encoding]] owning the content. Nothing moves here — this issue keeps residency and layer 2 (chaining ergonomics, the `?`-shaped question), which is the half none of those touch.

- 2026-09-14: Result residency and function/lambda-scoped `?` with explicit Ok are implemented by [[result-propagation]], including a runnable parser client. This issue retains Option chaining and any customer-driven generic propagation protocol; implicit success wrapping remains an unselected design option.
- 2026-10-31: 2026-10-31: docs/language/sequencing-surface-design.md §3.5: layer 2 closes with R2 ([[binding-statements]]), which adds Option as a carrier (Option::bind/pure) and ? for Option. Implicit success wrapping stays unselected.
- 2026-11-01: Binding statements landed ([[binding-statements]]): `Option` is a carrier
  (`let x <- o;` exits with `None`), which covers the `gather` shape. `?` for
  `Option` is still open: the parser lowers `?` to `result::Result::and_then`
  before any type is known, so choosing `Option::and_then` is type-directed and
  belongs in the elaborator (docs/language/sequencing-surface-design.md §13 item 6).
