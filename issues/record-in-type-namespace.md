---
title: A record declared in a type's namespace, written t.Held(...)
status: closed
thread: Make compiler correctness proofs elegant
labels: [language,records,proofs]
area: language
created: 2026-11-18
updated: 2026-11-18
---

A record cannot be declared in a type's namespace. `record Target::Held(self t: Target, …) { … }` is refused by the parser ("`Target::Held` is a qualified name, which can only refer to something declared elsewhere"), so a claim about a `Target` that should be a record with named fields has two choices today, and both cost something.

1. A top-level record, written `Held(t, live, env, g, m)`. The name must be free across everything the module imports (`Held` and `Placed` are already records of `function_ir_lower` and `native_build`), and every use loses the method spelling `t.Held(live, env, g, m)`.
2. A top-level record under another name and a one-line method over it, which is what `lib/native/native_compile_region.hthr` and `native_compile_homes.hthr` do since 2026-11-18:

   ```
   record Hold(t: Target, live: List<Nat>, env: Env, g: Gprs, m: X86Memory(t.r.profile)) {
       words: List<Nat>,
       placed: t.Placed(env.with_words(words), m),
       agreeing: t.Agreeing(live, env, words, home_values(g)),
   }

   fn Target::Held(self t: Target, live: List<Nat>, env: Env, g: Gprs, m: X86Memory(t.r.profile)) → Type { Hold(t, live, env, g, m) }
   ```

   Uses keep `t.Held(…)` and read fields (`held.placed.keeps`), and a construction names the record (`Hold(words := …, placed := …, agreeing := …)`). The cost is two names for one claim (`Held`/`Hold`, `Placed`/`Placement`, `Agreeing`/`Agreement`, `Stacking`/`Activation`, `Landed`/`Landing`), and the parameter list written twice.

## Wanted

`record Target::Held(self t: Target, live: List<Nat>, …) { … }`: a record whose name lives in `Target`'s namespace, applied as `t.Held(…)` or `Target::Held(t, …)`, constructed as `Target::Held(words := …)` (or by the expected type alone), with fields read as today. Then the pairs above collapse to one declaration each, and the loop invariants that became top-level records in the same round (`CopyAt(t, …)`, `PathAt(t, …)`, `ArgAt(t, …)`) can go back to `t.CopyAt(…)`.

## Questions for the design

- `docs/language/modules-design.md` §4 says nothing is declared under a qualified name except functions and theorems on a type. A record there adds constructors and projections under a two-segment prefix (`Target::Held::words`); check what the name tables and the method lookup assume.
- Whether the same should hold for `inductive`/`enum` (`Target::State`), or only records, which are the case with a use.

## Exit

The five alias pairs in `native_compile_region.hthr`, `native_compile_homes.hthr` and `native_compile_calls.hthr` are each one record declaration, with no use site respelled.

## Resolution (2026-11-18)

Built: `record Target::Held(self t: Target, …)` parses (one qualifier; `self` on the first value parameter only), the owner is checked as at a `fn` member, the base name enters the member table off the inductive's name (live and on image replay, no format change), and `t.Held(…)` resolves to the record's *type* (`dispatch/member.rs`), never its constructor. Spellings and limits: `docs/language/surface-records.md` §1.3. Probes: `lib/_tests/lang/record_member_tests.hthr`. `inductive`/`enum` stay unqualified: nothing asked.
