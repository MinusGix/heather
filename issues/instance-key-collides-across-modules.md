---
title: "Instance keys are the carrier head's surface name, so two modules' relations collide"
status: closed
labels: [traits,stdlib,modules]
created: 2026-08-17
updated: 2026-08-17
---

Filed by the `Int` round ([[std-int-encoding]]). It is the **one row of that
round's kit that could not be written**, so per [[std-api-waves]]'s doctrine it
was stalled rather than worked around, and `lib/std/num/int.hthr` carries a comment
where the instance would be.

`std/nat` registers the order's decision generically in both values
(`docs/value-generic-instances-design.md`):

```heather
instance(n, m: Nat) Decide<Le(n, m)> { dec := le_dec(n)(m) }
```

`std/int` declaring the same thing at its own order is refused:

```
`Le` already has an instance of `Decide` (`Le::Decide`), declared as
`Decide<Le(n, m)>`: at layer 1 the canonical name is keyed on the carrier's
*head* and the index spelling, so two carriers with the same head collide
```

The two `Le`s are different declarations in different modules — `nat::Le` and
`int::Le` — and nothing about them is ambiguous *to a reader* or to name
resolution, which qualifies by module (`docs/modules-design.md` §4). The registry
key is the head's **surface name**, so it cannot tell them apart.

## Why the workarounds are worse than the stall

- **Rename to `Le_int`.** This is what `std/bool` already pays (`Le_bool`,
  `le_bool_refl`, `le_bool_dec`), and it works — but it is exactly the encoding
  that erases the datum, and it costs the carrier its operator: `<=` at `Int`
  resolves through `designation <= at Int := Le` and reads the carrier off the
  operand, which is the mechanism that lets a downstream file write `x <= y` at
  both carriers. `bool`'s dodge predates that mechanism; reproducing it in 2026-08
  would be moving backwards.
- **Skip `Decide` and name the decider.** This is what the file does, and it is
  the same position `nat::eq_dec` is in for the neighbouring reason
  ([[decidable-equation-carrier]]): the decision is *available*, it is just not
  *found*. `Cmp<Int>` registers fine, because it is keyed on `Int`.

## The fix

Key an instance's canonical name on the carrier head's **resolved declaration**
(module-qualified) rather than on its spelling. `Le::Decide` becomes
`nat::Le::Decide` and `int::Le::Decide`, and nothing else about resolution moves:
a goal arrives with a resolved head already, since the goal's type was elaborated.

This is layer 1's key, so it is adjacent to but *not* the same as
[[decidable-equation-carrier]]'s layer-2 (class, carrier-syntax) key — that one is
about a carrier with *no* head to key on, this one about two heads with one name.
Both would be answered by a key that is a declaration reference.

## What it assumes from elsewhere

- **[[decidable-equation-carrier]]** owns the equation-carrier key. Assumed here:
  only that it is a *different* missing key, so neither issue subsumes the other.
- **[[std-int-encoding]]** owns the stalled row. Assumed here: only that the row
  is `Decide` at `int::Le` and that it is stalled, not worked around.

## Log

- 2026-08-17: Filed by the `Int` round as the round's only refused row. Ranked #3 of six, and it is the one that cost a *kit item* rather than proof lines.
- 2026-08-17: CLOSED by `docs/instance-resolved-key-design.md` (2026-08-17). The full round in one entry.

**The decision.** Identity by resolution, never by spelling. The registry key is `(class key, carrier-head key, index spelling)` with every component a RESOLVED declaration reference: `("logic::Decide", "int::Le", "")` and `("logic::Decide", "nat::Le", "")` are two instances that coexist. Duplicate semantics are unchanged — same resolved carrier twice is refused, and the refusal now module-qualifies the carrier, the class and the occupant.

The enabling step is worth recording because it is why this was cheap where `docs/traits-layer1-design.md` §7.1 thought it expensive: **a key never had to be spellable, only a name did.** §7.1 keyed on the head because a canonical name must be an identifier — true, and still true — but the key is a tuple in a HashMap no program writes down. Dropping spellability-as-a-key-constraint made the cheap form of §8's 'full canonical key' available with no layer-2 canonical-derivation table.

**Names did not move.** The canonical name is still `Le::Decide`, declared in the declaring module like any other declaration; the external face is `int::Le::Decide`. Nothing is minted, so `docs/repr-access-spellings-design.md`'s minted-name policy needed no extension — the round's brief expected to extend it, and there was nothing to extend (design §7.2). One thing did move: `InstanceInfo.global` is now module-qualified, because it is emitted as a `Var` at a use site that may see two `Le::Decide`s.

**The lexer joins a chain** (`if` → `while`), so `int::Le::Decide` is writable and 'printed paths are writable verbatim' is an invariant again rather than an invariant-with-a-carve-out. Boundaries checked and unmoved: `m::{a, b}` (a `::` before `{` never joined), `Impl(add, R)::member` (its `::` follows a `)` and never reaches the identifier scanner). Nothing relied on the one-join rule — `a::b::c` used to lex as `a::b` `::` `c` and the parser's postfix `::` arm needs an APPLIED owner, so it was a parse error everywhere.

**The library win, all three carriers.** `std/int` gets the stalled row (`instance(a, b: Int) Decide<Le(a, b)>`); `std/bool` drops the `Le_bool`/`le_bool_refl`/`le_bool_dec`/`leb_bool` suffixes for the real names and gains both the `Decide` instance and a `<=` designation; `std/algebra`'s two `Cmp` rows qualify (`nat::Le`, `bool::Le`). `x <= y` now means the right order at Nat, Int and Bool in one downstream file with nothing qualified.

Two corrections reality made. (1) The index component was ALREADY resolved — `index_spelling` has called `key_of` per argument since value indices — so only the head was infected; the round's rule ('no component of the key is a spelling') is what keeps that from drifting back. (2) The `<=` **designations were not optional**: `<=`'s fallback is the bare name `Le`, so with three modules declaring one, `lib/std/data/list.hthr` (which imports `nat` and `bool` and writes `len(filter(xs, p)) <= len(xs)`) had a symbol resolving to nothing. `nat` and `bool` grew the row `int` already had.

Fixture churn, and it is the whole cost of the rename: five test files write a bare `Le`/`le_dec`/`leb` in a probe that imports `nat` AND `bool`, and each now qualifies (`logic.rs`, `nat_order.rs`, `lib_std_list.rs`, `lib_algebra.rs` ×2). One of them is worth reading — `a_member_name_that_shadows_a_global_is_ambiguous_at_a_receiver` STARTED PASSING for the wrong reason: with `leb` ambiguous at the value it no longer resolves as a global at all, so the member/global collision the test exists for stopped happening and the snippet checked. The fixture moved to `sub`. That failure mode is invisible to a test that asserts only 'it was refused', and it was caught because this one asserts WHICH refusal. Separately, the trace-nesting test in `traits_resolution.rs` now expects a module-qualified candidate line — a deliberate reading of [[diagnostics-name-the-written-form]] and not an exception to it (a trace line is data about the registry, not a quotation of what the writer typed).

Suite 1854 → 1864 (8 in the new `instance_resolved_key.rs`, 2 in `lib_std_int.rs`), green; `scripts/bench --check` ok, 106 comparisons within thresholds, no flags.

Residue filed: [[designation-key-collides-across-modules]] — the designation table beside the registry has the same latent (symbol, written head) key, with no failing customer today. Cost note logged on [[decidable-equation-carrier]]: its new-key half is paid, and what remains is the NAME for a headless carrier plus UX.
