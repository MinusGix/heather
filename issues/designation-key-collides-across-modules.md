---
title: The designation table is keyed on the carrier head's written name, as the instance registry was
status: open
labels: [traits,elaboration,modules]
created: 2026-08-17
updated: 2026-08-17
---

Filed as residue by the round that fixed [[instance-key-collides-across-modules]] (`docs/instance-resolved-key-design.md`).

That round's rule is *no component of a registry key is a spelling*. It was applied to the **instance** registry and deliberately not to the **designation** table beside it, which is keyed on `(symbol, carrier head written name)` (`docs/operators-onto-classes-design.md` §3.2, `Elaborator::designations`) and has the same latent collision for the same reason.

## The shape of it

`designation ++ at List<A> := append` keys `("++", "List")`. Two modules each declaring a `List` and each designating `++` at it is one entry, and the second is refused as a duplicate — the exact sentence [[instance-key-collides-across-modules]] reported, one table over.

It is **latent** rather than live: today's carriers whose heads collide across modules are the relations (`nat::Le`, `int::Le`, `bool::Le`), and those are designated at *type* carriers (`Nat`, `Int`, `Bool`) whose names do not collide. So nothing in `lib/` is blocked, and no row is stalled.

## The fix, and why it was not swept in

`Elaborator::carrier_key` already exists and is one call: `designations` would key on it exactly as `instances` now does, and `designated`/`designations_at` would resolve their argument the same way. The reason it was left is scope discipline rather than difficulty — the fixing round had a library win to collect and a lexer change to test, and a table with no failing customer is not evidence about anything.

The one design question this owes an answer to, and the reason it is a design issue and not a chore: a designation is looked up from an **operand's carrier**, i.e. from a lowered type's declaration name, and that lookup has to resolve to the same key the declaration registered. The instance side pays this in `value_slot_refusal` (one `carrier_key` call on a `type_namespace` result); the designation side has more lookup sites, and each is on the operator path.

## What it assumes from elsewhere

- **[[instance-key-collides-across-modules]]** owns the rule and the `carrier_key` helper. Assumed here: only that the helper exists and that the rule is stated as a rule.
- Nothing about `op_fallback` or the resolution rungs moves.

## Acceptance

Two modules declaring a type of the same name, each designating one symbol at its own, both register; a use at each carrier gets its own operation; a genuine duplicate (one module, one resolved carrier) is still refused naming both parties qualified.
