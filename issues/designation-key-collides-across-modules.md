---
title: The designation table is keyed on the carrier head's written name, as the instance registry was
status: closed
labels: [traits,elaboration,modules]
created: 2026-08-17
updated: 2026-08-18
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

## Log

- 2026-08-18: Paid. The registration side was the one `carrier_key` call the issue predicted; the lookup side — the part it owned — turned out to be **four** sites, and the design question was not *how* to resolve but *from what*.

Three of the four hold a lowered operand's type, not a name: `resolve_op_name` rung 2 (both sources — the operand's carrier and the checking position's), `fill_index_from_designation`, and `value_slot_refusal`'s designation list. For those, resolving the *written* head at the use site would have been wrong, not merely slow: in a file importing two modules that each declare `List`, `key_of("List")` is ambiguous and answers nothing, about a type nothing at the use site is ambiguous about. So `type_namespace` grew a sibling, `carrier_of_ty`, which reads the declaration's own key (`qkey(ind.scope.module, ind.name)` — the string `inductives` is keyed by) straight off the lowered type, and returns it beside the written name as a `Carrier`. `Nat` answers for itself, which agrees with `carrier_key`'s fallback for the three names the language declares itself. The fourth site, `class_at_type`'s `Bool::Mon(+)` spelling, is a name the writer *did* spell, so it takes `carrier_key` in the scope they wrote it. No site could not resolve.

The written head did not become unnecessary — it became a separate field. `DesignationInfo.carrier` keeps it, because the two diagnostics that list the table (`nothing designates `++` at `Box``, and the row list beside it) quote something the reader can type; the key is now the registry's business only.

Acceptance is `crates/elab/tests/designation_resolved_key.rs` (6 tests): the collision pair registers and each use gets its own operation, pinned by `refl` against the qualified operation at neutral operands and at computing ones; a third `Box` declared where it is used is *not* covered by its namesake next door (the control without which the positive passes over a one-entry table); the genuine duplicate is still refused, qualifying carrier and occupant; and a duplicate at another module's carrier is refused too. `++` throughout, because it has no fallback name, so a lookup that misses cannot be quietly rescued by rung 3. Latent as filed — nothing in `lib/` moved.

One test fixture said the old rule out loud and was updated: `the_designation_declaration_refuses_by_name` asserted 'one entry per (symbol, carrier head)'. `docs/operators-onto-classes-design.md` §3.2 carries the amendment.
