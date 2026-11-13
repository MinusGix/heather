---
title: Two writes of one register are not the one write: make the register file canonical
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [nh-procedures]
created: 2026-11-11
updated: 2026-11-11
---

`Gprs` is a function from registers to words and `write_gpr` wraps it in
a λ, so `write_gpr(r, a, write_gpr(r, b, g))` and `write_gpr(r, a, g)`
agree at every register and are not convertible: there is no function
extensionality to make them one term. The program compiler's invariant
(`Target::Held`, `lib/native/native_compile_region.hthr`) is stated at a
register file, and most of its proofs move a claim across a block by
evaluation, so a block that writes one register twice leaves a file the
next lemma cannot name by the single write.

U5's step 5b met this in slot access: a word in the frame is reached by
`MovRI(Rbx, 8 * id)`, `AddRR(Rbx, Rsp)`, so RBX is written twice before
the word's load or store. The round named the result instead of
normalising it (`Target::slot_gprs`, `Target::rbx_gprs`,
`Target::rbx_known_gprs` in `lib/native/native_compile_segments.hthr`),
with a read lemma for every other register (`slot_gprs_other`,
`rbx_gprs_other`, `rbx_known_other`), a transfer of the claim
(`held_rbx`, `held_rbx_known`) and a case split for the sites that must
state a predicate of the file (`rbx_cases`, `rbx_known_cases`: the system
call sites in `native_compile_opens.hthr` and `native_compile_args.hthr`
wrap their proof in one). It works and it is a tax on every later rule
that touches a slot.

## Options

1. **A canonical file.** `Gprs` as a record of sixteen words, `write_gpr`
   replacing a field. Two writes of one register are then the one write
   by conversion, and so is a write commuted past another register's.
   Costs: `lib/std/arch/x86_64/x86_64.hthr` and every lemma that unfolds
   `Gprs` as a function (the read-after-write lemmas become `refl` per
   register); the function compiler's `File` already works this way for
   its own register file ("the register file as data", PR #548), which is
   the evidence that it pays.
2. **Claims up to pointwise equality.** State `Held` and the block rules
   over `Gprs` up to `(x) → read_gpr(x, g) = read_gpr(x, g2)`. No change
   to the machine model, a setoid argument at every rule.
3. **Remove the double write.** `[rsp + disp32]` slot forms
   ([[x86-stack-wide-displacement]]) make a slot access write no scratch
   register at all, which retires this instance and leaves the general
   problem for the next block that needs a scratch twice.

Option 3 is the cheapest and fixes the cost paid today; option 1 is the
one that stops it recurring, and [[gprs-read-write-methods]] would be
done in the same pass over the model.

## Done when

`rbx_gprs`, `rbx_known_gprs`, `slot_gprs` and their lemmas are gone from
`native_compile_segments.hthr`, and a slot access's effect on the
register file is stated by conversion.
