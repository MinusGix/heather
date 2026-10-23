---
title: Make read_gpr/write_gpr methods on Gprs
status: open
labels: [x86,style]
area: heather-in-heather
created: 2026-10-21
updated: 2026-10-21
---

`read_gpr(register, gprs)` and `write_gpr(register, value, gprs)` are free
functions over `Gprs`. Following the method style the verified lowering
moved to (`Gpr::same`, `File::write`, PR #92), they should be methods on
`Gprs`: `gprs.read(register)` and `gprs.write(register, value)`, with
`read_gpr_after_write` and the other-register lemmas
(`read_gpr_after_other_write` in `x86_64_call_summary`) as `Gprs::`
theorems beside them.

## Scope

- **Heather, by hand:** roughly 680 uses across 36 files. Most of them are in
  `lib/std/arch/x86_64/` and the FunctionIR x86 modules.
- **Rust that writes Heather source:** the certificate generators in
  `crates/elab/src/function_ir_x86_lower*`, `crates/elab/src/function_ir_source/`
  (`structured*`, `loop_native.rs`) and `crates/cli/src/native/calls*` spell
  `read_gpr(…)`/`write_gpr(…)` in emitted text. The regenerated module
  `lib/native/function_ir/function_ir_x86.hthr` (`UPDATE_FUNCTION_IR_X86=1`) follows from that.
- **Timing:** B2 (`docs/native-program-logic-design.md` §3.2) burns most of
  the generator side and several of the modules, so doing it after B2 is
  much smaller. Doing it before B2 means editing code that is about to be
  deleted. The foundation that stays (`x86_64`, `x86_64_block`,
  `x86_64_data_read`, `x86_64_store`, the Linux model, `function_ir_lower`)
  is the part worth converting.

## Watch for

- The register-write proofs match on `register.same(query)` from
  `write_gpr`'s body (for example `File::represents_write`, `write_spares`,
  `read_gpr_after_other_write`). The method's body must keep that exact
  scrutinee, or those motives stop converting.
- A refactor like this should change no terms. Compare the counts with
  `scripts/timings --diff` on a whole-library run before and after.
