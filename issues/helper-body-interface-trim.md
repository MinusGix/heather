---
title: Helper bodies name every value in scope, so their arguments cannot be consumed in place
status: open
labels: [x86,codegen]
created: 2026-09-30
updated: 2026-09-30
---

The structured reflector gives a helper body an interface naming every value in scope (`inputs = outer + arguments`, `function_ir_source/structured.rs`, `produce`), whether the body reads it or not. Each region's certificate takes a placement fact for every interface input, so the selector must keep every named value in place ("live after" is the interface, docs/structured-lowering-code-size-design.md §3.1). Liveness by reads alone was tried and refused as `DuplicateRegister`.

The cost is a `mov` pair where a `times256` call hands over in `raise32`: seven `mov`s in each field word. Trimming a helper body's interface to the values it reads, in the reflector, would let the selector consume the argument in place. The trim must keep the source expansion and the crossings (`SourceValue::Call` arguments) agreeing.
