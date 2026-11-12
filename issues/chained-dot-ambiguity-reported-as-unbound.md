---
title: Report an ambiguous dot call's receiver, not an unbound outer name
status: open
labels: [elaborator,diagnostics]
area: language
created: 2026-11-09
updated: 2026-11-12
---

A dot call that is ambiguous between a member of the receiver's type and a
name in scope on its own is refused with a clear message:

```
import tactic;
record Bx { v: Bool }
fn Bx::pure(self b: Bx) → Bool { b.v }
fn f(b: Bx) → Bool { b.pure() }
// `pure` here is both `Bx::pure`, reached through the receiver's type, and a name in scope on its own …
```

But the same call as the receiver of a further dot call loses that message:

```
fn g(b: Bx) → Type { b.pure().IsTrue() }
// error: unbound name `IsTrue`
```

`member_head` (crates/elab/src/dispatch/member.rs) infers the outer
receiver with `elab_infer(cx, recv).ok()`, so the inner refusal is dropped
and the outer name falls through to "unbound". The inner error should lead,
as `application.rs` already arranges for an unbound name inside an argument.

Found 2026-11-09 when `import tactic;` in `native_compile_structured`
(needed then for any `by`) made `node.pure().IsTrue()` report `IsTrue`
unbound at four sites. `by` no longer needs `import tactic;` in the client
(the protocol is found through the import closure), so tactic clients do
not hit the collision, but the diagnostic stands for any imported short
name.

## Log

- 2026-11-12: A second way to meet it, with no ambiguity against a bare name (PR #551). `native_alloc.hthr` has `StructuredRegion::touches(self) → List<Nat>`; a second `StructuredRegion::touches(self, b: Nat) → Bool` was added in a module that `native_compile.hthr` also imports. Every use of the old one that was the receiver or an argument of a further call was reported as that outer name unbound, twelve errors and none of them naming `touches`:

      error: unbound name `guard`
          (layout.words_fit([exhausted, exit]) && loop_keeps(out, outputs, exhausted, Cons(count, parameters ++ body.touches()))).guard(

  and from there `code`, `emits` and `emit` unbound wherever a function whose body had failed was called. What the reader needed was one line: two modules in scope define `StructuredRegion::touches`. The defining module itself checked clean, since it does not import the other. So the same fix (the inner refusal leads) covers it, and a method defined twice for one type across imported modules wants its own message naming both.
