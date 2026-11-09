---
title: Report an ambiguous dot call's receiver, not an unbound outer name
status: open
labels: [elaborator,diagnostics]
area: language
created: 2026-11-09
updated: 2026-11-09
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
