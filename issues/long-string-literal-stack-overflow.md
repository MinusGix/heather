---
title: A string literal of a few thousand characters overflows the native stack
status: open
labels: [elaborator,kernel,literals]
area: kernel
created: 2026-11-07
updated: 2026-11-07
---

A string literal of about 2,000 characters aborts `heather check` with a
native stack overflow instead of a refusal, and with a larger main stack the
same literal aborts a kernel worker at about 4,000. Found while assessing
[[self-hosted-lexer]]: a lexer evaluated by the kernel takes its input as a
literal, and most files under `lib/` are longer than that.

## Reproduction

```heather
import logic; import nat; import list; import char; import string;
theorem q(): String::len("aaaa…") = N { refl }   // N copies of `a`
```

At master `89ea8bb`, release build, `ulimit -v 8388608`:

- N = 1,600 checks; N = 2,000 aborts on the main thread (8 MiB stack).
- With `ulimit -s 1048576`, N = 4,000 and N = 16,000 elaborate, then abort in
  a `heather-kernel-N` worker (`NATIVE_STACK_BYTES`, 8 MiB).
- With `ulimit -s 1048576` and `HEATHER_KERNEL_WORKERS=1`, both check.

So both the elaborator's string-literal path (`elab_string_check` in
`crates/elab/src/literals.rs`, which elaborates the literal's
`String(chars := …)` intro) and the kernel recurse once per character. A
1,000-element bracket literal is covered by the depth guard of
[[nested-constructor-elaboration-stack-overflow]]; a string literal is not.

## Done when

A string literal of any length either checks or is refused with a located
diagnostic, at the default stack and worker count; never a process abort
([[kernel-native-depth-budget]]'s rule). A literal the size of a large
`lib/` file (tens of KB) checks in the time its length suggests.
