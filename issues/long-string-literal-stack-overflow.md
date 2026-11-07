---
title: A string literal of a few thousand characters overflows the native stack
status: closed
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

## Log

- 2026-11-07: Root cause: the literal's *term* was as deep as the literal was
  long. `check_vec_lit` built the characters' `[Char; n]` as a right-nested
  pair chain, and `collection_literal_spine` reduced the `List` conversion
  to a constructor spine of the same length; every syntax-directed walk then
  recursed once per element. `gdb` at N = 2,000 showed the kernel's typing
  (`tm_check_inner` ↔ `tm_infer_inner`, about four frames per character) on
  the main thread checking the statement, and at N = 16,000 with the body on
  a worker, `subst::map_term` under `Term::apply_global` in `check_decl`
  first — so the elaborator's own walks were in it too, not only the
  kernel's. Nothing about strings: any collection literal past a few
  thousand elements had it.

  Fix (kernel + elaborator): a new term `Term::VecItems{ℓ, T, items, from}`,
  the packed literal's construction for arbitrary elements — the chain as one
  array, one level deep at any length, with `term::vec_items_unfold` as its
  one-step view (crates/kernel/DESIGN.md, "A long vector literal is one
  node"). Typing checks `T` and each item in a loop; substitution, `bounds`,
  `syntax_eq`, the Merkle hash, the module image (tag 71, image magic bumped)
  and the emission walk loop over the live items; the evaluator and the
  projections go through the view, the quote boundary and the exporter write
  the chain. The elaborator emits it for a vector literal of more than 256
  elements and builds only a 64-element constructor spine over one; shorter
  literals elaborate exactly as before.

  Result, release build, default stack and workers: N = 2,000, 4,000, 16,000
  and 32,000 check (32,000 took 13.5 s at a 4 GiB stack before; 3.7 s now,
  most of it per-character elaboration); a 178 KB file's text (`creal.hthr`)
  elaborates as a `String` in about 9 s. `String::len(…) = N` by `refl` past
  about 100,000 characters is refused `OutOfFuel` with the declaration's span
  (the length computation's fuel, not depth); 1,000,000 characters is refused
  the same way, never aborted. Pinned by `crates/cli/tests/long_literals.rs`
  (16,000-character strings in a body, a statement and an inferred `let`;
  3,000-element lists of an open element and of a type parameter; a
  `[Nat; 3000]`; wrong-length negative controls) and the `VecItems` rows of
  `crates/kernel/tests/bitvec_values.rs` (its chain, its live window, open
  items and substitution, refusals, projections, the `box` boundary, a
  200,000-element node on a test thread's stack).

  Not fixed here, and filed: comparing two long vectors *by value*
  (`s() = "…"` with `s` a definition, or `"…" ++ "b" = "…b"`, at 3,000
  characters) meets the conversion's native depth budget and is refused
  `OutOfFuel` — a refusal where it used to be an abort, but a limit a lexer's
  token list will meet ([[long-vector-conversion-depth]]).

