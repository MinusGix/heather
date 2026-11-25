---
title: The bytes level's system calls and exit lowered: the going and exited clauses of Site::Meets
status: open
labels: [native,x86,linux,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Item 7 of [[bytes-level-lowering]]: the world. The `Sys` node's step lemma for `read` and `write` (for every answer and resumption the Linux model allows; a failed read leaves its window undefined, which `Injected::undefined_change` absorbs), `Exit`, and the going and exited clauses of `Site::Meets` (`lib/std/arch/x86_64/x86_64_call_contract.hthr`). `EmitsBy` is a claim about machine steps (`Site::Moves`); a system call needs the claim form `Site::Performs`, so a region holding one is proved in that form, the regions without one lifted into it.

## Done when

`Site::Meets` in all three clauses for every routine of every program the lowering returns; the language's world probes (`echo_*`, `failed_read_undefines`, `exits`) compiled with their theorems.

## What it assumes from elsewhere

- **[[bytes-level-lowering-routines]]** owns the done clause. Assumed: it is proved for programs without system calls.
