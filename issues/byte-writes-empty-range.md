---
title: A store of no bytes changes nothing: the empty-range law of ByteWrites
status: open
labels: [x86,semantics,stdlib]
area: heather-in-heather
milestone: [hih-memory-model]
created: 2026-11-26
updated: 2026-11-26
---

A store of no bytes changes nothing and needs no room, and an empty range is always readable and writable. This is a law of memory, not of Linux and not of lending, and it belongs with `ByteWrites`' laws, proved for each instance. Found by the `Sys` read of [[bytes-level-lowering-world]] (item 3): the language reads zero bytes into a window at its block's end, as an empty slice at a list's end is allowed, and nothing in the library says what that store does.

## The law

For every memory `m` and address `a`:

- `writes.writable(m, a, 0)`
- `writes.store(m, a, Nil) = m`

## Where it goes

- `ByteWrites<M>` is declared in `lib/std/arch/x86_64/x86_64_store.hthr` (`writable: M → BitVec(64) → Nat → Type`, `store: M → BitVec(64) → List<BitVec(8)> → M`). The record carries no laws today.
- Its laws live in the records that hold one: `Stack<M>` (`x86_64_stack.hthr`: `writable`, `stored`, `kept`, `keeps_code`, … for stack words) and `Loan<M>` (`x86_64_memory_contract.hthr`: `writable`, `stored`, `apart`, `keeps`, `keeps_code` for a lent span's bytes). The empty-range law is neither a stack fact nor a lending fact. It is one law of the writes themselves, as a record of laws beside `ByteWrites` or a field of it.

## Instances, and who constructs each

- `X86Profile::writes` (`x86_64_byte_memory.hthr`): `writable` is `Memory::Allows(Perm::writes, a, k)` (`lib/std/machine/memory.hthr`: every `p < k` allowed, so vacuous at `k = 0`), and `store` is `set_span(a, bytes.to_vector())` (to be proved the identity at `Nil`). `DataRegion::stack` builds the `Stack` over it and `DataRegion::loan` the `Loan`. `Target::loan` (`lib/native/native_compile_function.hthr`) builds the native compiler's `Loan`.
- `linux_writes(io)` (`linux_x86_64_io.hthr`), `ByteWrites(io.writable, io.store)` from a `LinuxIo`. `Site::linux` builds that `LinuxIo` from a stack's writes, so it inherits whatever the stack's writes satisfy.
- `Stack::loan_none` and `Loan::sub` (`x86_64_memory_contract.hthr`) build `Loan`s from other ones; they construct no `ByteWrites`.
- Generated certificates: no `crates/linked/generated` file and no Rust source spells `ByteWrites`; the native certificates reach the instance through `Target::loan`/`DataRegion`. Re-check this when the law is added.

## What loses `k < size` at an empty range

- `Loan`: `writable`, `apart`, `keeps`, `keeps_code` and `stored` take `k < spans.size(b)`. At `bytes = Nil` each follows from the law with no bound (`stored` is vacuous).
- `Stack::wrote_in_store` (`k < size`).
- `Spans::Window` (call contract), whose `ReadCmd` case asks `k < spans.size(b)` for `Site::window_keeps_code`/`resumes_resident`.

## The probe that must become a theorem

One written block of size 0, a reference to `Loc(0, 0)` at `buf`, the word 0 at `len`, and `Sys(Read(fd, buf, len, result))`:

- In the language, `Heap::open` holds, the call `ReadCmd(fd, 0)` is made, and the world may answer `ReadBytes(Nil)` or `ReadFailed(e)`.
- On the machine, `LinuxBuffers` asks `writable(m, RSI, 0)` and `linux_read_return` stores `Nil` at RSI.

Today the lowering's read claim names this case as one hypothesis, `EmptyEnds(stack.writes, spans)` (`bytes_level_lower`: `EmptyAt` at `spans.byte(b, spans.size(b))` for every `b`). The law discharges it, and nothing else should. The same gap waits for a write of zero bytes and an empty typed copy.
