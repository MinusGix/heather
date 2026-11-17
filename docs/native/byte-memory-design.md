# Byte memory with explicit access outcomes

The `hih-memory-model` milestone's first round
(`issues/byte-memory-access-model.md`): a library model of byte-addressed
memory that the native machine model, the program logic and FunctionIR's
state edges can all use. It is in `lib/std/machine/memory.hthr`, with vector reversal
in `lib/std/data/vector.hthr` and word packing in
`lib/std/bitvec/bitvec_bytes.hthr`. The showcase
`docs/showcase/memory_client.hthr` runs it and proves things with it. The
controls are in `crates/elab/tests/lib_std_memory.rs`.

The issue dates from before the program-logic redesign
(`docs/native/native-program-logic-design.md`), so this note also says where the
model sits in that design (§6).

## 1. Three layers

Each layer can be used without the next one.

| Layer | What it is | Its laws |
| --- | --- | --- |
| Address space `Space<A>` | `same: A → A → Bool` and `offset(a, i)`, the address `i` cells past `a` | `SpaceLaws`: `same` decides equality |
| Cells | `Memory::get`/`set`, and spans of `k` cells as `[C; k]` (`get_span`/`set_span`), total and policy-free | read-after-write, preservation elsewhere, the span forms, disjoint spans commute |
| Access | a `Perm` per address, and checked `read`/`fetch`/`write`/`read_span`/`write_span` returning `Result<_, Fault<A>>` | normal-path theorems turn a checked op into the cell op once the permission premise is met; refusal theorems state the exact `Err` |

A memory is a value:

```heather
record Memory<A, C> { space: Space<A>, cells: A → C, perms: A → Perm }
```

The stored cells and the access policy are separate fields, so a policy that
is left out can't turn into a guarantee by accident. No store changes
`space` or `perms`. Stores are built on the cells function alone
(`Space::put`/`put_from`), so `m.set_span(…).perms` *is* `m.perms` even at
an open span length. If the record were rebuilt step by step, its fields
would get stuck behind the recursion.

## 2. Addresses: where finiteness and wraparound live

Both belong to the space and not to memory. A span is always addressed by
absolute index from its base (`offset(a, 0)`, `offset(a, 1)`, …), so no law
about composing offsets is needed. The two premises a span theorem may need
are stated as hypotheses and proved separately for each space:

- `space.Distinct(a, k)`: the span does not overlap itself.
- `space.Apart(a, k, b, l)`: two spans share no address.

| Space | `offset` | Wraps? | Premises discharged by |
| --- | --- | --- | --- |
| `BitVec::space(n)` | `a.iterate_increment(i)` | modulo `2^n` | `space_distinct` (`a + k ≤ 2^n`), `space_apart`/`space_apart_above` (one span below the other, both below `2^n`) |
| `Nat::space()` | `a + i` | never | `space_distinct` (always), `space_apart` (`a + k ≤ b`) |

`BitVec::space(64).offset(a, i)` is x86's `next_rip(a, i)` by definition.
Both are `iterate_increment`, so an x86 address `i` bytes on needs no lemma
to be a span address. Only the non-wrapping `Distinct`/`Apart` lemmas are
proved. A span that wraps without overlapping itself (`k ≤ 2^n` from near the
top) is still distinct, but proving that needs modular injectivity, which
nothing needs yet. The controls exercise wrapping spans by evaluation.

**The recorded policy.** A span that wraps continues at address 0 (`span_wraps`
in the showcase). A span longer than its space overlaps itself. Its cells are
stored in index order, so the later index is the one left (`later_index_wins`),
and it doesn't read back (the negative control). Both follow from the
definitions. Neither is a fault, because a fault is the policy's to raise.
x86's canonical-address rule, for example, belongs in the x86 instance's
`perms`, not in the space.

`Space` is generic so that one buffer's index space `0..cap` is a space, not
only an address range. The effect-source design (S3, PR #117) treats each
`uniq Buf` as its own small memory (§6).

## 3. Cells

`C` is generic. A byte memory is `Memory<A, BitVec(8)>`. The generality costs
nothing, and it is the seam for Rust's abstract bytes, where a cell is
uninitialised or a byte with provenance (`rust-design`).

Stores are functions, so two memories can only be equal pointwise. Heather
has no function extensionality. `Agrees(m, n)` (same space, same permissions,
cells equal at every address) is that equality. `set_set_comm` and
`set_span_comm` (apart spans commute) are stated with it, and so is
`agrees_set_from` (stores respect it). The read laws need no such relation:

- `get_set_same`, `get_set_hit`, `get_set_other`: one store.
- `get_set_span` (under `Distinct`): a span reads back what was stored.
- `get_set_span_outside`: addresses outside a span keep their cells.
- `get_set_span_apart` (under `Apart`): a span apart from the one stored
  reads as before.

This is also why a single address can't instantiate `lib/std/machine/location.hthr`'s
`LocationLaws`. `get_put` there is an `=` between stores. The frame kit
(`issues/state-location-and-frame-kit.md`) owns how partial or pointwise
locations meet total lenses. This model supplies memory's own disjointness
facts (`Apart`, `Distinct`) for it.

## 4. Access and outcomes

```heather
record Perm { read: Bool, write: Bool, execute: Bool }
inductive Fault<A> { ReadFault(address: A), WriteFault(address: A), ExecuteFault(address: A) }
```

The policy is a decidable `Bool` per address and access, so outcomes compute.
A literal memory evaluates to its `Ok` or `Err`, and the showcase checks
these by `refl`.

- **Single accesses.** `read`, `fetch` and `write` check the address's bit.
  A refused `write` is `Err(WriteFault(a))`, and there is no memory after it.
  The type rules out stating anything about an "updated store after a
  rejected write".
- **Spans.** `read_span` and `write_span` check every address first
  (`Memory::refused`, the first refused address in index order) and then
  touch the cells. A refused span stores nothing, wherever the refusal falls,
  and reports its first refused address. `refused_some` makes that exact
  (`FirstRefused`): the address is in the span, its bit is clear, and every
  earlier address has its bit set. A machine whose stores fault part way
  through would be modelled as a sequence of single writes, not as one span.
- **Normal path.** `read_allowed`/`write_allowed`/`fetch_allowed` take the
  bit. `read_span_allowed`/`write_span_allowed` take `m.Allows(bit, a, k)`,
  the bit at each of the span's addresses. Each one rewrites the checked
  operation to `Ok` of the cell operation, so arithmetic proofs work on
  `get`/`set` alone.
- **Buffers.** `Memory::buffer(cap, fill)` is a memory over `Nat` that can be
  read and written below `cap` and nothing else (`Perm::below(cap)`).
  `buffer_reads`/`buffer_writes` discharge `Allows` for any span
  `a + k ≤ cap` at once, for every buffer value of that shape (stores keep
  it). That way a region whose indices are bounded below `cap` discharges
  its accesses together rather than one by one, as S3 asked.

## 5. Words and endianness

Endianness is a packing choice, never a property of memory. A `k`-byte word is
a `BitVec(8 * k)` and its bytes are a `[BitVec(8); k]`, so both round trips
are stated without a cast. `8 * Succ(k)` reduces to `8 * k + 8`, which is
`concat`'s index for one low byte below `k` more.

- `BitVec::bytes_le`/`of_bytes_le` put the low byte first. The round trips
  are `of_bytes_le_bytes_le` and `bytes_le_of_bytes_le`.
- `BitVec::bytes_be`/`of_bytes_be` are the little-endian forms read through
  `reverse` (`lib/std/data/vector.hthr`). Their round trips come from
  `reverse_reverse`.
- `Memory::get_le`/`set_le`/`read_le`/`write_le`, and the `_be` forms, are
  the span operations through a packing. `read_write_le` is the whole normal
  path: if the span is readable, writable and distinct, a written word reads
  back as `Ok(w)`.

## 6. Where it sits in the native design

- **FunctionIR state edges.** A memory is a plain value, so a load node is
  `m ↦ m.read(a)` and a store node is `m ↦ m.write(a, c)`, both pure. S3
  (`docs/native/native-effect-source-design.md` §6, PR #117) keeps this outcome
  shape. FunctionIR's eval of a region returns the `Result`, and the
  layer's `Pure` leaf turns an `Err` into a process-end outcome (`Faulted`)
  distinct from `Exited(status)`. The memory model does not depend on
  `itree`, and a fault is not encoded as an exit code. Its machine side, a
  trap or signal, belongs to `linux-syscall-trace-model`.
- **The machine model.** x86's access records (`FetchAccess<M>`,
  `ByteReadAccess<M>`, `ByteWrites<M>`, `LinuxIo<M>`) are instantiated from
  this model (`lib/std/arch/x86_64/x86_64_byte_memory.hthr`,
  `lib/std/os/linux/linux_x86_64_byte_memory.hthr`;
  `issues/memory-model-machine-instances.md`). The machine's `M` is
  `X86Memory(x)`: cells, permissions, and a proof that the permissions are
  what the run relies on, which the profile `x` (`X86Profile { relies }`)
  names. `x.at(m)` is the model's `Memory`, over `BitVec::space(64)`.
  `Stack<M>` states its laws for every `M`, and over bare `Memory` values a
  memory with no permissions would be one of them, where `writable` is
  false. A memory of the profile cannot be one. A store keeps the
  permissions, so it keeps the proof unchanged. A step that changes
  permissions (allocation, mmap, mprotect; §7) builds a new memory and proves
  the reliance again, for the regions the run relies on and nothing else.
  Reads go through `read` as an `Option`, an address
  is executable by its execute bit, `writable` is `Allows(Perm::writes, …)`
  and `store` is `set_span` of the list's vector (`List::to_vector`). The
  canonical-address rule is in the permissions: at or above `2^47` an address
  has none, whatever the memory's permissions say. `DataRegion::stack` builds the
  `Stack<M>` of #106 from `size` bytes below `2^47` that the profile relies
  on having the data permission:
  `stored` from `get_set_span_list`, `apart` from `get_set_span_outside` and
  `BitVec::space_apart`/`space_apart_above`, and `keeps_code` because the
  region never executes, so no code byte is in a stored span. No span wraps
  inside a canonical region, so the wrapping form of `Distinct` was not
  needed.
- **Views and footprints.** The `View` interface carries `Holds(v, m)`.
  `DataRegion::buffer_view` (§6.1's third view) knows a buffer's cells `v`:
  `Holds(v, cells)` says the region's cells are those of `DataRegion::buffer(v)`
  (`Memory::buffer`'s shape) index by index, so the region's `get_span` is
  the buffer's (`holds_span`). A load reads the buffer at the index the
  caller names, a store (the program's, or Linux's read answer) goes in at
  an index and the view knows the buffer with `set_span` there, and a call
  is asked of every memory holding the buffer. `buffer_view_sound` proves it
  against the profile's `LinuxIo`. A separation-style footprint is `Apart`
  between ranges, which round 1 supplies.
- **The process image.** The Linux process the I/O profile's ELF makes is a
  memory of the profile `X86Profile::io()` (`lib/std/os/linux/linux_x86_64_image.hthr`;
  `issues/io-image-on-byte-model.md`). The profile relies on the page
  (0x410000) and the frame (0x411000) having the data permission and on
  nothing else, so both are `DataRegion`s of it. The loader
  `X86Memory::io_load(file)` maps the file's bytes at 0x400000 with
  `Perm::code()` (read and execute), the RW segment zero-filled, and nothing
  else. The code is deliberately not part of the profile: a run needs it
  resident, and residency is a fact about cells, which every store would
  have to re-prove if the memory carried it. It is in the view instead:
  `View::with_code` adds `CodeResident` to a view's `Holds`, and
  `X86Profile::with_code_sound` keeps it across any store that lands on
  non-executable memory (`store_keeps_code`), which a data region's stores
  always do. `DataRegion::program_view` is the buffer view with the code.
  The loader proves the code resident at the entry
  (`X86Memory::io_load_entry`) and the page and frame zero, so a program's
  theorem from its loop head becomes one from the loaded process
  (`drain_entry` in the Wp controls). A word kept in a region (the old
  frame's slots) is a lemma over the buffer (`DataRegion::x86_word_stored`),
  not a view of its own; a view over two regions at once is
  `issues/wp-view-separating-product.md`.
- **The process's stack.** A process as the ELF theorem takes it by default
  is a memory of `X86Profile::process(size, top, depth)`: what
  `X86Profile::io(size)` relies on (the segment, since
  `issues/native-data-capacity.md`) and `depth` bytes below the entry RSP
  `top` data (`issues/io-image-process-stack.md`). `StackPlaced` is where
  Linux puts it. That the `depth` bytes are data is a premise about the
  system (`LinuxStart`'s `stack`): Linux maps the stack as it is touched,
  down to RLIMIT_STACK, so it holds when the stack limit leaves `depth`
  bytes below the entry RSP (`issues/io-stack-below-rsp-not-mapped.md`).
  `DataRegion::process_stack` is a `DataRegion`, so `DataRegion::stack` is a
  `Stack` of the process from its entry, top at RSP; its stores keep the
  segment (`process_stack_keeps_data`). The loader with the stack
  (`X86Memory::process_load`) is `LoadedFrom` the file, which keeps the ELF
  theorem's premises satisfiable.
- **The program's own stack** (`write-elf --stack segment`). The process is
  a memory of `X86Profile::io(size)`, relying on the segment alone, and the
  stack is the `room` bytes after the `used` bytes of the layout
  (`DataRegion::own_data` and `DataRegion::own_stack`, two regions of the
  one profile). It rests on the file's `PT_LOAD` header and asks nothing of
  the stack limit; its size is fixed when the file is written
  (`docs/native/system-contract-design.md` §4.2).

## 7. Outside v1, and the seam for each

| Left out | Seam |
| --- | --- |
| Paging and page tables | `perms` is any function. A page-table walk computes it, and a remap replaces it. Cells are untouched. |
| Privilege levels | A `Perm` per mode, by choosing `perms` per mode (or a `Perm` record per privilege). The checked operations don't change. |
| Alignment faults | An architecture check before the access. If it needs its own outcome, it becomes another `Fault` constructor. Spans are not aligned by the model. |
| Atomics and memory ordering | Not representable: this is a sequential model of one memory value. A concurrent model would relate several of these. |
| Devices and MMIO | An address the architecture routes before memory (or marks refused in `perms`). Cells are plain storage. |
| Allocation | Changes `perms` (and `cells`) between program steps. Bounds and metering are `memory-bound-certificates`'s (`hih-alloc-metering`). |
| Uninitialised bytes and provenance | The cell type `C`. |
