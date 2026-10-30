# Zeroization: proving an old value is gone, in a compiler we own

Status: **survey and design sketch**, 2026-10-30. Not scheduled: no current
milestone needs it. Owner: `issues/native-secret-erasure.md`.

Sources: Frank Denis, *Zeroization*, parts
[1](https://00f.net/2026/10/06/zeroization-1/) ("Wiping can make things
worse"), [2](https://00f.net/2026/10/06/zeroization-2/) ("Clearing the stack
and registers") and [3](https://00f.net/2026/10/06/zeroization-3/), all
6 October 2026. Background papers are in §8. Heather is referenced against
master at `f07adea`, and only lightly: the shape of the idea matters more
than today's compiler, which will change.

The question Minus asked: given that Heather owns its native compiler
(certificates, register allocator, frames), how could it support
zeroization soundly? And can it prove that *at some point the old value no
longer exists in any readable memory*?

---

## 0. The answer in brief

1. **"The value is gone" should be stated as non-interference at a cut, not
   as the absence of a byte pattern.** At a chosen program point, the whole
   observable machine state (every register, the flags, every byte of every
   region the program can read) must be a function of the public inputs and
   of what was deliberately released. Two runs that differ only in the
   secret must reach that point in *identical* states. This one statement
   covers registers, spill slots, dead frames, copies the compiler made,
   derived values such as `k ⊕ 0x5a`, and all-zero keys. A "no byte equals
   the key" statement covers none of these well (§3).

2. **A verified compiler can reduce that two-run property to a one-run
   invariant**, which is the design's main point. At each cut the compiler
   proves a *canonical state*: every location outside the declared live set
   holds a fixed constant (zero), so the target state is a *function* of the
   source's live words. Non-interference at the target then follows from
   non-interference of those few live words at the source, which is a
   small, ordinary fact about the source program (§4). The compiler does
   not need to know which values are secret. It wipes everything that is
   not live at the cut and *proves* that it did.

3. **Every failure in the three posts is a compiler whose correctness
   statement cannot see stale state.** Dead-store elimination, a wipe that
   clears the wrong copy, a spill created by the wipe call itself, a
   callee-saved register restored over the wipe: in each case the compiler
   is behaviour-correct, and the leftover copy is invisible to that notion of
   correctness. Heather's `native_compile_correct` (`SimProgram`: the
   machine produces exactly the source tree's traces) is blind in the same
   way. A compiler that leaves keys in every slot is still correct under it.
   So erasure is not something to add on top of the current theorem. It is a
   **strengthening of the compiler's theorem at cut points**, and every
   later pass (optimisations under `hih-passes` included) must prove the
   strengthened version. That is what stops a future pass from removing the
   wipe (§5).

4. **Heather already has the hardest piece of the posts' best mitigation.**
   Part 2's recommendation is a dedicated stack of known bounds, wiped
   whole on exit. Heather's programs already run in a `DataRegion` whose
   size the compile computes (`Layout::of`), with no foreign ABI, no
   unwinder and no hidden runtime. "How big is the stack" is a number the
   certificate already proves (§6).

5. **What no proof here can reach**, stated plainly: state outside the
   machine model (vector registers until the model has them,
   microarchitectural copies such as Zenbleed's physical registers and
   caches), copies the kernel makes (saved registers on syscall entry, pipe
   buffers, page cache, swap, core dumps), and argv as the kernel holds it.
   Each one becomes an explicit assumption or a released event, never a
   silent gap (§7).

---

## 1. What the posts show

**Part 1: wiping can make things worse.** On arm64 with Clang 21:

- A `memset` of a dead intermediate is removed by dead-store elimination,
  and the intermediate never reached memory anyway. It lived in `x8`.
- Volatile byte stores survive optimisation but clear stack slots the
  secret never visited. The secret stays in `x8`.
- An opaque wipe compiled in another file forces the caller to *create* a
  stack copy, so the callee has an address to clear. The register copy
  remains, and LTO can undo the opacity.
- In `compare_and_wipe`, the compiler postponed the comparison past the
  wipe call and kept the tag alive in a spill slot that nothing cleared.
  Without the wipe there was no stack copy at all. In the post's words,
  "Adding the wipe created the copy we left behind", and this is not a
  compiler bug, since C promises no such ordering.
- Registers matter: context switches save them, and core dumps, hibernation
  and VM snapshots record them. Zenbleed leaked them. A single SIMD register
  holds a whole key.

**Part 2: clearing the stack and registers.** Jasmin is the best answer, a
compiler that tracks secret-tagged values and wipes them before return.
For mainstream languages the post recommends a *boundary*, a function inside
which the secret is derived and used, and on whose exit the stack and
registers are cleared. Clang's `zero_call_used_regs` clears registers on
return but misses spills inside callees. GCC's `-fstrub` clears to a
watermark. A hand-written register wipe fails because the epilogue restores
callee-saved registers from a stack save, which undoes the wipe and leaves a
copy. Stack size is hard to compute (callees, spills, padding, the red zone,
recursion, variable frames). The robust option is a **dedicated stack**:
allocate it, run the boundary on it, switch back, and wipe all of it. That
works even around libraries that never wipe. Its costs are unwinders,
signals (`sigaltstack` saves register context elsewhere), and banned
non-local exits.

**Part 3: avoiding copies; WebAssembly.** Fused designs (compare the tag as
it is computed, never materialise it) avoid buffers instead of wiping them,
but nothing guarantees it. In Wasm the engine owns registers and the native
stack: Wasmtime and Wasmer compiled the code identically with and without
the zeroing `local.set`, spilled tags to native stack slots the module cannot
address, and left a caller's `x19` saved on the native stack. The
conclusion: "Zeroing memory using compiled languages and/or virtual machines
is pretty much impossible to do correctly." The advice that follows is to
inspect the generated code, because it, not the source, is the truth.

The common thread across all three posts is that the source language has no
notion of *where the value is*, so a wipe written in it can't refer to the
copies that matter. Every compiler is free to make more copies, because its
semantics doesn't observe them.

## 2. Why owning the compiler changes the problem

The posts treat the compiler as an adversary that has to be outwitted with
`volatile`, opacity, flags, or by switching stacks underneath it. When the
compiler is ours and its output comes with a proof, the question becomes
different: what theorem should the compiler prove, so that the
"generated code is the source of truth" check is done by the kernel
instead of by a person reading disassembly?

That theorem has to talk about the **whole machine state at a point**,
not about traces. Heather's current statement, `SimProgram(io,
src.denote(args), s)`, quantifies over what the machine *does* (the Linux
calls it makes and the answers it accepts). Leftover state is unobservable
to it until the program does something with it. That is exactly the
loophole every compiler in part 1 used, so a new kind of statement is
needed, one that `SimProgram` can't express.

## 3. Stating "the old value no longer exists"

### 3.1 Byte absence is the wrong statement

"No readable byte equals the key" fails in several ways:

- It is **unsatisfiable** for some keys. An all-zero key byte "exists" in
  every zeroed slot.
- It **misses derived values**. `seed[i] ^ 0x5a` from part 1, a key
  schedule, half a key in each of two registers, or a key shifted by one
  bit: none of these equals the key, and each one gives it away.
- It **depends on representation**. Byte-wise, word-wise, and across two
  registers are three different statements, and the attacker gets to choose.

Instrumented taint (each cell carries a label, and copies propagate it) is a
good *proof technique*, but a poor *statement*. Its meaning depends on
propagation rules that would themselves be trusted, and it gets implicit
flows wrong (a secret branch can write constants that still reveal the
branch).

### 3.2 Erasure as non-interference at a cut

Let `view(σ)` be everything an attacker could later read from machine
state `σ`. Take it to be the **whole architectural state** in the model:
`gprs`, `flags`, `rip` and every cell of `memory` (perms included). The
weaker variant "only cells readable by the process" is a projection of
this one, so it is better to prove the strong one and derive the others.

> **Erased at cut `c`.** For all initial states `σ₁, σ₂` that agree on
> everything except the secret inputs, and for any two runs that agree on
> every event released before `c` (the outputs the program was allowed to
> show: a ciphertext, a MAC verdict), if both runs reach `c` then
> `view(σ₁@c) = view(σ₂@c)`.

Equivalently, `view(σ@c)` is a function of the public inputs and the
released events. This is the shape of the classic information-erasure
definitions (§8): the secret *may* influence what was released, and *must
not* influence anything else that still exists.

Three properties make this the right statement:

- **Location-free.** The statement doesn't list registers, slots or
  copies. It quantifies over the whole state, so a copy the compiler made
  in a place nobody thought of is still covered. This is the one property
  the posts never manage to get from a source-level wipe.
- **Derived values and implicit flows are covered automatically.** If
  `k ⊕ 0x5a` survives, the two runs differ. If a secret branch leaves a
  different constant behind, they differ too. That includes `rip`, so the
  cut must be reached at the same address regardless of the secret (§4.3).
- **It only needs to be proved once, at the cut.** After `c`, the
  program's behaviour depends on the cut state and on later public inputs.
  The machine step is deterministic, so a cut erased at `c` stays erased at
  every later state, unless the program reads the secret again from
  outside (in which case it is a new secret input). One generic lemma,
  `erased_forward`, carries the guarantee to every later syscall, context
  switch or core dump.

It is a two-run (2-safety) property, and proving two-run properties directly
over x86 machine runs would be expensive. §4 avoids having to.

## 4. Reducing it to a one-run invariant the compiler proves

### 4.1 Canonical states

Let a cut carry a **keep set** `K`: the source words and buffers that
remain live across it (for MAC verification, the one-bit verdict). The
compiler proves, at the target state reached at the cut:

> **`Canonical(K, env, σ)`.** Every home of a word in `K` holds that word's
> value (as `native_compile_correct`'s matching relation already says).
> Every other register is zero, the flags are a fixed constant (say
> `clear_flags()`), `rip` is the cut's address, and every cell of the
> program's writable region outside `K`'s slots and buffers is zero.

Then two lemmas finish the job:

1. **`Canonical` is functional.** `Canonical(K, env, σ₁) ∧ Canonical(K,
   env', σ₂) ∧ env|K = env'|K → view(σ₁) = view(σ₂)` (given equal
   read-only regions, such as the program text, which do not depend on the
   input). This is a one-state fact and is cheap to prove.
2. **Source erasure.** `env|K` at the cut is a function of the public inputs
   and the released events. This is a fact about the source program, over
   `Env`, at the abstraction level where it is easy to state. For the MAC
   example it is close to trivial: `K` holds only the verdict, and the
   verdict is released by the exit status anyway.

Together: compiler canonical state + source erasure ⇒ target erasure. The
two-run argument happens only at the source, over a handful of words. The
x86 part is a one-run invariant of the same kind as the matching relation
the compiler already proves.

### 4.2 The compiler doesn't need to know what is secret

The reduction never mentions a secret label at the target. The compiler
wipes *everything not in `K`*. That costs more than wiping only secret
locations, but it is the reason the scheme is sound. A compiler that tries
to wipe "the locations the secret might be in" has to track every copy,
which is what failed in all three posts. Wiping everything that isn't live,
in a region of known size, cannot miss a copy, because there's no copy
whose location must be known.

Secret labels still help in two places, both of them outside the trusted
path:

- choosing **where** to cut and how small `K` can be (costs);
- proving **source erasure** (§4.1 lemma 2), perhaps one day by a security
  type system over `Source`, instead of by hand.

A cheaper scrub set is possible later, following the allocator's pattern
(`docs/native-register-allocation-design.md`: an untrusted proposer and a
trusted check). An untrusted analysis proposes "these slots were never
written since the last canonical point". The compile checks that claim by
evaluation and skips the wipe where it holds. The canonical invariant stays
the theorem, and the analysis only removes stores the check proves
redundant.

### 4.3 Control flow at the cut

`rip` is part of `view`, so the cut must be **one join point** reached
whatever the secret was. Loops whose trip count depends on the secret, or
branches that leave through different exits, are fine before the cut,
because canonicalisation erases their residue. They just have to converge
before it. Timing is a separate side channel. This design does not make
code constant-time. It is related work (§8, CompCert-CT), and could share
the source-level label machinery.

## 5. Why optimisations can't remove the wipe

In part 1, dead-store elimination deleted the `memset`, and it was right
to, under C's semantics. In Heather the scrub's stores are not dead,
because the compiler's theorem *requires* them: without them `Canonical`
fails, and so does the certificate. The register-allocation round already
removes "the stores of words that nothing reads afterwards"
(`docs/native-register-allocation-design.md` §1). That is a dead-store
elimination, and it stays sound because the scrub's obligation is part of
the theorem, not a statement in the source.

The general rule follows: **the compiler's correctness statement is
`SimProgram` plus `Canonical` at every declared cut**, and a pass that
transforms native code (`hih-passes`) proves preservation of both. This is
the Heather form of Besson, Dang and Jensen's observation (§8) that ordinary
semantic preservation does not preserve information-flow properties, and
that dead-store elimination and register allocation must be proved to
preserve them as well.

## 6. Where the copies live, one by one

| Location | In Heather's terms (lightly) | What the design does |
|---|---|---|
| General registers | `MachineState.gprs`: the home pool, RBX, call and leaf scratch | All registers outside `K`'s homes are zeroed at the cut (about 16 `xor`s). |
| Flags | `MachineState.flags`. A comparison against a secret leaves ZF/SF/CF behind | Set to a fixed constant by a last flag-writing instruction whose result the model fixes. Note that on real x86 `xor` leaves AF undefined, so the model's choice there must be checked. |
| `rip` | The address of the cut | One join point (§4.3). |
| Spill slots and homes in memory | Slots in the `Layout` region | Every slot not in `K` is zeroed. The canonical invariant covers slots of dead words the allocator stopped storing to. |
| Frames, return addresses, saved registers | `CallTo`/`Callee` frames on the stack region | Frames below the live part are zeroed whole. A return address is a code address and public, unless control flow was secret, which §4.3 excludes. Part 2's callee-saved restore problem doesn't arise: whatever a callee restores is its caller's live value, which is in the caller's `K` or wiped by the caller's own cut. |
| "How big is the stack" | `Layout::of(…).size() ≤ r.size`, proved per compile | The dedicated, bounded stack of part 2 is the default, not an add-on. The scrub writes over the known region, not up to a guessed watermark. |
| Buffers (I/O, data) | `Memory<Nat, C>` buffers inside the region | Ordinary non-`K` memory: zeroed unless kept. A kept buffer holding secret-derived bytes makes the source-erasure obligation fail, which is the correct outcome. |
| Copies sent out | Syscalls (`Invoke`, `Vis` events): `write` copies bytes into the kernel | A sent copy is a **released event** by definition. The tree states exactly what left the process, and erasure is stated relative to it. |
| Inputs | `read` into a buffer, argv on the initial stack | `read` is where a secret enters. Argv also lives in the kernel (`/proc/pid/cmdline`), so wiping the process copy is possible but only partial (§7). |
| Heap / allocator (future, `hih-memory`) | Not built yet | The allocator's state, free blocks included, is part of `view`. A moving `realloc` or a compacting collector leaves the old block, and `Canonical` sees that block as non-live and requires it zeroed. So *scrub-on-free* (or scrub-on-move) is forced by the invariant rather than being a convention. `munmap` returns pages to the kernel, which zeroes them before reuse: an assumption, see §7. |
| Vector registers | Not in the model | See §7. The model must grow them before a vector instruction is emitted, and then they join `view` with no other change. |

## 7. What the proof cannot reach

These are limits of *any* architectural proof. The design states them as
assumptions instead of leaving them as silent gaps.

- **Unmodelled architectural state.** `MachineState` is `{gprs, flags,
  rip, memory}`. The guarantee covers exactly that. It is sound for the rest
  only because the compiler emits no instruction that writes unmodelled
  state, and the decoder/semantics are the model's own (the native lane's
  existing trust base). Vector registers, x87 and segment bases enter `view`
  when the model gains them.
- **Microarchitectural state.** Physical register files (Zenbleed's leak),
  caches, store buffers, branch predictors. Zeroing `rax` does not clear the
  physical register that held its old value. No architectural model reaches
  this.
- **The kernel's copies.** On every syscall, the kernel saves user
  registers on its own stack. Pipe buffers, the page cache, swap,
  hibernation images and core dumps all keep copies. Stating erasure *at*
  the cut, plus `erased_forward`, means every state the kernel saves from
  then on is clean. Copies saved *before* the cut aren't covered, which
  argues for putting the cut before the next syscall. Swap and dumps can be
  addressed by modelling `mlock`/`madvise(MADV_DONTDUMP)` as Linux calls in
  the tree. Their effect on the kernel is an assumption.
- **Signals.** Heather programs install no handlers today. If they ever do,
  a signal frame is written on the stack region (inside `view`, so it is
  covered) or on an alternate stack (part 2's warning: that stack must be
  inside the region too, or the frame escapes the scrub).

## 8. Related work

- **Arranz Olmos, Barthe, Gonzalez, Grégoire, Laporte, Léchenet, Oliveira,
  Schwabe, *High-assurance zeroization*, TCHES 2024(1), 375–397**
  ([ePrint 2023/1713](https://eprint.iacr.org/2023/1713)). Jasmin extended
  to wipe stack and registers on return, with the compiler's correctness
  proof extended to cover it. Overhead is reported under 2% except for
  short-input symmetric routines. This is the closest prior work: a
  verified compiler that proves erasure. **Only its abstract was read**
  (the ePrint and TCHES PDFs refused this container). It is worth reading
  before an implementation round, to compare its exact theorem with §3.2
  and its stack strategy with §6. Minus could attach the PDF, as for earlier
  surveys.
- **Besson, Dang, Jensen, *Securing Compilation Against Memory Probing*,
  PLAS 2018**, and ***Information-Flow Preservation in Compiler
  Optimisations*, CSF 2019.** These define information-flow-preserving
  transformations against an attacker who probes memory, and show how to
  validate (and, where needed, repair) dead-store elimination and register
  allocation. They are the formal version of part 1, and the source of §5's
  rule. Read here at the abstract level only.
- **Information erasure as a language property**: Chong and Myers'
  language-based information erasure (CSFW 2005), and Hunt and Sands, *Just
  forget it* (ESOP 2008). These are the definitions §3.2's shape follows: a
  secret may affect released outputs and nothing else after the erasure
  point. Cited from memory, not re-read for this note.
- **Constant-time-preserving compilation** (CompCert-CT, Barthe et al.,
  POPL 2020; Jasmin's constant-time and Spectre checks). This is the
  adjacent property §4.3 sets aside. A later round could share a
  source-level label system with it.

## 9. If it is ever built: a sketch

Nothing here is needed by `hih-tools`. Roughly, the order would be:

1. **Statement only.** Define `view`, `Erased` (two-run, at a cut), and
   prove `erased_forward` and `Canonical` functional, over `MachineState`,
   in the native library. No compiler change. A hand-built canonical state
   tests the lemmas.
2. **One cut at program exit.** A program-level option that scrubs the
   region and registers before `exit`, with `native_compile_correct`
   strengthened to give `Canonical(∅, …)` there. Exit has no keep set and
   no successor state. It exercises the scrub emission and its proof alone.
3. **Cuts inside the program.** A source construct, such as
   `Stmt::Erasing(body, keep)`, denoting `body` unchanged in the tree (the
   construct has no source-level meaning beyond the cut). The compiler
   proves `Canonical(keep, …)` at its exit, and the surface offers a
   boundary block whose result words form `keep`.
4. **Source erasure by hand, then by labels.** A first program (constant-
   time MAC verify, or a key derivation) proves `env|K` public directly.
   A label/type discipline over `Source` comes later, perhaps shared with
   constant-time work.
5. **Cheaper scrubs.** An untrusted "untouched since last cut" analysis,
   checked by evaluation (§4.2), when the cost shows up in a real program.

Open decisions, to settle when the work becomes real:

- **Strong or process-only `view`.** Whole state (recommended: it implies
  the rest) versus process-readable cells only.
- **Where the scrub runs.** Inline at each cut (simple) or as one shared
  proved routine (smaller code, needs a call).
- **Release by event.** Is "released" exactly the `Vis` events before the
  cut (recommended, since the tree already lists them) or an explicit
  `declassify` source statement on top?
