# Zeroization: proving an old value is gone, in a compiler we own

Status: **survey and design sketch**, 2026-10-30. Not scheduled: no current
milestone needs it. Owner: `issues/native-secret-erasure.md`.

Sources: Frank Denis, *Zeroization*, parts
[1](https://00f.net/2026/10/06/zeroization-1/) ("Wiping can make things
worse"), [2](https://00f.net/2026/10/06/zeroization-2/) ("Clearing the stack
and registers") and [3](https://00f.net/2026/10/06/zeroization-3/), all
6 October 2026. The closest prior work, Arranz Olmos et al., *High-assurance
zeroization* (TCHES 2024), was read in full; §8.1 compares it with this
design. Other background papers are in §8.2. Heather is referenced against
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

6. **Jasmin has already done a version of this, and it supports the
   approach.** The TCHES 2024 paper wipes all the stack an exported
   function used, not just its secret parts, and machine-checks a one-run
   theorem: every target cell outside the source's valid memory either
   keeps its old value or is zero. The design here keeps that "keep or
   zero" form (§4.1). It goes further in three places. Registers and flags
   are inside the theorem. The step from canonical state to
   non-interference is proved rather than argued on paper. And the words
   the program keeps carry a source-level obligation (§8.1).

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

**Keep or zero.** Jasmin's theorem (§8.1) allows a cleared location
either to be zero *or to still hold the value it had when the boundary
began*. Heather should take that form too. Let `entry` be the target state
where the boundary began. Then:

> **`Canonical(K, env, entry, σ)`.** As above, except that every cell and
> register outside `K` is zero **or equal to its value in `entry`**.

This keeps the one-run shape, and wiping a location the boundary never
wrote becomes unnecessary. All the proof needs is a frame fact (the code
did not write there), which the compiler proves anyway. The price is one
premise: `entry` itself must be independent of the secret. That holds when
the secret is first derived or read *inside* the boundary, which is part
2's "derive the key inside the boundary" advice, made a hypothesis. It
also holds when the previous cut was canonical. The functional lemma then
reads: equal kept words and equal entry states give equal views.

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

Under the keep-or-zero form, a cheaper scrub set needs no change to the
theorem. It can follow the allocator's pattern
(`docs/native-register-allocation-design.md`: an untrusted proposer and a
trusted check). An untrusted analysis proposes "these slots are not
written inside the boundary". The compile checks that claim by evaluation,
and skips the wipe where it holds, because those slots satisfy the
"equal to entry" branch.

Jasmin reached the same decision for its own reasons (§8.1). Wiping only
secret data would mean deciding, for each stack address at function exit,
whether its last write was secret, which is complex and gains little. And
its Spectre-v1 protection already labels most data secret, so a secret-only
wipe would clear almost the whole stack anyway.

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
- **Speculation can skip the scrub.** Jasmin's authors note that a
  zeroization *loop* can be cut short under misspeculation. An attacker who
  trains the branch predictor gets an early abort (their reference SBB+22).
  Their answer is a fence after the loop, or an unrolled scrub. An
  architectural theorem cannot see this, so the choice of scrub shape
  belongs with any future speculative-constant-time work. Until then,
  prefer an unrolled scrub, or a loop followed by `lfence`.
- **Signals.** Heather programs install no handlers today. If they ever do,
  a signal frame is written on the stack region (inside `view`, so it is
  covered) or on an alternate stack (part 2's warning: that stack must be
  inside the region too, or the frame escapes the scrub).

## 8. Related work

### 8.1 *High-assurance zeroization* (Jasmin), read in full

Santiago Arranz Olmos, Gilles Barthe, Ruben Gonzalez, Benjamin Grégoire,
Vincent Laporte, Jean-Christophe Léchenet, Tiago Oliveira, Peter Schwabe,
TCHES 2024(1), 375–397, DOI 10.46586/tches.v2024.i1.375-397 (CC BY 4.0).
Section and figure numbers below are the paper's.

**Attacker.** The attacker acts when an `export` function (a library entry
point) returns, not when internal functions return. At that moment it
reads the registers, the flags, and the stack between `sp − n` and `sp`,
where `n` is the extra stack the compiler computed. Microarchitectural
attacks, swap and hibernation (left to `mlock`), and the caller's own
arguments are out of scope (§1).

**Failure modes (§2).** These are the posts' failure modes, measured on
eleven libraries (nine C/C++, ring and Dalek in Rust):
- no zeroization at all (BearSSL, ring);
- `memset` removed by dead-store elimination (TinyDTLS, NSS);
- zeroization only in API frames, which misses copies further down the call
  stack. libsodium's and OpenSSL's ChaCha20 leave the full key on the
  stack, and the authors built a key-recovery demo.
- source-level zeroization (`zeroize`, `clear_on_drop`), which can't see
  spills and callee-saved saves. ref10 X25519 declares 328 bytes of locals,
  but GCC reports 464 bytes of stack.

**Design (§4.2–4.4).**
- Wipe *all* the stack the export function and its callees used, not just
  the secret parts, and only at export exit. Per-function wiping was judged
  too costly.
- The stack bound comes from the Stack Allocation pass, propagated up an
  acyclic call graph, since Jasmin has no recursion. It is rounded up to
  the alignment and the clear step.
- The pass runs after Linearization, so after stack and register
  allocation.
- Two strategies: a loop, or unrolled stores, using `MOV`/`VMOV` with a
  clear step of 8 to 256 bits.
- Registers, flags and XMM can be cleared too. "No analysis is needed in
  this case."

**Theorem (§4.5, Figure 2).** Suppose the source function takes `σs` to
`σs'`, the target takes `σt` to `σt'`, and `σs ≡ σt`. Then:
- **Correctness:** `σs' ≡ σt'`.
- **Security:** `¬valid(σs, p) ⟹ σt'[p] = σt[p] ∨ σt'[p] = 0`.

In words, any memory the source did not consider valid either kept its
value from before the call, or is zero. The security property is proved
for the zeroization pass. It is shown preserved by the passes after it,
and the passes before it are shown not to write outside the stack region
the compiler predicted. All of this is machine-checked in Coq.

**What is argued, not checked (§4.6).**
- Composition with constant-time ("stack constant-time") is argued on
  paper. The zeroed region is statically determined, and zeroing the same
  part of two indistinguishable states keeps them indistinguishable.
  §4.6 says plainly that this is not machine-checked, and that compiler
  preservation of constant-time is proved only for an older Jasmin
  version.
- Validation (§5) fills the stack with PRF output and checks that it reads
  back zero. Register clearing was checked by inspecting the assembly.

**Cost (§5).** Overhead is mostly under 2%, and close to zero on large
inputs, since the scrub is a fixed cost. It peaks on short inputs to
symmetric routines: Poly1305 avx2 at 128 bytes is +32.6% with the loop
(about 56 cycles) and +7.0% unrolled. Clearing runs at roughly 32 bytes
per cycle.

**How it compares with this note.**

| | Jasmin (TCHES 2024) | This design |
|---|---|---|
| Statement | One-run, per cell: invalid memory is unchanged or zero | Two-run non-interference over the whole state (§3.2), reduced to a one-run keep-or-zero invariant (§4.1). |
| Registers, flags | Cleared on request, validated by reading the assembly; Figure 2 is about memory | Inside `Canonical` and inside `view`. |
| Step to non-interference | Argued on paper (§4.6) | The functional lemma, proved once (§4.1 lemma 1). |
| Live / valid data | The client's responsibility: valid source memory is not in the claim | Kept words `K` carry a source-erasure obligation (§4.1 lemma 2). |
| Where | Export-function exit | Any declared cut, with `erased_forward` for later states. |
| Stack bound | Acyclic call graph, no recursion | The region `Layout::of` proves per compile. |
| Secret labels | Not needed; everything used is wiped | Same (§4.2). |
| Speculation | Fence after the loop, or unrolled | Noted as a limit (§7). |

The paper supports the two main choices here: wipe everything used rather
than track secrets, and state a one-run, per-location property that a
compiler proof can carry. Heather's additions are the parts the paper
leaves to prose or to the client. It also gives Heather the keep-or-zero
form, which §4.1 now uses.

### 8.2 Other work

- **Besson, Dang, Jensen, *Securing Compilation Against Memory Probing*,
  PLAS 2018**, and ***Information-Flow Preservation in Compiler
  Optimisations*, CSF 2019.** These define information-flow-preserving
  transformations against an attacker who probes memory, and show how to
  validate (and, where needed, repair) dead-store elimination and register
  allocation. They are the formal version of part 1, and the source of §5's
  rule. Read here at the abstract level only.
- **Simon, Chisnall, Anderson, *What You Get is What You C*, EuroS&P
  2018** (the TCHES paper's SCA18). This proposed `__zero_on_return` for
  LLVM, with function-, stack- and call-graph-based variants (code at
  `lmrs2/zerostack`), and no unbounded recursion. It was never merged into
  mainline LLVM. Its call-graph variant is the one closest to Jasmin's
  design.
- **Yang, Johannesmeyer, Olesen, Lerner, Levchenko, *Dead Store
  Elimination (Still) Considered Harmful*, USENIX Security 2017.** This
  surveys scrubbing techniques and adds a scrub-safe DSE option to LLVM.
- **Daniel, Bardin, Rezk, *Binsec/Rel*, ACM TOPS 2022.** A relational
  symbolic binary analyser covering constant-time *and secret erasure*. It
  is a checker for binaries that come with no proof, and the nearest tool
  to the two-run statement of §3.2.
- **Chow, Pfaff, Garfinkel, Rosenblum, *Shredding your garbage*, USENIX
  Security 2005.** This gives the "data lifetime" vocabulary. The secure
  deallocation lifetime (first write to deallocation) is the TCHES
  attacker's model.
- **Information erasure as a language property**: Chong and Myers'
  language-based information erasure (CSFW 2005), and Hunt and Sands, *Just
  forget it* (ESOP 2008). These are the definitions §3.2's shape follows: a
  secret may affect released outputs and nothing else after the erasure
  point. Characterised as the TCHES paper's related work characterises
  them: Chong and Myers give a type system with declassification and
  erasure operators, and Hunt and Sands treat erasure as non-interference
  with a checking type system. Neither considers compilation. Not re-read
  for this note.
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
5. **Cheaper scrubs.** An untrusted "not written inside the boundary"
   analysis, checked by evaluation, which the keep-or-zero form admits with
   no change to the theorem (§4.2). Build it when the cost shows up in a
   real program. Jasmin's numbers say the wipe is a fixed cost, which
   matters only for short boundaries.

Open decisions, to settle when the work becomes real:

- **Strong or process-only `view`.** Whole state (recommended: it implies
  the rest) versus process-readable cells only.
- **Where the scrub runs.** Inline at each cut (simple) or as one shared
  proved routine (smaller code, needs a call).
- **Release by event.** Is "released" exactly the `Vis` events before the
  cut (recommended, since the tree already lists them) or an explicit
  `declassify` source statement on top?
