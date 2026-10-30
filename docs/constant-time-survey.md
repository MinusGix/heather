# Constant-time code: stating, proving and requiring it in a compiler we own

Status: **survey and design sketch**, 2026-10-30. Not scheduled: no current
milestone needs it. Owner: `issues/native-constant-time.md`. Companion to
`docs/zeroization-survey.md`, which frames secret erasure the same way
(§8 here says how the two fit together).

Sources: Thomas Pornin's BearSSL pages
[*Constant-Time Crypto*](https://www.bearssl.org/constanttime.html) and
[*Constant-Time Mul*](https://www.bearssl.org/ctmul.html), read in full;
the related work in §10, mostly at the level of abstracts and the papers'
own statements of their theorems (each entry says how far it was read).
Heather is referenced against master at `b5cb6fa`, and only lightly: the
shape of the idea matters more than today's compiler, which will change.

The question Minus asked: constant-time functions for cryptography and
security, as something Heather should be able to **prove** and to
**require**. Heather owns its native x86-64 compiler, and every compile
carries a kernel-checked certificate. What should the theorem say, where
does the proof burden sit, and what can no proof reach?

---

## 0. The answer in brief

1. **"Constant-time" is not a statement about time.** It is
   non-interference on a *leakage trace*. A leakage model says what each
   step reveals to a timing attacker: which instruction ran (control flow),
   which addresses were touched (cache), and the operands of instructions
   whose latency depends on them (division, and multiplication on some
   CPUs). Code is constant-time when two runs that differ only in the
   secrets produce the same leakage trace. BearSSL's definition ("execution
   time may vary, but not in a way that can be traced back to secret
   values") is this, phrased informally (§2.1).

2. **The leakage model is a contract with the CPU, and it should be a
   parameter, not a constant.** Control flow and addresses leak on every
   CPU with a cache and a branch predictor. Which instructions are
   variable-time depends on the CPU. BearSSL's multiplication table shows
   `mul` leaking on the 80486, the VIA Nano 2000, ARM7/9 and the
   Cortex-M3. Intel's DOIT list and Arm's DIT bit are vendors publishing
   such a contract. Heather should state constant-time *relative to a
   named contract*, with a conservative x86-64 default: everything on
   Intel's DOIT list is data-independent, and nothing else is, so `DIV`
   and `IDIV` leak their operands (§2.3).

3. **Every compiler problem on the BearSSL page is a compiler whose
   correctness theorem cannot see leakage.** GCC deleting a carry fix-up
   because signed overflow is undefined, Clang turning a mask back into a
   branch, `-Os` keeping a division by a constant that `-O2` would have
   turned into a multiply (KyberSlash): each of these is behaviour-correct.
   Heather's `native_compile_correct` (`SimProgram`) is blind in the same
   way. A compile that branches on a key is still correct under it. So,
   as with zeroization, constant-time is **a strengthening of the
   compiler's theorem**, which every later pass must also prove (§3).

4. **The compiler can reduce the two-run property to a one-run fact**,
   which is the design's main point, and the same move as the zeroization
   note's `Canonical`. The compiler proves, for each run, that **the
   target's leakage trace is a fixed function of the source's leakage
   trace**: `leak_x86(run) = T_P(leak_src(run))`, where `T_P` is computed
   from the program text alone. Then constant-time at the source
   (a two-run fact over a small, structured language) gives constant-time
   at the target, by one generic lemma. The compiler never needs to know
   what is secret (§4). This is Barthe, Grégoire and Laporte's *leakage
   transformer*, which Jasmin's compiler proof uses.

5. **The source obligation belongs to a checker proved once, over the deep
   embedding.** FunctionIR's `StructuredRegion` and the effectful `Stmt`
   are ordinary Heather data. A label checker over them ("no branch,
   loop condition, buffer index or variable-time operand is secret") is a
   Heather function with a soundness theorem proved once, and its verdict
   on a program is `= True` by `refl`. That is Vale's design (a verified
   taint analysis over a deep-embedded assembly), and it fits the "proved
   once, not per program" direction of the native work (§5). A surface
   `Secret` type, in the style of HACL*'s secret integers or CT-Wasm's
   `s32`/`s64`, can come later and elaborate into the checker's labels.

6. **Branch-free selection needs no new instruction.** Today's x86 subset
   (`MOV`, `ADD`, `SUB`, `AND`, `OR`, `XOR`, `CMP`, `TEST`, `SETcc`, loads
   and stores at fixed slots, `Jcc`, `CALL`/`RET`, `SYSCALL`) is all on
   Intel's DOIT list. A `Select` node lowered as
   `b ⊕ ((a ⊕ b) ∧ −m)` is constant-time with what the model already has.
   `CMOVcc` is on the list too, and is the faster lowering once modelled.
   Leakage problems arrive with `MUL`, `DIV`, shifts and bit scans (§6).

7. **Zeroization and constant-time share almost everything.** Both are
   two-run properties reduced to one-run compiler facts (a canonical state
   at a cut; a leakage transformer over the run). Both need the same
   source labels. Constant-time code satisfies zeroization's "one join
   point" premise automatically, and the scrub is constant-time because
   its addresses come from `Layout`. Jasmin argued that composition on
   paper. Here it would be a lemma (§8).

8. **What no architectural proof reaches**, stated plainly: speculation
   (Spectre), frequency scaling (Hertzbleed), data memory-dependent
   prefetchers that dereference *values* (GoFetch), power and EM, and any
   CPU that breaks its published contract. Each one is an assumption of
   the contract or a separate, later property, never a silent gap (§7).

---

## 1. What the BearSSL pages say

### 1.1 *Constant-Time Crypto*

**Definition.** Constant-time code "does not leak secret information
through timing". The run time may vary, but not in a way that can be
traced back to secrets. The page is careful that a constant-time TLS
library does not make a whole system timing-immune.

**What leaks**, as the page lists it:

- **Memory accesses.** The address of a table read leaks through the cache,
  including evictions observed later by another process. Some flash
  controllers add delays at block boundaries.
- **Conditional jumps.** Through branch prediction and through the
  addresses of the instructions fetched. A branch is only a problem when its
  condition is secret: AES-128's ten rounds are fine.
- **Integer division.** Hardware division is often microcoded with fast
  paths for small operands, and software division routines behave the same
  way. Even division by a power of two can be conditional code on signed
  types.
- **Shifts and rotations** on CPUs without a barrel shifter (the
  Pentium IV): the *count* leaks, the shifted data does not.
- **Multiplication** on some older CPUs (80486, ARM9). BearSSL assumes
  multiplication is constant-time on modern CPUs and says so explicitly.

**Compilers.** The C "as if" rule leaves timing outside the observable
behaviour, so the compiler may change it freely. The page shows GCC at a
high optimisation level deleting the offset additions of a carry
computation written with signed `int32_t`, because signed overflow is
undefined. The same freedom could turn constant-time code into
variable-time code with no test failing. The guidelines: avoid `_Bool`
(use 32-bit control words holding 0 or 1, so the compiler has no Boolean to
branch on), use unsigned types, and read the assembly.

**Techniques**, which are the vocabulary a Heather library would offer
(§5.5):

- *Control words* (0/1 in a full word) that enable or disable a
  computation, instead of an `if`.
- *Conditional copy* (`CCOPY`): the same memory accesses whether or not the
  copy happens.
- *Constant-time table lookup*: read every entry, keep one by conditional
  copy (the elliptic-curve 2-bit window reads 0, P, 2P, 3P).
- *Bitslicing* and multiplexer trees: replace table lookups by fixed
  Boolean circuits (AES via the Boyar–Peralta S-box, DES). The costs are
  register pressure, code size and serial modes.
- *Fixed-count operations*: always do the work and keep or discard the
  result by a control word (Montgomery reduction, square-and-*always*-
  multiply).
- *Announced lengths*: big-integer code runs on an "announced bit length",
  so only the modulus *length* drives control flow, never its value. Lengths
  are deliberately public. HMAC over a variable-length record
  (`br_hmac_outCT`, the Lucky Thirteen fix) runs the same instruction
  sequence for every length in a range.

**Primitives.** ChaCha20 and the SHA family are constant-time by
construction (additions, XORs, fixed rotations). AES and DES have both table
implementations (not constant-time) and bitsliced ones (the defaults).
GHASH and Poly1305 rely on multiplication being constant-time. CBC record
decryption is a seven-step constant-time procedure whose good/bad flag is
used only at the end.

### 1.2 *Constant-Time Mul*

The second page is a per-CPU table of whether multiplication is
constant-time, at the widths 32→32, 32→64, 64→64. Highlights:

- **x86-64 (Intel Core 2 onward, AMD K8 onward): constant-time** at all
  widths. **VIA Nano 2000: not.**
- **32-bit x86:** the 80386/80486 are not. MSVC's 64→64 helper returns
  early when the top words are zero or all ones, which the page says was
  exploited against a Curve25519 server.
- **ARM:** ARM7T/ARM9T are not. **Cortex-M3's `umull` takes 3–5 cycles**,
  short when an operand is small, zero or a power of two. GCC in Thumb mode
  calls `__aeabi_lmul`, which is not constant-time even for 32→64.
- **PowerPC 603/7xx/74xx: not.** POWER8/9: yes.

BearSSL's countermeasure is a *lowering*, not a source change. `MUL31`
under `BR_CT_MUL31` forces the top bit of each operand to 1 and subtracts
correction terms, so an early-exit multiplier never sees a short operand.
`MUL15` does the same with the top two bits. It is "noticeably slower", so
it is opt-in per platform. The page's caveat is the important one for this
note: a CPU could also shortcut on a power-of-two operand, and the Cortex-M3
does for 32→64. A countermeasure is only as good as the contract it was
designed against.

### 1.3 What the two pages add up to

Constant-time is a property of the **machine code on a particular CPU**.
It is stated in terms of a model of what that CPU leaks. The source
language has no notion of it, and the compiler is free to break it.
Everything below follows from taking those three facts seriously in a
compiler whose output comes with a proof.

## 2. The leakage model

### 2.1 The statement

Let a **leakage model** `L` map each machine step to an observation. A run
then produces a leakage trace `leak_L(run)`, interleaved with the run's
events (the Linux calls it makes and the answers it gets).

> **Constant-time under `L`.** For any two runs whose initial states agree
> on everything except the secret inputs, and which agree on every event
> released so far (the outputs the program was allowed to show), the
> leakage traces agree, prefix by prefix.

This is the standard 2-safety shape (Almeida et al., ct-verif; CompCert-CT;
Jasmin). Three choices are worth naming:

- **Prefix by prefix**, not "on terminated runs". Heather's programs are
  interactive interaction trees, possibly non-terminating, and a timing
  attacker watches a running process. Lockstep prefixes also make the
  property *termination-sensitive*: a secret-dependent infinite loop leaks.
- **Released events are the declassification.** As in the zeroization note
  (§3.2 there), the program may reveal what its tree says it outputs: the
  ciphertext, the MAC verdict, the exit status. ct-verif calls this
  "publicly observable outputs". An explicit `declassify` (CT-Wasm, FaCT)
  is an alternative, discussed in §11.
- **Leakage is not time.** Equal leakage traces mean equal timing only
  under the assumption that the CPU's timing is a function of what `L`
  observes. That assumption is the contract (§2.3). It is the honest place
  to put it, since no proof about instructions can establish it.

### 2.2 The three channels

At the x86 level, with Heather's `MachineState { gprs, flags, rip, memory }`:

| Channel | Observation per step | Why | What makes it public in practice |
|---|---|---|---|
| **Control flow** | `rip` (the instruction executed) | Branch predictor state, instruction cache, the number of instructions run | No branch or loop condition depends on a secret. Loop counts are public (AES's rounds, an announced length). |
| **Memory addresses** | The address of every load and store, instruction fetch included | Data cache and TLB, observable across processes | Slots and frames live at addresses fixed by `Layout`. Buffer indices are public. Tables are read by full scan. |
| **Variable-time operands** | For each instruction the contract lists as variable-time, the operands the contract names (a divisor, a shift count, a multiplier on a weak CPU) | Early-exit microcode, missing barrel shifters | Such instructions take only public operands, or are replaced by a fixed-time sequence. |

Two simplifications, both chosen in the conservative direction, in the same
spirit as the zeroization note taking the whole state as `view`:

- **Whole addresses, not cache lines.** A model that leaks only the line
  index is weaker and admits more code (scatter/gather within one line). It
  also depends on line size, prefetchers and bank conflicts (CacheBleed
  broke a line-granular assumption). Leaking the whole address implies the
  rest and is simpler to state.
- **Every `rip`, not only branch outcomes.** Leaking the program counter
  subsumes branch outcomes, call targets and loop trip counts. It is also
  what the zeroization cut already uses.

### 2.3 Instructions as a contract

Which instructions belong in the third row is a fact about the CPU, not the
ISA. The note proposes stating it as a **leakage contract**, a value of a
Heather type, passed to the theorem:

```
// sketch, not Heather as it stands
record LeakContract {
    // for each instruction, the operand values its latency may depend on
    varies: Instruction → MachineState → List<BitVec(64)>,
    // e.g. "DOITM set", "PSTATE.DIT = 1", "no frequency boost"
    assumes: List<Assumption>,
}
```

This is Guarnieri et al.'s *hardware–software contract* idea
(S&P 2021), applied to the non-speculative part. It makes BearSSL's
multiplication table a set of contract instances, and lets one compiled
program carry theorems for several of them.

**The x86-64 default should be Intel's DOIT list.** Intel publishes the
instructions whose latency does not depend on their data operands
("Data Operand Independent Timing"). Read for this note, the list includes
`MOV`, `MOVZX`/`MOVSX`, `ADD`/`ADC`/`ADCX`/`ADOX`, `SUB`, `AND`/`OR`/`XOR`/
`NOT`/`NEG`, `CMP`, `TEST`, `SETcc`, **`CMOVcc`**, `SHL`/`SHR`/`SAR`,
`ROL`/`ROR`, `SHLD`/`SHRD`, the BMI2 shifts, **`MUL`, `IMUL`, `MULX`**,
`LEA`, `BT*`, `BSWAP`, `PUSH`/`POP`. It does **not** include `DIV`, `IDIV`,
`BSF`, `BSR`, `LZCNT`, `TZCNT` or `POPCNT`. Three caveats travel with it:

- On recent Intel cores the guarantee holds only when the OS sets the
  DOITM control (an MSR, not something a user process can set). Older cores
  behave as if it were set. That is an `assumes` entry, exactly the kind of
  fact the contract exists to name.
- Intel's page itself says the list says nothing about power, thermal or
  frequency channels (§7).
- AArch64 has the analogue as an architectural bit (`PSTATE.DIT`,
  FEAT_DIT, required from Armv8.4, settable by user code), and RISC-V has
  the Zkt extension listing its data-independent-latency instructions.
  Neither matters until Heather targets them, but the contract type should
  not be x86-specific.

So the default contract is: **instructions on the DOIT list leak only
`rip` and their memory addresses; every other instruction also leaks all
its operands.** A weaker-CPU contract (VIA Nano 2000, or a future
Cortex-M3 target) moves `MUL` into the leaking set, and the BearSSL `MUL31`
trick becomes a lowering the compiler may choose under that contract (§6.1).

### 2.4 What the model is relative to

The guarantee is: *under contract C, the machine code is constant-time*.
It is exactly as good as C. BearSSL's power-of-two caveat (§1.2), DOITM,
Hertzbleed and GoFetch (§7) are all cases where a CPU's real behaviour falls
outside the contract someone assumed. That is not an argument against the
proof. It is an argument for writing the contract down where the theorem
can be read, instead of in a comment.

## 3. Why owning the compiler changes the problem

The BearSSL pages, and the more recent literature, treat the compiler as
an adversary to be outwitted:

- the signed-overflow carry deleted at high optimisation (BearSSL);
- *Breaking Bad* (Schneider et al., 2024) compiled crypto libraries across
  GCC and LLVM versions and flags and found compiler-introduced
  secret-dependent branches and accesses, including in code whose source
  had been verified constant-time;
- *Fun with flags* (Geimer and Maurice, 2025) traced most of those to a
  handful of optimisation passes and proposed turning them off by flag;
- KyberSlash (Bernstein et al., 2024): reference Kyber divided a secret by
  the public constant `q`. At `-O2` compilers turn that into a multiply and
  it is harmless; at `-Os` they keep the `DIV`, and it leaks;
- fiat-crypto adds a value barrier inside its `cmovznz`, so that Clang
  cannot see through the mask and reintroduce a branch;
- LLVM gained `__builtin_ct_select` / `llvm.ct.select.*` in 2025 (Trail of
  Bits), an intrinsic whose whole meaning is "do not optimise this into a
  branch".

Each of those compilers is **correct**. Timing is not part of C's
observable behaviour, so nothing in the compiler's correctness statement
forbids any of it. Heather's statement, `SimProgram(io, src.denote(args),
s)`, says the machine produces exactly the source tree's traces. It is
blind to leakage for the same reason: a compile that branched on every key
bit would still satisfy it.

When the compiler is ours and its output carries a proof, the question
becomes the one the zeroization note asked: what theorem should the
compiler prove, so that "read the assembly" is done by the kernel? The
answer has to mention leakage, and it has to be proved by **every** pass,
including the optimisations `hih-passes` will add. A future pass that
turns a `Select` into a branch then fails its certificate, the way a pass
that dropped a scrub fails `Canonical`.

## 4. Reducing it to a one-run fact the compiler proves

Proving 2-safety directly on x86 runs would mean relating two machine runs
step by step: a product of two `MachineState` executions, with every lemma
duplicated. That is expensive, and it is what the zeroization note
avoided too. The same trick works here.

### 4.1 Source leakage

The source languages are deep embeddings (`Stmt`, and FunctionIR's
`StructuredRegion` inside `Compute`). Their leakage is defined directly on
their syntax, under the same contract:

- a `Branch`, `Repeat`, `Conditional` or `Loop` leaks its condition bit;
- a buffer read or write leaks its index (not its value);
- an operation the contract lists as variable-time leaks its operands;
- a `Select`, arithmetic, comparisons producing a word, and fixed-slot word
  reads and writes leak nothing.

`leak_src(run)` is the sequence of those observations, interleaved with the
tree's events. It is short and structured, and two-run reasoning over it is
reasoning about a handful of condition bits and indices.

### 4.2 The leakage transformer

The compiler proves, per run:

> **`leak_x86(run) = T_P(leak_src(run))`**, prefix by prefix, where the
> function `T_P` is computed from the compiled program `P` (its layout,
> labels and lowering) and from nothing else.

`T_P` expands each source observation into the target observations of the
code that implements it: a condition bit becomes the `rip` sequence of the
taken arm; a buffer index becomes the address `base + offset(buf) + i`;
fixed-slot spills and reloads, frames and return addresses contribute
addresses that depend only on `Layout`. Then:

> **Lemma (transfer).** If `P` is constant-time at the source under C, then
> its compiled code is constant-time at x86 under C.
> *Proof:* equal source leakage, then apply `T_P` to both sides.

The lemma is generic and proved once. The per-compile work is a one-run
statement of the same kind as the matching relation `native_compile_correct`
already proves: it walks the same code, and only adds "and this is what the
step leaked". The compiler never sees a secret label.

### 4.3 Why this is the right tool here

There are two established ways to prove constant-time *preservation*:

- **CT-simulations** (Barthe, Grégoire, Laporte, CSF 2018; CompCert-CT,
  Barthe et al., POPL 2020). A pass comes with a two-run simulation: from
  two related source runs with equal leakage, the two target runs have
  equal leakage. This is general, and it handles passes whose leakage
  depends on more than the source leakage. Its cost is that every pass
  proves a relational diagram.
- **Leakage transformers** (Barthe, Grégoire, Laporte, Priya, *Structured
  leakage*, CCS 2021; used for Jasmin's compiler). A pass comes with a
  function from source leakage to target leakage. It is one-run, composes
  by function composition across passes, and fails exactly on passes that
  introduce leakage the source did not have (a branch on a value the
  source only computed).

Heather's compiler is a deterministic function whose output is checked by
evaluation, and its certificates are one-run simulations. The transformer
fits that shape and the CT-simulation does not. A pass that cannot produce
a transformer (an if-conversion that is only sometimes applied, say) is a
pass whose decision depends on something the source did not leak, which is
the bug the theorem exists to catch.

### 4.4 Why Heather's target makes `T_P` easy

Most of what makes constant-time preservation hard in a C compiler is
absent:

- **Addresses are a function of the program text.** Words live in slots and
  homes that `Layout::of` places; there is no `malloc`, no address
  arithmetic in the source, no ASLR-dependent layout inside the region
  (the load address is public, and the same in both runs). The register
  allocator's spills (`docs/native-register-allocation-design.md`) go to
  fixed slots, so they leak nothing new.
- **No undefined behaviour to exploit.** BearSSL's carry example works
  because signed overflow is undefined in C. FunctionIR's operations are
  total `BitVec(64)` functions, so there is nothing for a pass to assume
  away.
- **No foreign runtime.** No libc helper like MSVC's 64-bit multiply, no
  `__aeabi_lmul`, no unwinder. Every instruction in the binary was emitted
  by a compiler that proves things about it.

## 5. The source side: proving and requiring constant-time

### 5.1 A checker proved once, over the deep embedding

The transfer lemma needs "P is constant-time at the source". Proving that
per program by a relational argument is possible (the program logic could
grow a product construction), but it is the wrong default. The direction
of the native work is a compiler proved once, not per-program proofs, and
the same should hold here:

> **`ct_check(C, labels, P) : Bool`**, a Heather function over FunctionIR
> and `Stmt`, with **`ct_check_sound`**: `ct_check(C, labels, P) = True →
> ConstantTime(C, labels, P)` at the source. Proved once.

A program's verdict is then `ct_check(…) = True` by `refl`, the
`docs/proof-patterns.md` rule for closed verdicts. Requiring constant-time
becomes a premise in a theorem's statement, or a build option of
`write-elf` that refuses a program the checker rejects, naming the first
offending node.

This is the design of Vale's verified taint analysis (Fromherz et al.,
POPL 2019): an analysis over a deep-embedded assembly, written in the
prover, proved sound once, and run by evaluation on each procedure. CT-Wasm
does the same with a type checker whose soundness is mechanised in
Isabelle. Heather's version sits one level higher, over FunctionIR rather
than assembly, and the compiler's transformer carries it down.

### 5.2 The rules

FunctionIR is a good place for the checker because it already separates
control (`Conditional`, `Loop` in a `StructuredRegion`) from data (the
value DAG of nodes). Labels are `Public | Secret` per word, buffer and
input, propagated through the DAG (a node is secret if any input is):

| Construct | Rule |
|---|---|
| Arithmetic, logic, comparison to a word, `Select` | Any labels; the output is the join. |
| `Conditional`, `Loop`, `Branch`, `Repeat` | The condition must be public. |
| Buffer read or write | The index must be public. The value may be secret. |
| Variable-time instruction under C | Every operand the contract lists must be public. |
| `Invoke` (a Linux call) | The call's arguments are released. A secret argument is a declassification and must be allowed explicitly; data written is released by definition (§2.1). |
| `read` into a buffer | The buffer's label says whether what arrives is secret. |
| `Exit(status)` | The status is released. |

These are the rules of every constant-time type system (Jasmin's checker,
CT-Wasm, FaCT's checker), and they are what BearSSL's programmers impose on
themselves. The one Heather-specific point is that **a `Bool` the source
matches on is a branch**. BearSSL's advice to avoid `_Bool` has a direct
translation: a secret comparison should produce a word (a 1-bit `BitVec`
or a mask), consumed by `Select`, and never a `Bool` consumed by `match`.

### 5.3 Selection without branches

`Select(m, a, b)` is the one construct constant-time code needs that a
structured IR would otherwise express as a `Conditional`. Its lowering has
to be branch-free and visible to the theorem:

- With today's instructions: `mask = 0 − m` (`SUB` from a zeroed
  register), then `b ⊕ ((a ⊕ b) ∧ mask)`. All on the DOIT list.
- With `CMOVcc` in the model: `TEST m, m; CMOVNZ dst, a`. On the DOIT list,
  and shorter.

Either way the transformer maps a `Select` to a fixed `rip` sequence with
no data address, which is the whole point. The functional fact
(`select(m, a, b) = if m = 1 then a else b`) is ordinary.

An alternative, FaCT's, is to let source code branch on secrets and have
the compiler **if-convert** secret conditionals into selects automatically
(FaCT also eliminates early returns on secrets the same way). In Heather
that would be a pass with its own proof: it would have to produce the
transformer, which it can, since after conversion the leakage no longer
mentions the condition. It is a convenience to add later, once the checker
exists to say which conditionals need it.

### 5.4 The surface

Three increasingly ambitious options, not exclusive:

1. **Labels as an argument to the checker** (a list of secret inputs and
   buffers). Enough for a first constant-time program, and no surface
   change.
2. **A `Secret<W>` wrapper in the library**, in the style of HACL*'s
   secret integers and CT-Wasm's `s32`/`s64`: arithmetic, logic, `select`
   and `ct_eq` on it, but no `Bool`-valued comparison and no use as an
   index. The compile of a function over `Secret` words produces the labels
   for the checker. In HACL* the abstraction alone carries the guarantee,
   which rests on a metatheorem about F*'s module system that is not
   checked per program. Here the checker would still run, so the wrapper is
   ergonomics, not trust.
3. **A modality.** "This value may influence only these observations" is
   the shape of the Dependency Core Calculus and of information-flow modal
   types, and parametricity gives non-interference in some type theories.
   Whether a secrecy modality could sit beside DeLaM's layers is the
   question `issues/multimodal-modalities.md` already asks about other
   modalities. It is noted here as a link, not a proposal.

### 5.5 A library of BearSSL's techniques

Each technique in §1.1 becomes a Heather function with a functional
theorem, and is constant-time because the checker accepts its body:

- `ct_eq`, `ct_lt` returning masks; `ct_select`; `ct_is_zero`;
- `ccopy(m, dst, src, n)`: the same accesses whether or not it copies;
- `ct_lookup(table, i)`: a full scan, keeping entry `i` by `ccopy`;
- `ct_compare(a, b, n)`: the MAC verify, with a fixed length;
- `ct_rotate(buf, k, n)`: rotation by the bits of `k`
  (BearSSL's CBC MAC extraction), O(n log n), no division.

The first constant-time program worth building is the MAC comparison that
the zeroization note also picks as its first example (§9 there): it needs
`ct_compare`, has a one-bit released verdict, and exercises both theorems
at once.

### 5.6 What is allowed to be public

Constant-time code is not secret-free code. BearSSL's announced lengths,
AES's round count, a buffer's capacity and the length of a `read` are
deliberately public. In Heather, buffer capacities are part of the
`Source` value and are public by construction. Lengths that arrive from
Linux (`read`'s answer) are public unless a buffer is labelled otherwise.
The checker's labels should make this explicit, so "the HMAC length leaks"
is a visible label choice, not a surprise.

## 6. Variable-latency instructions

None of these is in Heather's x86 model today. They will arrive as
FunctionIR gains operations (`issues/std-nat-multiplication.md`,
`issues/nat-div-mod-lemma-kit.md` and the bitvector rounds are where
multiplication and division come from). The contract decides what each
costs.

### 6.1 Multiplication

Under the default x86-64 contract, `MUL`, `IMUL` and `MULX` are
data-independent (DOIT list; BearSSL's table agrees for every x86-64 core
except the VIA Nano 2000). So the default compiler can emit them on secrets
with no special lowering.

Under a weaker contract, the operands leak and the checker rejects a
secret product. Two answers, each the compiler's choice and each with a
transformer:

- **BearSSL's forced-top-bit lowering** (`MUL31`): set the top bit of each
  operand, multiply, subtract the correction terms. The multiplier then
  always sees full-width operands. Its correctness is a ring identity,
  which `ring` closes. Its constant-time-ness is relative to a contract
  that says "early exit only on short operands", which is exactly the
  assumption BearSSL's caveat warns about.
- **A software multiply** from shifts and adds over a fixed count, when
  the contract trusts nothing about `MUL`.

64×64→128 (`MUL` writing `RDX:RAX`, or `MULX`) is what big-integer and
field arithmetic want. It is on the DOIT list, and modelling it is the
same work as the other two-destination instructions.

### 6.2 Division

`DIV` and `IDIV` are not on the DOIT list and are variable-time on current
x86 cores: microcoded, with latency depending on operand magnitudes.
KyberSlash is the reminder that this is a practical attack, not a
theoretical one. So:

- **Division by a public constant** lowers to multiply-high and shift
  (Granlund–Montgomery). That is what GCC does at `-O2`, except here it is
  a lowering the compiler *must* choose when the dividend is secret,
  because the alternative fails the checker. Its correctness is a
  `Nat`/`BitVec` lemma per divisor, or one general theorem over the
  magic-number computation.
- **Division by a public variable** may use `DIV`: the operands are
  public, so the leak is harmless.
- **Division with a secret divisor** gets a fixed-iteration restoring
  division (64 rounds of shift, compare-to-mask, conditional subtract), or
  is rejected. BearSSL avoids division altogether for this reason.

### 6.3 Shifts, rotations, bit scans

Shifts and rotations by a register count are on the DOIT list, so under
the default contract a secret count is fine. The Pentium IV caveat would
live in that CPU's contract. `BSF`, `BSR`, `LZCNT`, `TZCNT` and `POPCNT`
are not on the list. A constant-time leading-zero count is a fixed
sequence of masked shifts, which the library can provide.

### 6.4 Floating point

CT-Wasm treats every float as public, because "most floating point
operations are variable-time" (subnormal operands are the classic case:
Andrysco et al., S&P 2015). Heather's float library
(`lib/std/num/float`) computes in integers, so compiled float code would be
integer code. Whether it is
constant-time depends on its normalisation (a leading-zero count, a loop
that shifts until the top bit is set), which is generally a secret-
dependent branch. Constant-time floats are not a goal. The checker would
reject float code on secret inputs, which is the correct outcome.

## 7. What the proof cannot reach

These are limits of any architectural leakage model. The design states
them as contract assumptions or as separate, later properties.

- **Speculation.** Under Spectre-PHT (v1) a mispredicted bounds check runs
  a secret-indexed load that architecturally never happens. Speculative
  constant-time (Cauligi et al., PLDI 2020) extends the leakage semantics
  with adversarial branch directions. Jasmin has a speculative
  constant-time type system with selective speculative load hardening
  primitives (Shivakumar et al., S&P 2023), and showed that the property
  is *not* preserved by ordinary compilation, GCC at `-O0` and `-O1`
  included, before proving a Jasmin-like compiler preserves it (Arranz
  Olmos et al., POPL 2025). Spectre-STL (v4) and Spectre-RSB need further
  rules. For Heather: a speculative semantics is a second machine model,
  and the transformer would be proved against it separately. Two
  observations make it less daunting than it sounds. The code Heather
  emits today has no indirect jumps, and each `RET` returns to the site of
  its own `CALL` (which narrows the BTB and RSB variants). And the
  zeroization note already records
  that a scrub loop needs a fence after it (§7 there), which is the same
  machinery.
- **Frequency and power.** Hertzbleed (Wang et al., USENIX Security 2022)
  turned data-dependent *power* into remote *timing* through dynamic
  frequency scaling, against code that was constant-time under every
  model above. Intel's DOIT page says outright that the list does not
  address this. It is outside any instruction-level contract.
- **Data memory-dependent prefetchers.** GoFetch (2024) showed Apple M-series
  prefetchers dereferencing *values* in memory that look like pointers, so
  secret data leaks through addresses the program never computed. Under
  such a CPU, the contract would have to leak the values of loads, and
  essentially no code is constant-time. The x86 contract must assume the
  absence of such a prefetcher, or that it is disabled. That assumption is
  an `assumes` entry.
- **The OS.** DOITM is set by the kernel, not by the process. A context
  switch, a page fault on a secret-dependent page (none exist here, by the
  address rule) or a co-resident process's cache use are outside the
  process's run.
- **Physical side channels** (EM, power analysis) need masking, which is
  a different discipline (BearSSL's other defence), and different
  theorems (probing security).

Empirical testing still has a place. dudect (Reparaz et al., 2017) runs a
binary on two input classes and tests the timing distributions. It cannot
prove anything, but it can catch a CPU that violates its contract, which
no proof can.

## 8. Composition with zeroization

The two notes describe two halves of one discipline.

| | Zeroization (`docs/zeroization-survey.md`) | Constant-time (this note) |
|---|---|---|
| What the attacker sees | The whole machine state at a cut (`view`) | The leakage trace over the run |
| Two-run statement | `view(σ₁@c) = view(σ₂@c)` | `leak(run₁) = leak(run₂)`, prefix by prefix |
| Released | `Vis` events before the cut | `Vis` events so far |
| One-run fact the compiler proves | `Canonical(K, env, entry, σ)` at each cut | `leak_x86 = T_P(leak_src)` |
| Generic lemma | `Canonical` is functional | the transfer lemma |
| Source obligation | The kept words `K` are public at the cut | `ct_check` accepts the program |
| Compiler knows secrets? | No | No |
| Later passes | Preserve `Canonical` | Produce a transformer |

Four consequences:

1. **One label system serves both.** The checker's labels already prove
   which words are public. The zeroization note's source obligation, "the
   kept words `K` are public at the cut", is a corollary: if `ct_check`
   labels every word of `K` public at the cut, the obligation holds. One
   analysis discharges both theorems, which is what both notes expected
   (zeroization §4.2, §8.2).
2. **Constant-time code meets zeroization's control-flow premise for
   free.** Zeroization requires the cut to be one join point reached at
   the same `rip` whatever the secret (§4.3 there). A constant-time region
   has no secret-dependent control flow, so every point in it qualifies.
3. **The scrub is constant-time.** It writes a region whose bounds come
   from `Layout`, with a public length. Its leakage is a function of the
   program text, so it extends `T_P` trivially. The TCHES 2024 Jasmin paper
   argues exactly this on paper (§4.6 there, "stack constant-time"). Here it
   would be a lemma about the scrub's transformer.
4. **The compiler theorem grows in one place.** `native_compile_correct`
   becomes `SimProgram` + `Canonical` at cuts + the leakage transformer,
   and each pass under `hih-passes` proves all three. Neither property is a
   bolt-on to the other.

## 9. Relation to other Heather work

- **Cost.** `issues/cost-aware-semantics.md` (calf) asks for cost as a
  provable property. Constant-time is *not* "cost independent of
  secrets": equal instruction counts with different addresses still leak.
  But the leakage trace is a refinement of a cost trace (count the `rip`
  observations), so a cost semantics built on Taus could share the
  instrumentation. calf's own non-interference runs the other way
  (behaviour cannot depend on cost).
- **Procedure contracts.** `issues/native-procedure-contracts.md` gives
  compiled procedures target contracts. A procedure that should be callable
  from constant-time code needs a leakage clause in its contract: its
  leakage is a function of its public arguments. That is a transformer
  restricted to one procedure, and it is how a separately compiled
  constant-time routine composes.
- **Register allocation.** The allocator's homes and spills go to fixed
  places, so it contributes nothing secret to leakage. Any future
  allocator whose decisions depend on values (none is planned) would have
  to say so in its transformer.
- **Machine model growth.** `CMOVcc`, `MUL`/`MULX`, `DIV`, shifts and
  vector registers each need their leakage line in the contract when they
  enter the model. Adding the line is part of adding the instruction.

## 10. Related work

Each entry says how far it was read.

**Foundations and attacks**

- Kocher, *Timing Attacks on Implementations of Diffie-Hellman, RSA, DSS,
  and Other Systems*, CRYPTO 1996; Brumley and Boneh, *Remote Timing
  Attacks Are Practical*, USENIX Security 2003. Background only, as cited
  by BearSSL.
- AlFardan and Paterson, *Lucky Thirteen*, S&P 2013. The CBC/HMAC padding
  timing attack BearSSL's `br_hmac_outCT` answers. Background only.
- Bernstein, Bhargavan, Bhasin et al., *KyberSlash*, IACR ePrint 2024/1049.
  Secret dividend divided by the public `q`; exposed when compilers keep
  the `DIV` (e.g. `-Os`). Read at the abstract and advisory level.
- Wang et al., *Hertzbleed*, USENIX Security 2022; Chen et al.,
  *GoFetch*, USENIX Security 2024 (Augury, S&P 2022, before it). Attacks
  on the contract itself (§7). Read at the summary level.
- Andrysco et al., *On Subnormal Floating Point and Abnormal Timing*,
  S&P 2015. Why floats are public in CT-Wasm. Background.

**Vendor contracts**

- Intel, *Data Operand Independent Timing Instructions* (the DOIT list),
  read for the scalar integer entries in §2.3; the DOITM control from
  Intel's guidance and the 2023 Linux discussion. Arm FEAT_DIT /
  `PSTATE.DIT` (Armv8.4). RISC-V Zkt. Read at the register-description
  level.

**Verification of constant-time code**

- Almeida, Barbosa, Barthe, Dupressoir, Emmi, *Verifying Constant-Time
  Implementations* (ct-verif), USENIX Security 2016. Reduces constant-time
  to safety of a product program over optimised LLVM IR, with a
  "publicly observable outputs" variant that is §2.1's released events.
  Read at the level of its definitions.
- Daniel, Bardin, Rezk, *Binsec/Rel*, S&P 2020; extended to secret erasure
  in ACM TOPS 2022 (cited in the zeroization note). Relational symbolic
  execution on binaries, so it checks what the compiler produced. Its
  studies found Clang-introduced violations and, at the time, fewer from
  GCC. Read at the abstract level.
- Watt, Renner, Popescu, Cauligi, Stefan, *CT-Wasm*, POPL 2019. Secret
  types `s32`/`s64` in Wasm; no branching on secrets and no secret memory
  indices; floats always public; `declassify` only in functions marked
  trusted. The leakage model leaks branch conditions, memory access
  patterns and the operands of division and remainder (§5.4 of the
  paper). Soundness mechanised in Isabelle, with a verified type checker.
  Read in part (the type system, leakage model and theorem statements).
- Cauligi et al., *FaCT: A DSL for Timing-Sensitive Computation*,
  PLDI 2019. Secret/public types, and a compiler that if-converts secret
  conditionals and early returns into constant-time code (§5.3). Read at
  the abstract level.
- Bond et al., *Vale*, USENIX Security 2017; Fromherz et al., *A Verified,
  Efficient Embedding of a Verifiable Assembly Language*, POPL 2019. A
  taint analysis for leakage freedom over deep-embedded assembly, verified
  in F* and run by evaluation: the model for §5.1. Read at the abstract
  level.
- Zinzindohoué, Bhargavan, Protzenko, Beurdouche, *HACL\**, CCS 2017, on
  Low* (Protzenko et al., ICFP 2017). Secret integers as an abstract type
  exposing only constant-time operations. "Secret independence" rests on
  typing and on the C compiler not breaking it. Background.
- Erbsen, Philipoom, Gross, Sloan, Chlipala, *Simple High-Level Code for
  Cryptographic Arithmetic* (fiat-crypto), S&P 2019. Generates
  straight-line field arithmetic, constant-time by construction. Its C
  output's value barrier is the C-world workaround §3 describes.
  Background.

**Constant-time-preserving compilation**

- Barthe, Grégoire, Laporte, *Secure Compilation of Side-Channel
  Countermeasures: The Case of Cryptographic "Constant-Time"*, CSF 2018.
  CT-simulations, and leakage transformers in their simplest form.
- Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, Trieu, *Formal
  Verification of a Constant-Time Preserving C Compiler* (CompCert-CT),
  POPL 2020. CompCert's passes proved to preserve constant-time, with
  leakage of branches and memory addresses. Read at the level of its
  theorem.
- Barthe, Grégoire, Laporte, Priya, *Structured Leakage and Applications
  to Cryptographic Constant-Time and Cost*, CCS 2021. Leakage transformers
  for the Jasmin compiler, in Coq; the same leakage also yields cost. The
  model for §4.2. Read at the abstract level.
- Arranz Olmos et al., *High-assurance zeroization*, TCHES 2024. Read in
  full for the zeroization note; its §4.6 argues the composition this note's
  §8 would prove.

**Speculation**

- Cauligi et al., *Constant-Time Foundations for the New Spectre Era*,
  PLDI 2020 (Pitchfork). Speculative constant-time.
- Guarnieri, Köpf, Reineke, Vila, *Hardware-Software Contracts for Secure
  Speculation*, S&P 2021. Leakage contracts between ISA and
  microarchitecture: the frame for §2.3.
- Shivakumar et al., *Typing High-Speed Cryptography against Spectre v1*,
  S&P 2023. Jasmin's speculative constant-time type system with selective
  SLH.
- Arranz Olmos, Barthe, Blatter, Grégoire, Laporte, *Preservation of
  Speculative Constant-Time by Compilation*, POPL 2025 (ePrint 2024/1203).
  Shows the property fails under GCC `-O0`/`-O1` and an earlier Jasmin,
  then proves a Jasmin-like compiler preserves it. Read at the abstract
  level.

**Compilers breaking constant-time**

- Schneider, Lain, Puddu, Dutly, Čapkun, *Breaking Bad: How Compilers
  Break Constant-Time Implementations*, arXiv 2410.13489 (2024).
- Geimer, Maurice, *Fun with flags: How Compilers Break and Fix
  Constant-Time Code*, arXiv 2507.06112 (2025).
- *Analyzing Compiler-induced Constant-time Violations* (CTGREP), IACR
  ePrint 2026/2653. Not read beyond its listing.
- Trail of Bits, *Introducing constant-time support for LLVM*, 2025:
  `__builtin_ct_select`, lowered to `CMOV`/`CSEL` or masks. Read at the
  blog level.

**Testing**

- Reparaz, Balasch, Verbauwhede, *Dude, is my code constant time?*,
  DATE 2017. Statistical timing tests; CT-Wasm used it for evaluation.

## 11. If it is ever built: a sketch

Nothing here is needed by `hih-tools`. Roughly, the order would be:

1. **Statement only.** Define `LeakContract`, the x86 leakage of one step
   under a contract, `ConstantTime` (two-run, prefix by prefix), and the
   default x86-64 contract from the DOIT list. Prove the transfer lemma
   for an abstract transformer. No compiler change.
2. **The transformer for today's compiler.** Prove that the current
   compile's leakage is `T_P` of a source leakage defined on `Stmt` and
   `StructuredRegion`. The instruction set is all on the DOIT list and
   addresses come from `Layout`, so this is mostly bookkeeping on proofs
   that already walk the code. It also shows whether today's compiler is
   leakage-preserving, which nothing currently checks.
3. **`Select` and the checker.** A FunctionIR `Select` node lowered by
   masks (or `CMOVcc` once modelled); `ct_check` and `ct_check_sound`;
   `write-elf` accepting labels and refusing a rejected program with the
   offending node named.
4. **A library and a first program.** `ct_eq`, `ct_select`, `ccopy`,
   `ct_lookup`, `ct_compare`; a constant-time MAC compare as the first
   program, shared with zeroization's first cut (§8).
5. **Variable-time instructions as they arrive.** `MUL`/`MULX` with their
   contract lines; division by a constant through multiply-high, forced
   when the dividend is secret; a fixed-iteration division routine.
6. **Later, separately.** A `Secret` surface type; FaCT-style if-conversion
   as a proved pass; a speculative semantics and SLH.

Open decisions, to settle when the work becomes real:

- **Contract granularity.** One conservative x86-64 contract (recommended:
  the DOIT list, with `DIV`/`IDIV`/bit scans leaking) versus per-CPU
  profiles from the start. Per-CPU profiles cost nothing in the theorem,
  since the contract is a parameter, but each one is a claim about hardware
  someone has to stand behind.
- **Declassification.** Released `Vis` events only (recommended, and the
  zeroization note's choice) versus an explicit `declassify` statement in
  `Stmt`. CT-Wasm and FaCT have the explicit form; the tree already lists
  what leaves the process, which makes the implicit form cheap.
- **Where the checker runs.** FunctionIR only (pure regions, where most
  crypto would live) versus FunctionIR and `Stmt` together (needed as soon
  as a secret arrives by `read`). The second is the honest scope; the first
  is a smaller start.
- **Address granularity.** Whole addresses (recommended, §2.2) versus cache
  lines. Lines admit scatter/gather tricks and tie the theorem to a cache
  geometry.
