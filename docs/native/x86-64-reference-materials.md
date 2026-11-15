# x86-64 reference material and model boundary

Status: **reference and direction note, pre-design** (2026-08-25).

This note records the local research cache assembled before Heather's x86-64
backend design and the boundary at which that material may influence Heather.
It is not an ISA specification.  The eventual Heather model must state its own
rules and cite the normative source and cross-checks for each rule.

## 1. Local cache

Downloaded artifacts and third-party checkouts live under
`.references/x86_64/`.  The whole `.references/` tree is gitignored: manuals,
papers, third-party code, and their licences are not Heather source and must not
silently enter Heather's distribution or licence surface.

The cache assembled on 2026-08-25 contains:

| Local path | Upstream/version | Role | Licence boundary |
|---|---|---|---|
| `manuals/intel-sdm-combined-092.pdf` | [Intel SDM combined volumes](https://cdrdv2.intel.com/v1/dl/getContent/671200), revision 092, June 2026 | Normative Intel architecture reference | Copyrighted specification.  Cite and independently restate facts; do not copy its prose or tables. |
| `manuals/intel-sdm-documentation-changes-092.pdf` | [Intel SDM documentation changes](https://cdrdv2.intel.com/v1/dl/getContent/671294), revision 092 | Errata/change trail; particularly useful when two models disagree | Same boundary as the SDM. |
| `manuals/amd64-apm-volumes-1-5-4.10.pdf` | [AMD64 APM combined volumes](https://docs.amd.com/v/u/en-US/40332_4.10_APM_Vol1-5), revision 4.10, July 2026 | Normative AMD64 architecture reference | Copyrighted specification marked AMD Public Use.  Cite and independently restate facts; do not copy its prose or tables. |
| `papers/k-x86-64-semantics-pldi2019.pdf` | [Dasgupta et al., PLDI 2019](https://fsl.cs.illinois.edu/publications/dasgupta-park-kasampalis-adve-rosu-2019-pldi.pdf) | Explanation and validation story for the K model | Research paper; cite, do not transplant text. |
| `papers/x86isa-books-acl2-2017.pdf` | [Goel et al., ACL2 2017](https://arxiv.org/abs/1705.01225) | Explanation, views, and validation story for X86ISA | Research paper; cite, do not transplant text. |
| `models/xed/` | [Intel XED](https://github.com/intelxed/xed), `0bcb6237345c5066726dcc08b3d87928df3b5b26` | Encoding forms, operands, features, implicit resources, read/write metadata | Apache-2.0.  Suitable as a tool/oracle; it does not define value-level instruction semantics. |
| `models/acl2/` | [ACL2 X86ISA subtree](https://github.com/acl2/acl2/tree/master/books/projects/x86isa), `5c88b9c7c6c18a84a1ffa08ece304cb5b11ecdd5` | Primary proof-oriented executable cross-check | BSD-3-Clause-derived Community Books material.  Read and compare; do not derive Heather source from it without recording attribution and reviewing the affected component's licence. |
| `models/k-x86-64-semantics/` | [K x86-64 semantics](https://github.com/kframework/X86-64-semantics), `592380aea04820ea11cfa5475b343f0257f2474e` | Broad per-instruction user-level semantic cross-check | University of Illinois/NCSA permissive licence.  The model is tied to an old K revision, so it is reference material rather than a build dependency. |
| `models/sail-x86-from-acl2/` | [ACL2-to-Sail x86 model](https://github.com/rems-project/sail-x86-from-acl2), `0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf` | Alternative presentation of the ACL2 model and translation-validation material | Translator BSD-2-Clause; generated model derived from BSD-3-Clause X86ISA. |
| `models/remill/` | [Remill](https://github.com/lifting-bits/remill), `d5ec1ebd6411c23626ceb322c54e73f4050cf3ea` | Pragmatic explicit-state semantics and native differential-test patterns | Apache-2.0.  Engineering cross-check, not architectural authority. |
| `models/ghidra/` | [Ghidra x86 SLEIGH/p-code](https://github.com/NationalSecurityAgency/ghidra), `6b502aab73ff22397f3f1fb5d6dcf42822464ccb` | A second pragmatic decomposition into small state effects | Apache-2.0.  Decompiler semantics, not architectural authority. |

SHA-256 checksums for the cached PDFs:

```text
16a9336104750613ae2f2bab6eb7a1b21a7e1ef60ced35e9ab2e0d8c7efcec68  intel-sdm-combined-092.pdf
c10dbd2892d7374094e8326e101b496ae377e8d386a04fb15fb00d7476652d94  intel-sdm-documentation-changes-092.pdf
b95c6db015807bf38daed8cc0c294c42e479c42c62cf25655661754d21f591db  amd64-apm-volumes-1-5-4.10.pdf
dffbc08b32b9f0d76b08826b1d3d507368fe0eac5dfbc0a2d336ae61b59a2c74  k-x86-64-semantics-pldi2019.pdf
17561838476eaf4d2d7dfa70b55df73fc557a9ae8e5bcd37ce81947736e27873  x86isa-books-acl2-2017.pdf
```

### AMD manual links

AMD moved the combined manual from the revision 4.09 URL found by its search
index to [revision 4.10](https://docs.amd.com/v/u/en-US/40332_4.10_APM_Vol1-5).
The 4.10 PDF was downloaded manually through that human-facing page and added
to the cache on 2026-08-25; no unofficial mirror is involved.  Individual
volume landing pages remain useful for narrower downloads:

- [Combined volumes 1--5, revision 4.10](https://docs.amd.com/v/u/en-US/40332_4.10_APM_Vol1-5)
- [Volume 1: Application Programming, revision 3.24](https://docs.amd.com/v/u/en-US/24592_3.24)
- [Volume 2: System Programming, revision 3.44](https://docs.amd.com/v/u/en-US/24593_3.44_APM_Vol2)
- [Volume 3: General-Purpose and System Instructions, revision 3.37](https://docs.amd.com/v/u/en-US/24594_3.37)
- [Volume 4: Media Instructions, revision 3.26](https://docs.amd.com/v/u/en-US/26568_3.26_APM_Vol4)
- [Volume 5: 64-Bit Media and x87, revision 3.16](https://docs.amd.com/v/u/en-US/26569_3.16)

The older stable direct-PDF paths are also useful fallbacks when AMD's viewer
works poorly:

- `https://www.amd.com/content/dam/amd/en/documents/processor-tech-docs/programmer-references/24592.pdf`
- `https://www.amd.com/content/dam/amd/en/documents/processor-tech-docs/programmer-references/24594.pdf`

The AMD APM is a normative peer of the Intel SDM, not an optional secondary
blog-style source.  A rule on which the vendors differ must either use the
common guarantee, carry a vendor/feature parameter, or be excluded from the
initial target.

## 2. Authority and licence policy

Use sources in this order:

1. Intel SDM and AMD APM for the architectural contract.
2. Intel/AMD architecture errata and documentation changes.
3. ACL2 X86ISA and K as independent, executable interpretations.
4. XED for encoding/resource metadata.
5. Remill and Ghidra as implementation experience and additional bug-finding
   oracles.
6. Native differential tests on both Intel and AMD processors as validation,
   never as permission to strengthen a published architectural guarantee.

Permissive third-party licences are compatible with many distributions in the
ordinary aggregation/derivation sense, but that does not make importing code
free of bookkeeping.  Heather avoids the question initially: its semantics is
an original statement of architectural facts, with citations and cross-check
provenance, not a translation of ACL2, K, Sail, Remill, or SLEIGH source.  If a
future implementation copies or closely adapts third-party expression, that
component must retain the applicable notice and receive a specific licence
review.  This note is engineering policy, not legal advice.

## 3. One bottom model, several proved views

There should be one canonical x86-64 step relation.  Simpler arithmetic,
register, memory, and stack worlds are reusable libraries and proof views that
refine into that relation; they are not competing machine semantics.

Indicative shape:

```text
step : FeatureSet -> Instruction -> MachineState -> Outcome -> Prop

Outcome = Normal MachineState | Fault Exception

coverage : Instruction -> Supported | Unsupported CoverageReason
```

Architectural nondeterminism belongs inside `step`.  Model incompleteness
belongs in `coverage`.  A documented fault is an `Outcome`.  These three cases
must never be represented by one `Unknown` constructor.

The canonical initial state should include general registers, individual flag
bits, RIP, and byte-addressed memory.  Operating mode and advertised features
belong in an explicit environment.  Page tables, privilege transitions,
interrupt delivery, and the concurrent memory model are initially omitted,
but every use of the simplified memory interface must expose the precondition
that replaces them.  The coverage ledger in section 5 is what prevents an
omission from later being mistaken for an architectural guarantee.

## 4. Reusable simple worlds

### 4.1 Fixed-width arithmetic

Instruction rules should call a reusable fixed-width arithmetic library, for
example:

```text
add : BitVec n -> BitVec n -> BitVec n
carry_add : BitVec n -> BitVec n -> Bit
signed_overflow_add : BitVec n -> BitVec n -> Bit
```

The x86 `ADD` rule then says where the arithmetic result and each specified
flag are stored.  It does not privately reimplement addition.  This gives
Heather one body of bitvector arithmetic and proofs for compiler transforms,
constant evaluation, data representations, and ISA semantics alike.

The library must support at least widths 8, 16, 32, and 64; truncation,
zero/sign extension, slices and concatenation; signed and unsigned comparison;
carry/borrow and signed overflow; and shifts whose count policy is supplied by
the caller.  X86-specific count masking and undefined flags remain in the
instruction rule rather than contaminating the generic operation.

Undefined architectural outputs should be relationally chosen only at their
specified locations.  A fresh existential bit/value is preferable to a taint
style `Unknown`, because it retains correlations and lets an overwrite make
the uncertainty irrelevant.

### 4.2 Locations and frames

Registers, partial registers, flags, and memory operands want a common notion
of readable/writable location plus frame lemmas.  The x86 layer supplies the
peculiar location behavior: a 32-bit GPR write clears its upper half, smaller
writes preserve the rest, and encoding validity controls access to high byte
registers.  Instruction proofs should compose generic arithmetic facts with
these location-write facts.

### 4.3 Abstract stack, refined to memory and RSP

An abstract finite or trapping stack is useful for proofs of call lowering,
expression evaluation, and resource bounds.  At the real ISA boundary there
is no separate hardware stack: stack instructions update ordinary memory and
RSP.  Therefore define an abstraction relation such as:

```text
represents_stack : MachineState -> Stack Word64 -> Prop
```

and prove, under explicit normal-access and capacity preconditions, that the
machine rule for `PUSH`, `POP`, `CALL`, or `RET` refines the corresponding
abstract stack operation.  Fault ordering and restart state are deliberately
outside that first normal-path theorem and remain named obligations.  This
gets the convenience of a simple stack world without adding a second trusted
meaning for a stack instruction.

The same pattern should serve abstract memory regions, calling conventions,
and eventually allocation: simple algebra first, a representation relation,
then a theorem connecting the concrete state update to that algebra.

## 5. Coverage ledger

Every supported instruction *form*, not merely mnemonic, should record:

- operand and address widths, modes, feature bits, and legal encodings;
- explicit and implicit locations read and written;
- normal-state relation and locations provably unchanged;
- each flag as read, defined, preserved, or architecturally undefined;
- faults modeled, replaced by a stated precondition, or not yet modeled;
- Intel SDM revision/section and AMD APM revision/section;
- the ACL2/K/XED/Remill/Ghidra cross-check status;
- differential-test coverage and which observations were masked as undefined;
- `supported`, `partial`, or `unsupported`, with the reason for either latter
  status.

This ledger is part of the eventual model's review surface.  In particular,
"we did not model page faults" must appear as a missing fault plus a normal
memory-access precondition, never as a total load silently attributed to x86.

## 6. Likely dogfooding boundaries

The first semantic spike should be small enough to discover what Heather is
missing before fixing APIs prematurely.  The audit filed these standalone
owners; the architecture-specific sequencing and integration live in
`issues/x86-64-machine-model.md`:

1. `issues/fixed-width-bitvectors.md` — fixed-width values and their generic
   arithmetic/proof kit;
2. `issues/relational-semantics-refinement-kit.md` — relations, finite choice,
   and relational refinement;
3. `issues/state-location-and-frame-kit.md` — state locations and frame
   reasoning;
4. `issues/byte-memory-access-model.md` — byte memory with explicit access
   outcomes and normal-path assumptions;
5. `issues/finite-trapping-stack.md` — abstract finite/trapping stacks and
   their representation interface;
6. `issues/x86-64-machine-model.md` — instruction coverage/provenance, typed
   x86 operands, the canonical machine relation, and the validated encoder
   boundary.

The initial instruction fragment remains scalar integer code: moves and
extensions, LEA, add/sub/neg/inc/dec/imul, boolean operations, shifts,
compare/test, conditional selection and branches, and the basic stack/call
forms.  `DIV`/`IDIV`, floating point, SIMD, strings, atomics, privileged
instructions, concurrency, and system behavior stay explicitly unsupported
until their own slices.
