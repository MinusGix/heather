# Determinism of fetched execution

The native process theorems currently construct a `LinuxRuns` witness. To say
that its trace is the trace of every run with the same syscall responses, the
step relation must first be deterministic on the state components that the
program can observe.

## The exact observation

`TEST r64, r64` leaves AF architecturally undefined. The `Execute` relation
correctly permits either value. Thus equality of complete `MachineState`s is
false even for two executions of the same decoded instruction. The relation
`SameDefinedState` compares all registers, RIP, memory, and CF/PF/ZF/SF/OF;
it omits AF. `execute_pair_same_defined` proves that two executions of the
same decoded ordinary instruction agree on this observation. The proof uses
the functional `execute_normal` as a common state and treats TEST separately.

The observation is preserved by each emitted operation. `erase_af` supplies a
canonical representative of a state; equality of these representatives is
equivalent to `SameDefinedState`. Executing an ordinary instruction or branch
commutes with erasing AF. The byte-load proof additionally uses equality of
memory and the base register to show both executions read the same byte; the
store proof uses equality of the base, source, and memory. These yield
`execute_canonical_respects_defined`, `emitted_exec_respects_defined`, and
`word_store_respects_defined`.

## Byte and decoding boundary

`fetched_bytes_same_length_related` proves that two successful fetches of the
same length from related memories and RIPs return equal bytes.
`canonical_bytes_unique` uses the direct decoder to prove that equal canonical
ordinary encodings name the same instruction.
`ordinary_fetched_respects_defined` composes these facts with execution
agreement for two ordinary steps of equal encoded length, even when the
starting states differ in AF. The analogous short branch proof needs no
length premise (both encodings occupy two bytes); the near branch proof still
takes equal lengths as a premise.

The premise about length cannot be dropped without a prefix argument. A
successful read of two nonempty spans from the same address gives the same
head byte; `readable_tail` lets a prefix proof repeat that observation. The
short and near branch encoders are injective through their respective direct
decoders. The
emitted families are ordinary instructions, byte loads, short and near
branches, and word stores. A complete step theorem needs a checked decoder or
prefix-disjointness proof across those families, including that a store's
`MOV [base], source` encoding cannot also be a register `MOV`. For a fixed
emitted witness, `fetched_step_respects_same_witness` and
`store_step_respects_same_witness` now carry agreement across related input
states. Selecting the same witness from bytes is the missing step.

## From steps to a process trace

Once byte selection is unique and fetched/store steps are exclusive at a
given RIP, induction over `LinuxStepsN` gives agreement after
the same number of steps. The process theorem then needs a progress/exclusion
argument: a syscall cannot be skipped by a fetched or store step, and no
earlier state can satisfy `LinuxSyscallAt`. Its event rules must carry the
same read or write response and quantify over RCX, R11, and failed-read junk,
as `LinuxRuns` already does. Those lemmas should strengthen
`read_print_runs` to a universal statement over runs with those responses.

This is a proof boundary, not a change to the Linux environment assumption:
the response history remains supplied by the environment.
