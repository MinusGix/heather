# Determinism of fetched execution

Status: **landed 2026-09-28** (§5–§7). Owner: `issues/fetched-step-deterministic.md`.

The native process theorems construct a `LinuxRuns` witness: a run with the
claimed events exists. To say that its trace is the trace of every run with
the same syscall responses, the step relation must first be deterministic on
the state components that the program can observe. §1–§4 are the proof
boundary as it stood after the first slices (2026-09-27); §5–§7 close it.

## 1. The exact observation

`TEST r64, r64` leaves AF architecturally undefined, and IDIV, MUL and the
shifts by an imm8 leave others. The flags carry a mask of which are defined
(`DefinedFlags`, the `defined` field of `Flags`), and the `Execute` relation
permits any value in an undefined flag. Thus equality of complete
`MachineState`s is false even for two executions of the same decoded
instruction. The relation `SameDefinedState` compares all registers, RIP,
memory, the mask and the defined flags. It is defined as equality after
`erase_undefined`, which clears each undefined flag and so supplies a
canonical representative of a state: the pullback of `=` along
`erase_undefined` (`SameDefinedState::pullback`), registered as an
`Equivalence` and written `≈` at `MachineState`.
`execute_pair_same_defined` proves that two executions of the same decoded
ordinary instruction agree on this observation, through the functional
`execute_normal` as a common state. An instruction that reads an undefined
flag (SETcc, JCC) has no `Execute` at all (docs/native/runtime-fn-setups-design.md
§16.13, round 5), so readers are related only where what they read is
defined (`same_defined_respects_reading`).

The observation is preserved by each emitted operation. A function that
commutes with erasing respects the relation (`same_defined_respects`);
a load's result and a store's result each commute and are registered as
`evidence theorem`s of `PreservesRelation`, so `rel_cong` finds them; an
ordinary instruction or branch commutes only where the flags it reads are
defined, so it is stated with that premise
(`execute_normal_respects_defined`, `short_control_respects_defined`,
`near_control_respects_defined`) and not as evidence. The byte-load proof additionally
uses equality of memory and the base register to show both executions read
the same byte; the store proof uses equality of the base, source, and memory.
These yield `execute_canonical_respects_defined`,
`emitted_exec_respects_defined`, and `store_step_respects_same_witness`.

## 2. Byte and decoding boundary

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

## 3. From steps to a process trace

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

## 4. What §2 left open

Two things: the premise of equal lengths (the near branch, and any pair of
forms from different families), and selecting one witness across the
families at all, store included. §5 does both at once, without a length
argument.

## 5. One decoder, read from the front

`lib/std/arch/x86_64/x86_64_step_forms.hthr` (module `x86_64_step_forms`) names
every form a step can fetch, `StepForm`: an emitted instruction, a word
store, or SYSCALL. `decode_step_form` reads a form back from the front of a
byte list and never looks past the form's own bytes, so completeness is
stated with an arbitrary tail:

```text
step_form_complete(form, rest): decode_step_form(step_form_bytes(form) ++ rest) = Some(form)
```

The decoder is complete on the forms and claims nothing else: it is not a
recogniser, and a byte list that is no form may decode to anything. It
dispatches on bits that are literal in every encoding (a REX prefix is
0100WRXB; the other first bytes are 0F, 74, E9, EB), then on literal opcodes,
and rebuilds registers from REX and ModRM fields (`gpr_fields_roundtrip`),
immediates and displacements from their bytes (`immediate_bytes_roundtrip`,
`rel32_round_trip`). A register form and the word store share `REX.W 89`;
ModRM's mod bits tell them apart.

Two successful fetches from one memory at one address agree as far as the
shorter goes (`readable_prefix`, by `readable_head_same` and
`readable_tail`), so one is the other followed by a tail. Decoding both
gives the same form (`prefix_forms_equal`), whatever the lengths:
`fetched_forms_equal`. The near-branch length premise and the cross-family
selector of §4 are both this one theorem.

`step_respects_defined` follows: two steps (fetched or store) from states
equal on defined components select one form, and the same-witness theorems
of §2 carry the relation through. `syscall_excludes_step`: where SYSCALL is
fetched, no step runs, from that state or a related one.

## 6. The run is the run

`lib/std/os/linux/linux_x86_64_determinism.hthr` states it for any `LinuxIo`.

- `LinuxRun` is a run as it happened: `LinuxRuns`' shape with every
  quantifier over what Linux leaves behind (RCX, R11, a failed read's junk)
  turned into a choice. It keeps only what a real Linux run satisfies and the
  requests need: the syscall number, the descriptor, a write's length and
  bytes, a failed read's junk within the requested length. The rest of
  `LinuxRuns`' side conditions (capacity, writability, errno range) are
  Linux's promises about responses; a run need not state them.
- `SameResponses(claim, run)`: event by event, the same kind with the same
  result. Requests are not compared; they are what is proved equal.
- `linux_steps_meet`: runs from related states that each reach a SYSCALL
  reach related states. Induction on both step counts; unequal counts meet
  `syscall_excludes_step`.
- `linux_runs_determine`: from related states, a claimed run and any run with
  the same responses have equal event lists. At each syscall the request is
  read off related registers and memory (`writes_from_unique` for a write's
  bytes), and Linux's returns read only defined components
  (`same_defined_respects`, by `erase_undefined` commuting with each return).
- `linux_runs_every` is the one-state corollary. It is not vacuous:
  `claim_is_run` turns a claim into a run (zeros for RCX and R11, an empty
  junk buffer) and `same_responses_refl` matches its answers.

The claim's side of one syscall is `ClaimAt`, spelled as `LinuxRuns` spells
it; `claim_at` checks by conversion that the two agree, so `linux_x86_64_io`
did not change.

## 7. At the built file

The read-loop producer (`crates/cli/src/native/read_loop.rs`) bundles both
modules and writes, next to each program's `{prefix}_runs`,

```text
{prefix}_runs_every(… the same premises …, run, ran: LinuxRun(io_linux(), run, io_initial(file, page, gprs, flags)),
    answers: SameResponses(eof_events(…), run)): run = eof_events(…)
```

for both the exit and the print profile. It proves the claim again with the
same library call rather than naming `{prefix}_runs`, so a refused claim is
reported once and not again as an unbound name (the native refusal tests
check for that). This is the acceptance line of the issue: every run of the written file that got the history's answers produced
exactly the claimed events.

What it does not say: a `LinuxRun` ends at an exit, as `LinuxRuns` does, so
the theorem compares complete runs. That no run of the file diverges or
stops between syscalls is not stated, because no relation for a partial run
exists yet. `linux_steps_meet` is the ingredient: a partial run tracks the
claimed one step for step and meets the same SYSCALL. That statement belongs
to `issues/linux-syscall-trace-model.md`.

Tests: `crates/elab/tests/linux_determinism.rs` checks both modules over the
read-loop library prefix, with negative controls (a decoder that reads ADD as
SUB, takes a store for a register form, or looks for SYSCALL at another
opcode; a run whose failed read leaves unbounded junk, or whose answers are
compared by kind alone). The native read-loop tests check `_runs_every` at
each built file.
