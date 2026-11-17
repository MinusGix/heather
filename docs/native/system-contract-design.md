# The system contract: what a compiled program presumes of where it runs

Status: **proposal, nothing here is built** beyond `LinuxStart`
(`lib/native/native_compile_elf.hthr`). Written 2026-11-17 after the audit of
the Linux model (`issues/io-stack-below-rsp-not-mapped.md`,
`issues/elf-theorem-runtime-premises.md`,
`issues/native-target-minimal-system-assumptions.md`). Open questions are
marked **Q**.

## 1. What this is for

A compiled program's theorem is about a machine and an operating system that
are models. Whatever the theorem takes for granted about the real system is
an axiom of the compilation. Minus's requirements (2026-11-17):

- Programs run on normal Linux systems and, within stated limits, on odder
  ones (other kernels' Linux layers, emulators, sandboxes, small limits).
- A program should not explode under a resource limit or a memory shortage
  when that can be avoided. Some of it can be checked when the program
  starts.
- At the least, compiling a program says what it presumes about the system.
- Stack overflow is avoided statically, and programs will recurse.
- The design is sized for large, intricate software, not for the programs
  that exist today (`cat`, `head`, the lexer).

The rule the audit already follows stays: a model's rule is one a written
standard backs; anything else is undefined, checked, or a named premise.

## 2. The contract is one object, and the compiler prints it

Every written program has one record of what it presumes, instantiated with
the program's own figures. The certificate's theorem takes that record as its
single premise about the system, and the driver prints it in plain words:

```
head10 presumes of the system:
  [standard]  the file is loaded as its two PT_LOAD headers say (ELF gABI)
  [standard]  execution starts at the entry address
  [standard]  system calls follow the x86-64 Linux convention; it calls: read, write, exit
  [checked]   stack: N bytes below the entry stack pointer (tested against the stack limit at startup)
  [presumed]  the command line is at the entry stack pointer as the psABI lays it out
  [presumed]  no fatal signal is delivered (includes the kernel's out-of-memory kill)
```

The printed form and the theorem's premise are generated from the same
record, so the list cannot drift from what is proved. **Q1**: also embed it
in the file (an ELF note) so a binary carries its own axioms?

Each line has one of three kinds.

- **standard**: a written contract says it (ELF gABI, psABI, the syscall
  convention). It stays a premise, and the line names the document.
- **checked**: the program tests it when it starts. It is then no premise.
  The theorem's conclusion widens instead: the run is the source's run, or
  it is the **refusal**, a fixed message on standard error and a fixed exit
  status, with no other effect before it.
- **presumed**: nothing written promises it and the program cannot test it.
  These are the limits of support, and the value of the record is that they
  are all in one place.

Moving a line from presumed to checked or standard is the measure of
progress. Adding a presumed line needs a reason in the doc.

## 3. How the choices fail today (measured, 2026-11-17)

| Situation | What happens |
| --- | --- |
| System stack, stack limit below the program's need | Starts, produces output, then SIGSEGV mid-run |
| Stack inside the data segment, segment over the data or address-space limit | SIGSEGV during exec, before the first instruction |
| Either, with memory exhausted and default overcommit | Pages are committed on first touch, so an out-of-memory kill can come mid-run |

So no placement of the stack is reliable by itself. The segment stack moves
a limit's failure to before the run and fixes the stack's size when the file
is written. The system stack grows and has a guard page, and fails late.

## 4. The stack: how much, and where from

These are two questions and the current code already separates them:
`native_compile_correct` is proved against an abstract `Stack` of at least
the source's room, and says nothing of where that stack is.

### 4.1 How much: proved statically, recursion included

Today a function's theorem carries its stack room as a number (the room
table, `issues/function-frame-sized-by-use.md`), and a statement procedure's
depth is the source's `depth`. Both are constants because nothing recurses
without fuel.

The general form: a function's contract states its room as an expression in
its arguments. For a recursive function that expression is built from its
termination measure (a frame for each step of the measure). A call site
shows the callee's room fits what remains below the caller's frame, which is
a proof obligation like any other precondition and is discharged by the same
automation.

At the top of a program the room is then either a constant, and the program
simply needs that much stack, or it depends on input. A program whose depth
depends on input must bound or test its input with an ordinary branch of the
source language, which has ordinary semantics. There is no overflow outcome
in the semantics and no probe in the emitted code.

**Q2**: is "the source bounds its own input" acceptable as the only route, or
do we also want a library combinator that runs a recursion on an explicitly
allocated stack (heap-allocated continuation), for depth that should scale
with memory instead of with a fixed bound?

### 4.2 Where from: a provider

A provider is entry code with one law: after it, RSP is the top of a `Stack`
with at least the proved room, and the command line is still reachable. The
compiler is proved once against the law. Each provider adds its own lines to
the contract.

| Provider | Contract lines | Good for | Weakness |
| --- | --- | --- | --- |
| **System stack, checked** | checked: the stack limit leaves the room (`getrlimit` at startup, refusal otherwise). presumed: the kernel grows the stack down to its limit | Normal systems: grows, has a guard page, tools understand it | Growth is Linux behaviour, not a standard |
| **Segment** (built on PR #722, to be kept as a provider) | standard: ELF loading only | Systems where nothing but ELF loading is wanted | Size fixed when written; a limit kills at exec with a signal, not a message; needs the stack placed at the low end to keep a guard |
| **Mapped** | checked: `mmap` of the room plus a guard page succeeded | Large or configurable stacks; threads | Needs `mmap` and memory that appears during the run in the model (§5) |

**Q3**: the default. I recommend the checked system stack: it is what every
other program on the system does, and the check turns the common failure (a
small limit) into a refusal.

## 5. Memory in general

The same pattern as the stack: memory is acquired by a call whose failure is
a modelled outcome, and never assumed. Today's memory profile
(`X86Profile`) fixes the permissions a process relies on for the whole run.
A program that maps memory needs regions that begin during the run, which is
a change to the memory model and the largest piece of work in this doc.
`docs/native/native-heap-arena-design.md` is the heap's side of it and
should be read with this.

What cannot be checked: with overcommit, a successful mapping does not mean
the pages exist, and the kernel may kill the process when one is touched.
Touching every page at startup makes that happen before any output, at a
cost proportional to the memory. **Q4**: offer that as an option, or leave
"no out-of-memory kill" as a presumed line everywhere?

## 6. Signals

A fatal signal ends a run without an exit, and the model has no such step.
The honest options are a presumed line (above), or modelling termination by
signal as an outcome that any run may take at any step, which weakens every
"the program exits 0" statement to "exits 0 or was killed". SIGPIPE is the
one a correct program meets in ordinary use (its reader closed the pipe);
it can be made a non-event by ignoring it at startup, after which the write
fails with an error the model already has. **Q5**: ignore SIGPIPE at startup
by default?

## 7. Order of work

1. The record and its printing, over what exists (`LinuxStart` as it is).
2. The refusal outcome in the ELF theorem, and the checked system stack as
   its first use.
3. Providers as a compile option; the segment provider restored from PR #722's
   history with the stack at the low end.
4. Room as an expression (§4.1), with the first recursive function.
5. `mmap` and regions that appear during the run; the mapped provider.

Steps 1 and 2 are small and independent of the rest. Step 4 belongs with the
function compiler's work, step 5 with the heap's.
