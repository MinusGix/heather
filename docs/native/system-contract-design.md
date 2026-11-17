# The system contract: what a compiled program presumes of where it runs

Status: **partly built.** Built (`lib/native/native_compile_elf.hthr`,
`heather write-elf`): the contract record and its printing (§2), and two
stack providers, the system's and the program's own segment (§4.2). Not
built: the contract embedded in the file (§2.1), the startup check and the
refusal outcome (§2, §4.2), room as an expression and the explicit-stack
combinator (§4.1), the mapped provider and memory acquired during the run
(§5), signals (§6). Written 2026-11-17 after the audit of the Linux model
(`issues/io-stack-below-rsp-not-mapped.md`,
`issues/elf-theorem-runtime-premises.md`,
`issues/native-target-minimal-system-assumptions.md`). Minus's decisions of
2026-11-17 are marked **Decided**; what is still open is marked **Q**.

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
`head10` presumes of the system that runs it:
  [standard]  the processor is an x86-64, as the vendors' manuals describe the instructions it runs
  [standard]  the file is loaded as its two PT_LOAD headers say, its data segment 4096 zero bytes (ELF gABI)
  [standard]  execution starts at the header's entry address (ELF gABI)
  [standard]  the command line is at the stack pointer as the process starts (x86-64 psABI)
  [presumed]  184 bytes below the stack pointer as the process starts are usable (Linux grants it when the stack limit leaves that much)
  [standard]  system calls follow the Linux x86-64 convention and answer as their manual pages allow
  [presumed]  no fatal signal is delivered, the kernel's out-of-memory kill included
```

As built: `Contract` (where the stack is from, the segment's size, the stack
room) and `Contract::lines`, a list of `Presumes`, each with its `Basis`.
`Contract::Start` is the premise the file's theorem takes, by provider
(`LinuxStart` or `SegmentStart`), and `Source::elf_runs` is the one theorem
over either. A certificate states `<p>_contract()`, proves its lines equal a
literal list (`<p>_presumes`), and `write-elf` prints that same list after
the kernel has checked it. So the printed lines are the ones the certificate
names. What is not yet mechanical: that each line corresponds to a field of
`Contract::Start` or a rule of the model is by the comments on `Presumes`,
not by a theorem. The stack line is still `presumed`: it becomes `checked`
with the startup check (§4.2). The line for system calls does not yet list
which calls the program makes.

### 2.1 The contract in the file, and what it is worth there

**Decided**: the contract is embedded in the file (an ELF note), marked as a
claim. A reader of the file alone cannot tell a true note from a false one,
and no encoding fixes that: a note is bytes, and anyone can write a file
with any bytes. What can be had, from weakest to strongest:

- **No mismatch for whoever has the certificate.** The theorem is about the
  file's exact bytes, note included. Checking the certificate (which holds
  the lowered program and its proofs, not the Heather source text) shows the
  note is the contract of that file. This costs a check, and it is the only
  route that trusts nothing but the kernel.
- **A hash of the certificate in the note.** The file then names the one
  certificate that vouches for it, so a certificate cannot be swapped for
  another program's. It still has to be fetched and checked.
- **A signature.** Someone who checked the certificate signs the file. The
  reader trusts the signer instead of checking. This is how distributions
  work, and it is the practical answer for binaries handed to people who
  will not run the kernel.
- **A reproducible build.** Anyone with the source and the compiler gets the
  same bytes. This needs the source, which the question wanted to avoid.
- **A succinct proof** (a proof short enough to embed and cheap to verify)
  is the only thing that would make a bare file self-certifying. Proof
  systems of that kind for a kernel check of this size are not practical
  today.

So the note says what the compiler claimed, and its header says it is
unverified unless checked against a certificate.

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

**Decided**: both routes. A recursion may be bounded statically, for
programs that want a known size, and a library combinator runs a recursion
on an explicitly acquired stack, so that depth can use whatever memory the
system gives while the program still fails by an ordinary modelled outcome
(the acquisition's failure) and not by overflow.

As built today the figure is `Source::need(homes, bodies)`: `main`'s frame,
the deepest chain of calls its procedures make under the placement, and the
functions' room table (`docs/native/native-procedure-frames-design.md` §6).
It is a constant of the compiled program.

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

**Decided**: the default is the system stack with a startup check. As built
the system stack is the default and the check is not written yet, so its
line is `presumed`. `write-elf --stack segment` selects the segment
provider.

What the check can and cannot establish. `getrlimit` answers the limit, and
the limit also covers what the system already put on the stack (arguments,
environment, auxiliary vector), so "limit at least N" is not "N bytes below
RSP". And that the kernel grows the stack down to the limit is Linux
behaviour, with exceptions (another mapping within the guard gap). Two
mechanisms, which compose:

- **Ask**: `getrlimit` at startup, refuse with a message when the limit is
  plainly too small. This turns the common failure into a refusal. The line
  stays partly presumed: the limit is evidence, not proof.
- **Touch**: write one byte in each page of the room, top down, before any
  effect. After it the pages are mapped and committed, which is the premise
  itself and no longer a presumption. A system that cannot give them kills
  the process there with a signal, before any output. It costs one write a
  page of the *stack room*, which is small; it is not the page-touching of
  all memory that §5 rules out. To state it the model needs a write below
  the mapped stack to have two outcomes, mapped or killed (§6).

**Q3a**: ask, touch, or both. I recommend both: ask for the message, touch
for the truth.

A mapped provider can also be entry code: `mmap` before the compiled
program starts, the memory profile chosen from the address it returned. That
needs the syscall in the model but not regions that appear during the run
(a suggestion from the thread that built frames by use, 2026-11-17).

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
cost proportional to the memory. **Decided**: that is not workable, and "no
out-of-memory kill" is a presumed line of every contract. It is how the
system works.

## 6. Signals

A fatal signal ends a run without an exit, and the model has no such step.
The honest options are a presumed line (above), or modelling termination by
signal as an outcome that any run may take at any step, which weakens every
"the program exits 0" statement to "exits 0 or was killed". SIGPIPE is the
one a correct program meets in ordinary use (its reader closed the pipe);
it can be made a non-event by ignoring it at startup, after which the write
fails with an error the model already has. **Decided** in direction: signals
should be handled eventually, and it is known to be hard; until then the
presumed line stands. **Q5** stays open: ignore SIGPIPE at startup by
default?

## 7. Order of work

1. Done: the record and its printing.
2. Done: providers as a compile option (`--stack system|segment`), the
   compiler proved once against "RSP is the top of a stack with the room,
   RDI is where the command line is" (`Source::runs_after`).
3. The contract in the file as a note (§2.1): a fourth program header and
   the note's bytes after the code.
4. The refusal outcome in the ELF theorem, and the startup check of the
   system stack as its first use (§4.2).
5. Room as an expression and the explicit-stack combinator (§4.1), with the
   first recursive function.
6. `mmap` in the model; the mapped provider; memory acquired during the run.
7. Signals (§6).

Steps 3 and 4 are independent of the rest. Step 5 belongs with the function
compiler's work, step 6 with the heap's.
