# The system contract: what a compiled program presumes of where it runs

Status: **partly built.** Built (`lib/native/native_contract.hthr`,
`lib/native/native_compile_elf.hthr`, `heather write-elf`): the contract
record, its printing and its note in the file (§2, §2.1), two stack
providers, the system's and the program's own segment (§4.2), and the check
of the system's stack: the program touches every page of its room as it
starts (§4.3, `lib/std/os/linux/linux_x86_64_stack_growth.hthr`). Not built:
the limit read and its refusal message (§4.2), the lines of §2.2, room as an
expression and the explicit-stack combinator (§4.1), the mapped provider and
memory acquired during the run (§5), signals (§6). Written 2026-11-17 after the audit of the Linux model
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
  [presumed]  the stack pointer as the process starts is 4280 bytes or more above the data segment's end, in the lower half of the address space
  [checked]   184 bytes below the stack pointer as the process starts are usable: the program stores into each page of them as it starts, and ends there with a signal if one is refused
  [standard]  a store within a page below the stack extends the stack or ends the process with a signal (Linux: mmap(2), getrlimit(2))
  [standard]  system calls follow the Linux x86-64 convention and answer as their manual pages allow
  [presumed]  no fatal signal is delivered, the kernel's out-of-memory kill included
```

As built: `Contract` (where the stack is from, the segment's size, the stack
room) and `Contract::lines`, a list of `Presumes`, each with its `Basis`
(`lib/native/native_contract.hthr`, which also words them:
`Contract::lines_text`, `Contract::text`, `Contract::note`).
`Contract::Start` is the premise the file's theorem takes, by provider
(`SystemStart` or `SegmentStart`), `Contract::Runs` is what the theorem then
says of the process, and `Source::elf_runs` is the one theorem over either. A certificate states `<p>_contract()`, proves its lines equal a
literal list (`<p>_presumes`), and `write-elf` prints that same list after
the kernel has checked it. The words printed are the library's
(`Contract::lines_text`), read back from the kernel's evaluation, not a
second spelling in the driver. So the printed lines are the ones the
certificate names. What is not yet mechanical: that each line corresponds to a field of
`Contract::Start` or a rule of the model is by the comments on `Presumes`,
not by a theorem. On the system's stack the room's line is `checked` (§4.3)
and no field of `Start` says it; where the stack is, a page and the room
above the segment, is the `presumed` line beside it, which nothing written
backs and no test in the program can replace (the program is already running
on that stack). The line for system calls does not yet list which calls the
program makes (§2.2).

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
  With a hash of the source in the note the file also names the source it
  claims to come from, so whoever has that source can rebuild and compare
  without a certificate. Not built: the note carries no hash, and nothing
  tests that two `write-elf` runs of one source give the same bytes (no
  step of it is known to vary).
- **A succinct proof** (a proof short enough to embed and cheap to verify)
  is the only thing that would make a bare file self-certifying. Proof
  systems of that kind for a kernel check of this size are not practical
  today.

So the note says what the compiler claimed, and its header says it is
unverified unless checked against a certificate.

As built: the file has a fourth program header, a `PT_NOTE` naming bytes
after the code (`io_elf_header`, `io_elf_file(code, note, size)`,
`lib/std/os/linux/linux_x86_64_image.hthr`; the header is 288 bytes and the
entry 0x400120). The note is an ELF note of name `Heather`, type 1, whose
description is `Contract::text`: two lines saying what it is and what it is
worth, then the contract's lines as `write-elf` prints them. The file's
theorem is about the file with that note: `Source::elf_runs` takes
`io_elf_file(code, contract.note(), size)`, and a certificate proves its
literal note equal to `<p>_contract().note()` (`<p>_note_is`). The loader
maps the note with the code (it lies inside the RX mapping) and the program
never reads it (`X86Memory::loaded_entry_before`). `readelf -n` lists it,
and `strings` shows its text.

Each line has one of three kinds.

- **standard**: a written contract says it (ELF gABI, psABI, the syscall
  convention). It stays a premise, and the line names the document.
- **checked**: the program tests it when it starts. It is then no premise,
  and the theorem's conclusion is what changes. A test the program survives
  failing (the limit read, §4.2) makes the conclusion "the source's run, or
  the **refusal**": a fixed message on standard error and a fixed exit
  status, with no other effect before it. A test the system answers by
  ending the process (the touch, §4.3) makes the conclusion a claim over
  every state the system may leave at the test: of a process ended there
  the theorem says nothing, since it has no later state, and it has made no
  system call.
- **presumed**: nothing written promises it and the program cannot test it.
  These are the limits of support, and the value of the record is that they
  are all in one place.

Moving a line from presumed to checked or standard is the measure of
progress. Adding a presumed line needs a reason in the doc.

### 2.2 What the record does not say yet

Each of these is true of a written program today and is in no line of its
contract. They were collected from the threads working on frames and on
linked code (2026-11-17).

- **The load addresses must be free.** The file is a fixed-address
  executable: its code at 0x400000, its data at 0x410000. `FileLoaded` says
  the headers are honoured, which is the gABI's rule, but a system that
  cannot give those addresses (a minimum mapping address above them, an
  emulator's own layout) fails the exec. The line should name the ranges.
  A position-independent file would remove it.
- **The compiler's own limits.** A data segment is at most 1 GiB
  (`io_data_limit`) and a file at most 65535 bytes (its length is in
  sixteen bits of the header, `issues/io-elf-file-length-sixteen-bits.md`).
  `write-elf` refuses past either. They are limits of what can be written,
  not presumptions about a system, and belong beside the contract as what
  this target cannot do.
- **Which system calls.** The line for calls should list the ones the
  program makes, so that a sandbox's allowed set can be compared with it.
- **Linked code has a contract too** (`crates/linked`): each exported
  function presumes the System V calling convention of its caller, the
  buffers its caller passes, and room on its caller's stack, which its
  theorem carries as a number (the room table,
  `issues/function-frame-sized-by-use.md`). Nothing prints it, and the Rust
  side that calls it is trusted to leave that room.

## 3. How the choices fail today (measured, 2026-11-17)

| Situation | What happens |
| --- | --- |
| System stack, room presumed (as written before §4.3), stack limit below the program's need | Starts, produces output, then SIGSEGV mid-run |
| System stack, room touched at startup (§4.3), stack limit below the program's need | SIGSEGV in the entry code, before any system call |
| Stack inside the data segment, segment over the data or address-space limit | SIGSEGV during exec, before the first instruction |
| Either, with memory exhausted and default overcommit | Pages are committed on first touch, so an out-of-memory kill can come mid-run |

So no placement of the stack is reliable by itself. The segment stack moves
a limit's failure to before the run and fixes the stack's size when the file
is written. The system stack grows and has a guard page; presumed, it fails
late, and touched, it fails before the program has done anything. None of
them fails with a message yet (§4.2, the limit read).

The two system-stack rows were measured with a pair of small files, one
starting with the library's own entry code for a room of 1 MiB
(`stack_touched_entry(1048576)`) and then writing a line, the other writing
the line first and then storing 1 MiB below RSP (Linux 6.18). Under stack
limits of 8 MiB and 2 MiB both print and exit 0. Under 1 MiB, 512 KiB and
64 KiB the touched one dies with SIGSEGV having printed nothing, and the
presumed one prints and then dies.

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

**The check calls already make.** A statement procedure's call counts the
source's `depth` down in a word of the data segment and, at zero, exits with
status 139 (`call_depth_status`, `Prog::count_down`; the "deep exit"). That
is a run-time check of the stack, it is in the source's meaning
(`Source::tree` returns `Exited(139)` there), and every call pays it,
including calls that cannot recurse. Where it should go (proposed with the
thread that built frames by use, not yet decided):

- No check where the call graph is acyclic: `Source::need` already follows
  the calls a body makes and not the depth alone (`doubling_need_any_depth`),
  so the room is exact and nothing can run past it.
- No check where a recursion is proved bounded (the measure's bound gives
  the room, as above).
- Otherwise one check, in bytes: a call compares what is left of the room
  with what it needs. A count of calls is the wrong unit once frames differ
  in size, which they do since frames are sized by use. The short side is
  a refusal of the compiled program, not an outcome of the source: how
  many bytes a frame takes depends on the placement, so it cannot be in the
  source's meaning (Minus, 2026-11-17). The guarantees the theorem is to
  give, refusal only where the current chain does not fit and at the
  call's entry, are `docs/native/native-procedure-frames-design.md` §7.

The explicit-stack combinator is the same check made against memory the
program acquired, with the acquisition's failure as the outcome.

### 4.2 Where from: a provider

A provider is entry code with one law: after it, RSP is the top of a `Stack`
with at least the proved room, and the command line is still reachable. The
compiler is proved once against the law. Each provider adds its own lines to
the contract.

| Provider | Contract lines | Good for | Weakness |
| --- | --- | --- | --- |
| **System stack, checked** (built, the default, §4.3) | checked: the room below RSP, by touching it. standard: a store within a page below the stack extends it or ends the process. presumed: the stack is a page and the room above the segment | Normal systems: grows, has a guard page, tools understand it | Fails with a signal, not a message, until the limit read is added; growth is what Linux's manual pages say, not a standard across systems |
| **Segment** (built, `--stack segment`) | standard: ELF loading only | Systems where nothing but ELF loading is wanted | Size fixed when written; a limit kills at exec with a signal, not a message; needs the stack placed at the low end to keep a guard |
| **Mapped** | checked: `mmap` of the room plus a guard page succeeded | Large or configurable stacks; threads | Needs `mmap` and memory that appears during the run in the model (§5) |

**Decided**: the default is the system stack with a startup check, and the
check touches every page of the room, since a limit read does not show the
room is there (Minus, 2026-11-17). As built the system stack is the default
and its entry code touches the room (§4.3). `write-elf --stack segment`
selects the segment provider.

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

**Decided**: touch (built, §4.3). The ask may be added beside it for the
message; it is not built.

How the ask would be built (not started):

- **Ask, as source.** The check is ordinary source code put in front of
  `main`: a call of `getrlimit(RLIMIT_STACK)` into a word, a branch on it
  against `Source::need` plus a margin for what exec put on the stack, and
  on the short side a fixed message to standard error and a fixed exit
  status. The refusal outcome is then the source's own behaviour, and the
  compiler's one theorem covers it with nothing new at the ELF level. What
  it costs: `LinuxCmd` gains a call (`getrlimit`, or `prlimit64`), so every
  match over `LinuxCmd` in the library gains an arm, and `Perform` reaches
  it. `RLIM_INFINITY` passes. As source it would run after the entry code,
  so after the touch, and a short stack would still end the process with a
  signal first. For the message to come first the read has to be entry
  code before the touches: a system call in the entry phase, whose answer
  the file's theorem then ranges over as it does over the memories a touch
  leaves. The room's line is `checked` by the touch either way; the ask
  adds only the message.

A mapped provider can also be entry code: `mmap` before the compiled
program starts, the memory profile chosen from the address it returned. That
needs the syscall in the model but not regions that appear during the run
(a suggestion from the thread that built frames by use, 2026-11-17). It
would reuse the touch's shape: the entry phase in the profile that relies on
the segment alone, the new memory as a fact beside the state, and one
`Alike` step to the profile the program runs in.

### 4.3 The touch, as built

**The entry code** (`stack_touched_entry(room)`): keep RSP in RDI and move
RSP below the room; then, for each stride from the top, lower RBX by the
stride and store a byte there (`mov [rbx], al`); then put RSP back. Strides
are a page at a time and then what is left (`stack_strides`), so each store
is within a page of memory already known to be the stack's, and the last
lands on the room's lowest byte. RSP sits below every store because kernels
before 5.0 refuse an access far below RSP. The touches are unrolled, sixteen
bytes of code a page: a room of 1 MiB is 4118 bytes of entry code, and with
the file's 65535-byte limit a room cannot pass about 15 MiB
(`issues/stack-touch-entry-loop.md`).

**The rule of the model** (`StackTouch`, `StackGrown`). Growth changes what a
memory permits, which no instruction's step does, so it is a rule beside the
machine's steps and not one of them. At a store whose address is within a
page below the `known` bytes of stack, with RSP at or below the address,
Linux leaves a memory with the same cells in which the stack reaches the
address and nothing above the stack's top or more than a page below the
address has changed permission, or it ends the process. `StackTouch` is a
claim for every such memory; a process that is ended has none, and the claim
says nothing of it. What backs the rule: mmap(2) on `MAP_GROWSDOWN` (a touch
of the guard page under the mapping extends it by a page, or the process
gets SIGSEGV when it cannot) and getrlimit(2) on `RLIMIT_STACK` (the
process gets SIGSEGV on reaching the limit). The stride of at most a page is
why the rule needs no figure for the guard gap: the store is in the stack
or in the page under it. That the grown bytes are data and not code rests
on the file's `PT_GNU_STACK` header.

**The theorem.** `SystemStart` asks nothing of what is below RSP, and the
process is one of `X86Profile::io(size)` throughout: its memory's type
relies on the data segment only. `Source::elf_touched_runs` concludes
`TouchedRuns`: the process runs to its first store, where `StackTouch`
holds; in every memory Linux may leave it runs to the next; and after the
last it reaches a state which, seen as a state of
`X86Profile::process(size, top, room)` with the same registers, cells and
permissions (`Alike`), simulates the source. `Contract::Runs` is that for
the system's stack and the plain simulation for the segment's.

**What is not proved.** `Alike` identifies a state of one profile with a
state of another that differs only in the proof its memory carries. That the
two then run alike is not a theorem: no step reads that proof
(`X86Memory.relied` is used by the proofs about steps, not by the steps), so
it is true by inspection of the model, and a lemma that says it is owed
(`issues/elf-touched-runs-exact.md`, which also asks for the converse, that
every run of the touched process is a run of the source, as
`Source::elf_runs_exact` says of the presumed one).

**What it costs a run.** One store a page of the proved room, before
anything else. The pages are then committed, so an out-of-memory kill for
the stack can only come here, before any output. Cat's room is 168 bytes
and `head -c 10`'s is 184: one store each.

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
fails with an error the model already has. The touch (§4.3) is the first
statement with a signal in it, and its shape needs no change to the
semantics of a run: a rule gives the states the system may leave, and a kill
is the absence of one. **Decided** in direction: signals
should be handled eventually, and it is known to be hard; until then the
presumed line stands. **Q5** stays open: ignore SIGPIPE at startup by
default?

## 7. Order of work

1. Done: the record and its printing.
2. Done: providers as a compile option (`--stack system|segment`), the
   compiler proved once against "RSP is the top of a stack with the room,
   RDI is where the command line is" (`Source::runs_after`).
3. Done: the contract in the file as a note (§2.1).
4. Done: the startup check of the system stack, by touching it (§4.3).
   Left of it: the limit read with a refusal message (§4.2), the lemma and
   the converse of `issues/elf-touched-runs-exact.md`, the touch as a loop
   (`issues/stack-touch-entry-loop.md`), and the lines of §2.2.
5. Room as an expression and the explicit-stack combinator (§4.1), with the
   first recursive function.
6. `mmap` in the model; the mapped provider; memory acquired during the run.
7. Signals (§6).

Step 5 belongs with the function compiler's work, together with the depth
check of §4.1; step 6 with the heap's.
