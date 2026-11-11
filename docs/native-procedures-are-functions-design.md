# Procedures are functions: one frame, one call, one contract

Status: **proposed 2026-11-11; steps 5a, 5b and 5c built the same day**
(§3), 5d not. The contract is built as `Target::Callable` (§2.5, "As
built"). §1 describes the code before 5a. Round U5 of
`docs/native-one-compiler-design.md` (§2.4, §3), which asked for this note
before the round. Owner: `issues/native-one-compiler.md`; it draws in
`issues/native-procedure-contracts.md`,
`issues/native-register-moves-and-convention.md` and
`issues/rt-effectful-callees.md`. It extends `docs/compilation-vision.md`
§2.4 and replaces §3 to §5 of `docs/native-procedures-design.md` (the
convention, the compile and its proof); that note's §1 and §2, what a
procedure is and what a call means, stand unchanged.

## 0. Summary

A program today has two kinds of callable. A **function** is a region with
a result, compiled into registers, called by System V, proved to return
(`Site::CallsOver`). A **procedure** is a statement with parameters and
results, compiled over the program's one file of words, called by a
convention of its own in which the caller pushes every word it still
needs, proved to run as a tree (`Target::Calls`). U5 makes them one thing
in the machine, and says plainly where they stay two.

1. **Words live in the activation's frame.** A statement's words sit on
   the stack below its return address, addressed from RSP, and no longer in
   static slots of the data region. `main` gets its frame from the
   start-up. This is the one change with a large proof under it, and it is
   contained: `Target::Held` is restated and the lemmas that read and write
   a word's home are proved again; the statements above them do not change.
2. **One call.** The callee saves the registers it uses and makes its own
   frame; the caller pushes nothing. Arguments, kept registers and the
   memory clause are the function compiler's, which are already proved. A
   call site is the same code whichever kind it calls.
3. **One contract, tree-valued.** A callee is entered with its arguments
   and returns with its results, its caller's frames and kept registers as
   they were and the file as its meaning leaves it, having run as its tree.
   A function's proved return is the case where the tree is a value.
4. **Two levels stay, because they are two kinds of meaning.** A region is
   a total function of its words, so what a region calls must answer with a
   value. A statement is a tree, so what a statement calls may ask Linux
   for things, run out of depth, or exit. One table of callables would
   make every region's evaluation a tree. This refines §2.4 of the
   one-compiler note, which said `Perform` and `Call` become one construct:
   they become one in the code and stay two in the meaning (§2.1).
5. **Recursion is at the statement level**, where it already is, with the
   depth in the meaning. A recursive `runtime fn` becomes a function of
   that level (§2.8), after the unification and not part of it.

The meaning of a `Source` does not change in U5. Every step is a change to
the compile and its proof, and each leaves the tools running.

## 1. What is there

Checked against the branch of PR #551, 2026-11-11.

| | function (value level) | procedure (tree level) |
|---|---|---|
| record | `Function { parameters, body: StructuredRegion, result, lent }` | `Procedure { params, results, body: Stmt }` |
| called by | a region's `Call(callee, arguments, result)` | a statement's `Perform(procedure, args, results)` |
| meaning | a word and the file after: `program_run`, answered to a region as `call: Writers()` | a tree: `Source::performs(call, n, depth)`, the body run from `Procedure::enter` and read back by `Procedure::leave` |
| may call | functions before it in the list, so depth is static | any procedure, itself included; a call past `Source.depth` exits with 139 |
| values live in | registers by a checked placement (`Place` is `Into(register)` or `Folded`; there is no spill slot) | one home each for the whole program (`Home`: a static slot of the data region, or a register of `home_pool`) |
| frame | eight slots below the return address, for the caller-saved registers around a call | none of its own; the stack holds return addresses and what callers pushed |
| arguments | RDI, RSI, RDX, RCX, R8, R9 | the same six |
| results | one, in RAX | up to six, in the argument registers |
| what a call keeps | `callee_kept()`: RBX, RBP, R12 to R15, because a body never writes them (`leaves_all`) | nothing: the callee may write any home, so the caller pushes `out` less the results and pops them back (`Prog::pushes`, `pops`) |
| callee's words at entry | its parameters, placed where they arrive | "zero but the parameters" in the meaning; the code has whatever the homes hold, and a body that reads anything else is refused (`Procedure::fits`) |
| RSP | the frame, for the whole body | before 5a, not in the invariant: reloaded from a static slot before each CALL (`call_enters`, `Layout::frame_at`); since 5a the frame, in `Target::Held` |
| contract | `Site::Returns` from the label under `Stack::CalledOver` to `Stack::AnsweredOver`: result in RAX, `Kept(callee_kept())`, stores only below the entry and into lent spans (`Stack::WroteIn`), the file after in memory | `Target::Runs(Perform(…))`, continuation-passing over `Target::At` |
| linked by | induction on the list (`lower_program_lent_correct`) | induction on the room left (`Target::calls`), the callee at `Target::activation` |
| a call's code in a program | `Prog::call_lent`: RSP reloaded, arguments, lent homes as immediates, R10 carried in RBX, CALL, RAX to the result's home | `Prog::performs`: depth test and count, RSP reloaded, pushes, arguments, CALL, pops, count back, results to their homes |

Five facts in the code decide the design.

**The caller's side of a function call is already what a frame needs.** A
function's contract says memory is as it was but for stores below the
entry RSP and into lent spans. A caller whose words are stack words above
that RSP keeps them by that clause with nothing more to prove. Today the
program compiler turns the clause into "my data region is as it was"
(`Target::functions_run`); with words in the frame it reads the clause
directly.

**"Callee-saves was unprovable" is a fact about global homes.** The
procedures note records it: a claim speaks only of words live at its end,
and a register a callee must keep is some other activation's word, of
which the callee's claim knows nothing. With a frame, a kept register is a
stack word the prologue stored. The target already carries such words as a
ghost list read from the stack (`Target.frames`, `Target::FramesAt`: the
return addresses and what callers pushed), kept by every store into the
region (`Target::frames_store`) and every store below it
(`Target::frames_stack_store`). Saved registers join that list; nothing
about liveness enters.

**The invariant is opened in few places.** `Target::Held` is everywhere,
but what it is made of (`Target::Placed`, `Layout::Keeps`) is opened only
in the storage modules (`native_compile_region`, `_homes`, `_segments`,
`_perform`) and in the modules that store into the region (the Linux
calls, the command line, the byte nodes). Every word a statement reads or
writes goes through three functions, `Prog::word_to`, `word_from` and
`word_store`, and their lemmas (`goes_word_to_slot`, `goes_word_store`,
`goes_word_from` and the register cases).

**RSP is already spared.** `Target::Spares` says a write to a word's home
leaves every register that is no home and is not RBX, and RSP is one of
those. The leaf pool (`register_pool`) excludes RSP. Only the leaf's
`leaves_all` check, which today lists the home registers, has to name it.

**The machine model needs nothing new.** `AddRI32` exists, so a slot's
address is RSP plus an offset through RBX, and `Site::moves_load` and
`moves_store` are stated at any address. The stack's laws (`stored`,
`writable`, `canonical`, `keeps_code`) supply their premises as they do for
a push today (`Target::stack_store_read`, `stack_store_apart`,
`stack_store_holds`).

## 2. The design

### 2.1 Two levels, one machine

The value level is FunctionIR: `Function`, called from regions, total, no
recursion, lent buffers by their homes, exportable. The tree level is
`Source`: `Procedure`, called from statements, a tree over Linux's calls
with a depth. They stay two records and two tables, for three reasons.

- *The meanings differ in kind.* `Env::compute(call, region)` is a value
  because every callee answers with one. A callee that may exit, or run
  out of depth, has no value to give, and a region that called it would
  have to be a tree. The same line runs through any language with effects:
  a call inside an expression, and a call that is a statement.
- *The records cannot merge without a cycle.* `Stmt` holds regions, so a
  `Function` whose body was a `Stmt` would define FunctionIR in terms of
  `Source`, and the whole function compiler is proved over the region body.
- *The dependency is one way already.* Functions do not know procedures;
  `Source::performs` takes the functions' answers as a parameter. Linking
  one list by a depth and a list order at once would buy nothing.

What becomes one is everything below the meaning: the frame, the call
sequence, the registers kept, the contract a caller reasons from. And a
function is usable at the tree level by a theorem, not a wrapper: a call of
a function is a call whose tree is `Ret` (§2.5).

The one-compiler note's end state reads: "a function has a frame, System V
registers, buffers it is lent, and a body that may ask Linux for things; a
pure function is one whose body asks for nothing". That holds of the code
after U5. In the source, "a body that asks for nothing" is a `Function`,
and the name `Procedure` stays for the tree level until a later round has
a reason to rename it.

### 2.2 The frame

An activation entered at stack offset `i` (RSP there, the return address
on top):

```text
stack.at(i)                  the return address
…                            the s registers this function saves
stack.at(i - 8·(s + W))      its W word slots; RSP for the whole body
```

- **Slots.** Word `id` with home `InSlot` is the stack word at
  `RSP + 8·id`. `InReg(k)` is `home_register(k)`, as now.
- **Access.** `MovRR(Rbx, Rsp)`, `AddRI32(Rbx, 8·id)`, then the `Load` or
  `Store` a slot uses today. One instruction more than the static address
  costs; a `[rsp + disp32]` form in the stack model would make it one
  instruction in all (the model's `StackStore` and `StackLoad` take a
  byte displacement, which is too short for a file of words). That form is
  an optimisation with its own issue, and the function compiler's future
  spill slots want it too. *As built (5b):* `MovRI(Rbx, 8·id)`,
  `AddRR(Rbx, Rsp)`, forms the model already had.
- **RSP is the frame, in the invariant.** `Target::Held` gains
  `read_gpr(Rsp, g) = t.frame()`. The static frame slot
  (`Layout::frame_at`), its store at every entry and its load before every
  CALL go.
- **Entry.** At the label: make room for the saved registers
  (`AddRI8(Rsp, …)`), store each (`Spill`, a byte displacement reaches
  them), then make room for the words (`AddRI32(Rsp, …)`). RBX is saved
  first, since everything after uses it for addresses. Then the depth
  (§2.6), then each parameter from its argument register to its home.
  *As built (5b):* each register is saved by lowering RSP a word and a
  `Spill` at displacement zero (`Prog::saves`), then `MovRI(Rbx, 8·W)`,
  `SubRR(Rsp, Rbx)` (`frame_down`); RBX is scratch between statements
  and is not saved, which an export changes when it needs System V's
  set. *As built (5c):* the depth is counted first, at the label and
  through RAX and R11, which hold nothing there, so a call past the depth
  leaves before anything of the callee's is pushed; then RBX and the
  registers below are saved.
- **Exit.** Each result from its home to its register, the words' room
  given back, the saved registers reloaded, their room given back, RET.
- **What is saved.** RBX, and each register of the home pool that some
  word of the program lives in. With homes global to the program (they
  are, §2.7) that is one list for every procedure, computed once from the
  `Homes`. *As built (5c):* `Homes::kept`, RBX and of R12 to R15 and RBP
  those a word lives in. R10 is a home too, and the callee does not save
  it: every caller carries it in RBX (§2.3).
- **`main`.** The start-up saves the entry RSP for the command line as it
  does now, makes `main`'s frame below it, and sets each word that is live
  at `main`'s entry to zero in its home. Today such words must be slotted
  because static slots start zero (`homes.slotted(live)` in
  `Source::allocation_ok`); that condition goes. There are usually none.
  *As built (5b):* the start-up zeroes them (`Prog::zeroes`), and the
  condition stays for now: `Target::goes_zeroes` proves the store to a
  slot only, so a word live at `main`'s entry is still slotted. No
  allocator gives such a word a register.
- **The data region shrinks** to the buffers, the scratch range, the saved
  entry RSP and the room count.

A callee's fresh slots hold whatever the stack held. The meaning says
"zero but the parameters", and the two agree for the reason they agree
today: `Procedure::fits` refuses a body whose entry set is not within its
parameters, and `Target::Held` claims only live words (its file of slot
words is existential).

### 2.3 The convention

The internal convention is ours to choose
(`issues/runtime-extern-c-abi.md`: "keep native convention design free of
accidental C defaults"). U5 takes the function compiler's, because it is
proved and because it coincides with System V on everything an export
uses, so an export needs no adapter. Where it goes past System V it is our
own, and nothing outside sees it.

- **Arguments:** `argument_registers()`, at most six. A function lent
  buffers takes their homes first, as now.
- **Results:** the first in RAX. A procedure's second to sixth go in RDX,
  RCX, RSI, RDI, R8. System V returns a pair in RAX and RDX; the rest is
  the extension.
- **Kept:** `callee_kept()` and RSP. A function keeps them by never
  writing them, a procedure by saving the ones it uses.
- **R10** stays in the home pool. System V does not keep it and a function
  may write it, so every call carries it in RBX across the CALL, as
  `call_lent` does today. Taking R10 out of the pool instead would cost
  every program a register to save two moves at a call.
- **Memory:** stores below the entry RSP; stores into the file's buffers
  that the callee's meaning accounts for; and, for a procedure, the
  program's own bookkeeping in the data region (the scratch range, the
  room count).

A call site is then one function of the callee's label, the homes it is
lent, its arguments and its results: arguments to their registers, R10 to
RBX, CALL, RBX to R10, results to their homes. `Prog::performs` and
`Prog::call_lent` become it. `Prog::pushes`, `pops`, `call_enters` and
`call_leaves` go, with `goes_pushes`, `goes_pops` and the frame slot's
lemmas.

### 2.4 The invariant restated

```heather
// The region's buffers and bookkeeping, the command line, the frames above
// this activation, and this activation's slot words on the stack at RSP;
// every live word as the environment's in its home.
fn Target::Held(self t: Target, live: List<Nat>, env: Env, g: Gprs, m: X86Memory(t.r.profile)) → Type {
    Exists<List<BitVec(64)>>(λ slots => (slots.len() = t.words) ∧ (read_gpr(Rsp, g) = t.frame()) ∧
        t.Placed(env, m) ∧ t.FramesAt(m, slots ++ t.frames, t.index) ∧ t.homes.Agrees(live, env, numbers(slots), home_values(g)))
}
```

A sketch: the step fixes the spelling (`Agrees` reads slots as numbers
today, and the environment's own words no longer pass through `Placed`).
What changes under it:

- `Layout::Keeps` loses its words clause and keeps the buffers'.
  `Target::Framing` loses the frame slot and keeps the room count.
- The slot lemmas are proved over `FramesAt` by the stack's laws in place
  of the region's cells. The proofs exist in the shape of a push and a pop.
- Every rule that stores into the region already shows the frames kept
  (`Target::frames_store`); the slot words ride in the same list, so those
  rules lose an obligation (the word slots lie below the store) and gain
  none.
- Every rule that changes registers shows RSP kept. For the home writes
  that is `Target::Spares`; for a leaf it is the `leaves_all` check with
  RSP named; a SYSCALL keeps it by the Linux model.
- `Target::activation` moves the index down by the callee's frame, and
  `roomy` counts a level as a frame: the words, the saved registers and
  the return address.

What does not change: `Stmt::emit` above the three word functions, the
liveness check, the allocator and its Rust mirror (homes are still slot or
pool register), `Stmt::emit_runs`' cases for `Compute`, `Then`, `Branch`,
`Repeat`, `Exit`, the tree side entirely.

The theorem's premise changes in one place. Today a program with no
procedures needs no stack below its entry RSP; after U5 it needs `main`'s
frame, so `deep` (`native_compile_correct`, `Source::elf_simulates_paid`)
counts one level more than `Source.depth`.

### 2.5 The contract

```heather
// Function or procedure `f`, entered at stack offset `i` with its
// arguments, over the file `env` holds, with `t.room` levels of stack below.
fn Target::Entered(self t: Target, f: Callee, args: List<BitVec(64)>, env: Env, i: Nat) → MachineState<…> → Type
// Back at the return address: RSP above it, the results in their
// registers, `Kept(callee_kept(), s.gprs, u.gprs)`, the stack from `i + 8`
// up as it was (`Stack::Unchanged`), and the region placed with the file
// the callee left.
fn Target::Returned(self t: Target, s: MachineState<…>, results: List<BitVec(64)>, after: Buffers(), i: Nat) → MachineState<…> → Type

// Every callee runs as its tree: wherever the caller goes on from each
// return, the entry goes as the callee's tree bound to that.
fn Target::Performs(self t: Target, trees: Callee → List<BitVec(64)> → Env → ITree<Answer>(Events::linux())) → Type {
    (f: Callee) → (args: List<BitVec(64)>) → (env: Env) → (i: Nat) → (k: Answer → ITree<BitVec(64)>(Events::linux())) → t.Exiting(k) →
    (s: MachineState<…>) → t.Entered(f, args, env, i)(s) →
    ((results: List<BitVec(64)>) → (after: Buffers()) → (u: MachineState<…>) → t.Returned(s, results, after, i)(u) →
        SimPaid(t.io(), k(Answered(results, after)), u)) →
    SimPaid(t.io(), ITree::bind(Events::linux(), trees(f, args, env), k), s)
}
```

Again a sketch. `Answer` is what a call gives back, results and the file,
or an exit; it is `Flow` seen from the caller, and `Procedure::enter` and
`leave` are the two maps between an environment and it.

- **A procedure meets it** by `Stmt::emit_runs` at the callee's target,
  between its entry and exit code: the proof `Target::calls` has today,
  with the saved registers reloaded where the pushed words were popped.
  Induction on the room, as now.
- **A function meets it with a value.** Its tree is
  `Ret(Answered([answer.word], answer.buffers))` at
  `program_writers(functions)`. From `Site::CallsOver` the proof is the
  one inside `Target::functions_run`: a `Returns` is a silent run, a tree
  claim absorbs silent runs, and the lending's `InMemory` after is the
  region placed. The function compiler and its theorems are not touched;
  `Site::CallsOver` stays the export's contract, over any memory.
- **A call site is proved once** from `Target::Performs`, for `Perform`
  and for a region's `Call`: the statement after the call holds over the
  file the callee left, the caller's slot words are as they were by
  `Stack::Unchanged`, its pool registers by `Kept`, R10 by RBX.
- **The derived contract `native-procedure-contracts` asks for is this
  one.** Its per-slot footprint is the frame: a procedure owns its slots
  because they are below its caller's, which is the "real frame per
  activation" that issue names. Its negative control, a callee that
  writes a caller's slot, cannot be written in `Source` at all, since a
  procedure's words are its own by the meaning; the control that can be
  written is at the machine level, a hand-made callee that stores above
  its entry, refused by `Target::Performs`.

**As built (5c).** The contract is `Target::Callable`
(`native_compile_perform.hthr`), and it differs from the sketch in four
ways.

```heather
inductive Answer { Returned(results: List<BitVec(64)>, buffers: Buffers()), Gone(status: BitVec(64)) }

fn Target::Callable<A>(self t: Target, label, lent: Nat, accepts: List<BitVec(64)> → Env → Type,
    tree: List<BitVec(64)> → Env → ITree<A>(Events::linux()), answer: List<BitVec(64)> → Env → A → Answer) → Type {
    (env: Env) → (words: List<BitVec(64)>) → accepts(words, env) → (g0: Gprs) → g0.Holding(call_registers(), t.passed_homes(lent) ++ words) →
    (ret: BitVec(64)) → (above: List<BitVec(64)>) → t.index + 8 * above.len() <= t.stack.size →
    (k: A → ITree<BitVec(64)>(Events::linux())) → ((x: A) → t.Ends(answer(words, env, x), env, g0, ret, above, k(x))) →
    t.Goes(asm_labels(t.program, label), ITree::bind(Events::linux(), tree(words, env), k), λ s =>
        t.Bare(env, t.room, t.index - 8, Cons(ret, above), s.gprs, s.memory) ∧ (s.gprs = g0))
}
```

- **It is generic in what the callee's tree returns, with a reading of
  that as an `Answer`.** A contract in continuation form asks its caller
  for a continuation at every value of the tree's type. A procedure's
  site has one: its tree returns a `Flow` and the statement after the
  call is given at each (`Procedure::answer` reads a `Flow` as results
  and the file, or an exit). A function's site does not. What
  `Target::Functions` gives a region's `Call` is one tree, the rest of
  the region over the one value the function computes, so there is no
  continuation at any other `Answer` to hand over. A function therefore
  meets the contract at `A = True` with the tree `Ret(trivial)`, and its
  reading is the value: `function_answer(call, f)` is
  `Returned([call(…).word], call(…).buffers)`. One statement, two
  instances, and neither site is asked for what it cannot give.
- **`lent` is in it.** The buffer homes a callee is lent come first in
  the call registers (`Target::passed_homes(lent) ++ words`); a
  procedure is lent none, since a procedure of a target reaches the
  region by the layout.
- **One state predicate each end, not `Entered` and `Returned`.** The
  entry is `Target::Bare` at the callee's label, a word down, with the
  return address on top of whatever the caller has above (`above`) and
  the registers as the caller left them. The other end is
  `Target::Ends`, by cases on the answer. At a `Returned`: the RIP is
  the return address, `Bare` is back at the caller's offset with the
  same `above` over the file the callee left, the registers of
  `Homes::kept` read as they did at the entry, and the results are in
  `result_registers()`. At a `Gone`: an exit with that status is paid.
  That the caller's stack is as it was is `above` being the same list on
  both sides, which is `Stack::Unchanged` with nothing to unfold.
- **The name.** `Performs` is already the type of the meaning's callee
  table (`native_source`), and the elaborator refuses a method spelled
  like a name in scope; `Callee` is a record of the function compiler's
  program logic.

A call site is `Target::goes_calls` (`native_compile_function.hthr`),
proved once for any `A`: from `Target::Callable` at a label, and the
caller's claim after the call at each answer (`Target::Taken`, which
`Target::ends_taken` turns into the contract's `Ends`), the code of
`Prog::calls` runs as the callee's tree bound to the rest. A region's
`Call` uses it at `True` (`Target::functions_run`) and a `Perform` at
`Flow` (`Target::calls_of`).

- **A function is callable** (`Target::function_performs`) from
  `Target::Answered`, the function compiler's `CallsOver` at this
  profile, by what `functions_run` held inline before: the lending's
  cells are in memory at entry, the function's `Returns` is a silent run,
  and the region is placed after with what it stored
  (`Target::based_left`).
- **A procedure is callable** (`Target::Procedures`, in
  `native_compile_correct.hthr`) by induction on the room. With no room
  the count refuses and the tree is the depth's exit
  (`procedures_deep`); with room the body runs by `Stmt::emit_runs` at
  the callee's target, whose own calls are the contract a level down
  (`procedures_body`). Both start from `Target::goes_counted`, the label
  and the count. The top theorems' statements did not move.
- **Mutual recursion is the positive control.** `alternating` in
  `native_compile_tests`: two procedures over the same words calling
  each other, each keeping its parameter across its call, with a status
  that is another number if either calls itself or loses the word. Its
  binary runs in `procedures_run` (`crates/cli/tests/native_cat.rs`),
  with the shallow variant refused at the depth.
- **The machine-level negative control is not built.** A `¬
  Target::Callable` for a hand-made callee that stores above its entry
  needs a concrete target and an inversion of `SimPaid` at a state the
  callee reached, which no lemma gives yet; it is what
  `native-procedure-contracts` stays open for.

### 2.6 Depth

The meaning keeps its depth and its exit, for the reason the procedures
note gives: a finite stack can meet a depth exactly and cannot meet fuel.

The count moves from the call site into the procedure's entry and exit:
at entry, after RBX is saved, the room is read; at zero the code jumps to
the shared exit (`Prog::deep_exit`), otherwise it is counted down, and the
exit counts it back. The callee's claim then covers a call at depth zero
by itself (its tree there is `Ret(Exited(call_depth_status()))`), the call
site has no test, and it is the same code as a call of a function, which
has no depth. *As built (5c):* the room is read at the label, before
anything is pushed and through RAX and R11, so a refused call has used
its return address and nothing more; the stack bound takes that one word
(§3).

The stack bound is per level: a procedure's frame, and below the deepest
one the functions' frames as now.

### 2.7 What stays as it is, and why

- **Word ids and homes stay global to the program.** Every frame has a
  slot for every word of the file, as every level may push that many
  today, so the stack bound has the shape it has now. A file of words per
  procedure, each numbering its own from zero with its own homes, is what
  linking separately reflected procedures needs (§2.8), and it is a change
  to `Layout` under every emit; it goes with that round.
- **A procedure's buffers are the program's**, by number, at the layout's
  addresses. A function is lent a prefix of them by their homes. Lending
  any buffer, a slice of one, or a block of the frame is
  `issues/source-buffers-as-views.md`, which U5 does not take.
- **Two body compilers.** A statement compiles a leaf at a time over
  homes; a function compiles a whole region over a placement. Both hand
  their leaves to the one region lowering, and after U5 both sit in the
  same kind of frame under the same contract. Making them one is a
  register allocator with spilling over a whole body. That is an
  optimiser's question, not a joint in the proof, and the one-compiler
  note's §4 already says the levels stay.

### 2.8 What it opens for `rt`

Not part of U5, and listed so the unification is aimed at them.

- **A computation over `Io` calls a function**, a writer included: one
  `ETm` node, lowered to a `Compute` of a region `Call`, the buffer it
  hands over gone afterwards as a read's is. U4 step 4c-4 left this node
  out and said U5 would merge the layer over Linux into the layer over the
  file. That overstated it. The layers nest as their targets nest, `ETm`
  over the file layer over pure terms, because a statement is over regions
  and not beside them; one computation type with `Invoke` beside `Put`
  would still need its region lowering for every function without
  `Invoke`, the exports among them. The node is built once either way,
  and it does not depend on U5.
- **A computation over `Io` calls another** (`issues/rt-effectful-callees.md`):
  an `EFun` with parameters lowers to a `Procedure`, the call to
  `Perform`, and its case of `ETm::lower_sound` is the procedure's meaning
  (`Procedure::enter`, `leave`). `f::program` then links procedures as
  well as functions, which is where a file of words per procedure comes
  in.
- **Recursion in a `runtime fn`.** A function that calls itself other
  than last reflects to a procedure whose body `Perform`s itself, each
  call a statement (rt is already in a form where calls are bound one at a
  time). What it publishes is its tree at a depth: a value, the Heather
  function's, where the depth covers the recursion's own depth at that
  argument, and the exit otherwise. A pure recursive function is therefore
  a tree-level function that asks for nothing but depth. How the depth a
  call needs is stated (a generated companion function, a bound the user
  proves) is a surface question for its own note. This is the milestone
  `nh-procedures`' "a non-tail recursive function compiles" from a
  `runtime fn`; from the builder it holds today.

## 3. The steps

Each is a PR's worth, changes no meaning, and ends with the tools' GNU
gates passing on the new code.

- **5a. RSP is the frame** (built 2026-11-11). RSP in the invariant; the
  static frame slot, its store at each entry and its load before each CALL
  go. Words stay where they are and the caller still pushes. Small, and it
  settles how every rule shows RSP kept before the large step leans on it.
  *Runs:* every tool; `grep -F` for the procedures.

  What it settled:
  - *The invariant.* `home_values` reads RSP after the six pool registers,
    and `Target::Agreeing` is the homes' agreement and that seventh value
    being `t.frame()`. A write to any other register keeps the claim as
    before, by evaluation; `Target::held_rsp` reads RSP off it.
  - *What moves RSP moves the claim.* With RSP in `Held`, the claim cannot
    be stated at a displaced RSP, so a push, a pop, a CALL and a RET are
    each a move to another activation (`Target::activation`), through one
    lemma, `Target::held_moved`: RSP written with the address of offset
    `index`, the frames from there given. A pushed word is the top of the
    lower activation's frames, and so is a return address. `goes_pushes`
    and `goes_pops` are inductions over activations; the callee's entry
    and return are stated in the callee's own activation, and the call's
    proof (`Target::goes_calls` since 5c) names the four a call passes
    through.
  - *The proofs of an activation.* `Target` carries two proofs (`framed`,
    `roomy`), and a claim at an activation built with other proofs of the
    same facts is the same type only by unfolding. Statements that end in
    an activation they compute take those proofs as arguments
    (`(fr: …) → (ro: …) → …`), and `Target::held_proofs` changes them.
    Step 5b meets this again and may prefer a `Target` whose bounds are
    evaluated verdicts.
  - *The code.* The start-up is four items (was six), a call's way in six
    (was eight) and out four (was six), a procedure's entry its label and
    its exit its RET; a function call loses its two. The data region is a
    word shorter.
  - *What 5b replaces of it.* `goes_pushes` and `goes_pops` go with the
    pushes. `held_moved`, RSP in `Agreeing` and the entry and return
    stated in the callee's activation stay.
- **5b. Words in the frame, and the callee saves** (built 2026-11-11).
  Slot words on the stack; `main`'s frame made by the start-up and a
  procedure's by its entry, which saves what it must keep; pushes and
  pops go. The two land together because a push moves RSP under the
  slots it would be read from: keeping pushes over a frame would mean
  proving a biased addressing that the next step deletes. This is the
  step that re-proves the storage lemmas and rewrites
  `native_compile_perform`. *Runs:* every tool; a probe that recurses to
  its depth and one past it (`summing`, `summing_shallow`,
  `summed_input`), on a stack the theorem's `deep` premise sizes.

  What it settled:
  - *The invariant keeps its shape.* `Target::Placed` still has one
    function from offsets to bytes; a frame's words are read from it at
    ghost cells past the canonical boundary (`Layout::frame_cell`), where
    no region offset is, and a separate clause (`Target::Slots`) says the
    stack word at RSP plus eight times `i` reads as cell `i`. A store to
    the region or to another stack word keeps a frame by the lemmas that
    kept the region (`keeps_agree` takes "below the scratch range or past
    the layout", so a ghost cell is untouched by every region store). The
    statement proofs above `native_compile_segments` did not change.
  - *A frame is claimed over whatever the stack held.* `Stack.readable`
    gives every stack word a value, so a callee's frame needs no
    initialising: `Target::held_fresh` builds the claim at the lower RSP
    from the bytes found there, for a body with nothing live in a slot at
    its entry but its parameters, which the entry then stores. `main`
    reads its words before writing them (a word starts as zero), so the
    start-up zeroes the words live as `main` starts and no others
    (`Prog::zeroes`, `Target::goes_zeroes`). No assumption about the
    stack's contents at process entry was added.
  - *The caller's frame on return.* Between a CALL and its RET the claim
    is `Target::Bare`: the region's part of the invariant, the words above
    some stack offset as a list, and RSP. The callee's entry, body and
    exit store only below the caller's frame, so on return that list is
    the one the CALL left, and `Target::bare_caller` rebuilds the
    caller's claim from the witness it had before the call, the region's
    bytes taken from the callee's (`splice`). The registers the program's
    homes use are back because the callee saved and restored each
    (`goes_saves`, `goes_restores`); it saves all of them, since homes are
    still the program's and not the procedure's
    (`native-register-moves-and-convention`).
  - *A call's stack.* A return address, at most six saved registers and
    a frame: `8 * (words + 7)` bytes a level. `native_compile_correct`'s
    `deep` adds `8 * words` for `main`'s frame, so a program with no
    calls now asks for that much stack (cat's theorems carry it).
    `Layout::call_fits` no longer bounds the words live across a call,
    and `Refusal` 14's count went with the pushes.
  - *RBX is written twice by a slot access* (`MovRI(Rbx, 8 * id)`,
    `AddRR(Rbx, Rsp)`, then the word's load or store), and `Gprs` is a
    function, so two writes of one register are the one write only
    pointwise. The register file after an access is named
    (`Target::slot_gprs`, `rbx_gprs`, `rbx_known_gprs`,
    native_compile_segments) with its read lemmas and a case split for
    the sites that state it. Filed as `native-gprs-writes-not-canonical`;
    `x86-stack-wide-displacement` would remove the access's RBX
    altogether.
  - *The proofs of an activation again.* The callee's activation is built
    inside the CALL's continuation, where its frames (the saved values of
    the registers as the CALL found them, the return address, the
    caller's cells) are known; its bounds come from `Gprs::saved_len` and
    `Homes::registers_few` by `omega`. Nothing needed bounds as evaluated
    verdicts.
  - *`write-elf`.* The entry is stated over the set live before `main`,
    which the allocation's check already spells (`{p}_ck_0`,
    `Source::entry_of`, `Source::entry_at`), so the certificate does not
    work the set out again; the frame's items are counted back from the
    initial bytes' stores.
  - *What 5c takes from it.* `goes_callee_entry` and `goes_callee_return`
    are stated over `Bare` and a register file `g0` the callee must give
    back, which is the shape of the one contract; the count's move into
    the entry changes who runs `call_enters`, not these.
- **5c. One call, one contract.** The count moves into the entry, results
  move to RAX and on, `Perform` and `Call` emit through one function;
  the contract is stated (`Target::Callable`, §2.5), a procedure and a
  function each an instance, and the call site proved from it once.
  *Runs:* the same tools, and two procedures calling each other. It
  landed in two halves, both 2026-11-11: the call sequence, then the
  contract. The machine-level control of §2.5 is not built, and
  `native-procedure-contracts` stays open for it.

  What the call sequence settled:
  - *One function emits every call.* `Prog::calls(layout, label, lent,
    arguments)`: the arguments to the call registers after the homes
    lent, R10 to RBX, the CALL, RBX to R10. `Prog::performs` is it with
    nothing lent and the results taken from `result_registers()`;
    `Prog::call_lent` is it with RAX taken, and is the code it was by
    conversion, so the function compiler's proofs did not move.
    `call_enters` and `call_leaves` went.
  - *The count is the callee's.* `Prog::count_down` after the label and
    `Prog::count_up` before the frame closes. Their lemmas
    (`Target::goes_count_down`, `goes_count_up`) take whatever else the
    site claims as a predicate closed under a write of the two scratch
    registers and a store to the room slot, so one statement serves the
    callee before it has a frame and after it has given its results.
    Between a callee's label and its frame the count is not yet the
    callee's, so `Target::Based` and `Target::Bare` carry the room as an
    argument beside the target's.
  - *A refused call has pushed its return address.* The test is in the
    callee, after the CALL. `Target.roomy` asks a word past the levels,
    and `native_compile_correct`'s `deep` is `(depth * (8 * (words + 7)) +
    80 * functions) + 8 * (words + 1) <= stack`. A program with no calls
    carries the word too (cat's theorems), the price of one statement for
    every source.
  - *What a callee keeps.* `Homes::kept` (§2.2). Not R10: saved by the
    callee it would be a seventh word a level, and the caller's carry in
    RBX is needed for functions anyway (`Homes::returned` reads every
    home's register back after a call from the two). A call still takes
    a return address, at most six words of registers and a frame.
  - *One proof of the way to a callee.* The arguments, R10 into RBX
    (`Target::homes_carried`, the function compiler's lemma), the CALL,
    then the label and the count. Since the contract this is two lemmas,
    the caller's side in `Target::goes_calls` and the callee's in
    `Target::goes_counted`.
  - *A gap the first several-parameter probe found.* The allocator built
    a body's interference from its statements' writes, and no statement
    writes a parameter the body only reads, so two such parameters got
    one register and `Procedure::fits` refused the procedure. The entry
    writes the parameters with what is live as the body starts, and the
    graph and the fallback's check now say so (`List::bodies_graph`,
    `bodies_check`, native_alloc). `spreading` in `native_compile_tests`
    holds it: three parameters and three results, a status that tells
    any two out of place.
  - *What the contract takes from it.* Past its count a callee is claimed
    by `Target::Bare` at the return address with one call less of room
    and the registers as the CALL left them but RAX, R11 and RSP; at its
    RET, by `Bare` past that address with the room back, the registers it
    keeps as they were, and the results in theirs. That pair is the
    contract to state, and a function's `CallsOver` to read as an
    instance of.

  What the contract settled (§2.5, "As built", has the statement):
  - *One call site.* `Target::goes_calls` replaces the function
    compiler's inline proof in `functions_run` and the procedure
    compiler's `goes_called`, `perform_deep` and `perform_call`. It is
    the only proof that walks a `Prog::calls`.
  - *The answer type is the instance's.* A function at `True`, a
    procedure at `Flow`; why is in §2.5.
  - *The procedure's induction is on the contract.* `Source::calls_at`
    was an induction on the depth whose step proved a whole call. It is
    now `Target::calls_of` (a `Perform` from the contract) over
    `procedures_deep` and `procedures_body`, and the step proves only a
    callee, entry to return.
  - *The function side reads the region through `Based`.* The lemmas
    that place a lending before a call and read it after
    (`buffer_readable`, `lent_sized`, `in_memory`, `based_left`) are over
    `Target::Based` and the frames, so they serve a callee's entry, where
    there is no `Held`. `Layout::buffers_byte` is the buffers' half of
    `Layout::keeps_byte` for the same reason.
  - *What went.* `Target::held_left`, `held_stack_store`, `Gprs::args_in`
    and `homes_back`, each a special case of a lemma the contract's
    proofs use.
- **5d. One byte lowering** (U4's step 4d). A leaf with byte nodes goes
  through the shared lowering, its buffers' homes loaded as immediates
  the way `Layout::homes_block` loads them for a callee, and
  `native_compile_bytes`' own code goes. *Runs:* `tr` and the tools that
  index a buffer.

Then **E**, the export, as ordered. The three `rt` items of §2.8 are
rounds after the unification; they are independent of E and of each
other, and which comes first is a choice about what the lexer and the
first recursive component need.

## 4. Decisions

| question | decision | why |
|---|---|---|
| one table of callables or two | two, value level and tree level | a region is a total function; §2.1 |
| where words live | the activation's frame, at RSP | the caller keeps them by the callee's memory clause; callee-saves becomes provable |
| frame pointer | RSP, in the invariant | it is spared already; an export has no data region to keep a frame's address in |
| slot addressing | through RBX from RSP now, `[rsp + disp32]` as a follow-on | no change to the machine model in U5 |
| convention | the function compiler's; System V on what an export uses | proved already; no adapter at the export |
| R10 | stays a home, carried in RBX at every call | a register for every program against two moves at a call |
| where the depth is counted | the procedure's entry and exit | one call sequence; the callee's claim covers depth zero |
| per-procedure words and homes | not in U5 | needed by linking procedures, built there |
| the two body compilers | stay | an optimiser's question; one-compiler note §4 |
| `ETm` and the file layer | nest; do not merge | their targets nest; §2.8 |

## 5. Issues this touches

| issue | role |
|---|---|
| `native-one-compiler` | owns the order; U5 is 5a to 5d |
| `native-procedure-contracts` | 5c is its contract; closes there |
| `native-register-moves-and-convention` | 5b and 5c fix the convention; per-procedure homes and moves between homes stay with it |
| `native-procedures-write-elf-capacity` | untouched; the Rust mirror of the allocator still skips procedures |
| `source-buffers-as-views` | not taken; §2.7 |
| `rt-effectful-callees` | the second item of §2.8 |
| `function-ir-verified-leaf-frame`, `function-ir-verified-live-spills` | the function compiler's own frame, untouched |
| new: `x86-stack-wide-displacement` | `[rsp + disp32]` loads and stores in the stack model |
| new: `runtime-fn-recursion` | the third item of §2.8, with the surface question |
| new: `rt-io-calls-functions` | the first item of §2.8, the node 4c-4 left out |
