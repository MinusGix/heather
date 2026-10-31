# Procedures in the native compiler — design

Status: **proposed 2026-10-31**, slice 1 landing with it. Owner:
`issues/native-compiled-procedures.md` (milestone `nh-procedures`, round R8
of `docs/compiler-milestones-proposal.md`). It draws in
`issues/native-procedure-contracts.md` and
`issues/native-register-moves-and-convention.md` where they are needed to
make a call compile, and leaves the rest of them open (§8).

Today a native tool is a closed `Source` (`lib/native/native_source.hthr`)
whose procedures are Heather functions returning an `Act`, inlined where
they are called (`lib/native/native_build.hthr`). That has two walls: code
grows once per call site, not once per helper, and recursion that is not a
tail loop cannot be written at all. This note fixes what a procedure is in
the source, what a call means, how a call compiles, how the compile is
proved once, and the order the pieces land in.

## 0. Recommendation

- A **procedure** is a statement with parameters, results and locals, kept
  in a table beside `main` (`Source.procedures`). A call is a new statement,
  `Perform(procedure, args, results)`.
- **Words are passed by value and are the procedure's own; buffers are
  shared.** A call copies the arguments into the parameters, runs the body,
  then gives the caller back its own values of the callee's locals, with the
  results copied out. A procedure changes a buffer in place.
- **Calls nest at most `Source.depth` deep.** The call one deeper exits
  with a fixed status (`call_depth_status`, 139). This is the source's
  meaning, not a property of the machine, so the compiled code has nothing
  to approximate.
- The meaning is **by depth, not by fuel**: a call at depth `d` runs its
  body at `d - 1`, so the denotation is total by structural recursion on
  the depth and then on the statement. Fuel still bounds loops, as now.
- **Compiled, each procedure is emitted once**, after `main`, at a label of
  its own. A call is a CALL; the procedure's frame is on the process stack
  (`X86Profile::process`, `StackPlaced`, PR #309). The callee saves its
  locals' current values in its frame on entry and puts them back before it
  returns (callee-saves-its-own-words). Words keep their one home each, as
  `docs/native-register-allocation-design.md` §2 fixed; a frame is where
  the caller's values wait.
- **The proof stays the one proof.** The stack frames are a ghost list in
  the `Target`, read through the same access as the command line above the
  data region. Every existing rule already keeps that access, so no rule
  but the new ones learns about the stack. A procedure's contract is
  `Stmt::emit_runs` at the callee's target: derived, never proved per
  procedure (the move `native-procedure-contracts` asks for).

## 1. The source

```heather
// A procedure: its parameters and results (word ids of its own), the
// words it owns (each restored for its caller), and its body.
record Procedure { params: List<Nat>, results: List<Nat>, locals: List<Nat>, body: Stmt }

inductive Stmt {
    …,
    // Procedure `procedure`, its parameters given the words `args`, its
    // results put in `results`.
    Perform(procedure: Nat, args: List<Nat>, results: List<Nat>),
}

record Source { functions, buffers, words, main,
    procedures: List<Procedure> := [], depth: Nat := 0 }
```

Ids are global: a procedure's words are ids of the one word file, and the
builder gives each procedure ids of its own. Nothing in the meaning needs
them disjoint; the compile is simpler when `locals` covers every word the
body writes (§4.2), and the builder makes it so.

## 2. What a call means

```text
Perform(p, args, results) at depth d, env:
  d = 0:            Exited(call_depth_status)
  d = d' + 1:       let P = procedures[p]
                    let entry = env with P.params := env's args (all read first)
                    bind(P.body at depth d', entry, λ flow =>
                      Onward(e) => Onward(e with P.locals := env's,
                                            then results := e's P.results)
                      Exited(s) => Exited(s))
```

The callee sees the caller's words (it is a deterministic reading, and a
callee that reads a word it never wrote reads the caller's value). On
return every local the callee owns is the caller's again, the results are
copied out after that (so a result may be one of the callee's own locals,
which recursion needs), and the buffers are as the callee left them. A word
outside `locals` that the body writes flows back to the caller: the
meaning is defined by `locals`, whatever it holds, which keeps the compile
free of any frame property of the source (§4.2).

`Stmt::denote` takes the meaning of a call as a parameter, a `Performs()`
handler, and is otherwise unchanged. `Source::performs(call, n, d)` is the
handler at depth `d`, by recursion on `d`. `Source::denote(args)`'s tree at
fuel `n` is `main` at depth `src.depth`. Fuel is shared by every loop at
every depth, as `Program::bind` shares it; `grows` is proved for any
handler that grows, and `performs` grows by induction on the depth.

**Why a depth and not fuel.** A tree cut at fuel `n` is a lower
approximation, and a machine meets the whole family only if it can do what
every fuel allows. No machine can recurse without bound in a finite stack,
so a fuel-cut call would make every compiled recursion unsound. A depth
that is part of the meaning is exact: the machine counts activations and
exits at the same call the source does. It is the same choice the heap
round makes for arena exhaustion (N4: "arena exhaustion as a defined
exit"). A program whose calls never nest past its depth never sees the
status, and the theorem's stack premise (§5) says how much stack that
needs.

*`mrec`*: the issue asked whether `mrec` over the fuelled `Program` spends
fuel per call. With a depth, the question disappears: the handler is
`mrec`'s unrolling at depth `d`, and no call spends fuel.

## 3. Words across a call: the convention

- **Arguments** go in RDI, RSI, RDX, RCX, R8, R9 (SysV's order), at most
  six; **results** come back in the same registers, at most six. None is in
  the home pool (`home_pool`, native_alloc), and the prologue and epilogue
  use only RAX and RBX beside them.
- **Homes are global.** A word has one home for the whole program, in a
  register or its slot, as now. A procedure's code keeps every home it does
  not write, because that is what the check already proves of any
  statement's code (`Target::Held`).
- **Callee saves its own.** The callee spills its locals from their homes to
  its frame on entry and reloads them before it returns. A caller saves
  nothing. So recursion is safe: an inner activation saves the outer one's
  locals before it overwrites any.
- **Every word but the callee's locals passes through.** The body is
  compiled with `results ∪ (all words − locals)` live after it, so its
  claim carries every other word through the call. The price is liveness:
  at a call, every word outside the callee's locals that the body does not
  write counts as live. That keeps such words out of a register they could
  have shared, and keeps a word live at `main`'s start in its slot. A
  per-call-site pass-through set, with each procedure's clobber set, is the
  refinement, and it is `native-register-moves-and-convention`'s (§8).

## 4. The code

### 4.1 Layout

The data region gains two slots past the saved entry RSP: `sp`, the current
activation's frame address, and `room`, the depth left. The entry code
stores `src.depth` into `room` and the entry RSP into `sp`.

### 4.2 A call, the prologue and the epilogue

```text
caller:     each arg word into its argument register (word_to)
            RSP := [sp]                   ; the caller's own frame top
            CALL P                        ; return address pushed
            each result register into its result word's home (word_from)

P:          RAX := [room]; TEST; JE deep  ; d = 0: exit(call_depth_status)
            [room] := RAX - 1
            RSP -= 8 · |locals|
            each local: RAX := home; [RSP + 8i] := RAX
            [sp] := RSP
            each argument register into its parameter's home
            body                          ; compiled with results ∪ others live
            each result into its result register
            RSP := [sp]
            each local: RAX := [RSP + 8i]; home := RAX
            RSP += 8 · |locals|
            [sp] := RSP + 8               ; the caller's frame top
            [room] := [room] + 1
            RET
```

Body code may leave RSP anywhere (nothing proves it is kept, and nothing
needs it): `sp` is the truth, and every CALL and the epilogue reload RSP
from it. A frame is `8 · (|locals| + 1)` bytes; a local's slot is a
`[rsp + disp8]` spill (x86_64_stack's form), so a procedure owns at most 15
locals until a disp32 form lands.

Each procedure is emitted once, after `main`'s closing exit; the shared
`deep` exit sits after the last one. `Prog::laid_out`'s one check covers
the CALLs as it covers the jumps.

### 4.3 What the check asks

`Homes` gains each procedure's entry set (the body's `live_in`, declared by
the allocator and checked, as a loop's set is, so that a recursive call
reads the declared set and the check needs no fixpoint). The check refuses a
call with more than six arguments or results, and a procedure with more
than 15 locals. It need not refuse a body that writes a word outside
`locals`: that word is live after the body (it is outside `locals`), so the
body's claim carries the value it wrote back to the caller, which is what
§2 says it means.

## 5. The proof

- **Frames as a ghost list.** `Target` gains `frames` (the bytes from the
  current `sp` to the stack's top: each activation's saved locals and
  return address) and `room`. `Target::Stacking` gains one conjunct: the
  `sp` slot holds `top − frames.len()`, the `room` slot holds `room`, and the
  memory from there up reads `frames`, all through `Target::argv()` (the
  access that reads only above the region). `Target::stacking_store` already
  keeps any fact read through that access across every store into the
  region, and the syscall rules keep it across Linux's writes, so the
  existing rules carry the frames unchanged; only `Stacking`'s eleven
  projections are renumbered.
- **New rules**: CALL (one machine step, the push a store above the region
  and below `sp`), RET, a spill and a reload at `[rsp + disp8]`, and the
  lemma that a stack store keeps the region's cells
  (`DataRegion::process_stack_keeps_data` is its process instance).
- **The procedure's claim** is the body's `Target::Runs` at the target
  whose `frames` is the callee's frame on the caller's, and whose `room` is
  one less, with the epilogue and RET as the continuation. It is proved for
  every procedure at once, by induction on the depth: the `Perform` case of
  `Stmt::emit_runs` at depth `d + 1` cites every procedure's claim at depth
  `d`. That is the paper's linking theorem (Abate et al.,
  `docs/wp-preserving-compilation-survey.md` §4, Theorem 3), by induction on
  the depth instead of Löb.
- **`native_compile_correct`** gains a stack: a `Stack` of the profile
  above the region, its top the entry RSP, at least
  `8 · (depth · (largest frame) + 1)` bytes deep. The ELF theorem's
  `StackPlaced` gives it with `depth ≤ io_stack_limit()`, so a program whose
  depth needs more than 128 KiB is refused by `write-elf`.

## 6. Why callee-saves into a frame, not words addressed in the frame

The issue's scope reads "a real frame per activation". The design keeps a
real frame per activation on the process stack, but addresses a word at its
home, not at `[rsp + 8i]`. The alternative, a procedure's words living only
in its frame, would give every word load and store a stack-relative form,
and every rule of `native_compile_*` would have to prove RSP kept across
its code. Saving into the frame adds one spill and one reload per local per
call and touches no existing rule. Words homed in the frame stay possible
later as a home kind (`InFrame(k)`) beside `InSlot` and `InReg(k)`, with
the frame's base in `sp`.

## 7. Slices

1. **The source** (this note's PR): `Procedure`, `Perform`, `Source.depth`,
   `Stmt::denote` over a `Performs()` handler, `Source::performs`, `grows`
   for both, the liveness of a call, and probes run by evaluation (a
   recursive sum that uses a local after the call, and the depth exit). The
   compile refuses `Perform` (`emit` is `None`), so the theorem is unchanged
   but for the handler it now quantifies over.
2. **The compile and its proof**: §4 and §5. Done when a source with a
   helper called from two sites and a non-tail recursion compiles and the
   compile is proved.
3. **`write-elf` and the builder**: a `proc` form in `native_build` whose
   locals the builder numbers, `Source::spelled` and the Rust mirrors
   (`crates/cli/src/native`), and an ELF test that runs the recursion.
4. **`grep -F`**, with the line-buffer helper a procedure, against GNU's
   tests under `LC_ALL=C`.

## 8. Left open, each with an owner

- Per-call-site pass-through sets and per-procedure clobber sets, so that a
  word outside a callee's locals needn't be live across a call, and moves
  between homes: `issues/native-register-moves-and-convention.md`.
- A per-slot footprint and a relational frame for a `Proved` contract, the
  shared-counter control and the negative control:
  `issues/native-procedure-contracts.md`. This design derives the contract
  and needs no footprint, because the callee's words are its own by
  construction and buffers are shared.
- Words homed in the frame (§6), and a disp32 spill for more than 15
  locals: to be filed when a procedure needs them.
