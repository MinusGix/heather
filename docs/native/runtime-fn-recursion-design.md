# Recursion in a `runtime fn`: procedures, levels and the depth a call needs

Status: proposal (2026-11-20), the short surface note that
`issues/runtime-fn-recursion.md` asks for before code. It replaces that issue's
"depth in the meaning": since #806 to #812 a program's stack room is asked
for in levels of checked calls, a call past them is a refusal of the
compiled program, and the room costs the same to check at any number of
levels (`docs/native/native-procedure-frames-design.md` §7.4).

## 1. What is there

- **The back end can recurse.** A `Source` procedure may `Perform` itself or
  a cycle of others. The compile checks a call only at the entry of a
  procedure that reaches itself, asks for `Source.levels` levels of such
  calls, and `Source::compiled_levels` proves, for every source it accepts,
  that every run whose checked calls nest at most `levels` deep is a run of
  the compiled program, never refused. Past them the program stops at the
  call, with the call-depth status, its output so far the source's.
- **The front end cannot.** A `runtime fn` reflects to `rt`
  (`lib/native/runtime/rt.hthr`). A pure one lowers to FunctionIR regions,
  whose functions call only functions before them; a self-call in tail
  position becomes one `Loop` (`rt_loop`, setups design §7.4) and any other
  is refused, "a recursive call that is not a loop needs procedures". A
  function over `Io` lowers to statements (`rt_io_lower`), but `ETm` has
  no call of another effectful function (`issues/rt-effectful-callees.md`).
- **The probes meet it first** (`docs/native/dogfooding-plan.md` §2.1, row 8,
  `port_depth`): nesting depth, the shape of recursive descent, is the first
  recursion anyone writes, and the parser Heather-in-Heather needs is that
  shape.

## 2. The route: a recursion is a call between statements

A region is a total function of its words, so what it calls must answer
with a value; a statement is a tree, so what it calls may ask Linux for
things, run out of levels or exit (procedures-are-functions §0 item 4).
A non-tail recursion can run out of levels, so it is a call between
statements. That fixes the route (built in the order of §6, pure recursion first):

1. **`ETm` calls an `EFun`** (`rt-effectful-callees`, not yet built): an
   `ETm` node calling another function of the program on variables, binding
   its answers and continuing. It lowers to a `Source` procedure and a
   `Perform`; its case of `ETm::lower_sound` is the callee's meaning
   (`Procedure::enter`, `leave`). Nothing recursive yet.
2. **The callee may be the caller, or a cycle.** With calls between
   statements built, a self-call is the same node naming entry 0; mutual
   recursion between `runtime fn`s is a cycle of entries. The compile's
   ranks and checks already find which entries reach themselves.
3. **A pure recursive function takes the statement lane with no effects.**
   Its body is an `ETm` with no `Io` node. Its meaning as a statement is a
   value or a stop at the levels, which is all §4 needs.

One consequence is a rule rather than a choice: **recursion lifts its
callers to statements.** A pure function that calls a recursive one cannot
stay a region, because its call can stop. The refusal says so and names the
recursive callee; the generator then reflects the caller as a statement
too. A tail recursion still becomes a loop, and a loop stays a region.

## 3. Levels: stated by the program

`Source.levels` belongs to the whole program, as the stack does, so it is
stated where the program is, not on each recursive function.

- **Recommended: written, and required where the call graph has a cycle.**
  `runtime fn main(…) levels 10000 { … }` (or the builder's `room(n, …)`). A
  program with a recursive callee and no `levels` is refused with the
  sentence "this program calls `parse_expr`, which calls itself: say how
  many nested calls it has room for, `levels n`". The number is the
  writer's, it is the number the theorem quotes, and nothing about it
  depends on the frames the compiler picked.
- **The alternative: as many as fit.** The compile picks the most levels
  whose room fits a stack size the system contract presumes (Linux's
  default 8 MiB). The writer writes nothing, but the theorem then quotes a
  number they never saw, and a change to a frame changes it. Proposed as a
  later convenience (`levels fit`), not the default.

Past 8 MiB the room is more than Linux's default stack gives; the system
contract's mapped stack (`docs/native/system-contract-design.md` §4.1) is the route
there, and until it lands a `levels` whose room passes the presumed stack
is refused at compile time with the room it would need.

## 4. What it publishes: the depth a call needs

The guarantee should be in the function's terms: no bytes, no fuel.

- **`Fun::depth`, once, in `rt`.** The nesting of a function's checked calls
  at an argument, defined once over the reflected body by the same
  recursion as the function: a leaf is 0, a branch the depth of the arm
  taken, a sequence the most of its parts, and a self-call one more than
  the callee's depth at its arguments. It is bounded by the function's own
  measure (a fuel of `measure(x) + 1`, as `Measured` loops bound their
  passes), so it is a total function, and at a closed argument it
  evaluates by `refl`. The generator publishes `f::depth(x)` as that
  function at `f`'s program, one equation, with nothing elaborated per
  function.
- **The theorem.** For every input `x` with `f::depth(x) <= levels`, the
  compiled program's run is the function's: its answer is `f(x)` (for a
  whole program, its output and exit). For any `x`, the compiled run is
  the source's up to its first refused call, which stops with the
  call-depth status. Proved once in `rt`: the lowering's meaning under
  `Source::calls_within` at `k` levels agrees with the function wherever
  the depth fits, by induction on the depth, with the self-call's
  continuation read through `f::ext` and `f::irrel` as `Fun::Guarded` reads
  a measured loop's (setups design §16.10). Then `Source::compiled_levels`
  carries it to the machine.
- **Bounds are the writer's theorems.** `f::depth(x) <= g(x)` is an ordinary
  theorem about an ordinary function, proved by `f`'s functional induction,
  and it is exactly what guarantee 4 (procedure-frames design §7) needs to
  check the room once at startup and not per call. Nothing in this note
  needs it.

The alternative to `Fun::depth` in `rt` is a companion the elaborator
generates per function (`f::depth` by the same recursion, like `f::ext`).
It reads better in a goal but adds a generator per function, and its
agreement with the reflected body would itself need proving. `rt`'s
definition needs neither.

## 5. What it shares with the depth-free tree

Programs over `Io` are read through the coinductive tree (`Source::tree_co`,
`rt_io_program`), which still nests calls by a depth; the depth-free
co tree is its own thread ("Remove the call-depth limit from the fuel-free
meaning"). The theorem of §4 needs the levels in that meaning too: the co
tree's calls cut past `k` counted levels, as `Source::calls_within` cuts
the inductive one. Whichever lands second states its result with the
other's.

## 6. Steps

Reordered after reading the `Io` lowering (2026-11-20): a pure callee
leaves the world and every buffer as they were, so its call is answered
by a value or a stop and nothing else, while an `Io` callee's own buffers
share the program's one file of buffers with its caller's, which a
contract for it must sort out first. So pure recursion comes first.

1. **Statements read with their calls answered.** `Stmt::thread` today does
   nothing at a `Perform` (`Stmt::straight` refuses it). A threading that
   takes each call's answer as a function of the caller's environment
   (`Stmt::thread_by`), and its reading theorem under the premise that
   each call's tree reads as its answer, is the statement-level piece the
   rest stands on.
2. **A pure recursive function as a procedure.** `ETm` gains a call of a
   pure procedure on word variables, its result a fresh word; the lowering
   emits `Perform`, and `ETm::lower_sound` gains its case from the premise
   of step 1. The procedure's own body is the function's term with each
   self-call such a node. Its answer at `k` levels is the function's value
   where `Fun::depth` fits and the call-depth stop otherwise, proved once
   by induction on the levels.
3. **The levels reach the co tree.** `Source::tree_co` charges calls in
   bytes as the compiled program does; with the charges of
   `Source::charges_room`, a call within the levels is never refused
   there either, which makes the answer of step 2 the procedure's tree.
4. **The generator.** The reflector reads a non-tail self-call as the new
   node, the program states `levels`, and `f::depth` and the theorem of
   §4 are published. `port_depth` compiles, runs to its value within the
   levels and stops one past; then a recursive-descent recogniser over a
   byte span.
5. **Calls between `Io` functions** (`rt-effectful-callees`), with a
   buffer contract, and recursion over `Io` through them.
6. **Guarantee 4**, separately: a proved `f::depth(x) <= g(size)`, the room
   computed and checked once at startup (the room is a cheap formula in
   the levels since #812).

### 6.1 Built so far (2026-11-20)

- **Step 1** is `Stmt::thread_by` and `Stmt::reads_where`
  (`lib/native/native_source_io.hthr`): a statement with no loop, each
  call it makes `ok` and read as its answer, reads as its threading.
- **Step 2** took a narrower node than an `ETm` call: `PTm`
  (`lib/native/runtime/rt_proc.hthr`), a pure body over `rt`'s `Tm` with
  `Recur(p, args, rest)`, a call of procedure `p` on word variables. Its
  meaning reads calls through the procedures' meanings, `PTm::need` is its
  depth, and `PTm::lower_sound` proves its statements. A call of a
  recursive function cannot sit in a region (`Tm::CallsAgree` quantifies
  over every callee), which is why the node is on the statement lane and
  `Tm` is unchanged. `PDef::bodies` turns a list of `PTm` definitions into
  procedures meeting `Source::PureBodies`, given the one pin the generator
  will supply (`PDef::Unfolds`, the meaning's equations) and which entries
  fit within how many levels (`PDef::Fits`). `Source::pure_reads` (`lib/native/native_source_pure.hthr`)
  then reads every call within the levels as its value, by induction on
  the levels and, at one level, on the ranks of unchecked calls.
- **Step 3**, the part about charges: `Source::pure_program_reads`
  (`lib/native/native_compile_pure.hthr`) takes the charges and ranks of a
  compile that accepted the source, so a compiled source's `main`, its
  calls run as deep as they go, reads as `main` threaded with each call
  answered, for every run whose calls keep within `Source.levels`. Joining
  the co tree to the machine is the depth-free tree's thread (§5).
- **The depth became a predicate, `PDef::fits(k, p, xs)`**: whether the
  call runs within `k` levels, by recursion on `k` (each call it makes fits
  within `k - 1`). It needs no measure and no fuel, so it is total for any
  recursion, terminating or not, and at a closed argument it is `refl`;
  `PDef::fits_fit` proves it is what the bodies keep wherever every call
  is counted (a self-recursive function's are). §4's `f::depth(x) <= levels`
  reads as `f::fits(levels, x) = True`, and a depth bound is the writer's
  theorem `f::fits(g(x), x) = True`. A cycle with unchecked calls in it
  would need the ranks in the recursion too; the generator refuses it for
  now.
- **Step 4, the guard and a whole program.** `Tm::to_ptm` reads a reflected
  body's calls of itself (`Call(0, …)`) as `Recur`s, under `if` and `if h:`
  too. `PTm::Guarded` is `Fun::Guarded`'s statement over a `PTm`, which the
  generator can prove as it proves a measured loop's; `PDef::bodies_one`
  takes it to every obligation. `PTm::program_reads`
  (`lib/native/runtime/rt_proc_program.hthr`) is a pure program's theorem:
  main a `PTm` over no parameters calling the recursive function's
  procedure, its value the exit status; for any compile that accepts it,
  where main's calls fit within `Source.levels`, the run exits with main's
  value and leaves the world as it was. `crates/cli/tests/native_recursion.rs`
  runs `sum(10)` compiled: 55 within 16 levels, the call-depth status 139
  within 9.
- A closed probe (`lib/_tests/native/runtime/rt_proc_tests.hthr`): a
  non-tail recursive sum lowers, fits within 10 levels at 10 and not 9,
  its statements run to 55 at 10 with the world untouched, and a wrong-arity call and a bit-valued body are
  refused.

## 7. Decisions for Minus

1. `levels` written and required where there is a cycle (recommended), or
   picked to fit a presumed stack by default.
2. Recursion lifts its callers to statements (§2): a consequence, listed so
   it is seen.
3. `Fun::depth` defined once in `rt` (recommended), or a companion
   generated per function.
