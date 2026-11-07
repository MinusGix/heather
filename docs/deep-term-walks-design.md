# Deep terms and the kernel's walks

Status: change 1 (§3) built 2026-11-07; §4 and §5 are directions, not plans.
Follows [`issues/long-string-literal-stack-overflow.md`] (closed by
`Term::VecItems`) and closes [`issues/long-vector-conversion-depth.md`].

## 1. The problem

Almost every kernel walk is a structural recursion: one native frame per
level of the term it walks. That is the natural way to write a type checker,
and for terms people write it is fine, because terms people write are
shallow. Data is not. A list of a thousand elements is a term a thousand
`Cons` deep, a string is a list of characters, a vector is a chain of pairs,
a successor numeral is a chain of `Succ`. When such a value reaches the
kernel — as a literal, or as the reduct of a computation it has to compare —
each walk over it pays one frame per element, and somewhere between a few
thousand and a few tens of thousands of elements one of them overflows the
8 MiB stack and the process aborts.

The depth budget ([`docs/native-depth-budget-design.md`]) turned some of
these aborts into `OutOfFuel` refusals: evaluation and conversion count
their frames and refuse at `NATIVE_DEPTH_LIMIT`. That bounds the walks but
does not make them any less linear in depth, so a refusal is all a deep
value gets. The question this note answers is what it takes for a deep
*data* value to be checked, substituted and compared at all.

## 2. What `VecItems` does and does not do

`Term::VecItems` (PR #473) is a representation fix: a long vector literal
is one node holding an array, so its term is one level deep at any length
and every walk over it is a loop over the array. It stays the right
representation for literals — it is also smaller, hashes in one pass, and
is one image record — and nothing below replaces it.

It does not help a deep term that is not a literal: the unfolded chain the
conversion compares when two separately built vectors meet, a list built by
a fold, a long `Cons(…)` written out, a successor chain. It also leaves the
kernel's walks shaped so that the next long form needs its own node. Minus
asked (2026-11-07) for the kernel change that removes the depth limit for
data rather than for one spelling of it.

## 3. Change 1: loop over the spine (built)

Data is deep in one direction. A list, a vector chain, a `Succ` chain, a
`Wf` constructor tree's last child: each node has small children and one
child that carries the rest. Walks recurse into every child, so their
native depth is the length of that one path, the *spine*. Change 1 makes
the spine a loop in each walk that met it, and leaves every other child's
recursion as it was. It is keyed on depth, not on the form: a walk behaves
exactly as before until it is [`SPINE_ITERATE_AT`] (128) frames deep, so
shallow terms — all of the library — take the old path, and only the deep
tail of a deep term takes the new one.

`term::spine_child` names, for a node, the child most likely to carry the
rest of a chain: a pair's `snd` (or `fst` when `snd` is a leaf, as in a
`(rest, x)` chain), an injection's payload, a `Sup`'s children tuple, a
successor's predecessor, an application's argument. The choice is a cost
heuristic only: guessing wrong costs one ordinary frame per node, never a
different answer. What each walk does with it:

### 3.1 Bounds (`bounds.rs`)

`term_use` computes a node's free-variable summary from its children's and
caches it by node. Past the threshold, before computing a missed node, it
walks down the spine collecting the nodes not yet cached
(`Cache::warm_spine`), then computes them deepest first. Each of those
computations then finds its spine child cached and recurses only into the
small children; the loop is the heap-held path. Results are unchanged: the
cache answers the same summary either way.

### 3.2 Substitution (`subst.rs`)

`sub_tm` rebuilds a node from its mapped children. Past the threshold
(thread-local `SUB_DEPTH`), `sub_tm_spine` collects the path down spine
children while each node is a spine form and is not answered by the
prologue (no-op skip, variable, memo hit), maps the bottom with the ordinary
walk at depth zero, and rebuilds upward in a loop: each node's other
children are mapped by ordinary recursion in their original field order
(`map_spine_node`), its spine child is the accumulated result. Sharing is
kept the way the recursive walk keeps it: a node whose children did not
change is returned as itself, and a shared node's result is memoized
(`sub_tm_settled`, the epilogue both paths now share; the path's own clone
is discounted when counting sharers).

### 3.3 Typing (`typing.rs`)

The checker answers yes or no, and a rule's premises are a conjunction, so
the order they are judged in is free. A `tm_check` met
[`SPINE_ITERATE_AT`] open checks deep is not descended into: it is pushed on
`Tc::deferred` with its environment and expected type, and counted as
passing for now. The outermost check (depth zero) drains the queue before
it answers: it pops each item and judges it from depth one, and an item may
queue more, which the same loop takes. A long list's spine is therefore
checked as a sequence of 128-deep slices, at constant native depth.

What keeps this sound:

- **No verdict leaves with a queued premise.** Only depth zero answers to
  the caller, and it drains first; a refusal at any point clears the queue
  and is the answer.
- **Memos.** A node's memo entry (the typing memo, the closed-type and
  closed-signature memos) is written when its own frame's rules succeed,
  which with premises queued is before the whole verdict is in. Within one
  outermost check that is harmless — the queued premise is judged before
  anything is accepted. After a *refused* outermost check that queued
  anything, the entries could stand on the failed premise, so the checker
  forgets those memos (`Tc::forget_after_refusal`). A refusal ends almost
  every gate, so the reset costs nothing measured.
- **Refusal location** (`locate_refusal`) still finds the failing check:
  the drained item is judged through the same rules, in noting mode.

### 3.4 Conversion (`conv.rs`)

The same argument holds for conversion's premises. `Conv::tm` past the
threshold (after the identity and memo shortcuts, which answer without
descending) queues the comparison on `Conv::deferred`. Three points needed
care:

- **Settling.** Every frame that returns the depth to zero — `Conv::tm`,
  `Conv::ty`, and the Nat tail loop `tm_nat_tail`, the only three that take
  a depth slot — drains the queue after success and drops it after a
  failure (`settle_at_top`). The root entries hold no slot, so their
  children settle themselves.
- **Speculation.** `delta_lazy` runs an attempt whose `NotConvertible`
  means "try unfolding instead", not "refuse". An attempt is a verdict of
  its own: it records the queue length, drains what it queued before it
  counts as a success, and truncates back to the mark when it fails, so a
  failed attempt's premises are never judged against the comparison that
  follows it. The attempt drains at its own depth, which may itself be past
  the threshold, so the threshold counts from the depth the queue is being
  drained at (`defer_base`); counted from zero, every popped comparison was
  queued straight back until the fuel ran out (the library gate's
  `x86_64_block` found this).
- **One drain at a time.** A comparison popped by the depth-zero drain
  returns to depth zero itself; it leaves the queue to the running drain
  (`draining_at_top`) instead of starting a nested one, so draining a long
  chain stays one native frame.
- **Memo.** A comparison whose subtree queued anything memoizes its
  `true` *provisionally* (`deferred_pushed` counts pushes; `tm` and
  `tm_nat_tail` compare the count before and after), and so does any
  success recorded while the queue is non-empty, since it may stand on a
  provisional entry's memo hit. The provisional entries are taken back when
  their queue is dropped: a failed δ-attempt takes back those made since
  its mark, a refusal at depth zero takes back all, and a successful drain
  at depth zero with no attempt open makes them final. Not memoizing them
  at all was the first version; a shared subterm then compared once per
  occurrence, and a `refl` over `CReal` sequences in `creal_tests` ran out
  of fuel. A `false` is always the subtree's own failure and is memoized
  as before.

### 3.5 What it buys

`crates/kernel/tests/deep_terms.rs` runs each walk over a 100,000-element
chain on an 8 MiB thread: drop, shift, typecheck, compare two separately
built chains, substitute into an open chain, refuse chains that differ at
the bottom, refuse an ill-typed bottom element, and check and compare a
successor chain. `bitvec_values.rs` now compares two separately built
20,000-element `VecItems` nodes by value (it pinned 500 before, under the
depth budget); that comparison is quadratic in time, because each unfolded
tail is a fresh node whose bounds walk the live window
(`issues/vec-items-window-bounds.md`). At the surface, `s() = "aaa…"` and `"aaa…" ++ "b" =
"aaa…b"` at 3,000 characters, refused `OutOfFuel` before, check.

The depth budget is untouched: a deep *computation* (a non-tail recursion
in a program) is still refused at `NATIVE_DEPTH_LIMIT`, because its depth
is in reduction, not in a data spine the walk can queue.

## 4. Change 2: refuse or grow at the stack for what is left (not built)

Some recursion change 1 does not reach: walks it was not applied to (§6),
and deep terms whose depth is not on a spine (a deeply left-nested
application, a tower of binders). For those the options are:

- **Extend the depth budget** to the walks that still recurse without a
  count — typing's syntax walk, `syntax_eq`, the hashers — so each refuses
  at a bound instead of aborting. This is the budget design's own move and
  costs a counter per walk. It is the cheap, always-correct option.
- **Grow the stack** (`stacker`-style: check the remaining stack at a walk's
  entry and continue on a fresh segment). The budget note rejected this
  (§6 there: it hides the abort without bounding anything, and the kernel
  would be total only up to the machine's memory), and the kernel has zero
  dependencies, so it would be hand-written `asm` in the trusted base.
  Change 1 makes the case weaker still: the deep inputs that matter are now
  loops.
- **A larger stack for the gate's threads.** The workers already run on a
  sized stack (`issues/kernel-worker-stack-below-depth-budget.md`); raising
  it moves every limit by a constant factor and is a configuration change,
  not a design.

The first is the recommendation if a non-spine deep input is ever met.

## 5. Change 3: fully iterative walks (not recommended)

Every walk could be written as an explicit-stack machine, as the evaluator's
trampoline is for its tail positions. That removes native depth from the
kernel entirely, but it rewrites the checker — tens of rules, each with a
continuation per premise — in a form much harder to read against the
rules in `docs/delam/04–06`, which is what the trusted base is for. Deferral
(§3.3–3.4) gets the data case for a few dozen lines because premises of a
yes/no judgment commute; the full machine would also have to carry results
back (inferred types, rebuilt terms), which is where the cost is. Not worth
it while §3 and §4 cover what is met.

## 6. What still recurses

- **The parser.** A written-out `Cons(1, Cons(1, …))` checks at 1,500
  levels and aborts in `heather_syntax::parser` at 2,000, before the kernel
  sees it. Its literal spelling, `[1, 1, …]`, has no limit (#473), and the
  lint already tells the user to write that.
- **Elaborator walks** over kernel terms (emission walk, module image
  writer and reader, Merkle hashing of a term that is not `VecItems`). They
  meet deep terms only when the elaborator emits one, which literals no
  longer do; the image writer's own bound is
  `issues/module-image-writer-ignores-depth-budget.md`.
- **`syntax_eq` and the kernel's hashers** over non-`VecItems` chains: not
  met by any reproducer; the same `spine_child` loop applies if one is.
- **`Drop`** of a deep chain was already iterative enough for 100,000
  elements on 8 MiB (the test pins it).
- **Deep computation**, by design (§3.5).

## 7. Cost

Below the threshold every walk runs its old code; the added cost is one
counter compare per `tm_check`, `Conv::tm`, `sub_tm` and bounds miss, which
`scripts/bench --check` gates. Past it, typing and conversion pay one queue
push and pop per deferred premise (an `Env` clone each), substitution one
path vector per spine, bounds one warm-up walk per spine. A
queued comparison's ancestors are memoized provisionally, which costs a
log entry each until the depth-zero drain.
