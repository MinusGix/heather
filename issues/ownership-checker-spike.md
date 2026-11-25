---
title: The ownership checker on a straight-line fragment: check, its residuals, and check_sound
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The first experiment of `docs/language/ownership-design.md` §15.6: the checker of §15.3 and its once-theorem `check_sound` (§15.4) on the smallest fragment that can refute the design. Library only.

## Scope

One module. Straight-line code over lists of numbers:

- **The fragment.** Atoms are a literal or a word variable. Operations: `Set(y, x, i, v)` (`let y = x.set(i, v)`, in place: `y` takes `x`'s buffer), `Get(z, x, i)`, `View(t, x, lo, n)` (`let t = &x[lo..lo+n]`, live to the end), `Read(z, t, i)`, `Clone(y, x)`.
- **`eval1`**: the meaning, lists as values; a view is its window's value.
- **`run2`**: the run over one buffer per object (a name followed through its in-place updates is one object); a view is a buffer and an offset.
- **`check(f, plan)`**: one forward pass with a state per place, answering `None` or the residuals it defers (a window and an index that must be apart), as closed data with a cheap meaning.
- **`check_sound`**: a closed verdict and the residuals' holding give `run2 = eval1`, from buffers that hold the parameters' lists.
- **Three programs**: a linear one accepted with no residual (its instance has no premise); a view then a write then a read of the view, accepted by one residual proved from a source hypothesis, with a `¬` theorem that the two runs differ where the residual fails; a read of a name after its update, refused, with a `¬` theorem that the two runs do differ.

## What refutes the design

Say plainly in the log if any of these happens, with the evidence: the invariant needs more than the place states (a separation algebra, say); residuals cannot be closed data with a cheap meaning; following a name through its in-place updates makes frozen tracking awkward; the kernel cannot evaluate `check` at tolerable cost (read `docs/proof-patterns.md` on closed verdicts and on measuring a proof's cost).

## Done when

The module and its probes pass the library gate, `check_sound` is proved, the three programs and their controls are theorems, and the log says what the proof needed and whether any refuting condition was met.

## What it assumes from elsewhere

- **[[ownership-paths]]** (closed) gives `Path::elem_in`, `PathIn.frame`, `PathIn::agree_apart`, `Path::hold_while_store`; `span_set.hthr` gives `Span::apart_sound`.
- **[[ownership-discipline-over-code]]** owns the judgment this is the first piece of.

## Log

- 2026-11-25: Built and proved. `lib/lang/ownership/place_check.hthr` holds the fragment, `eval1`, `run2`, `check` and `check_sound`. `lib/_tests/lang/ownership/place_check_tests.hthr` holds the three programs, their controls, probes of the verdict at literals and of the plan, and a 36-operation program. None of the refuting conditions was met.

  **Proved.** `check_sound(f, plan, rs, ok: check(f, plan) = Some(rs), env, file, rep: Rep(f, plan, env, file), holds: Residual::All(rs, eval1(f, env))): run2(f, plan, env.words, file) = eval1(f, env)`. The stages are `step_set`, `step_get`, `step_view`, `step_read`, `step_clone` (dispatched by `Op::step`), `Inv::moved` (what a set and a clone share), `license_sound` and `check_ops_sound`. The programs: `linear_checked` and `linear_sound` (no residual premise); `frozen_checked` and `frozen_sound` (one residual, `let apart: (Span(0, k).apart(Span(j, 1)).IsTrue()) = omega(h)`); `frozen_control_rep`, `frozen_control_fails` and `frozen_control` (at `k = 1, j = 0` every premise holds except the residual, and the runs give 9 and 5); `stale_refused` and `stale_control` (7 against 3). Also: `beside_*` and `inside_*` (apart and overlapping at literals, decided with no residual, the overlap refused with a `¬` control), `versions_checked` and `versions_bad_refused` (a window followed through `x`, `x1`, `x2`), `cloned_checked`, `cloned_same_buffer_refused`, `shared_parameters_refused`, and `long_checked` and `long_sound`.

  **Choices.** Each is the sensible default the brief asked for.
  - Three name spaces (lists, views, words), each bound in order from its parameters; a binder must be the next name of its space, and an atom may read only bound words. The meaning's environments are append-only.
  - A run's view carries its length, as a slice does, and a read past the length is 0, which is what the window's value gives. With the `(buffer, lo)` of the brief, `Read(z, t, i)` with `i >= n` reads past the window in `run2` but 0 in `eval1`. That needs a bound residual, and program 2 would then need `0 < k` too. A get or set past a list's end does the same thing in both runs, so this fragment has no bound obligations.
  - The checker checks the plan: a set's result is on its source's buffer, a clone's is on a free one, and the parameters' buffers are distinct. That leaves `Rep` with two facts: each parameter's buffer holds its list, and the file has every buffer the plan names (`room`, because a store past a list's end is dropped).
  - A residual is `Residual { lo, n, i: Atom }`, meaning `Span(lo, n).apart(Span(i, 1))`. The verdict is decided where all three atoms are literals and deferred otherwise.
  - Clone's source must be an owned name, not a view.

  **1. Is the place-state invariant enough? Yes.** `Inv` has three parts:
  - bookkeeping: the run's words equal the meaning's, and the counts agree;
  - `held`: a held buffer's holder is bound, the plan puts it there, and the buffer holds the holder's value. This is "a usable place reads its value";
  - `views`: each run view is the checker's window, read in the words the meaning ends with; its buffer is held; and it reads the meaning's window value.

  Nothing more is needed: no `Pcm`, `Sep`, `Held` algebra, history or ghost map. The one refinement is that the state is kept per object (buffer), not per name. The table records which name holds each buffer now, and the views each name their buffer and window. A name is gone when it no longer holds its buffer. Kept per name as §15.3 writes it, the invariant needs two more clauses: live names are on distinct buffers, and every live name on a view's buffer lists the window. Those two clauses are the per-object table rederived. §15.3 now records this.

  The write under a frozen window is framed by `PathIn::agree_apart(Path::elem_in(i), Span(lo, n), …)`, with the disjointness from the residual's verdict by one `omega` (`frame_write`). No lemma was missing from `path.hthr`, `list_path.hthr` or `span_set.hthr`, and none was added.

  The invariant is stated in the final words `ws` (what `eval1` ends with), a fixed parameter of the induction: `eval_ops(Cons(o, rest), s).words` is `eval_ops(rest, o.eval1(s)).words` by unfolding. That is why residual and window atoms are read once, with no clause saying they stay valid as words are bound. The only extra lemma is that words only grow (`eval_ops_grows`, `Atom::val_stable`).

  **2. Are residuals workable as closed data? Yes.** `Residual::All(rs, ws)` is a conjunction of `Span` verdicts, which `omega` reads through `Span::apart`. Two costs:
  - `omega` does not unfold `Residual::Holds` (it refuses the goal), so the instance spells the verdict in a typed `let` and passes it where `Holds` is expected. The kernel converts `Var(0).val(eval1(…))` to `k` by running the meaning's word spine at open lists. That is cheap: `frozen_sound` is about 6k kernel steps, and `long_sound` with 21 residuals is about the same.
  - Residuals are not de-duplicated. The 36-operation program defers 21 copies of one fact, which `long_sound` discharges with one `omega` and a replicate lemma.

  Residual atoms may name words read from a list. Their meaning stays the words the meaning builds.

  **3. Does "one object through its updates" stay light? Yes.** The frozen windows belong to the buffer, so `x1 = x.set(…)` only moves the holder. `versions_checked` follows a window through two versions with no lemma per version, and `versions_bad_refused` refuses a write into it through the second version.

  **4. What does the kernel pay?** Measured per `docs/proof-patterns.md` §7, on a fresh `--cache-dir`, with steps from `--timings`. The closed verdicts: linear about 1.2k steps, frozen 1.4k, stale 0.7k, the 36-operation program with 21 residuals 25k (15 ms at the gate). Generated programs of 12, 24, 48, 96 and 192 operations: 5.4k, 13.7k, 39k, 128k and 453k steps. Each doubling multiplies the cost by 2.5, then 2.9, 3.2 and 3.5, tending to quadratic. Programs with no views at all, of 16 to 128 operations, grow the same way (7.3k, 18.5k, 54k, 178k).

  So name lookup dominates, not the checker: unary names compared by `same`, `nth` into the plan, the holder table as a closure with a layer per write, and `++ [v]` and `len()` on the views. Each is linear per operation. The one cost the checker owes is a write scanning its object's live views. Filed as [[place-check-name-lookup-cost]]; it is tolerable here (192 operations, 0.27 s).

  The theorem itself elaborates in about 2 s for the whole module. `step_view` is the largest at 0.17 s and 84k steps.

  **5. What the next experiment changes** (filed as [[ownership-checker-call-and-write-view]]):
  - A write view needs `out` per span. An object's state becomes per span (whole, frozen windows, out windows), not one holder and a table of read views.
  - `Inv.held` weakens to: the buffer holds the holder's value outside its out windows, and each out window holds its viewer's value. This is the first real test of "usable implies current" against a loan.
  - The meaning's object environment, append-only here, must allow eager write-back to a name. While `x` is lent it cannot be set, so the name is a stable target.
  - `Residual` becomes a sum (apart, and below the window's length for a write through it).
  - Deaths need a removal from the views table.
  - A call needs a signature as data and the callee's `check_sound` as the premise the caller cites. `Inv` must then be stated against a frame (the caller's other buffers unchanged).

  The get, read, view and clone steps carry over unchanged. The set step's frame becomes `PathIn::agree_apart` over `Path::window` instead of `Path::elem`. `Clone` stays aside: cloning a view is a copy of its window and adds nothing.
