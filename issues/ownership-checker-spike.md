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
