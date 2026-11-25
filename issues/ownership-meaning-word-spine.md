---
title: The ownership meaning keeps its words as a snoc list read by position, so a pin reading late words is quadratic in the body
status: closed
labels: [ownership,library,performance]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Measured in [[ownership-residuals-from-source-proofs]]: the pin `mean_fn(w, f, xs, [i]).word = f(xs, i, …)` by `refl` costs 1.0k, 1.9k, 4.6k, 13.9k, 47.8k, 177k and 683k kernel steps at bodies of 8 to 512 statements (0.37 s at 512): about 2.6·N². `call_check`'s `Sem.words` grows by `s.words ++ [x]` and a word is read by position (`atom::word`, `nth`), so reading the last word peels every append. A residual that reads an early word is lazy and linear; the pin reads the answer, bound last.

`docs/native/runtime-fn-setups-design.md` §4.3 states its pin linear in the function; whether its interpreter's environment has the same shape was not checked.

## Wanted

The meaning's environment in a shape whose read of a recent word is constant and whose growth is constant: newest first with indices from the end (de Bruijn), or a written-out record per function. Whichever the one language (§14 item 2) takes, measure its pin at doubling sizes before building on it.

## Done when

The pin at 512 statements is linear in the measured series.

## Log

- 2026-11-25: Done in [[ownership-site-facts-into-the-checker]] (`lib/lang/ownership/call_check.hthr`, `Env`). The words are the parameters read by position and the body's words newest first with their count: `get(w)` reads a parameter where `w` is below the parameter count, else the local at `n - (w + 1)`, so a parameter and a recent word cost the same constant. Chosen over a de Bruijn list alone because a body reads its parameters at every statement (newest first alone is quadratic there, a scratch model measured it) and over a snoc list because the pin reads the newest word. Measured, fresh store per run, pin `mean_fn(…).word = src(…)` by `refl` at bodies of 64, 128, 256, 512 statements: through the parameter 3.9k, 7.2k, 13.9k, 28.7k kernel steps; through a chain of lets (each statement reads the word the last bound) 19.3k, 38.3k, 76.3k, 154k. Linear; the snoc pin was 683k at 512. Reading an old local late is still linear in its distance; no body here does it at every statement. Several objects: the environment holds words only, so a second object adds nothing here.
