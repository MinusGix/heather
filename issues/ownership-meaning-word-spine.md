---
title: The ownership meaning keeps its words as a snoc list read by position, so a pin reading late words is quadratic in the body
status: open
labels: [ownership,library,performance]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Measured in [[ownership-residuals-from-source-proofs]]: the pin `mean_fn(w, f, xs, [i]).word = f(xs, i, …)` by `refl` costs 1.0k, 1.9k, 4.6k, 13.9k, 47.8k, 177k and 683k kernel steps at bodies of 8 to 512 statements (0.37 s at 512): about 2.6·N². `call_check`'s `Sem.words` grows by `s.words ++ [x]` and a word is read by position (`atom::word`, `nth`), so reading the last word peels every append. A residual that reads an early word is lazy and linear; the pin reads the answer, bound last.

`docs/native/runtime-fn-setups-design.md` §4.3's pin is linear in the function; this fragment's meaning is the outlier.

## Wanted

The meaning's environment in a shape whose read of a recent word is constant and whose growth is constant: newest first with indices from the end (de Bruijn), or a written-out record per function. Whichever the one language (§14 item 2) takes, measure its pin at doubling sizes before building on it.

## Done when

The pin at 512 statements is linear in the measured series.
