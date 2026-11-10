---
title: Past a hundred comparisons a runtime fn meets its generator's limits
status: open
labels: [native,runtime-fn,performance]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-10
updated: 2026-11-10
---

With the emission's cost down
([[native-function-emission-one-statement]]), a single `runtime fn` a
little past a hundred comparisons is refused before its certificate is
written, by its generator. Measured on the cloud box at width one, each
function constants under comparisons of its argument:

| shape | result |
|---|---|
| 100-leaf balanced tree | certifies; 38 of its 39 seconds are the generator |
| 110-leaf, 120-leaf tree | `runtime fn …: the tactic returned an implausibly large Expr, after 2419 requests` |
| 64-arm `else if` chain | certifies |
| 100-arm chain | `the kernel rejected …::agrees: OutOfFuel` |

Three things, probably separate:

- **The reflector's plausibility cap.** The `Expr` a tactic may return is
  bounded, and a hundred and ten leaves' reflected body is past it. The cap
  is a guard against a runaway tactic, not a statement about programs;
  it wants to scale with the declaration, or to count what the reflector
  was asked for.
- **`agrees` for a deep chain.** The agreement theorem of a chain is one
  conversion whose depth is the chain's: it ran out between 64 and 100
  arms. A tree of the same size is fine, so the cost is in the nesting
  (each arm's meaning under every condition before it), the same shape
  `Tm::lower_sound` instantiated at a closed body always has.
- **The generator's time.** The 64-leaf tree takes about seven seconds
  end to end and the 100-leaf tree thirty-nine, nearly all before the
  first untrusted read: steeper than the function's size by a wide margin,
  and not attributed (reflection requests, the `Compile` instance, the
  `agrees` check).

## Done when

Each of the three is attributed, and a 200-leaf tree and a 100-arm chain
either compile or are refused by a limit that is written down with its
reason.
