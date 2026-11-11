---
title: A defaulted parameter cannot be handed to a recursive call, and blocks applying the result in the same list
status: open
labels: [frontend,syntax,ergonomics]
area: language
created: 2026-11-11
updated: 2026-11-11
---

A function whose last parameter has a default (`buffers: Buffers() := Nil`)
cannot give that parameter in two places a library wants to.

1. **Its own recursive call.** A recursive call takes positional arguments
   only, so a recursive function cannot hand its defaulted parameter on by
   name, and the parameter has no positional slot. The library's way round
   is two declarations: the recursion with the parameter first
   (`eval_nodes_over(buffers, nodes, values)`), and a wrapper that fixes
   the default.
2. **Over-application.** A function that returns a function
   (`eval_nodes(nodes, values): Valuation()`, applied on as
   `eval_nodes(nodes, values, w, id)`) stops accepting the further
   arguments once it has a defaulted parameter: "`eval_nodes` takes 2
   argument(s) by position, found 4". Adding a default to such a function
   breaks every caller that applied its result in the same argument list,
   though none of them names the new parameter.

Found 2026-11-11 giving FunctionIR's meaning and evaluator their buffers
(docs/native-one-compiler-design.md §2.3): `eval_nodes`,
`StructuredRegion::eval`, `NodesHold`, `Function::Computes`.

## Wanted

- A recursive call accepts `name := value` for a defaulted parameter, and
  omits it as any other call does.
- Positional arguments past the positional parameters apply the result, as
  they do for a function with no defaults; or the refusal says to write
  `f(a, b)(c, d)`, which already works.

## Done when

`fn f(xs: List<Nat>, k: Nat := 0) → Nat → Nat` can recurse as
`f(rest, k := k)` and be called as `f(xs, 3)` meaning `f(xs)(3)`, or each
refusal names the spelling that works, with a probe of each under
`lib/_tests`.
