---
title: "grind: a near match's hole solution that is no node of the graph is dropped"
status: open
labels: [tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

A near match with free binders asks `Defeq` with holes and looks each
solution up among the graph's nodes (docs/grind-design.md §13.4). Two cases
end the question though the instance exists:

- The solution is a term the graph does not hold (`?ys := g(zs)` where no
  node is `g(zs)`). The instance would bring that term in, as an ordinary
  instance's sides do. Interning it needs the solution's handles while the
  holes are still solved (`Spine` of a solved hole answers committed
  handles, so `intern` over them, without the top `whole` mark that would
  cite the hole), and `resolve_nears` would have to thread the graph.
- The question was answered before the node it needs was added by a later
  round. `NearTried.asked` keeps it from being asked again, since `Defeq`
  reads terms; the lookup alone could be retried over the nodes added since
  (as `upto` does for drawing one binder), keeping the solutions as nodes
  or as interned terms.

Neither has a probe that needs it yet; this is where to look when one does.
