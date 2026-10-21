# Interaction trees, first round: the core library (`it-core`)

Date: 2026-10-21. Question 2 of
[interaction-trees-container-model](../issues/interaction-trees-container-model.md),
first half: the library that
[`docs/interaction-trees-fit.md`](interaction-trees-fit.md) §2 and §4 argued
for, now that tier-2 inductives with value parameters let it be written
(PRs #88 and #89). The code is [`lib/std/itree.hthr`](../lib/std/itree.hthr),
the client is [`docs/showcase/itree_client.hthr`](showcase/itree_client.hthr),
and the tests are `crates/elab/tests/lib_std_itree.rs`.

The second round (`it-refinement`) adds traces, `is_trace_of`, trace
refinement, the bridge to `converges`/`fuel_monotone`, and a state handler
into world threading. Its consumer is round S1 of
[`docs/native-program-logic-design.md`](native-program-logic-design.md)
(`issues/native-linux-spec.md`), and this round is shaped for it.

## What landed

| Piece | Spelling |
| --- | --- |
| Events as a container | `record Events { Cmd: Type, Resp: Cmd → Type }`, `Events::sum(D, E)`, `Events::none()` |
| Container morphisms (the paper's `E -< F`) | `record EventMap(E, F) { cmd, back }`, `EventMap::left`/`right` |
| The tree | `inductive ITree<R>(E: Events) { Ret(r: R), Tau(t), Vis(c: E.Cmd, k: E.Resp(c) → ITree<R>(E)), Cut }` |
| Operations | `trigger`, `bind`, `map`, `translate` |
| Loops | `inductive Step<A, B> { Continue(a), Break(b) }`, `ITree::iter(E, n, body, a)` |
| Handlers | `ITree::interp(E, F, h, t)` with `h: (c: E.Cmd) → ITree<E.Resp(c)>(F)` |
| Recursion as events | `ITree::mrec(D, E, body, n, t)`, `ITree::rec(D, E, body, n, d)` |
| Equivalence | `ITree::Same`, reflexive, symmetric, transitive, a congruence for `bind` |
| Laws by `refl` | `bind_ret_l`, `bind_tau`, `bind_vis`, `bind_cut`, `bind_trigger`, `iter_zero`, `iter_succ`, `interp_ret`/`tau`/`vis`, `mrec_zero`, `mrec_call`, `mrec_pass` |
| Laws up to `Same` | `bind_ret_r`, `bind_assoc`, `map_id`, `interp_bind`, `interp_trigger` |

## Decisions

**A `Cut` leaf, not a fuel-indexed type.** A tree is a finite value; `iter`
and `mrec` take the fuel as an argument and stop at `Cut` when it runs out.
`Cut` means "nothing is claimed past here", which is the reading round 2 gives
it: its only trace is the empty one. A program's meaning is the family of its
unrollings, and that family is round 2's object (refinement quantifies over
the fuel). Keeping the fuel an argument, rather than a type index, keeps every
tree at one type and lets `bind` and `interp` need no fuel at all.

**`Tau` stays.** The fuel already makes every tree finite, so `Tau` is not
there for guardedness. It is there so that the trees match the paper's (the
Coq probe's depth-indexed result is stated over them), so that `iter` marks
each time round, and so that round 2's trace equivalence can be shown to
absorb it. `iter` puts one `Tau` before each further pass and `mrec` one
before each call; `interp` adds none, since it is structural.

**The equivalence is structural and has no depth index.** The laws through
`Vis` (right identity, associativity, `interp` over `bind`) are not
equations: two trees agreeing under every answer are equal only with funext
([inductive-tier2-w-lowering](inductive-tier2-w-lowering.md) §12 item 8). The
container-model issue planned to state them up to the depth-indexed
bisimilarity of its Coq probe. That relation exists for *coinductive* trees,
where the index approximates an infinite object. Here a tree is already
finite, so the index has nothing to approximate: `Same` is plain structural
equality with the continuations compared pointwise, defined by recursion on
one tree, and fuel does the index's job one level up, across the family.
The weak equivalence that does absorb `Tau` (eutt) is round 2's trace
equivalence, which the paper's §7 shows is the same thing for deterministic
trees.

**`Same` is read off the left tree alone.** Each case says "the right tree is
this constructor, with children so related":

```heather
fn ITree::Same<R>(E: Events, t: ITree<R>(E), u: ITree<R>(E)) → Type {
    match t {
        Ret(r) => u = Ret(r),
        Tau(s) => SameTau<R>(E, u, λ v => ITree::Same(E, s, v)),
        Vis(c, k) => SameVis<R>(E, c, u, λ a v => ITree::Same(E, k(a), v)),
        Cut => u = Cut,
    }
}
```

with `SameVis` holding the right side's continuation, `u = Vis(c, k2)` and the
pointwise relation. The command is the left tree's own, so the relation never
states `c = d` and never transports an answer along it. That sidesteps the
probe's caveat about the Vis clause's command equality (it must be
proof-irrelevant, or over a set of commands): there is no such equality.
Symmetry and transitivity rewrite the right side with `j` and recurse.

**A sum's continuation is refined by returning a function.** A `match` on a
command of `Events::sum(D, E)` does not refine the type of a continuation
bound before it ([elab-match-refines-hypothesis-kernel-rejects](../issues/elab-match-refines-hypothesis-kernel-rejects.md),
[deep-pattern-dependent-later-field](../issues/deep-pattern-dependent-later-field.md)),
so `mrec_vis` matches on the command in a function whose *result* is
`(Resp(c) → …) → …`: the motive then mentions the command, and each arm sees
the refined answer type. The host elaboration interface's tactics hit the same
wall and use a helper for it; any handler over a sum of events will.

**`interp` is structural; `mrec` is fueled.** Interpreting a `Vis` runs the
handler's tree and continues with the interpretation of the subtree, which is
structural recursion, so `interp` needs no fuel and no `Tau`. `mrec` replaces
a call by the body's tree at that call, which is not a subtree, so it recurses
on the fuel instead: `mrec(n+1)` walks one layer (`mrec_layer`) and hands each
call to `mrec(n)`.

## Costs

The library's elaborate time was dominated by the elaborator's whnf of types
computed by recursion over a tree (`Same(E, t, u)` at a constructor form).
The value machine found the former, but its readback declined on the `elim_W`
β's induction hypothesis, a λ the machine builds over the step's environment
(`Eval::fire_elim_w`), and the caller fell back to the substitution reducer,
which copies the definitions it unfolds. `crates/elab/src/readback.rs` now
reads that λ back (a unit test checks it spells exactly the reducer's
reduct), which removed roughly half of the module's elaborate time with every
count column unchanged. What remains is the kernel gate: tier 2 has no generated
definitions, so `ITree<R>(E)` is spelled inline at every use, and a profile of
one law puts most of its gate in comparing and shifting that spelling. Each
law proved by induction costs seconds, and the library's cold check is the
suite's slowest target, inside its CPU rail but not by much. Naming the
lowered type is the fix
([tier2-fragment-extensions](../issues/tier2-fragment-extensions.md),
generated definitions), and it should come before round 2 adds more
induction proofs. (Landed 2026-10-21 for the leaf predicate, which was nearly
all of the spelling: `docs/inductive-tier2-w-lowering.md` §13.)

## Frictions met

- A constructor of a value-parameterized inductive cannot infer its value
  arguments in inference position, so a law at a literal tree spells the
  element type (`ITree::interp<R>(E, F, h, Ret(r))`) and a `sym` at a computed
  `Same` names its endpoints (`@sym<ITree<R>(E)>(u, Ret(r), h)`).
- A field read of a hypothesis whose type is a computed `Same` needs the
  record type spelled by a `let` first (`let g: SameTau<R>(…) = h;`).
- A recursive call that varies a parameter is not seen by IH generalization
  when it is `j`'s base argument, and has to be hoisted into a `let`:
  [ih-generalization-misses-call-under-j](../issues/ih-generalization-misses-call-under-j.md).
