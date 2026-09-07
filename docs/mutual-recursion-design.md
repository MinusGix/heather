# Mutual recursion: declaration groups under one measure

`issues/mutual-recursion-declarations.md`. The customer is the showcase parser
(`docs/showcase/idealized.hthr` 55–105): `parse_expr` / `parse_factor` /
`parse_atom`, three **adjacent** declarations each `decreases ts.len()`, each
calling the next forward, and **no group keyword written anywhere**.

Part A (`docs/termination-measures-design.md`,
`docs/decreases-unfolding-design.md`) lowers one `decreases` declaration to
`f#obl_N` / `f#body` / `f#rec` / `f`, an `elim_Nat` on a bound. This round makes
that one recursion serve N declarations. The three-member lowering is
hand-written and checked end to end in the scratch file this document cites in
§11; every "probed" below means that file, or one of its siblings, checks
under `heather check -L lib/std`.

## 1. Group formation is inferred from adjacency, not written

**Decision: adjacency, no new keyword, no AST node, no image field.**

The customer writes no keyword, so an explicit `mutual { … }` block would have
to be *additional* sugar and adjacency would be needed anyway. Costed against
the code, the block is not free: a new `Item` variant in
`crates/syntax/src/ast.rs`, a parser arm, an encode/decode pair in
`crates/elab/src/module_image.rs` (the `Decl` shape is what the format
carries, and a nesting item is not a `Decl`) with a magic bump, a new arm in
`elab_module_source`'s item loop, and a decision about how it nests inside
`impl`. Adjacency costs a scan over a slice of `Vec<Item>` the loop already
holds. Nothing in this design is easier to state with the block.

The rule, precisely:

- A **run** is a maximal sequence of *consecutive* `Item::Decl` items, in one
  container (the top level of a file, or one `impl` block), every one of which
  carries `decreases`. Any other item breaks the run — an `inductive`, an
  `import`, a `class`, and in particular a `fn` **without** `decreases`.
  Comments and blank lines are not items and break nothing.
- Within a run, an edge `i → j` is recorded when member `i`'s body calls `j`
  by `j`'s **self-name** (the base name, exactly as `Cx.selfref` uses it,
  `crates/elab/src/lib.rs:2666`) at a position the walk of §3 rewrites, with
  the name not shadowed by an enclosing binder. This is the same untrusted
  name-reading `measure.rs` already does.
- The groups are the run's **strongly connected components**. A singleton
  component lowers by Part A, byte for byte as today — nothing about an
  existing `decreases` declaration changes. A component of size N > 1 is a
  group, lowered by §3.
- Members of one component need not be contiguous within the run; the run,
  not the component, is what a foreign item breaks.

Mis-grouping is benign in one direction and diagnosed in the other. Grouping
two functions that are only apparently mutual costs nothing but uglier
obligation statements (§4) — the lowering still checks. *Failing* to group,
because the target sits outside the run, is an unbound name, and §8 says what
it reports.

## 2. Nothing needs a forward-declared signature

The issue's first item — "the members' *signatures* registered before any
body" — **dissolves** rather than getting built. `elab_measure_decl` replaces a
declaration by a family of surface declarations *before* any elaboration; a
group does the same for N declarations at once, and every sibling call is
rewritten to a projection of the shared induction hypothesis by the same
syntactic walk that rewrites a self-call today. By the time the checker sees
anything, the emitted declarations are in dependency order and no name is
forward.

What the generator needs of a sibling is its parameter list, its result type,
and its measure — all surface `Ty`/`Expr` already in the AST. It asks the
elaborator nothing new. `Cx.selfref` is untouched, there is no group-scoped
name table, and `resolve_name` gains no case (§8's message is an *extra
sentence* on an existing failure, not a new resolution route).

Two consequences worth naming. A sibling call the walk does **not** rewrite —
named arguments, an unsaturated call — is refused with the message Part A
already gives for a self-call, now naming the group. And a **measure** that
mentions a group member is refused outright: the motive of §3 quantifies over
every member's measure, so a measure defined by the recursion would be
circular. The message says so.

## 3. One recursion for the group: the motive is the *product* of the members'

The group's shared helpers are keyed on the first member's name, with the
`#` precedent (`docs/decreases-unfolding-design.md` §2). For a group whose
first member is `f`:

| name | statement |
|---|---|
| `g#obl_N` | per member `g`, per self/sibling-call site — Part A's lifted obligation, unchanged in shape (§4) |
| `f#grp` | `(__dec_z: Nat) -> Type` — the product motive |
| `g#body` | per member: `(__dec_k, __dec_ih: f#grp(__dec_k), x̄_g, __dec_h) -> T_g` |
| `f#grp_rec` | `(__dec_z: Nat) -> f#grp(__dec_z)` — the one `elim_Nat` |
| `g` | per member: `f#grp_rec(Succ(m_g)).<proj_g>(x̄_g, nat::lt_succ_self(m_g))` |

with `m_g` the member's *combined* measure of §4 and `<proj_g>` a chain of
`.fst`/`.snd`. Concretely, for the parser (probed, `g3.hthr`):

```
fn Pmotive(z: Nat) → Type {
    Pair<(ts: List<Nat>) → nat::Lt(list_len(ts) * 3 + 2, z) → Nat,
    Pair<(ts: List<Nat>) → nat::Lt(list_len(ts) * 3 + 1, z) → Nat,
         (ts: List<Nat>) → nat::Lt(list_len(ts) * 3 + 0, z) → Nat>>
}
fn Prec(dz: Nat) → Pmotive(dz) {
    match dz as λ z => Pmotive(z) {
        Zero => Pair(λ ts dh => match dh {},
                Pair(λ ts dh => match dh {}, λ ts dh => match dh {})),
        Succ(dk, dih) => Pair(λ ts dh => Pbody_expr(dk, dih, ts, dh),
                         Pair(λ ts dh => Pbody_factor(dk, dih, ts, dh),
                              λ ts dh => Pbody_atom(dk, dih, ts, dh))),
    }
}
fn parse_expr(ts: List<Nat>) → Nat {
    Prec(Succ(list_len(ts) * 3 + 2)).fst(ts, nat::lt_succ_self(list_len(ts) * 3 + 2))
}
```

A sibling call from member `i` to member `j` is `__dec_ih.<proj_j>(ȳ, proof)`
with exactly Part A's proof term, `nat::le_trans(Succ(m_j[ȳ]), m_i, __dec_k,
⟨obligation⟩, __dec_h)`. A **self**-call is the same thing with `j = i`; the
group has no separate self-call route.

**The product, not a sum of telescopes.** The issue proposes indexing the
recursion by `which` member over the *sum* of the telescopes. That needs a
generated inductive per group, a type-level dispatch `fn G#result(w) -> Type`,
and a dependent result — and it buys nothing, because the eliminator's motive
is a *type*, and a type may just as well be the N-fold product of the members'
own motives. Dually the same recursion, strictly less machinery:

- **No common result type and no common telescope is required.** Each product
  component carries its member's own `(x̄_g) → nat::Lt(m_g, z) → T_g`. Probed
  with a deliberately heterogeneous two-member group — `f(n: Nat) -> Nat`
  against `g(xs: List<Nat>, b: Nat) -> List<Nat>` — which checks and computes
  (`ghet.hthr`). This is §8's answer to "a member with a different result
  type": there is nothing to diagnose.
- **Nothing is generated but declarations.** No inductive, no `#skel`, no new
  elaborator query.
- **Closed arguments still compute.** `parse_expr([7, 8]) = 3` is `refl`
  through the tuple projections and the eliminator, as are four other closed
  probes; `elim_Nat` steps at `Succ(m)` whatever `m` is, and a `record`
  projection of a constructor application reduces.

**Type parameters** are hoisted to the group's shared helpers: `f#grp<A>`,
`f#grp_rec<A>`, `g#body<A>`, with every reference pinned (`f#grp<A>(dk)`) as
Part A pins its companions. That requires every member to declare the **same**
type-parameter list, same names in the same order — a surface function type
cannot quantify one. A group whose members disagree is refused with a message
naming the two lists. Probed at a polymorphic two-member group over `List<A>`,
including `refl` at an open element type (`gpoly.hthr`), which is the open-type
axis `docs/testing-generated-terms.md` requires.

**`import pair;`** is required of a module containing a group, checked and
reported the way `elab_measure_decl` already checks `import nat;`. A
generated group-local record would remove the import and the `.snd.snd`
chains; it needs a record with a value parameter (`z`), which nested `Pair` does
not, so it is later tidying and not this round.

## 4. Obligations: a static member rank makes the measure lexicographic

`parse_expr` calls `parse_factor` on the **same** `ts`. Its measure does not
decrease, so a strict-decrease-only rule rejects the customer outright. The
answer is the standard one — lexicographic on `(measure, member rank)` — and
the cheap way to spell it is to **flatten the pair into the one `Nat` Part A
already recurses on**:

```
m_g(x̄) = e_g(x̄) * N + r_g          N = |group|,  0 ≤ r_g < N
```

which *is* the lexicographic order: if `e_j < e_i` then `e_j*N + r_j ≤
(e_i-1)*N + (N-1) < e_i*N + r_i` for any ranks, and if `e_j = e_i` it reduces
to `r_j < r_i`. Everything downstream — the bound, `nat::Lt`, `le_trans`,
`lt_succ_self`, the `Zero`-arm absurdity, the refinement convoy — is Part A
unchanged.

**The rank is declaration order, first-declared highest**: `r_g = N - 1 - (g's
index in the group)`. The customer's own comment is `atom < factor < expr`, and
its declaration order is expr, factor, atom — so the rule is exactly "a call at
an unchanged measure may only go to a member declared *below* you", which is
how the parser is already written and how a recursive-descent grammar is
conventionally laid out. The alternative — inferring ranks by topologically
sorting the same-measure edges — is cleverer, less predictable, and has no
answer when the same-measure edges themselves cycle. Declaration order has an
answer: reorder, and §8's message says so.

Soundness needs no argument beyond the flattening: a cycle in the call graph
must contain at least one edge that does not lower the rank, and that edge owes
a strict `e`-decrease. A pure rank cycle is refused because its obligation is
unprovable — probed directly: `nat::Lt(list_len(ts)*2+1, list_len(ts)*2+0)`
fails with `omega`'s real-shadow message (`neg.hthr`).

`omega` closes the rank arithmetic itself, with literal `N` and literal ranks;
no new `nat` lemma is needed. Probed (`p0.hthr`, `obl.hthr`):

```
Lt(a*3+1, a*3+2)                          -- a same-measure call, rank 1 < 2 -- ok
Lt(a*3+2, b*3+2)  given  h: a < b         -- a strictly smaller argument     -- ok
Lt(a*3+0, b*3+2)  given  h: a <= b                                           -- ok
```

**What the writer sees stays clean.** A site's `f#obl_N` is stated at the
*combined* measure, but its body binds the obligation the writer thinks in
first and lets `omega` do the arithmetic:

```
theorem parse_expr#obl_2(t: PTok, rest: List<PTok>)
      : nat::Lt(len(rest)*3 + 2, len(Cons(t, rest))*3 + 2) {
    let __dec_clean : nat::Lt(len(rest), len(Cons(t, rest))) = ?dec2;
    omega
    on ?dec2 := …;                     // the writer's own `on`, moved here
}
```

so `on ?dec2` still discharges `rest.len() < ts.len()` and never sees a `3 *`.
The clean statement is **strict** (`<`) when the call does not lower the rank
and **non-strict** (`<=`) when it does; the non-strict form is `omega`-trivial
at an unchanged argument, which is why the customer's `parse_factor(ts)` costs
the writer nothing. Probed: `let`-bound hypothesis, `on`-discharged, `omega`
closing the combined goal (`p1.hthr`).

**Lifting is not optional for a group.** Part A lifts obligations because
`omega` reconstructs against the local context (`decreases-unfolding-design.md`
§4). Here there is a second reason: inside `g#body` the context holds
`__dec_ih : f#grp(__dec_k)`, and `omega` renders its certificate as source text
and re-parses it — an unresolvable rendering there fails the obligation
outright (probed: `` `omega` got stuck: unexpected character 'â' ``, and the
same goal in the lifted context checks). A site that cannot be lifted —
`BinderTys` declining an arm binder — must therefore make the **group** fall
back to the un-lifted spelling only where the un-lifted `omega` still succeeds,
and otherwise report; unlike Part A, the fallback is not always available.

**One extension to `Rewrite::obligation` is required.** Today the refinement
convoy substitutes the enclosing arms' patterns into the *caller's* measure
only: the transport motive is `λ y _ => Lt(at_args, e_{i-1}[y/v])`, with
`at_args` fixed (`measure.rs:1793`). A same-measure sibling call passes the
scrutinee itself, so `at_args` mentions `v` too, and the unrefined statement
`Lt(list_len(ts)*3+1, list_len(Cons(t,rest))*3+2)` is unprovable. Both sides
must be refined and both generalized:

```
λ y _ => nat::Lt(at_args[y/v], e_{i-1}[y/v])
```

Sound for the same reason the one-sided version is — at `y := pat` it is the
statement in the arm, at `y := v` it is the ih's own — and a strict
generalization: where `at_args` does not mention `v` the two coincide. Probed
in both parser sites that need it (`g3.hthr`, obligations 1 and 3).

## 5. Structural mutual recursion is in scope only through a written measure

`even`/`odd` on `Nat` with no `decreases` is **deferred**, deliberately.

The structural checker's eliminator hands out an ih for *its own* recursion and
not a sibling's, so the structural route does not generalize; the issue says
so, and this design agrees. What *is* in scope is `even`/`odd` with the measure
written — `decreases n` on both — which is one line more from the writer and
the same lowering as everything else. Probed at two members with
`decreases n`, including `ev(4)`, `od(4)`, `ev(7)` by `refl` (`g2.hthr`).

Synthesizing the measure (taking `decreases x` from the argument the recursion
descends on when the writer wrote none) is a separate, purely syntactic
convenience with its own failure modes — which argument, when there are two —
and it would silently move a declaration off the structural route it takes
today. Residue on the issue, not this round.

## 6. Unfolding equations for a group are residue

Part A's companions (`f#ext`, `f#irrel`, `f_unfold`) do not extend to a group
this round, and every group member records the refusal on its `f_unfold` name
through the existing `unfold_refusals` path, so a citation reports the reason
and §6 of this document rather than an unknown name. `f` itself checks exactly
as it would.

What would be needed, for the record: `g#ext`'s hypothesis becomes N of them
(one per component, `hg_i : (ȳ_i) → (p) → (q) → g1.<proj_i>(ȳ,p) =
g2.<proj_i>(ȳ,q)`), and `f#grp_rec`'s bound-irrelevance is no longer one
statement but a tuple-level equality — `Pair` is a record, so `pair::pair_ext`
is the shape, applied N-1 times, and the `Succ`/`Succ` case needs all N `#ext`s
at once.

The customer does not pay for the deferral. The parser's bodies are outside the
companion walk's fragment already: `let (lhs, rest) = parse_factor(ts)?` is a
`let` whose right-hand side holds a recursive call, and the `match rest { … }`
that follows is a match on a computed scrutinee — both refused by
`docs/decreases-unfolding-design.md` §3 and its 2026-09-05 amendment. A group
companion generator would decline `parse_expr` anyway.

## 7. What this round inherits from Part A and does not fix

Two `omega` defects sit between the customer and a green showcase. Both are
Part A's, both reproduce on a **single** `decreases` declaration, and neither
is this round's to fix — but the showcase row cannot close without them, so
they belong in the issue log.

- **`omega` does not reduce a measure at a constructor pattern.**
  `fn drop1(xs: List<Nat>) -> Nat decreases list_len(xs)` recursing on the tail
  is refused: `` `list_len(t) < list_len(Cons(h, t))` was not proved
  automatically (`omega` got stuck: Omega could not spell a natural
  expression) `` — `list_len(Cons(h, t))` is an opaque atom to the reflection,
  not `Succ(list_len(t))`. The existing tests all discharge such sites by hand
  (`merge`'s `succ_add_le`, `runs`'s `drop_eq_le`), which is why this was not
  visible. Every hand lowering here works around it the same way, with a lemma
  stated at the `Succ` form. **Fixed 2026-09-06**
  (`docs/omega-measure-reduction-design.md`): such a site now closes by
  `omega` alone, and the hand lemmas came out of these tests.
- **`omega` spells a member function by its base name.** A goal over
  `xs.len()` reconstructs a certificate naming `len(…)`, which is unbound
  outside `list`: `` error: unbound name `len` ``. Writing the measure
  `list_len(xs)` avoids it. The 'â' failure of §4 is the same defect seen
  through the context renderer.

## 8. Diagnostics

- **A sibling call that decreases nothing.** Part A's reworded message already
  names the obligation and the `on` that discharges it; a group appends the
  rank rule when the two members' measures are the same and the callee is
  declared *above* the caller: "`parse_expr` is declared above `parse_atom`, so
  a call at an unchanged measure may only go forward in the group; reorder the
  declarations, or make the measure strictly decrease."
- **A member without `decreases`.** Such a declaration breaks the run, so the
  forward reference to whatever follows it is an unbound name. The elaborator
  knows the file's remaining declarations (`elab_module_source` holds the whole
  `File`), so the unbound-name message gains a sentence when the name *is*
  declared later in the same container: "`parse_factor` is declared below;
  adjacent declarations form a mutual group only when each of them carries
  `decreases` and nothing else stands between them." This is a message on an
  existing failure path, not a new resolution route (§2).
- **A member with a different result type** is not an error at all (§3).
- **Members disagreeing on type parameters** is refused, naming both lists
  (§3).
- **A measure naming a group member** is refused (§2).

## 9. Module images need nothing

The group exists only between the parser and `elab_measure_decl`'s successor:
by the time anything is registered it is a list of ordinary declarations, which
commit through `commit_decl` and ride in the `ModuleDelta` as ordinary
bindings, exactly as Part A's family does
(`docs/decreases-unfolding-design.md` §9 item 3). `Decl::decreases` is already
in the format at magic `\x03`. **No magic bump** — and that is a second cost
the explicit-block spelling of §1 would have carried and adjacency does not.

## 10. Where it will live

- `crates/elab/src/lib.rs`, `elab_module_source` — the run scan and the SCC
  split, over the `Vec<Item>` slice the loop already holds; a new
  `elab_measure_group` beside `elab_measure_decl`, which stays for singletons.
- `crates/elab/src/measure.rs` — `lower` generalized from one `Decl` to a
  slice: the combined measure of §4, the product motive and `#grp_rec`, the
  projection per member, and the sibling-call route in `Rewrite` (today
  `self_call` matches one name; it becomes a lookup in the group's name list
  that also yields the projection).
- `crates/elab/src/measure.rs`, `Rewrite::obligation` — the both-sides
  refinement of §4, which is the one change that also affects a singleton.
- `crates/elab/tests/` — a new acceptance file; the fixture style and `base()`
  prefix of `termination_measures.rs`.
- No kernel change, no syntax change, no image change.

## 11. Cheap verification items for the implementation's first hour

The hand lowerings live in this round's scratch directory and are the thing to
read first — each checks under
`(ulimit -v 8388608 -t 120; target/release/heather check -L lib/std <file>)`:
`g2.hthr` (two members, `Nat` measure, three closed `refl`s), `g3.hthr` (the
parser's three members, the same-measure sibling call, five closed `refl`s),
`gpoly.hthr` (polymorphic, open element type), `ghet.hthr` (different
telescopes and result types), `obl.hthr` / `p0.hthr` / `p1.hthr` (the
obligations alone), `neg.hthr` and `a1.hthr` (the negative controls).

1. **The both-sides refinement does not disturb a singleton.** Make only the
   §4 change to `Rewrite::obligation` and run
   `crates/elab/tests/termination_measures.rs` and `decreases_unfolding.rs`
   unchanged. If `gcd`, `merge`, `runs` and every companion still pass, the
   generalization is free; if not, that is the deviation to report before
   anything else is built.
2. **The scan sees the customer.** Before generating anything, log the runs and
   SCCs the §1 rule finds in a file holding the parser's three declarations,
   and confirm it is one component of three in declaration order. Confirm too
   that inserting a plain `fn` between two of them splits it.
3. **`f#grp` is registrable as a `fn` returning `Type`.** Part A's item 2
   confirmed a `#` name for a value global; this one is a type-valued global
   used in another generated declaration's *result type*. `g2.hthr` says it
   checks when hand-written; confirm the generator's spelling registers.
4. **The un-lifted fallback.** Part A falls back to obligations at the call
   when a lift is refused. Construct a group site whose arm binder `BinderTys`
   declines and confirm what happens: §4 predicts the fallback is *not*
   generally available for a group, because `omega` in `g#body`'s context has
   `__dec_ih : f#grp(k)` to render. If it turns out to render fine, §4's
   "not optional" is too strong and should be amended.
5. **N = 2 with no rank pressure.** `g2.hthr`'s `ev`/`od` both call strictly
   downward, so the ranks are inert. Confirm the generator still scales the
   measure (uniformly for N > 1) rather than special-casing, and that
   `ev(4) = 1` is still `refl` (the probe is `Nat`-valued: `Bool`’s
   constructors are `True`/`False`, and `False` collides with `logic::False`).
6. **A group inside `impl`.** §1 scopes a run to one container. Confirm a run
   of `decreases` members inside an `impl` block groups, and that a member
   recurses under its base name as `SelfRef` does
   (`docs/decreases-unfolding-design.md` §10 already has `List::nth2` as the
   singleton precedent).

Then the acceptance tests, per `docs/testing-generated-terms.md`: the group at a
**literal** and at a **neutral** argument; an **open** element type
(`gpoly.hthr` is the shape); a member used in a *checking* position; and the
negative controls — the rank cycle of §4, the broken run of §8, the
disagreeing type-parameter lists, and a citation of a group member's
`f_unfold` reporting §6's reason rather than an unknown name.

## 12. What the implementation found

Implemented 2026-09-05. Everything §§1–4 and §§8–10 promise landed; the
deviations and discoveries, each against the section it amends:

1. **§11 item 1 held.** The both-sides refinement of §4 is free for a
   singleton: `termination_measures.rs` and `decreases_unfolding.rs` pass
   unchanged. It is spelled as one generalization of `stages()` — `refine(e)`
   over any expression — so the caller's measure and the argument's are staged
   the same way, and the transport motive is
   `λ y _ => Lt(at_args[y/v], e_{i-1}[y/v])`.

2. **§1's "or one `impl` block" has no referent** (amends §1 and §11 item 6).
   Heather has no method-block `impl`: `Item::Impl` is the `datarepr`
   implementation, whose body is clauses and not declarations, and a member
   like `List::nth2` is an ordinary **top-level** declaration with a qualified
   name. So a run is scoped to the top level of a file, full stop. A run of
   qualified declarations groups exactly like any other and each member
   recurses under its base name, which is what `SelfRef` already did — probed,
   and the acceptance test `a_group_of_qualified_declarations_recurses_under_base_names`
   is that case. Note the corollary: a *written* qualified self- or sibling
   call (`List::od2(t)` inside the group) is not rewritten, exactly as Part A
   never rewrote one.

3. **The adjacency scan runs in two loops, not one** (amends §10).
   `elab_module_source` and `check_module_source_inner` are parallel item
   loops over the same `File`; both now go through `begin_container` (the
   groups plus §8's declaration table) and `elab_item_at`. Splitting the
   dispatch out is what keeps the two from drifting.

4. **A forward call the SCC does not close is a real failure mode** (amends
   §8). `f` calling `g` where `g` never calls back puts them in *different*
   components, so `g` is unbound at `f` — even though both carry `decreases`
   and nothing stands between them. §8's sentence was widened accordingly: it
   now says the members must call *each other*, and that a call which is not
   answered needs the callee declared first. The sentence also fires only for
   a declaration still ahead of the item loop, so it is never said about a
   name that failed for some other reason.

5. **The lift is mandatory, and its refusal is a diagnosis** (confirms §4,
   §11 item 4). A group whose site cannot be lifted is refused with a message
   naming the site, rather than falling back as Part A does. Probed on a
   `match` over a computed scrutinee, where `BinderTys` declines the arm
   binder. §4's "not optional" stands.

6. **The clean statement is `<=` at a rank-lowering call even when the
   argument also shrinks** (amends §4's ergonomics, not its rule). The writer
   who supplies `on ?decN := …` for such a site must supply a `nat::Le` proof
   where they would naturally reach for `nat::Lt`. This costs nothing at the
   customer's own site — `parse_factor(ts)` at an unchanged `ts` is
   `omega`-trivial and takes no `on` at all — and every case where it bites is
   downstream of `issues/omega-measure-at-constructor-pattern.md`, which is
   what forces the `on` in the first place.

7. **The generated eliminator is marked `generated`** (amends §3). `f#grp_rec`
   writes a motive that its own result type already states, so the
   redundant-match-motive lint fired on code no reader wrote. The `Match` node
   carries `generated: true`, which is what that flag is for.

8. **`f#grp`'s result is `Type<0>`.** A group whose members return something at
   a higher universe is not covered; nothing in the library or the customer is,
   and the failure is a refused generated declaration rather than a wrong term.

9. **The scaled measure is spelled `nat::add(nat::mul(e, N), r)`**, not through
   the `*`/`+` operators: that is the form `omega`'s reflection reads directly
   (`crates/elab/src/omega_cert.rs`), and `p1.hthr` had already probed it.

10. **The `_unfold` refusal message no longer double-points.** `resolve_name`
    appended ", see docs/decreases-unfolding-design.md §3" to every recorded
    reason; a group's reason names *this* document instead, so the suffix is
    now added only where the reason does not already name a document.

11. **Half of `issues/omega-renders-member-by-base-name.md` is fixed here**
    (§7's second bullet). `Elaborator::spell_term_source` is
    `spell_term_clean`'s re-parseable flavour: it spells a global **qualified**
    wherever the base name does not resolve back to it, which is exactly the
    member case (`xs.len()` came back as `len(…)`). `omega_cert.rs`'s
    reconstruction now uses it; the two display-only callers keep the base
    name. A context entry `reflect_assumption` cannot spell is now *skipped*
    rather than aborting the goal. §7's first bullet — a measure at a
    constructor pattern — is untouched here and was closed separately
    (`docs/omega-measure-reduction-design.md`).
