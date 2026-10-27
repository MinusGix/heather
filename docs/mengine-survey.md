# mengine: what a λ-DAG proof engine means for Heather

Status: **survey**, 2026-10-26. Sources:

- the repository <https://github.com/triviajon/mengine> at `0036923`
  (GPL-3.0, C, about 22k lines under `src/`), read in full for the kernel and
  the rewriter;
- Jon Rosario, *Prototyping a Scalable Proof Engine*, MIT MEng thesis, May
  2025, advised by Adam Chlipala (<https://hdl.handle.net/1721.1/162908>).
  The thesis is the design's first write-up. Its rights statement is
  "In Copyright, Educational Use Permitted", so it is **not** committed here;
  fetch it from the handle. Section numbers below are the thesis's.

The README announces a paper, *Efficient Proof Engines with Lambda-DAGs*, "expected
to appear at POPL 2027", with the code as its artifact (Zenodo DOI
`10.5281/zenodo.23197497`). On 2026-10-26 no preprint was findable and the
DOI did not resolve, so the paper itself is not read here. Where the thesis
and the current code differ (contexts, substitution, caches), this note
follows the code. Read against Heather master at `9486d1a`. Follow-up is in §7.

mengine is a proof *engine* written for speed on automation-heavy proofs:
rewriting, symbolic execution, hole filling. It is not a new foundation. Its
logic is a small Calculus of Constructions with `Type : Type`, inductives,
`match` and structural `fix`, and it trusts the whole engine (§1.5). Its value
for Heather is as an existence proof and a benchmark suite for one property,
**every cost linear in the term's DAG size**, which Heather has in its
evaluator but not in three of its other traversals.

---

## 0. The answer in brief

1. **Most of mengine's machinery buys what Heather already has.** Pointer
   sharing of subterms is Heather's `Arc` trees. mengine's per-node "minimal
   context", tested by an O(1) order-maintenance ancestry query, is what
   `bounds.rs`'s memoized free-index bound gives a de Bruijn kernel for free:
   both let substitution skip a subtree that cannot mention the variable.
   mengine's reduction is still substitution-based, so on the workload that
   made Heather adopt its environment machine (`issues/whnf-sharing-term-growth.md`)
   it would be the one doing the copying. §2 has the mapping.
2. **The one property worth taking is "check each shared node once".** In
   mengine a node is type-checked when it is built and stores its type, so
   the cost of a proof is the number of distinct nodes, never the number of
   paths. Heather's kernel gate re-checks a shared subterm once per path.
   That is the open `issues/kernel-typing-memo-on-node-identity.md`, whose
   `dep` family costs 2^k and fails with `OutOfFuel` at k = 16. mengine is
   evidence that the per-node discipline works across a whole engine, and it
   also shows which Heather constraint makes this harder: fuel determinism,
   which mengine does not have (§3).
3. **mengine has no shift, so DAGs survive binders. Heather's shift turns
   them back into trees.** mengine's variables are pointer-unique nodes, so a
   shared subterm used under a binder is the same node there. In Heather it
   is a fresh `shift_local(k)` copy, and the copy walks the DAG as a tree.
   Heather should not adopt the representation, but the cheap analogue,
   a per-traversal memo in `Mapper` for nodes that are actually shared, is
   named in the typing-memo issue and was never filed. Filed now as
   `issues/subst-shared-node-memo.md` (§3.2).
4. **The rewriter is the design reference for `rewrite-setoid-relations`.**
   mengine rewrites bottom-up, builds one congruence step per changed node,
   memoizes per (lemma, context, node) across calls, and so stays linear on
   goals where Rocq's `rewrite`/`setoid_rewrite`/`rewrite_strat` are
   quadratic or exponential (thesis Ch. 4, and the benchmark plots). Heather's
   `rewrite` is a single motive abstraction plus one `J`, and its abstraction
   walk (`AbstractLocal`) is a tree walk, and on mengine's `addr0_let_in`
   shape one Heather `rewrite` costs 2^k in the number of lets, in the gate
   and the frontend alike (probe in §4.2). The statement alone already
   costs 2^k in the gate, so until the typing memo lands nobody writes such
   goals, but the planned relational and repeated rewriting should be built
   bottom-up with a node memo from the start rather than inherit the tree
   walk (§4).
5. **The benchmark families transfer and Heather has none of them.** The
   frontend bench (`crates/elab/benches/frontend`) has no tactic family and
   no let fan-out family. mengine's `rewrite_fa`, `repeat_mod`,
   `addr0_let_in` and `rewrite_nm` are small generators with known linear
   lower bounds. Filed as `issues/tactic-scaling-bench-families.md` (§7).
6. **Native compilation is barely a customer.** The verified compiler runs in
   the kernel's value machine, which is the part of Heather that is already
   ahead of mengine. mengine's real-world case study, Bedrock2-style
   symbolic execution of straight-line code, is the per-program proof style
   that burn B1 retired. The native work meets mengine's ideas only where a
   program proof threads machine states through transparent `let`s, which is
   the typing memo of item 2 (§5).

---

## 1. What mengine is

### 1.1 Terms as λ-DAGs

Following Shivers and Wand, *Bottom-up β-reduction: uplinks and λ-DAGs*
(2004/2010), a term is a graph. Every compound node holds pointers to its
children, and every node keeps an intrusive list of **uplinks** to its
parents (`src/kernel/expression.h`, `Uplink`, `Relation`). Variables are
**pointer-unique**: one allocation per variable, and every occurrence is that
pointer. There are no indices and no names that matter. A binder owns its
variable node.

### 1.2 Every node is typed when it is built

The defining invariant (thesis §1.2, §3.1.1) is that the constructors
`init_lambda_expression_wc`, `init_app_expression_wc` and their siblings
type-check before they return. Each node stores its **type** and its
**minimal context**, and a client may assume any node it holds is
well-typed. An application's type is computed once, by substituting the
argument into the codomain, and cached (`g_app_type_cache`, keyed by the
pair of child pointers). Building a big term from checked pieces costs the
new nodes only.

### 1.3 Contexts are a tree of variables, queried in O(1)

A context is a variable node, and its parent is the variable before it, so
contexts form one tree shared by every term (`src/kernel/context.c`). "Is
`e` valid in `Γ`" is "is `e`'s minimal context an ancestor of `Γ`", and
"does `t` mention `x`" is "is `x` an ancestor of `t`'s minimal context".
Both are answered by an order-maintenance structure over an Euler tour of
the tree, with tag-range relabelling (`src/kernel/order_tagrange.c`,
amortized O(1) insert and query; a linked-list fallback is kept for the
ablation).

### 1.4 Substitution, holes and conversion

- **Substitution** (`src/kernel/mixed_subst.c`) returns any subtree whose
  minimal context does not contain the variable, memoizes per node within
  one call, and refreshes a binder's variable when its type changes. It
  reduces a β-redex it creates on the way. Reduction is substitution: there
  is no environment machine (`beta_reduction.c`, `normalize.c`).
- **Holes** are nodes. `fill_hole` checks the candidate against the hole's
  type and defining context, then rewires every parent through the uplinks,
  in place. There is no zonking pass.
- **Conversion** builds explicit derivation objects (`Conversion`: refl,
  sym, trans, β, δ, ι, congruences) and caches whnf and single steps on
  evar-free nodes (`src/kernel/conversion.c`).

### 1.5 Trust and logic

The kernel is the engine. Tactics, including the rewriter, construct terms
through the checked constructors, and `fill_hole` mutates terms in place, so
everything that calls those constructors is trusted. The backstop is export:
`Print Rocq` emits a term Rocq 9.1.1 rechecks, printing each shared subterm
once as a top-level `let` (`src/kernel/rocq_export.c`). The logic has
`Type : Type` (`init_type_expression` makes `TYPE` its own type), which the
thesis acknowledges and sets aside (§2.1.2). This is a performance prototype
of an engine, not a foundation.

### 1.6 The rewriter and the benchmarks

`rewrite` (thesis §3.2.1, `src/engine/rewrite_internal.c`) recurses to the
leaves first, rebuilds each changed application with an `app_cong` step,
tries the lemma at the rebuilt node, and chains with `eq_trans`. It rewrites
under a λ with functional extensionality, an axiom of its prelude. Results are
cached on the node, and since 2026-09 in a persistent cache keyed by lemma,
context and node, so a shared subterm is rewritten once and a second call
reuses the first's work. A rigid-head check on the lemma's left side skips
nodes that cannot match. The suite (`benchmarks/`) plots time against size
for mengine, Rocq and Lean:

| family | shape | why it is hard elsewhere |
|---|---|---|
| `rewrite_fa` | `g(f(f(…f(a))))`, rewrite by `f a = a` | Θ(n) sites; `repeat rewrite` re-walks the goal each time |
| `repeat_mod` | `(… (b mod p) mod p …) mod p` | the same shape through a binary operator |
| `addr0_let_in` | `let vᵢ := vᵢ₋₁ + vᵢ₋₁ + 0 in …`, remove the `+ 0`s | ζ-reduction makes the sites Θ(2ⁿ); rewriting needs the lets kept |
| `rewrite_nm` | `let x₁ := f x₀ … x₀ in …`, n-ary `f`, m lets | sharing and arity together |
| `separation_logic` | reorder separating conjunctions | AC-style search |
| `symbolic_execution` | Bedrock2-like `exec` over straight-line code with partial maps | lemma application plus `get_put` rewriting at every step |

A separate stdlib suite translates 77 Rocq lemmas and replays them. It is a
fidelity check more than a speed claim, and the README notes mengine is
slower than Rocq on list induction.

## 2. Mechanism by mechanism

| mengine | Heather | verdict |
|---|---|---|
| subterms shared by pointer | `Arc` trees; unchanged subtrees shared by every traversal (`subst.rs`, "Sharing unchanged subtrees") | have it |
| minimal context per node, O(1) "may `t` mention `x`" | `bounds.rs`: memoized 1 + max free local index, O(1) "may this traversal change `t`" | have it. A context chain prefix *is* a de Bruijn bound, so the two summaries carry the same information; mengine needs an order-maintenance structure to get back what integer comparison gives an indexed kernel |
| order maintenance over the context tree | none needed | not applicable |
| pointer-unique variables, no shifting | de Bruijn in three namespaces | do not adopt; take the memo of §3.2 instead |
| type stored on every node at construction | kernel re-infers per path; no memo on node identity | the gap: §3 |
| holes as nodes, filled in place through uplinks | metas as Ψ globals, zonked; terms have no interior mutability (`DESIGN.md` §Representation) | do not adopt: no measured zonk cost, and in-place mutation would undo the immutability the bounds memo, the conversion memos and the parallel gate rely on |
| reduction by substitution, β on the fly | environment machine over a value domain with closures (`docs/nbe-conversion-design.md`) | Heather is ahead; mengine's `list_fold` family is the shape that was exponential in Heather's old rewriter |
| conversion derivations as objects, whnf caches | conversion decided directly; value caches kept for the query | no customer for derivations; caches already there |
| bottom-up rewriting with a node memo | `rewrite` = abstraction + one `J` | reference design for relational and repeated rewriting: §4 |
| export prints shared subterms once | `crates/export/src/share.rs` hoists every repeated subterm into a definition | have it, done the same way |
| module images | `module_image.rs::put_term` writes trees | a residue, see §3.3 |
| benchmark suite of rewriting shapes | kernel and frontend benches, no tactic families | take it: §7 |

## 3. DAG-linear checking

### 3.1 The typing memo

Heather already diagnosed the cost (`issues/proof-let-substitution-cost.md`,
2026-09-25): a let alias is one `Arc`, so a let chain is a DAG in memory,
but the kernel gate, the shift under a binder and the module image each walk
it as a tree. `have` fixed the opaque case. The transparent case (`dep`: a
state `sᵢ` that later proofs must see through) is the open
`issues/kernel-typing-memo-on-node-identity.md`.

mengine's whole design is that memo, taken to the limit: the type is a
field, filled at construction, so there is nothing to look up. Three things
in its experience bear on the Heather issue.

- **What is keyed.** mengine caches an application's type by the pair of
  child pointers (`g_app_type_cache`), not only by the node, so two separately
  built `f a` nodes with the same children share the computation. Heather's
  issue keys on node address plus context identity. Child-pair keying may be
  a cheap widening for applications, if separately built applications over
  shared children turn out to be common; the memo's counters would say.
- **What is not cached.** mengine excludes nodes that contain an unfilled
  hole (`has_evar`) from its conversion caches, because filling mutates them.
  Heather's kernel never sees holes, so its memo needs no such exclusion; the
  analogue is the elaborator side, where metas exist.
- **What mengine does not have to solve.** It has no fuel, so a cache hit is
  free and nondeterministic hit patterns change nothing observable. Heather's
  issue spells out why that is the hard part here: a hit must not depend on
  addresses, or `--timings` counts and `OutOfFuel` verdicts would vary with
  the allocator. mengine offers no help there, and the issue's own
  design (an unbounded per-item map, entries chosen by node kind) stands.

### 3.2 The shift memo

In mengine a shared subterm under a binder is still the same node, because
no index moves. In Heather, `elab`'s alias use below its binding depth is
`shift_local(by)` (`crates/elab/src/lib.rs`, the alias arm), and
`map_term` has no per-traversal memo, so the result is a tree. The typing
memo issue's reach section asks for "a per-traversal memo in the shift,
applied only to shared nodes" to be named or filed. It is filed as
`issues/subst-shared-node-memo.md`.

The obvious objection is on record: `issues/whnf-sharing-term-growth.md`
measured a pointer memo inside `apply_local` at 0.05% hits and a slowdown.
That workload had no sharing left by the time substitution ran. A let chain
does, and mengine's memo (`MENGINE_SUBST_MEMO`, on by default) is on for
exactly that reason. The new issue therefore asks for the memo to be gated:
only nodes reached twice in one traversal pay for it, which a strong count
above one can pre-filter cheaply, since a miss only costs the memo, never a
verdict.

### 3.3 Images

`put_term` writes a tree, so an image of a let-heavy term is tree-sized,
and so are its node budget and replay. Since `have`, the library avoids
let fan-out, and no image has been measured as tree-blown. This stays a
note in the shift-memo issue's reach section rather than an issue of its
own: the trigger is an image whose node count is far above the term's
shared size, which `let-fanout-diagnostic`'s tree-versus-shared count would
also expose.

Update 2026-10-27: the trigger came from the library itself (the tactic
modules' images, ~110 MB), and images are now written as DAGs
(`docs/semantic-module-images-design.md`, Stage 4a). The merkle walk is
still a tree walk.

## 4. Rewriting

### 4.1 What Heather's `rewrite` is

`rewrite(h, e)` (`crates/elab/src/rewrite.rs`,
`docs/equation-rewrite-design.md`) abstracts every occurrence of `h`'s left
side out of the goal (`Type::abstract_local*`) and closes with one kernel
`J`. That is Rocq's `rewrite`, not `setoid_rewrite`: it does not rewrite
under binders, and it rewrites one instance per equation. It is a sound,
small design for the single step, and its cost is one walk of the goal.

### 4.2 The walk is a tree walk

`AbstractLocal` memoizes the weakened patterns per depth but not the result
per node, so a goal that is a DAG in memory is walked as a tree. The
occurrence numbering of `at := k` is defined over that tree order, so a
node memo would also have to say what the k-th occurrence of a shared
subterm is. On an `addr0_let_in`-shaped goal the walk is therefore
exponential in the number of lets.

A probe confirms the shape (release build of `9486d1a`,
`HEATHER_KERNEL_WORKERS=1`, generator not committed). The goal is
`addr0_let_in`'s chain with `g` for `+`:
`{ let v1 = g(g(v0, v0), 0); …; vk }`. `stmt` proves it equal to itself by
`refl`, and `rw` removes the outermost `+ 0` with
`rewrite(h, refl)`, `h: (x: Nat) -> g(x, 0) = x`. Kernel queries for the
theorem, from `--timings`:

| k | `stmt` queries | `rw` queries |
|---|---|---|
| 8 | 3,075 | 12,257 |
| 12 | 49,155 | 196,577 |
| 16 | 786,435 | 3,145,697 |

Both grow ×4 for every two lets, which is 2^k. The statement alone is
already 2^k in the gate, which is the typing memo's issue (§3.1), not
`rewrite`'s. The rewrite adds its own 2^k on top in both the gate (motive
and transport checked as trees) and in the frontend, whose time also grows
×4 per two lets at the larger k and is a growing multiple of the
statement's own frontend time. The probe does not split that frontend time between the
abstraction walk and occurrence matching. Neither part is shared-size
today, and mengine's version of this family is linear.

### 4.3 What to build for relational and repeated rewriting

`issues/rewrite-setoid-relations.md` (milestone `tac-general`) wants
rewriting along relations through `relational_context`'s compatibility
evidence, which is Rocq's `setoid_rewrite`. That is the tactic whose
superlinear behaviour Gross, Erbsen, Philipoom, Agrawal and Chlipala
diagnosed (*Towards a Scalable Proof Engine*, 2023; partial matches and evar
creation cubic, proof terms quadratic in binders), and mengine is the
follow-on that removed it. The parts that transfer:

- **Bottom-up, one step per changed node.** Each changed node gets one
  congruence step (`Respects2`/`PreservesRelation` instances for Heather,
  `app_cong` for mengine), unchanged nodes get none, and steps chain by
  transitivity. The proof is linear in the changed part of the DAG, not in
  the goal's tree size.
- **A node memo, persistent across calls** keyed by (equation, context,
  node). It is what makes a shared subterm cost once, and it is what makes
  `repeat`-style rewriting linear rather than quadratic.
- **A head prefilter**, which Heather's `rewrite` already has
  (`issues/rewrite-keyed-conversion-matching.md`).
- **Binders need a relation-preserving binder rule.** mengine uses
  functional extensionality, an axiom Heather does not assume
  (`lib/std/itree/itree.hthr` says so). Heather's route under a λ is the
  pointwise relation and a `Respects` instance for the binder, as
  `setoid_rewrite` does.

None of this needs to be trusted: the output is an ordinary proof term the
kernel checks, which is the shape `rewrite` already has. The log entry on
`rewrite-setoid-relations` records this as its design reference.

## 5. Native compilation

Taking Heather's native goals one at a time:

- **The compiler runs by kernel evaluation.** That cost lives in the value
  machine: environments, closures, the kept value caches, the depth budget.
  mengine's reduction is a term rewriter, the design Heather left because
  nested eliminator β copied branch bundles exponentially. Nothing to take.
- **Certificates of compiled code.** Since the B2 burn, `compile-x86` proves
  a program by evaluating a verified compiler, not by generating per-node
  theorems. The generated-certificate size problems mengine's sharing would
  have addressed (`issues/generated-source-semantic-term-sharing.md`) were
  deleted with that code.
- **Program proofs that thread machine states.** This is where mengine's
  property matters. The 216-second `read_print_after_read` was a native
  program proof whose `let` chain over machine states fanned out. `have`
  covers the opaque lets; the transparent ones (`s1 = w.after`, needed by
  later proofs) wait on the typing memo of §3.1. Any future Wp-style proof
  about a longer program has the same shape.
- **mengine's symbolic-execution case study** is a straight-line `exec`
  proof by repeated lemma application and `get_put` rewriting, the
  per-program style that burn B1 retired. It is a good stress test for a
  proof engine and not a design Heather is pursuing.
- **"DAG" in the x86 lowering** (`function-ir-shared-multi-result-dag`) is
  about sharing computed values between results of generated code, not about
  proof terms. mengine says nothing about it.

## 6. What not to take, and why

- **Pointer-unique variables and uplinks.** They remove shifting at the
  price of a context tree, an order-maintenance structure, binder refreshing
  in substitution, and parent lists on every node. Heather's bounds memo
  already gives the skip test, and the `□` rule needs syntactic `==` on
  terms, which de Bruijn terms make structural.
- **Typing at construction as a kernel API.** It makes every constructor
  caller trusted. Heather keeps one trusted checker over finished terms,
  with the elaborator outside it, and gets per-node sharing by memoizing
  inside that checker (§3.1). mengine is still a useful precedent for
  `issues/heather-checked-construction-api.md`, whose "useful errors at
  construction" is what mengine's null-on-failure constructors deliver, but
  there the kernel check of the output stays, as that issue requires.
- **In-place hole filling.** See §2. Heather's metas never reach the kernel.
- **Conversion derivations.** No consumer: Heather's kernel decides
  conversion and nothing downstream needs the derivation.

## 7. Follow-up

Filed:

- `issues/subst-shared-node-memo.md` (kernel): a per-traversal memo in
  `Mapper` for nodes reached more than once, so a shifted let alias stays a
  DAG. The residue that `kernel-typing-memo-on-node-identity` named.
- `issues/tactic-scaling-bench-families.md` (tactics): mengine's four
  rewriting shapes, plus `proof-let-substitution-cost`'s `fan`/`dep`, as
  frontend bench families with recorded exponents.

Logged:

- `kernel-typing-memo-on-node-identity`: mengine as precedent, child-pair
  keying for applications, and that its lack of fuel is why it does not
  meet the determinism constraint.
- `rewrite-setoid-relations`: §4.3 as the design reference.
- `open-payload-shift-copies`: the no-shift representation as the third
  known alternative, and why it is not taken.
- `heather-checked-construction-api`: mengine's constructors as precedent
  for errors at construction, with the kernel check kept.

Worth telling the author, if the paper invites comparison: Heather's
environment machine is the answer to mengine's substitution-based
reduction on nested eliminators, and Heather's bounds memo shows the
minimal-context skip needs no order maintenance in an indexed kernel.
