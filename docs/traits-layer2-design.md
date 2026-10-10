# Traits, layer 2: the instance resolver and `:= infer`

Status: **round slice**, carved out of `docs/traits-design.md` (the record) per
its §13 item (b), with (c) — trace-as-data diagnostics — riding along.
Tracking issue: `issues/traits.md`. Layer 1 is
`docs/traits-layer1-design.md`; its §8 is this round's inherited work-list and
its §7 corrections are constraints here.

This document states only what layer 2 decides. §9 is the "what implementing
this corrected" section the house style requires; §10 is the residue.

**No kernel change, no metatheory obligation.** Resolution is policy: it
*proposes* a term, which is then checked — by the kernel, at the goal type, at
the moment it is proposed (§4.4), and again at the declaration gate. The worst
failure mode is a rejected or slow elaboration.

---

## 1. One mechanism: the solver-default parameter

Layer 2 adds exactly one parameter kind. A **solver parameter** is a
declaration parameter whose argument, when the caller omits it, is produced by
a solver run in the caller's elaboration context (record §8). This round ships
one solver, `infer`, and two spellings for it:

```
fn sum<A> requires m: Monoid<A> (xs: List<A>) -> A { … }   -- the class spelling
theorem blah(x: Nat, hx: x > 0 := infer) : … { … }         -- the general one
```

Both desugar, **in the parser**, to the same thing: a parameter with
`implicit = true` and `solver = Some(Infer)`. `requires` binders are moved to
the front of the parameter list (they are what the later parameters' types
mention), exactly as an `instance`'s `requires` binders already precede its
members' own parameters.

Consequences, all deliberate:

- A solver parameter is filled by resolution when omitted, and passed
  **explicitly under `@`** when the writer wants to choose:
  `@sum(m, xs)` (type arguments are never passed at a call site, even under
  `@` — `issues/at-and-type-arguments.md`). "An instance is an ordinary value"
  is preserved; resolution only fills what is omitted.
- A solver parameter is an ordinary kernel Π binder. Nothing about the emitted
  term changes, so nothing about the trusted base does.
- `requires` on a *function* is new surface; `requires` on an `instance` is
  layer 1's, and this round changes what it means at a **use** site (implicit,
  resolved) without changing what it builds.
- `:= infer` is refused on a parameter that is already `{implicit}` (one
  filling discipline per parameter) and on a `self` parameter (its argument is
  the receiver, which is never omitted).
- A `requires` binder's type is a **class reference** (`name<args>`), not a
  general type — see §9.4.

## 2. The goal, and the seam layer 3 will take

A **resolution obligation** is `(goal: Type, level, whose parameter, span)`.
The goal is a kernel type — the parameter's declared domain, zonked at the
call site. The resolver's internal entry point is

```rust
fn resolve_goal(&self, cx: &Cx, goal: &Type, lvl: &Level, tr: &mut Trace)
    -> Option<Term>
```

i.e. **(goal, scope) → term**, deterministic, with the trace threaded through.
That is the record §10 contract with the goal in kernel rather than quoted
form; the seam is the argument, not the algorithm — a layer-3 resolver
receives `Code(Γ ⊢ Ty)` in this position and everything above it (the
obligation, the scheduler, the trace) is unchanged. Nothing in the resolver
consults the surface syntax of the goal, which is what makes that swap
possible.

## 3. The search: ascending scopes, then the registry

Record §5's order, in one function (preceded by a table lookup that is not a
scope: a hit in the canonical derived table (§8) is a reference to the very
value the registry route would rebuild, so it cannot shadow anything):

1. **Locals, innermost first** — every binder of `cx` whose type is
   convertible to the goal, then every `let` alias. Innermost-first is what
   makes "locals of instance type beat parameters" true without a second rule:
   a `requires` binder is a parameter, a `let`-bound dictionary is deeper.
   *An explicit value in scope always wins over derivation*, because this step
   runs first and returns.
1b. **The same scope again, by upcast** — a binder or alias whose class is a
   *descendant* of the goal's answers through the canonical parent record
   (`docs/traits-owner-dispatch-design.md` §3, 2026-08-08). After the exact
   pass and before the registry: an exactly-typed value the writer named beats
   one the resolver assembled, and an assembled scope answer still beats a
   derivation. Skipped outright unless the goal's type is a class.
2. **The registry** — the layer-1 instance table, which is the module scope
   and the wider registry both (declaring is registering, and the table is
   already subject to `docs/modules-design.md` §4's name regime through the
   instance's canonical name).

There is no third source. A goal whose type is not a class (`x > 0 := infer`)
gets step 1 only, and its failure trace says so.

### 3.1 Candidate selection is by trial, and the trial is checked

The record says "match the unique instance head on input positions". The
implementation selects differently and reaches the same place: it takes the
candidates of the goal's class **in a deterministic order** (by canonical
name), builds each, and **verifies the built term against the goal with the
kernel** (§4.4); the first that verifies wins.

Why not head-keyed matching: recovering a carrier from a *lowered* goal type
is not a lookup. Type parameters are monomorphized
(`docs/inductive-tier0-lowering.md` §2), so `Monoid<Pair<Nat, Nat>>` is a Σ
whose components are the instantiated field types — the carrier appears only
where the class's fields put it, and reading it back means matching the
class's surface field list against the lowered type. Trial needs none of that,
and given the declaration-time overlap discipline (§5) *at most one candidate
can verify*, so the outcome is the same function of (goal, scope) that keying
would have produced. The price is bounded — candidate counts per class are
small, a failed trial is a discarded `Result` — and the payoff is a better
trace: the failures are what the diagnostic reports (§7).

Determinism: the candidate order is the sorted canonical-name order, not the
declaration order and not a `HashMap` iteration order.

*Amended 2026-09-09.* The order is canonical-name order **within** two groups:
the instances registered at the goal carrier's head first, then the rest. The
head is not recovered from the lowered goal — the paragraph above still holds
— but read off the solver parameter's *written* type at the call site, where
its type argument is either a type parameter the application has already
applied or an applied former spelled out. Where nothing can be read the order
is the plain one. Ordering rather than keying, because a candidate at another
head can still fit by unfolding the goal, and that fit is kept; what changed
is that it is no longer built *first*, since building it is where the cost
went over computed operands (`docs/reflection-through-decide-instances-design.md`
§2–§3).

### 3.2 Backchaining is the existing insertion machinery

A candidate is built by elaborating the bare reference `InstanceGlobal` in
**checking** position against the goal. That is the whole of backchaining:

- the instance's type parameters are the leading implicit prefix, minted as
  metas and solved from the expected type by the bare-reference route
  (`docs/unifier-completeness-design.md` §5.3);
- the instance's own `requires` binders are solver parameters (§1), so they
  become resolution obligations of *that* call and recurse.

No second search algorithm exists. A generic instance's subgoals are found by
the same three-step search at the same call, which is also why a cross-member
call inside an `instance` block finds the block's `requires` binders: they are
locals there, and step 1 returns them.

A depth cap (32) guards the recursion; declaration-time termination (§6) is
what makes the cap unreachable, not what the cap replaces.

## 4. Scheduling: the obligation rides `Sol::Withheld`

A solver parameter's slot is minted exactly like an implicit's, and the
obligation joins `apply_implicit`'s existing deferred-argument machinery
(`docs/unifier-completeness-design.md` §§3–4):

1. the argument loop mints the meta and pushes a `ResolveOb`;
2. expected-type-directed solving runs (unchanged) — this is what solves the
   type parameters a goal mentions;
3. the **existing** retry-to-fixpoint loop now discharges two obligation
   kinds: a deferred argument (check it) and a resolution obligation (resolve
   it). An obligation fires only when `zonked(dom)` is `Some`, which is
   record §6.4's "input positions meta-free" — with modes cut (§10) every
   position is an input, so the two conditions coincide;
4. a resolution obligation still blocked at the end is reported at the
   argument span — the call's span for the parameter it belongs to — naming
   the parameter and the metas it waits on.

Termination is unchanged: the obligation list is fixed after step 1, each pass
moves at least one slot out of `Withheld` or stops, and resolution never
writes `sols`.

### 4.4 Every proposal is kernel-checked at its goal

`elab_check` is not a conversion check — the kernel is the gate, at the
declaration (`docs/unifier-completeness-design.md` §2). A resolver that
selects by trial cannot wait for that gate: a wrong candidate would be
*accepted* by the elaborator and rejected pages later. So each proposal —
scope hit and registry build alike — is checked with
`typing::check_term` at the goal type, in the use site's context, before it is
returned. This is the round's one new kernel call site, and it is a check, not
a trust: the failure it produces is "this candidate is not it", never a term.

## 5. Overlap: the layer-1 head key *is* the check

Layer 1 registers one instance per **(class, carrier-head)** and refuses a
second with an error naming both (its §4.1). That is exactly record §6.2's
"two instances whose input heads unify is a declaration-time error naming
both" for every class shape this round can express, so **no new machinery is
built**: the check exists, and this document is where it is claimed as the
overlap discipline rather than as a naming collision.

> **Amended 2026-08-17** (`docs/instance-resolved-key-design.md`). The key's
> carrier component is the head's **resolved declaration**, so two carriers
> whose heads share a *name* across modules (`nat::Le`, `int::Le`) are two
> keys and coexist. That is not a hole in the overlap discipline: their heads
> do not unify — they are different declarations — so record §6.2 never asked
> for them to be refused, and the old key was refusing more than the
> discipline required. Within one carrier declaration nothing changed.

Two instances whose heads unify but are not equal (`C<Pair<A, B>>` and
`C<Pair<Nat, B>>`) share a head and are therefore already refused — the
refusal is *coarser* than unification, never laxer, so nothing overlapping
slips through. The agreement-proof escape (record §6.2, §4) is not built: it
needs a second registered value at one key, which the layer-1 name scheme has
no room for. Residue, §10.

## 6. Termination: structural decrease at the declaration

Checked when the `instance` is declared, over **surface** types, against the
instance head. For each `requires` binder whose type is a class reference
`D<S⃗>` (a non-class `requires` type is an `infer` goal, not a subgoal, and is
skipped):

- `size(S⃗) < size(T⃗)`, where `size` counts type constructors and variable
  occurrences of the written arguments and `T⃗` is the instance head's
  arguments; and
- every type variable occurs in `S⃗` no more often than in `T⃗`.

This is Paterson's condition. `Monoid<A>` against `Monoid<Pair<A, B>>` passes
(1 < 3, one `A` against one `A`); `C<Box<Box<A>>>` against `C<Box<A>>` is
refused, and the refusal **names the offending binder and its type**. The
escape is record §6.3's: a named instance value, applied explicitly, which is
what an instance already is.

## 7. The trace is data

A failed resolution raises `ElabError::Resolution { goal, span, trace }`, where
the trace is a flat list of records

```rust
struct TraceLine { depth: usize, key: &'static str, value: String }
```

with a closed key vocabulary — `goal`, `scope`, `local`, `class`,
`candidate`, `rejected`, `subgoal`, `no-class`, `no-instance`, `blocked`,
`depth` — rendered one per line, indented by `depth`. (Amended 2026-10-10:
a proposition goal adds `computed`, `rules` and `no-rule`,
`docs/positivity-evidence-design.md` §9.) Nested subgoal failures
are the same list at `depth + 1`, so a whole search is one flat, machine-
readable structure and not a nested prose paragraph
(`issues/ai-facing-tooling.md` §7; the same doctrine as the e-graph explain
port).

The rendering is the diagnostic's own (`ElabError::render`), so the structure
survives to any consumer that wants it; the *values* are rendered types and
names, which is the layer at which the surface can say anything at all.

The goal is displayed as the parameter's **written** type (`Monoid<A>`, with
`A` the callee's own type parameter as the writer spelled it) — a display, not
a key: nothing keys on it (§8). Rendering the *instantiated* goal would mean
rendering a lowered kernel type, which §9.2 explains no component can do
totally; naming the parameter and its written type is what the surface can say
truthfully.

## 8. Canonical derived globals

Record §6.1: the first derivation of `Monoid<Pair<Nat, Rat>>` mints a real
global and every later resolution returns it by reference.

**Where minting happens.** Not mid-declaration: a global's reference is
`GlobalVar(|Ψ| - 1 - abs + goal_base)`, so growing Ψ while a declaration is
being elaborated invalidates every reference already built in it. Minting
therefore happens **between items**, from a queue the resolver appends to.
The consequence is stated rather than hidden: the *first* use site of a
derivation inlines its copy — it cannot reference a global that does not exist
yet — and every later use site references the mint. One value, reached by
name, one use site later than the record's wording suggests. (The alternative,
rolling the item back and elaborating it again once the queue is drained, was
rejected: it doubles the elaboration of every item that resolves anything new,
and it buys only the first use site.)

Queue entries carry the Ψ length they were captured at, because the item goes
on to push its own globals and a stored type's `GlobalVar`s are relative to
the Ψ that was; table entries carry it for the same reason. Only goals
captured while no goals are in flight (`goal_base == 0`) are queued, which is
what keeps that rebasing a single shift.

**What is canonicalized.** A *derivation* — a goal answered by a
**parameterized** instance (a generic one, or one with `requires` binders).
A declared instance's value is already one global reached by name, so minting
a second one for it would duplicate the very thing the table exists to keep
single. A goal answered from the scope is not canonicalized at all (design
§3, and it would not be closed).

**What is mintable.** Only a goal that is *closed* and whose derivation used
the registry all the way down — a derivation that hit the scope has free local
variables in it and is not a global. Both are decided the honest way: the mint
attempt kernel-checks the statement and the body in the empty context and
drops the entry if either fails. A dropped entry costs sharing, never
correctness.

**The key and the name.** The derived table is keyed by the goal type **up to
conversion** (a small vector, scanned with `conv_type`) — the right notion of
"the same goal", and the one that needs no encoding of a kernel type. The
name is `#{Class}#{k}`, minted in derivation order. This is *not* the record's
content-addressed name; see §9.2 for why and what it costs.

Locals and scoped values never touch this table: step 1 of the search returns
before it is consulted, and nothing writes it but a mint.

## 9. What implementing this corrected

### 9.1 Selection is by checked trial, not by head keying

§3.1, recorded there. Evidence: the goal arrives lowered and monomorphized, so
"the head of the carrier" is not readable from it without matching the class's
surface fields against a Σ; trial plus a kernel check is the same function of
(goal, scope) under the overlap discipline, and produces the trace for free.

### 9.2 Derived globals are keyed by conversion and named by ordinal

§8. The record (§12, "content-addressed minting") asks for a name derived from
the (class, carrier-syntax) key so that minting is idempotent *across*
elaborations and orders. Two facts stand in the way, and both were measured
rather than assumed: the carrier is not readable from the lowered goal (§9.1),
and no component can encode a kernel type as a string totally — `Debug` is
deliberately budget-bounded (`crates/kernel/src/fmt.rs`), and a bounded
encoding used as a *key* is a collision, i.e. the wrong instance.

What is kept: minting is idempotent **within** an elaboration (one mint per
goal up to conversion), which is what the coherence invariant needs
program-internally, and the name is a deterministic function of the
elaboration order, which is itself deterministic. What is lost: cross-run and
cross-module identity of the derived name — the parallel-checking interaction
record §12 hoped to dissolve. It needs a total structural encoding of kernel
types (a real content-address), which is its own small round and is filed as
such (§10).

### 9.3 `requires` at a *use* site is implicit; layer 1's two pins move

Layer 1 pinned that a cross-member call passes its `requires` binders
(`a_generic_instances_cross_member_reference_passes_its_requires`) and that a
generic instance's value is applied to them positionally
(`a_generic_instance_applies_and_computes`). Both were stated *as* layer-1
rules that layer 2 would change (layer 1 §4.2, §8). They are edited, not
deleted: the first now calls the member without its binders and the second
writes the instance value bare — and the positional spellings become the
negative controls, since a solver parameter has no positional slot.

The assembled instance value (layer 1 §4.3 rule 1) correspondingly stops
applying the member reference to the `requires` binders: `f<A, B>` is now a
partial application whose remaining implicit prefix is the solver parameters,
which resolution fills from the block's own binders. Layer 1 §7.3's finding
(a member reference writes its type arguments explicitly) is unchanged and is
what makes that reference legal.

### 9.4 A `requires` binder's type is a class reference, not a type

Layer 1 parsed it with the general type production, which was invisible while
`requires` sat between an instance head and a brace. In front of a *parameter
list* it is not: `requires m: Mag<A> (x: A)` reads `Mag<A>(x …` as a
value-parameter application (`docs/surface-value-parameters.md` §1) and dies at
the `:`. The binder's type is therefore parsed as a class reference, which is
what it always was — and the general goal has its own spelling, `p: T :=
infer`, where no such adjacency exists.

## 10. Residue, with owners

- **Modes (`out`-annotated class parameters)** — `issues/traits.md`, layer
  2.1. Cut, with evidence rather than for time: the construction route builds
  a candidate by checking it against a **fully zonked** goal, and an output
  position that is still a meta has no such goal to be checked against.
  Making outputs real means unifying the candidate's *result* type back into
  the caller's scratch world — a nested resolution world plus a learn-only
  unification across it — which is a slice of its own. Nothing is shipped in
  the meantime: no syntax that does nothing.
- **The agreement-proof escape for overlap** (§5) — `issues/traits.md`. Needs
  two values at one key, which the layer-1 name scheme cannot hold.
- **Content-addressed derived names** (§9.2) — needs a total structural
  encoding of a kernel type; interacts with
  `issues/parallel-checking-and-caching`.
- **`let instance C<T> = v;`** — a scoped override. Step 1 of the search
  already returns any local of the goal type, so the *behavior* exists for a
  plain `let`; the keyword form (and the "shadows without mutating the table"
  claim it makes explicit) is not built.
- **Receiver dispatch through instances** — layer 1 §8's entry, built as
  `docs/traits-receiver-dispatch-design.md` (2026-08-07) by calling
  `resolve_goal` at a goal built from the receiver's type. Nothing here
  changed; the "trial cost" entry below gained one multiplier (dispatch resolves
  every candidate class, since the ambiguity is the point).
- **Trial cost** — §3.1 is O(candidates) kernel checks per goal, and a failed
  candidate's nested resolutions are wasted work. If a corpus ever notices,
  the fix is the head-keyed prefilter that §9.1 explains the cost of, filed
  per the perf discipline rather than built in-round. One more multiplier
  (2026-08-08): step 1b's upcast pass rescans the local scope on every class
  goal the exact pass missed, at a `tag_of` per candidate plus a `build_ctor`
  and kernel check when the ancestor test passes; gated on the goal's type
  being a class, so nothing non-class pays. And one more (2026-08-08, the
  named-upcast round): a dispatched projection that reads *through* an upcast
  (`docs/traits-named-upcast-design.md` §2) still builds and gates the
  assembled parent it then discards (~0.08 s per occurrence on the algebra
  hierarchy); skipping the assembly for a projection consumer needs a
  carrier check that is not a `build_ctor`, which the monomorphized goal
  does not currently offer.

## 11. Acceptance

Per `docs/testing-generated-terms.md`, varying an **open** carrier, a
**checking** position, a **neutral** scrutinee/receiver and a **negative
control** for each positive:

1. `instance<A, B> Mag<Pair<A, B>> requires …` plus a declared `Mag<Z>`:
   `combine` called at `Pair<Z, Z>` without passing `m` resolves and
   *computes* to the right component; the derived global is minted once
   across two use sites, and a nested carrier (`Pair<Z, Pair<Z, Z>>`) mints
   two — the subgoal's and the goal's. The negative control is the program
   whose resolutions are all answered by the scope, which mints nothing.
2. Ascending scopes: a local dictionary shadows the registry at the same
   goal; explicit passing under `@` still works; a `requires` binder inside an
   instance block is found by a cross-member call.
3. Negatives: overlapping instances refused at declaration naming both; a
   self-feeding instance refused at declaration naming the binder; a goal
   whose input positions stay meta-bearing reported at the argument;
   an unresolvable goal reporting a trace that names the scopes consulted.
4. `:= infer` finds a proof in scope, and its failure trace says the goal is
   not a class.
5. The layer-1 suite green but for §9.3's two recorded edits; the full suite
   green, `lib/ir_v1.hthr` unchanged.
