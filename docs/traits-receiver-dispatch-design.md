# Receiver dispatch through instances: `x.op(y)`

Status: **round slice**, carved out of `docs/traits-design.md` §12 and
`docs/traits-layer1-design.md` §8 (the residue entry this round retires).
Tracking issue: `issues/traits.md`. Layers 1 and 2 are
`docs/traits-layer1-design.md` / `docs/traits-layer2-design.md`; their §7/§9
corrections are constraints here.

This document states only what this slice decides. §7 is the "what
implementing this corrected" section the house style requires; §8 is the
residue.

**No kernel change, no metatheory obligation, no new resolution machinery.**
Dispatch builds *one goal type* and calls layer 2's `resolve_goal`; the term
it emits is a record projection applied to arguments, which is what the
writer's own explicit spelling already elaborates to.

---

## 1. The problem

After layer 1 an instance member lands as the global `Rat::Monoid::op`, whose
qualifier is split at the **first** `::` (`names::split_qual`), so its
`member_bases` entry is `Monoid::op` and not `op`. A receiver call `x.op(y)`
therefore reaches neither the member (`member_head` looks for `Rat::op`) nor
the field (`op` is a field of `Monoid<Rat>`, not of `Rat`). Two carriers want
it:

- **concrete** — `x: Rat` with `instance Monoid<Rat>` declared;
- **generic** — `x: A` inside `fn f<A> requires m: Monoid<A> (x: A, y: A)`,
  where the dictionary is a binder and not a registry entry.

## 2. The decision: dispatch *is* a resolution goal

`x.op(y)` where `op` is a field of some class `C` becomes

```
goal   := C<typeof(x)>            -- built in kernel form, §2.1
dict   := resolve_goal(goal)      -- layer 2, unchanged
result := π_op(dict) (x, y)       -- the projection, receiver first
```

One route for both carriers. A concrete carrier is resolution at a closed
goal (step 2 of layer 2 §3 returns the registry instance `Rat::Monoid`); a
generic carrier is resolution at an open goal (step 1 returns the `requires`
binder `m`); and a carrier with no binder but a derivable instance
(`Pair<Nat, Nat>` under the generic `Pair` instance) works with no extra rule,
because backchaining is what step 2 already does. The alternative — a direct
scope scan for "any local whose type is a class with member `op`" — is a
second search with its own order, its own shadowing story and its own
diagnostics, and it would still not reach the derivable carrier. It is not
built.

The layer-2 order is inherited whole, and that *is* this round's answer to
"the same member reachable two ways": `resolve_goal` consults locals before
the registry (§3 step 1 returns), so a dictionary in scope wins over an
instance in the table. Nothing here re-decides it; §5.2 pins that it holds
through dispatch.

### 2.1 The goal is built, not parsed

The receiver's type arrives from `elab_infer` as a **kernel** `Type` with its
level, and `lower_instance(cx, C, [(recv_ty, recv_lvl)], [], span)` is exactly
what `lower_named` calls after lowering a written `C<T>`'s arguments. So the
goal is the same type the writer would have got by writing `Monoid<Rat>` — no
surface round-trip, and an **open** carrier (a type parameter, whose kernel
type is a `cx.tyvars` entry) needs no special case.

The narrowing this exposes: only a class with **exactly one** type parameter
participates in dispatch. A second parameter has nothing to be built from —
the receiver fixes the carrier and nothing fixes the rest — and a goal with a
meta in it is precisely what layer 2 §4 refuses to resolve. Multi-parameter
classes are skipped by name (§4, rule 7); their members are reached by the
explicit projection, which is what they were reached by before this round.

### 2.2 The emitted term is the projection, not the member global

`Rat::Monoid::op` and `Rat::Monoid.op` are definitionally equal (layer 1
§4.2): the instance value is a `fn` whose body is a record literal whose `op`
field *is* that global, so the projection δ-unfolds and β/π-reduces to it.
Dispatch emits the **projection**, for three reasons and one accepted cost:

1. It is the only form that exists in all three cases. A local dictionary and
   a derived instance have no member global to name; emitting the member
   global for concrete carriers alone would mean two emitted shapes and two
   test stories for one surface spelling.
2. It is *literally* what the writer's explicit spelling elaborates to —
   `Rat::Monoid.op(x, y)` and `m.op(x, y)` are `Dot` on a resolved receiver
   and take the same `apply_projection` path. So "the dispatched term equals
   the explicit spelling" is syntactic agreement, and `refl` between them is
   not even a conversion.
3. Its *type* is the class field's type at the carrier, which is what a
   diagnostic about a mis-applied argument should be talking about; the member
   global's type additionally carries the instance's own telescope.

The cost: a downstream error prints `Rat::Monoid.op` rather than the member's
name, and conversion has to δ-unfold the instance value to reach the member's
body. Both are the price of the explicit spelling too, so nothing regresses
relative to what a writer can already write.

## 3. The algorithm

In `resolve_dot`, after the record-field branch and after `member_head`, and
only for a call (`args: Some`):

```
dispatch(cx, recv, name, args, span) -> Option<DotResolution>:
  if name is no class's field           -> None            -- cheap negative test
  (recv_t, recv_ty, recv_lvl) := infer(recv)  or return None
  owners := [ C | C in classes, visible here, C DECLARES name ]
                                          sorted by qualified class name
  cands  := [ C in owners | |C.params| == 1 ]
  if cands empty -> None, or the multi-parameter refusal   -- §4 rule 7
  hits := []
  for C in cands:
      goal := lower_instance(C, recv_ty, recv_lvl)   -- §2.1
      if let Some(d) = resolve_goal(goal, display "C<head>", trace):
          hits.push((C, d))
  match hits:
      []       -> if another reading exists: None       -- §4 rule 5
                  else: the trace, as the diagnosis
      [_, _..] -> error naming every hit                -- §4 rule 3
      [(C, d)] -> if another reading exists             -- §4 rule 2
                     -> error naming both
                  else Dispatch(π_name(d), [recv] ++ args)
```

**Declares**, not "has a field of that name": as first shipped this read
`name in C.fields`, which is the *flattened* list, so every class in an
`extends` chain answered for an inherited member and the ambiguity rule below
made it undispatchable forever. Owner-keying is
`docs/traits-owner-dispatch-design.md` (2026-08-08); it changes the candidate
set and nothing else here, and §4's rules stand verbatim.

The **cheap negative test** is a `HashSet<String>` of every declared class's
field names, maintained beside `record_fields` and `member_bases` and for the
same reason (`docs/surface-records.md` §4.2): a `.foo()` call where `foo` is
nobody's class field infers no receiver, builds no goal and calls no resolver,
so every call that predates classes costs exactly what it cost. Like those two
it is program-wide and carries no visibility — a negative test may not depend
on which module is being read, and visibility is enforced where it belongs, in
candidate selection.

"Visible here" is `key_of(C.name) == the key C is stored under` — the ordinary
§4 name regime and not a second visibility rule (§4, rule 6).

"Another reading exists" is: `member_head` returned a qualified `D::name`, or
`name` is bound in scope (`shadowed`, or a constructor), or `name` is one of
the receiver-shaped builtins (`map`, `fold`, `head`, `tail`, `cons`, `cong`,
`inj`, `absurd`), which are Rust rather than declarations and so are invisible
to `shadowed` (§7.2). It is computed as the *description* of that reading, not
as a flag, because both diagnostics it feeds have to name it.

**The receiver is the field's first explicit argument.** A class field is a
function *type*, not a declaration, so it has no `ParamMeta` and no `self`
marker to consult; position 0 is what `subject_index` defaults to for
everything unmarked (`issues/method-receiver-position.md`), and it is what
`m.op(x, y)` already means. `self` conventions are untouched by this round.

## 4. The ambiguity rules

Deterministic, no priorities, decided before implementing.

1. **A field of the receiver's own type wins, and dispatch is not attempted.**
   `docs/surface-records.md` §4.4 already says the field wins unconditionally,
   and the reading is evidence of a different kind: the projection is the
   receiver's own structure, not a name attached elsewhere. Declaring
   `instance Monoid<D>` where `D` itself has a field `op` therefore does not
   reinterpret an existing `d.op(…)` — it adds nothing to that call — which is
   what the growth invariant asks (`docs/modules-design.md` §4).
2. **An ordinary type-owned member and a class member at one carrier are an
   error naming both.** Precedent and invariant agree:
   `member_head`'s own rule already refuses to race a bare `name` against a
   `D::name`, for the reason that preferring either would let a library
   addition silently reinterpret a call. `Rat::op` and `Rat::Monoid::op` are
   two attached names in exactly that sense. The message names both spellings
   (`Rat::op(…)`, `Rat::Monoid.op(…)`), since writing one of them is the fix.
   Same rule, same message shape, for a bare `op` in scope or a builtin.
3. **Two classes both *declaring* the same member name, both resolving at the
   carrier, are an error naming both** — never declaration order, never a first
   hit. (Two classes in one `extends` chain are not two candidates: only the
   declaring one is, §3.) Every
   candidate is tried even after one succeeds, because the error is the point.
   The message names the classes and the goals (`Monoid<Rat>`, `Group<Rat>`).
4. **Scope beats registry**, by inheritance: `resolve_goal` step 1 returns
   before the registry is consulted (layer 2 §3). Pinned in this round's suite
   with a *distinguishing* local — a dictionary whose `op` is not convertible
   to the registry instance's — because a `refl` against an accidentally equal
   dictionary would pin nothing.
5. **A failed dispatch removes no reading.** When no candidate resolves and the
   call has another reading, that reading runs exactly as before and the search
   is forgotten — which is what keeps a class field named `map` from breaking
   `xs.map(f)` at a receiver with no instance, and why rule 2's test is about a
   *successful* dispatch. When it has none, the search **is** the diagnosis and
   is reported in place of the "unbound name `op`" the desugaring would have
   produced (§7.1).
6. **Modules.** Candidate classes are those a reference here would resolve to
   (`key_of`), so an unimported module's class never captures a call and two
   visible classes of one name disqualify each other exactly as a written
   reference would be ambiguous. Instances are the registry's business and
   inherit layer 1 §4.1's regime unchanged; dispatch adds no visibility rule of
   its own.
7. **Two shape narrowings, refused by name rather than guessed.** Dispatch
   needs a call (`x.op` with no parentheses stays "a bare `p.f` is never a
   method call", `docs/surface-records.md` §4.2), and it needs a
   single-parameter class (§2.1). A member of a multi-parameter class says so —
   the class named, the projection spelled — rather than falling out as an
   unbound name; under rule 5 it says it only when there is no other reading.

## 5. Interaction with what `.` already does

| receiver / name | before this round | after |
| --- | --- | --- |
| `m.op(x, y)`, `m: Monoid<A>` | field projection applied | unchanged (rule 1) |
| `Rat::Monoid.op(x, y)` | projection of a global | unchanged (rule 1) |
| `p.trans(q)`, `xs.map(f)`, `p.absurd()` | method desugaring / builtin | unchanged — `trans`/`map` are no class's field, so the cheap test returns first |
| `xs.nth(k)` with `fn List::nth` | `member_head` → `List::nth` | unchanged (dispatch runs after, and only if `nth` is a class field) |
| `d.op(…)` where `D` has field `op` | projection | unchanged (rule 1) |
| `x.op(y)`, `x: Rat`, `instance Monoid<Rat>` | unknown name `op` | **dispatch** |
| `x.op(y)`, `x: A`, `requires m: Monoid<A>` | unknown name `op` | **dispatch**, through `m` |
| `x.op(y)`, `x: Pair<Nat, Nat>`, generic instance | unknown name `op` | **dispatch**, through the derivation |
| `x.op(y)`, `op` a class field, no instance | unknown name `op` | the resolution trace (rule 5) |

## 6. Acceptance

Per `docs/testing-generated-terms.md`, varying an **open** carrier, a
**checking** position, a **neutral** receiver and a **negative control** for
each positive:

1. Concrete carrier: `x.op(y)` elaborates, computes, and is `refl`-equal to the
   explicit spelling `Z::Mag.op(x, y)`; in checking position (a checked
   argument and an annotated `let`); on a neutral receiver (a parameter and a
   computed call) as well as a literal one; and at `Nat`, a kernel type with no
   declaration behind it.
2. Generic carrier: under `requires m: Monoid<A>`, the dispatched term and
   `m.op(x, y)` agree by `refl` at an open carrier and a neutral receiver.
3. Derived carrier: `Pair<Z, Z>` with the generic `Pair` instance and no
   binder in scope.
4. Negatives: two classes sharing a member name at one carrier; an ordinary
   `Rat::op` beside the class member; a bare `op` in scope beside it; a
   carrier with no instance and no dictionary (the trace); a member of a
   two-parameter class (refused by name, not mis-dispatched).
5. Rule 1 pinned positively: a record with a field `op` *and* an instance at
   it still projects the field.
6. Rule 4 pinned with a distinguishing local dictionary, and its negative
   control: with that dictionary in scope the registry's answer no longer holds.
7. Rule 6 pinned across modules: an imported class dispatches, an unimported
   one captures nothing. Rule 5 pinned in both directions, and a class field
   named like a builtin makes the builtin call ambiguous rather than silent.
8. The layer-1 and layer-2 suites green unedited; the full suite green with
   `lib/ir_v1.hthr` unchanged.

## 7. What implementing this corrected

### 7.1 A failed dispatch needs no error to rewrite

Rule 5 was first written as "carry the trace into the method reading and swap
its error if it also fails". That needs a judgment about *which* errors are
swappable — an argument-type mismatch inside the fallback is more informative
than any search — and it threads an error through a resolution result to get
it. It is unnecessary: whether the call has another reading is decidable
**before** the fallback runs, from `member_head`'s answer, `shadowed`, and the
builtin list. So dispatch either returns "not a dispatch" and the other reading
runs untouched, or reports its search — and it reports it exactly when the
alternative would have been `unbound name \`op\``. §3 and §4 rule 5 are written
as implemented. The pair that pins it:
`a_failed_dispatch_falls_back_to_the_bare_reading` and
`a_carrier_with_no_instance_reports_the_search`, which differ only in whether a
bare `op` exists.

### 7.2 `shadowed` cannot see the builtins, and that is a live hole

`map`, `fold`, `head`, `tail`, `cons`, `cong`, `inj` and `absurd` are Rust arms
of the application path, each gated on `!self.shadowed(cx, name)` — they are
reachable without any declaration, so `shadowed` answers `false` for them.
Without naming them, a `class Mapper<A> { map: A -> A }` with an instance at
the receiver's carrier would have made `xs.map(f)` **silently** the class's
member, which is precisely the reinterpretation the growth invariant forbids.
The list is therefore a named constant read only by dispatch, and
`a_class_field_named_like_a_builtin_is_ambiguous_not_silent` is the pin. The
hole was found by writing the test, not by reading the code.

### 7.3 The receiver's type is *inferred* three times on the dispatch path

`resolve_dot`'s record branch, `member_head` and dispatch each call
`elab_infer(recv)`, and dispatch's is the third. This is the existing shape (a
member call already infers twice) and it is bounded by the cheap negative test
— nothing that is not somebody's field, member base *and* class member pays it
— so it is recorded rather than fixed: caching an inferred receiver across the
three readers is a `resolve_dot` refactor with its own regression surface, and
this round is not it.

## 8. Residue, with owners

- **Multi-parameter classes are not dispatchable** (§2.1) — `issues/traits.md`.
  The goal built from the receiver alone has metas in the non-carrier
  positions, which layer 2 §4 declines to resolve on purpose. It wants the same
  nested-resolution world that layer 2 §10 already owns for modes, and should
  land with it rather than beside it.
- **A class field has no `self`** — `issues/traits.md`. The receiver is always
  the field's first explicit argument (§3), because a field is a *type* and has
  no `ParamMeta` to mark. A class whose member wants the carrier elsewhere
  (`at: Nat -> A -> Nat`) is not dispatchable and gets a type error rather than
  a message saying so. Marking a class field's subject is a surface question of
  its own.
- **A bare `x.op` never dispatches** — this document and
  `docs/surface-records.md` §4.2. The standing rule is that a bare `p.f` is
  never a method call; a partially applied class member would be the first
  reason to revisit it, and no corpus asks yet. It now has its first
  customer, from the other side (2026-08-08): a bare **type** projection
  `Z.op : Z -> Z -> Z` is writable and partially applicable
  (`docs/traits-type-projection-design.md` §3.2 — a type subject is not an
  argument, so there is no desugaring for bareness to block), so the
  asymmetry is observable in one file.
- **Two visible classes of one *name* disqualify each other silently** — the
  candidate filter asks `key_of`, which answers `None` for an ambiguous name,
  so neither class is a candidate and the call reports whatever its fallback
  says. Truthful (the class name *is* ambiguous) but not helpful; the fix is to
  distinguish "no candidate" from "ambiguous candidate" in the message.
  `issues/traits.md`.
- **Trial cost** — every candidate class is resolved even after one succeeds,
  because the ambiguity is the point. That is layer 2 §10's "trial cost" entry
  with one more multiplier, and it is filed there, not re-filed here.
