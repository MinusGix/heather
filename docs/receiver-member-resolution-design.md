# Receiver member resolution: owners without inference, disjoint readings

Design record for the namespace round chartered 2026-09-24 on
`issues/type-owned-namespaces.md` (#1a in that day's log). Anchor issues:
`issues/receiver-with-unsolved-implicit-unbound.md` and
`issues/type-member-missing-self-diagnostic.md`. The companion unifier slice
(#1b: `vector-literal-length-pins-implicit`, `unify-succ-under-addition`) is a
separate round and is **not** in scope here.

The round came out of the 2026-09-22 std namespacing refactor and the
2026-09-24 probe of the 80 `@` sites it left in `lib/` (all `BitVec`). Every
mechanism below was reproduced on master `ee4b7f27`. Two items the refactor's
notes listed turned out to be fixed already, and §5 retires them.

## 0. Verdicts (do not relitigate)

- **Evidence shrinks the candidate set; it never ranks candidates.**
  `docs/modules-design.md` §4 and the `member_head` doc comment stand. Nothing
  here prefers the member over an ambient name. §2 removes an ambient reading
  only when that reading *cannot* typecheck at this receiver. That is the
  filter `imported_receiver_head` and `selfref_disjoint` already apply, so
  this round extends an existing rule rather than adding one.
- **The path through full inference is unchanged.** Every new route runs only
  where the current code gives up. A program that resolves today resolves the
  same way, byte for byte.
- **Spelling ladder for the library sweep:** plain call, then a named
  implicit (`BitVec::zero(n := n)`), then `@` as the last resort. Any `@` left
  after the sweep must be accounted for by a filed issue.

## 1. The owner of a receiver whose type is not yet inferable

**Mechanism (verified by reading, and by the qualified-call control below).**
`member_head` (`crates/elab/src/dispatch/member.rs`) finds the owner by
`self.elab_infer(cx, recv).ok()`. `BitVec::zero()`, `R::mk()` and `Nil` are
not inferable on their own: their implicit is solved only by the use site. So
inference fails, `.ok()` swallows the failure, the name stays bare, and the
call ends at "unbound name `iterate_increment`". The one head-directed
fallback, `constructor_receiver_owner`, is gated on written type arguments.

Once the member is chosen, the rest already works. The qualified spellings
check today:

```heather
fn a03(n: Nat) → BitVec(n) { BitVec::iterate_increment(BitVec::zero(), 3) }   // ok
fn a01(n: Nat) → BitVec(n) { BitVec::zero().iterate_increment(3) }            // unbound name
```

**Design.** When `elab_infer(recv)` fails, ask for the receiver's **owner by
its head**, without elaborating it:

| receiver shape | owner |
|---|---|
| a constructor application or bare constructor (`Nil`, `Ok(x)`) | its inductive (`constructor_receiver_owner`, with the type-argument gate removed on this path) |
| a call to a global `g(…)` / a bare global `g` | the carrier of `g`'s declared **result** type, read from its committed signature under its own telescope, the way `imported_subject_carrier` reads a parameter |
| a method call `r.m(…)` | recursively, the result carrier of the member `m` resolves to |
| anything else | decline; the behaviour is unchanged |

The owner only picks the qualified name. Whether the call typechecks is still
decided by the desugared application, which receives the expected type, so
`a01` checks exactly as `a03` does. A result type the telescope cannot reduce
to a carrier (a type-level `fn` whose head depends on the arguments) declines.
The ambiguity tests after the owner is found (`shadowed_without_selfref`,
`selfref_shadows`) apply unchanged, as amended by §2.

**What a genuinely ambiguous receiver now says.** `R::mk().get()` in a
position that pins nothing no longer reports "unbound name `get`". It
reports the honest failure of the desugared call: "could not infer the
implicit argument `n` of `R::mk`". Add a named-argument hint (`R::mk(n := …)`)
to that message when the unsolved implicit belongs to the *receiver's* callee.
That hint is the spelling the sweep uses for statements like
`zero().band(zero()) = zero()`, which nothing pins.

## 2. Disjoint ambient readings stop blocking the member

**Mechanism (reproduced).** `member_head` refuses when the base name is also
"a name in scope on its own" (`shadowed_without_selfref`): a local, a `let`
alias, or any global. It does this whatever the other reading's type:

```heather
fn get(k: Nat) → Nat { k }
fn R::get({n: Nat}, self r: R(n)) → Nat { r.x }
fn b01(n: Nat, r: R(n)) → Nat { r.get() }                       // refused: both
fn l01(xs, ys: List<Nat>) → Nat { let len = xs.len(); len + ys.len() }   // refused: both
```

In `l01` the ambient `len` is a `Nat`. In `b01` the ambient `get` takes a
`Nat` where the receiver is an `R`. Neither reading can typecheck with this
receiver in its subject slot, so neither is a real alternative.

**Design.** An ambient reading is **discarded** when it provably cannot take
the receiver:

- a local or alias whose type (whnf) is not a Π, so it is not callable at all;
- a local or alias of Π type, or a global, whose **subject** parameter has a
  known outer carrier that differs from the receiver's known carrier.
  The subject is `subject_index` for a global (the `self` marker, else the
  first explicit parameter) and the first explicit parameter for a local.
  A global's carrier comes from its committed signature
  (`imported_subject_carrier` generalised to any global, not only imports).

Everything else keeps the ambiguity: an unknown receiver carrier, a generic
subject (`self a: A`), equal carriers, or a subject carrier that cannot be
computed. That matches the `ReceiverCarrier` doc comment ("an unknown carrier
keeps the ambiguity"). The discarded reading must also stop counting as the
`OtherReading` handed to `class_dispatch`.

**Why this keeps the growth invariant.** Adding `D::name` to a library can
change the meaning of an existing `t.name(…)` only where the ambient `name`
was a reading that typechecked at `t`. A reading with a disjoint carrier, or
one that is not a function, never did. So the member reaches only receivers
that previously had no well-typed reading at all.

## 3. Diagnostics

1. **"declared below" names the wrong declaration.** `begin_container`
   records `base_name(&d.name)`, so `V::get` further down the file makes a
   bare `get` miss read "`get` is declared below". Key the list by the full
   declared name and compare the full name the miss was for. The §8
   forward-reference message is about bare names in `decreases` groups and
   keeps its meaning.
2. **Missing `self`:** `issues/type-member-missing-self-diagnostic.md` as the
   issue specifies. Use its use-site variant, which runs only on the failure
   path of a dot call that selected a type-owned member with no `self` marker.
   It fires when the receiver is incompatible with parameter zero and
   compatible with exactly one later explicit parameter. It must not add work
   to a successful call.

## 4. Acceptance

- The probes above, as tests in `crates/elab/tests/type_members.rs` (the
  receiver-slice file). Per `docs/testing-generated-terms.md`, vary the
  position: a checking position that pins the receiver's implicit, a
  statement where only a named argument can, and the receiver of a method
  chain (`zero().iterate_increment(3).band(y)`). **Negative controls:**
  - an ambient `get<A>(self a: A)` (generic subject) stays ambiguous;
  - an ambient with the *same* carrier stays ambiguous;
  - an uninferable receiver whose head is a local of unknown type still falls
    back to the bare name.
- **Library sweep** over the receiver-position `@BitVec::zero` /
  `@BitVec::ofNat` sites (`lib/std/bitvec.hthr` ~60, 291, 367, 1026–1077,
  1645, 1751–1826; `lib/std/utf8.hthr` 451), using the ladder in §0. Plus
  the sites the probe found removable with today's elaborator:
  - `utf8.hthr` 139/144/151: annotated `let`;
  - `x86_64/model.hthr` 1154/1162: `eq_dec` as an argument;
  - `bitvec.hthr` 801–820: `borrow_sub_bit_true_iff`'s `@` does nothing;
  - `cons_bit_cong` in checking position;
  - `x86_64/block.hthr` 334/342: `ofNat(8, n := 8)`.

  Leave `from_bits`/`concat`/`head_bit` (#1b) and the `Decide` instance heads
  (`issues/instance-binder-occurrence-through-binder-types.md`) alone.
- **The showcase:** `docs/showcase/calc_text.hthr`'s `spell` becomes
  `Derivation::spell` with receiver self-calls (§5), and the README paragraph
  that excuses it goes.

## 5. Retired by this round's probes

- `issues/receiver-member-ih-generalization.md`: the issue's own repro
  (`Tree::flat_m`, `l.flat_m(r.flat_m(tail))`) and the qualified self-call
  both check on master. Close it once the `spell` conversion confirms it on
  the real client.
- Facade re-export of members: `Cursor::start` resolves through
  `import parser` (`issues/module-reexports.md`, closed).

## 6. Out of scope

`issues/record-partial-application-under-inferred-callee.md` (the
type-former-versus-constructor reading of a record name) looks like the
same family: a name with an unsolved implicit falls back to the wrong
reading. It lives in a different route, though, and gets its own round.
`issues/nullary-ctor-argument-not-deferred.md` (`List::append(Nil, xs)`) is
the unifier slice's.

## 7. As built (2026-09-24)

Landed as designed. Key functions are in `crates/elab/src/dispatch/member.rs`:
`receiver_owner_by_head`, `ambient_reading_survives` / `local_reading_takes`,
`method_call_failure` / `missing_self_message` / `receiver_implicit_hint`.
The telescope walk is shared as `read_signature`. The verification items came
out as follows. V1: the swallowed `elab_infer` error was the cause, confirmed
by instrument. V3: no existing ambiguity test had a disjoint or non-function
ambient reading, so §2 reverses no recorded decision. The deviations, each
amending the section named:

- **§1.** When an owner is found *by head* but an ambient reading survives §2,
  the call goes to the bare name, as it did before, rather than reporting
  "both". Reporting "both" would break a program that resolves today through
  the ambient reading (§0).
- **§3.2.** For a plain (non-generic) member, a receiver in the wrong slot is
  not an elaboration error; only the gate rejects it. So `resolve_dot`
  records `(receiver span, member)` in `DeclAttempt::unmarked_receivers` for
  each dot call that selects a member marking no `self`. That is one push on
  the success path, cleared per declaration with `check_notes`. The gate's
  note (`unmarked_receiver_note`) reads the record.
- **§4.** Two acceptance items reach only the honest error, because their
  qualified spelling fails identically on master. They are tested as such:
  - `zero().iterate_increment(3).band(y)`: a nested uninferable call in
    argument position, `issues/nested-uninferable-argument-under-checking.md`;
  - `Nil.rev()`: `issues/nullary-ctor-argument-not-deferred.md`.
- **Sweep.** The `@` lines in `lib/` and the showcases went from 90 to 42.
  - `cons_bit_cong` / `cong_ripple_add` take the named-implicit rung
    (`a :=`, `xs :=`, …), because the plain call fails wherever the goal needs
    unfolding before it shows `cons_bit`. That is the rigid-side reduction gap
    of `issues/unify-succ-under-addition.md`.
  - What is left: 24 lines belong to #1b (`concat`/`from_bits`/`head_bit`),
    7 are the `Decide` instance heads, and 11 were not examined
    (`@bitvec::BitVec::add(64, …)` ×8 in `lib/function_ir_x86.hthr`,
    `@byte_cons_cong` ×3 in `x86_64/model.hthr`).
