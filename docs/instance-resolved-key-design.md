# Instance identity is resolution, not spelling

Status: **round slice**, retiring `issues/instance-key-collides-across-modules.md`.
Constraints: `docs/traits-layer1-design.md` §4.1 and §7.1 (the canonical name,
and its 2026-08-17 amendment), §8's residue list; `docs/traits-layer2-design.md`
§3 (the search order — the resolver filters on the **class key alone**);
`docs/modules-design.md` §4 (the name regime this borrows entire);
`docs/repr-access-spellings-design.md` §2 (printed paths are writable
verbatim); `docs/operation-indexed-classes-design.md` §3.1 (the index
component of the key).

**No kernel change, no metatheory obligation, no new table.** The instance
registry keeps its shape, its cardinality and its single consumer. What
changes is what its *key* is made of, plus one loop in the lexer.

Adjacent and deliberately **not** in scope:
`issues/decidable-equation-carrier.md`. §7 records what this round did to its
cost.

---

## 1. The problem, in one line

An instance was registered under `(class key, carrier **head name**, index
spelling)`, and a head name is a *spelling*. `std/nat` and `std/int` both
declare a relation written `Le`; the second `instance … Decide<Le(n, m)>` was
therefore refused as a duplicate of the first, with a message that named `Le`
as though there were one of them. Nothing about the two is ambiguous to a
reader or to name resolution, which qualifies by module. Only the registry
could not tell them apart.

The cost was a *kit item*: `lib/std/int.hthr` carried a comment where its
`Decide` row should have been, and `lib/std/bool.hthr` paid a `Le_bool`
suffix — an encoding-around that erases the datum and costs the carrier its
operator.

## 2. The decision, in one line

**Identity by resolution, never by spelling.** Every component of the registry
key is a resolved declaration reference. No string in the registry is
load-bearing as identity.

The corollary that unblocks it is the one worth stating first: **a key does
not have to be spellable.** Layer 1 §7.1 parked the full (class,
carrier-syntax) key partly on the evidence that a canonical name must be an
identifier — true, and still true — but the *key* was never the name. It is a
tuple in a `HashMap` that no program writes down. Dropping
spellability-as-a-key-constraint is what makes the cheap form of §8's first
residue item available: identity is invisible, and names are for humans.

## 3. The key

```rust
pub(crate) type InstKey = (String, String, String);
//                         ^class     ^carrier   ^index
//                          key        head key   spelling
```

- **class key** — `key_of(class name)`, e.g. `logic::Decide`. Unchanged; it
  was already resolved.
- **carrier head key** — `carrier_key(head)`, which is `key_of(head)` with the
  bare name as fallback. `int::Le`, `nat::Le`, `bool::Le`, `list::List`. The
  fallback is reached by exactly the three names `names_a_type` claims with no
  declaration behind them — `Nat`, `Type`, `True` — and those are the
  language's own, cannot be declared twice, and so are constants rather than
  spellings.
- **index spelling** — unchanged, and *already* resolved: `index_spelling`
  has pushed `key_of(n)` per index argument since
  `docs/operation-indexed-classes-design.md` §3.1. See §7.1.

`instance_key(class_key, head_key, index)` is the one constructor, and its
parameter is named `head_key` precisely so that a future caller cannot hand it
`head_name`'s raw string without noticing.

**Duplicate detection is unchanged in semantics.** Two declarations at one key
are the declaration error they always were; two at different keys coexist.
What moved is which pairs are "one key": the same resolved carrier twice is
still refused, the same *written* head from two modules is now two instances.

The refusal reads:

```
`int::Le` already has an instance of `logic::Decide` (`int::Le::Decide`),
declared as `Decide<Le(a, b)>`: an instance is keyed on its class and its
**resolved** carrier, so this is the same carrier declaration and not merely
the same written name — refused rather than silently overwritten
(docs/instance-resolved-key-design.md §3)
```

Every party is module-qualified — the carrier, the class, and the occupant —
because "`Le` already has an instance" is exactly the sentence that used to be
a lie.

### 3.1 Why the head was not the only infected component

The head is what the issue reported, but it was not the only place a spelling
could have been load-bearing: a **module-local name inside the index** would
have had the same latent collision, since an index argument is a global
reference and two modules may declare one name. That component happened to be
resolved already. The rule this round states — *no component of the key is a
spelling* — is what makes that a property rather than an accident, and it is
why the change is stated as a rule and not as "qualify the head".

## 4. Names, and the qualified global

The canonical name is **unchanged**: `Le::Decide`, as the author sees it,
declared in the declaring module like any other declaration. There is no
mangling, no new minted name, and therefore nothing for
`docs/repr-access-spellings-design.md`'s minted-name policy to be extended
to. This is the C++-style split the round asked for, and the module system
already had it: a declaration is scoped in its module, and the external face
is the module-qualified path — `int::Le::Decide`.

One thing did have to move. `InstanceInfo.global` is what the resolver emits
as a `Var` when it *builds a candidate*, and it was the unqualified string. In
a downstream file that sees two `Le::Decide`s, that string is ambiguous at
use — the regime working exactly as designed, and the wrong answer here,
because the registry knows precisely which declaration it registered. So
`global` is now `qkey(module, prefix)`. Nothing else about resolution moves:
`names::split_qual` splits at the *first* `::`, so `int::Le::Decide` reads as
the module `int` and the declared name `Le::Decide`, which is how a member of
a type's namespace was already keyed.

**Diagnostics.** The standing discipline
(`issues/diagnostics-name-the-written-form.md`) is: print the bare name,
qualify only where the message would otherwise be ambiguous. Applied here:
the duplicate refusal qualifies (it is *about* two things that share a
spelling); the resolution **trace** qualifies too, and that is a deliberate
reading of the discipline rather than an exception to it — a trace line is
data about the registry (`issues/ai-facing-tooling.md` §7), not a quotation of
what the writer typed, and a `candidate: Pair::Mag` line in a program with two
of them names neither.

## 5. The lexer: `::` joins a chain

The lexer joined exactly one `::` (layer 1 §8's second residue item), so
`Rat::Monoid::op` was registered, resolvable, and unwritable; members were
reached by projection instead. The residue now has a paying customer —
`int::Le::Decide` is the *printed* form of a name the registry hands out — so
the one-join rule is lifted to a loop.

That restores `docs/repr-access-spellings-design.md`'s invariant ("what is
printed can be written") as an invariant rather than an
invariant-with-a-carve-out.

The change is four characters (`if` → `while`) and its whole content is the
boundary it does not cross:

- **`m::{a, b}`** — the import list. Adjacency already decided the join: a
  `::` followed by `{` does not join, at any depth in the chain.
- **`Impl(add, BinNat)::refines`** — the applied-owner path
  (`repr-access-spellings` §4), the one production that reads a *standalone*
  `::` after an expression. Its `::` follows a `)` and so never reaches the
  identifier scanner. It could not have been eaten.
- **Nothing relied on the one-join rule to mean something else.** `a::b::c`
  used to lex as `a::b` `::` `c`, and the parser's postfix `::` arm requires
  an *applied* owner (`render_owner` returns `None` for a bare `Var`), so that
  token sequence was a parse error in every expression position. The widening
  is a shrink of the error set, not a reinterpretation.

Both spellings coexist and are the same value: `left::Le::Judge::verdict()`
and `left::Le::Judge().verdict` are `refl`-equal, which is what layer 1 §4.2
always claimed and could only now be written down.

## 6. The library, collected

Three carriers, all of them written `Le`, all of them registered:

| module | relation | `Decide` row | `<=` |
| --- | --- | --- | --- |
| `std/nat` | `nat::Le` | already there | `designation <= at Nat := Le` (new) |
| `std/int` | `int::Le` | **lands** (the stalled row) | already there |
| `std/bool` | `bool::Le` | **lands** | `designation <= at Bool := Le` (new) |

- **`lib/std/int.hthr`**: `instance(a, b: Int) Decide<Le(a, b)>` replaces the
  stall comment.
- **`lib/std/bool.hthr`**: the `_bool` suffixes come off —
  `Le_bool`/`le_bool_refl`/`le_bool_dec`/`leb_bool`/`leb_bool_refl` become
  `Le`/`le_refl`/`le_dec`/`leb`/`leb_refl` — and the module gains the `Decide`
  instance and the `<=` designation its order could not have before.
- **`lib/std/algebra.hthr`**: the two `Cmp` instances now qualify
  (`nat::Le`, `bool::Le`, …). This is the API churn the rename buys, and it is
  the module regime working: a name declared in two visible modules is an
  error *at the use* naming both origins, and the answer is to say which.

### 6.1 The designations were not optional

`<=`'s fallback name is the bare `Le` (`op_fallback`). With three modules
declaring one, a file importing two of them had a symbol that resolved to
*nothing* — ambiguity, correctly reported, at a symbol the writer never
suspected of naming anything. A designation reads the carrier off the operand,
which is exactly the datum the bare name lost, so `nat` and `bool` grow the
row `int` already had. `lib/std/list.hthr` is the file that caught this: it
imports `nat` and `bool` both, and writes `len(filter(xs, p)) <= len(xs)`.

This is the mechanism the issue said the `Le_bool` dodge cost the carrier, now
collected: `x <= y` means the right order at `Nat`, `Int` and `Bool` in one
downstream file, with nothing qualified.

## 7. What implementing this corrected

### 7.1 The index component was already resolved

The round's premise was that *both* the head and the index were keyed on
spellings. The index was not: `index_spelling` has pushed
`self.key_of(n).unwrap_or_else(|| n.clone())` per argument since value indices
landed. Only the head was infected, and the change is one component.

This is a correction in the reassuring direction and it does not weaken §3.1's
rule: the rule is what keeps the resolved index from drifting back, and it is
now stated where a reader will find it.

### 7.2 Nothing needed minting, so the minted-name policy was not extended

The round's brief said the internal Ψ name would follow
`docs/repr-access-spellings-design.md`'s regime (minted names refused in user
source, with the designed form named). No name is minted. The canonical name
stays `Le::Decide` and qualification comes from the module system, which is
the point of §4: the *key* carries the identity and it is not a name at all,
so there is no second spelling to refuse. The policy is untouched, and the one
thing this round owed it — that a printed path be writable — is §5.

### 7.3 The resolver needed no change, and this is now tested rather than asserted

Layer 1 §7.1's amendment says the resolver filters candidates on the class key
alone and selects by elaborating each against the goal, so the carrier head
never enters a search. That was the load-bearing assumption of the whole
design, and it held: `resolve.rs`'s candidate loop is untouched.

It is pinned by two tests rather than by the sentence:
`resolution_picks_the_instance_at_the_goals_carrier` (both instances visible,
each goal answered at its own carrier, both carriers **open**) and its
negative control `a_carrier_with_no_instance_is_not_answered_by_its_namesake`
— without which the positive would pass over a registry that answered every
goal with whichever entry sorted first.

### 7.4 The equation carrier got cheaper, and is still not built

`issues/decidable-equation-carrier.md` wants `Decide<n = m>`, whose carrier is
an equation with no head to key on. Under the old key that needed a **new
notion of key** — the full (class, carrier-syntax) key layer 1 §8 parked —
because a single reserved head would have collided equality at every type.

It no longer does. The key is now a tuple of resolved references, and an
equation needs only *an entry in it*: a carrier component derived from the
equation's endpoints' type (a resolved reference like any other), plus the UX
of writing and diagnosing such an instance. The new-key half of that issue is
paid; what remains is a carrier entry and its ergonomics. The cost estimate is
logged on the issue and nothing here implements it.

### 7.5 The rename's blast radius was two test fixtures, and both were informative

Dropping `_bool` made `leb` a name two modules declare, and two tests in
`lib_algebra.rs` were written against a bare one.

- `a_member_name_that_shadows_a_global_is_ambiguous_at_a_receiver` **started
  passing for the wrong reason**: with `leb` ambiguous at the value, it no
  longer resolves as a global at all, so the member/global collision the test
  exists for stopped happening and the snippet checked. The fixture moved to
  `sub`, a global only `std/nat` declares. This is the failure mode a test
  that asserts only "it was refused" cannot see, and it was caught because the
  test asserts *which* refusal.
- Four others just needed a qualifier: `two_unrelated_owners_of_one_name_are_still_ambiguous`
  (`lib_algebra.rs`), and a bare `Le`/`le_dec`/`leb` in `logic.rs`,
  `nat_order.rs` and `lib_std_list.rs` — every one of them a probe module that
  imports `nat` and `bool` both.

Neither is a defect this round introduced; both are the module regime doing
what `docs/modules-design.md` §4 promises — library growth introduces errors,
never reinterpretations — and the errors landed at the uses, naming both
origins.

## 8. Acceptance

`crates/elab/tests/instance_resolved_key.rs` (synthetic modules — the key is
what is under test, and two declarations say it in ten lines):

1. two modules, one written head, both instances register (the issue's repro,
   now passing);
2. resolution picks the instance at the goal's carrier, at an **open** carrier
   on both sides — with the negative control in §7.3;
3. a genuine duplicate (one module, one resolved carrier) is still refused,
   and the message qualifies the carrier, the class and the occupant;
4. `left::Le::Judge` and `left::Le::Judge::verdict` resolve, the projection
   spelling agrees by `refl`, and a three-segment path naming nothing is a
   miss;
5. the lexer joins a chain, `m::{a, b}` and `Impl(…)::member` are where they
   were.

`crates/elab/tests/lib_std_int.rs` (the library win, at the real carriers):

6. `<=` and `decide` at **all three** orders from one downstream file that
   imports `nat`, `int` and `bool`, with nothing qualified at the operators;
   open operands for the resolution claim, closed ones for the computation
   claim, the three canonical names written verbatim, and a false decision
   refused as the control.

Plus: the full suite green, `lib/ir_v1.hthr` unchanged,
`scripts/bench --check` in band.
