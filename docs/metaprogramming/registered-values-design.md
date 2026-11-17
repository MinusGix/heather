# Registered values: tactic tables beside the lemmas they name

Round P3 of `docs/native/compiler-milestones-proposal.md`
(`issues/automation-lemma-registries.md`), and §10 of
`docs/surveys/stdlib-math-awkwardness-survey.md`: tactic lemma tables were strings
in the tactic's source.

## 1. The problem was placement, not spelling

`mono` named 99 lemmas as strings (`"Rat::add_le_mono_l"`), `cast` 17,
`norm_num` 16, `interval` 13. A tactic looks each one up at the `by`
(`Lookup`) and skips a name that does not resolve, which is how a client
that does not import `creal` pays nothing for `creal`'s laws. The same skip
hides a renamed or misspelled lemma: the automation silently loses a law.

Checking the strings where they are written is not possible either: `mono`
does not import `rat`, `creal` or the ordered classes, and must not (a
theory module below them, `int`, wants to be able to use it). Whatever
checks a name has to sit where the lemma is in scope. That is the registry
the issue asks for: the table moves to the lemma's module, and the tactic
reads the tables its client's world has.

## 2. Three surface forms

**`name_of(p)`** is a `String`: the qualified key of the global (or the
inductive) `p` denotes where it is written. A name that resolves to nothing
is an error there. `Lookup` resolves a qualified key wherever its module is
in the `by`'s import closure, so the string a table carries always finds its
lemma at a `by` that can see the table. Builtins (`Nat`, `Succ`, `True`,
`False`) are spelled as themselves. A string literal now needs `string`
only in the import closure, not imported directly, as a character literal's
spec already did (`literals.rs`, `closure_key`), so a module can register a
table without importing `string`.

**`register def x: T = e;`** is the value definition `x`, also entered in a
registry under its written type `T`, which must be a record or inductive
with no parameters, named exactly. It is the built-in declaration prefix
(`docs/metaprogramming/value-definitions-design.md` §3), so a generator named `register`
in scope wins. The registration is a module event
(`DeltaEvent::Registered { ty, global }`), so it is in module images, in the
registry digest that early cutoff compares, and in the slice-replay prefix.

**A generator registers what it publishes** with the declaration form
`AsRegistered(ty)` (`lib/std/tactic/tactic.hthr`): the member is a value,
as `AsValue`, entered under the type named `ty` as `register def` enters
one. It is elaborated as `register def name: ty = body;`, so the checks
are the same (a record or inductive with no parameters, registered once),
and the body the generator built is compared with that type. A prefix
generator can so put what it derives from a declaration into a table its
readers collect: `rule theorem` is the intended first client
(`docs/native/optimizer-rules-design.md` §6).

**`registered(T)`** is the `List<T>` of every value registered at `T` whose
module is in the current module's import closure, in canonical (global-key)
order: the order does not depend on how imports are arranged. Each element
is the global, cited by its key on the caller's behalf, as an evidence rule
the search finds is.

The intended use is a parameter default:

```heather
fn mono_with(hs: List<Expr>, depth: Nat := 64,
             entries: List<MonoEntry> := registered(MonoEntry)) → Tac<Expr> { … }
```

A default is checked where the call is (`docs/language/named-arguments-design.md`
§9), so `by mono()` reads the registry of the client's world. A tactic that
calls another passes its own `entries` on; a nested call left to its default
would read the tactic module's world.

## 3. What a table looks like

`lib/std/tactic/mono_laws.hthr` holds only the entry types, so a theory
module can import it without the tactic:

```heather
register def mono_rat_rules: MonoEntry = MonoRules(name_of(Rat::Le), [
    mono_law(False, name_of(Rat::add), [1], name_of(Rat::add_le_mono_l)),
    …
], [ … ]);
```

A carrier's laws may arrive in several entries, each where its lemmas are:
`big_operator` adds the sums' laws for `Nat`, `Int` and the located classes,
because `Int::range_le` lives there and not in `int`. `Int`'s whole table
is there too: `int` sits below `string` and the tactics, and importing the
entry types would put `string` in the closure of nearly every module.
`Nat`'s is in `mono_laws` itself. `mono` concatenates
the entries for one carrier in the registry's order. It still applies the
first law that covers a goal, so an operation's laws stay in one entry.

## 4. Why not a declaration attribute read off the statement

Lean's `@[gcongr]` reads a law's variance off its statement. Doing that here
means every `mono` run infers, opens and views every registered law before
it starts; the per-invocation floor is already the cost that dominates small
`mono` calls. A registered table costs what the old hard-coded one did, and
it can say things a statement does not (which law to prefer, which carrier
order is the reflexive one). An attribute can come later as sugar that
writes the entry.

## 5. Not done here

- `registered(T)` at a parameterised `T` (it would need the entries filtered
  by conversion).
- The other tables: `cast`'s edges and carriers, `norm_num`'s carriers,
  `interval`'s boxes and `grind_using`'s lemma names (a client's own
  strings). Each is the same move; `issues/automation-lemma-registries.md`
  tracks them.
