# Deep patterns and the `_` arm

Design document for `issues/nested-match-patterns.md`: two sugarings over
`match`, both motivated by hand-written towers in `lib/certgen/ir_v1.hthr`.

**Status: no kernel change is required, and none is proposed.** Both features
are a small grammar extension in `crates/syntax` plus one *preprocessing* pass
in `crates/elab` that runs in front of the existing single-level match
elaboration. The pass rewrites surface arms into surface arms; every lowering
below it — `elab_match_nat`, `elab_match_fin`, `elab_match_data`'s case tree,
`elab_match_wf`, `elab_match_indexed`, `elab_match_forded` — is called with
exactly the arm shape it accepts today, and none of them learns that anything
happened. That is the same construction argument `split` used
(`docs/language/matching/match-equation-split-design.md` §6): "it lowers to the same elimination
the `match` path builds" is a tautology rather than a proof obligation.

The theme, again: **the elaborator writes the term the user is already writing
by hand.** `step_letmatch` and `step_loopiter` are decision trees spelled as
towers of single-level matches; `pick_arm` writes seven identical arms because
every constructor must appear. Neither is new power.

## 1. What this round decides

1. **§3 — a `match` arm's binders are *patterns*, not names.** A pattern is a
   binder or a constructor applied to patterns. Deep patterns are compiled by
   the classic pattern matrix into nested single-level `match` expressions,
   *as surface syntax*, before any lowering runs.
2. **§3.3 — column selection is leftmost-non-wildcard, rows are first-match.**
   Both are chosen so the emitted nesting is the one the user would have
   written, in source order.
3. **§3.5 — a bare identifier in a sub-pattern is a constructor iff it names
   one at that pattern column's type.** `_` is always a binder.
4. **§4 — `_ =>` is a default arm**: no binders, last, at most one. It expands
   to the constructors with no arm of their own. A redundant `_` is dropped
   silently, because the pattern compiler generates redundant ones (§3.4).
5. **§5 — the default body is elaborated once and aliased**, not copied N
   times, when the motive does not mention the scrutinee *and* the row binds
   no pattern variables. Otherwise it is duplicated, and a duplicated body
   containing a `?goal` is a **named error** rather than the `internal:` one
   the hole machinery would raise.
6. **§6 — a deep pattern in a `match` that descends on a parameter *and*
   whose arms call the declaration is refused**, with a message naming the
   parameter and the guard. This is the v1 scope guard the issue asks for, and
   §6.1 says exactly which property of `guard-matches-self-calls-by-term`
   forces it — and why the trigger is the self-call and not the parameter.
7. **§7 — a deep pattern at an *index* field of an indexed or forded family is
   refused.** A finding, not a deferral: that binder is not a value binder
   (§7.1). Ordinary payload fields of the same families are unrestricted.
8. **§8 — `match h : e { … }` may carry deep patterns**, and the equation is
   about the **outer** scrutinee, refined to the outer constructor only.
   Sharing is unavailable there by construction, and §8 says why that is not a
   regression.

Out of scope and named as such: Lean-style equation definitions at the `fn`
head (the issue records them as sugar-on-sugar), and any kernel change.

## 2. Where the pieces stand (surveyed 2026-08-05)

`match_expr` (`parser.rs:1749`): optional `h :` equation binder, scrutinee with
`no_record_lit`, optional `as` motive, then `{ arm ("," arm)* }`. An arm is
`qual_ident` + an optional parenthesized list of `binder_ident`s + `=>` + an
expression (`Arm`, `ast.rs:354`).

Two facts about the current grammar that make both features additive:

- **`_` already lexes as `Ident("_")`.** `on _: P` reads it that way
  (`parser.rs:951`). So `match e { _ => x }` *parses* today and dies in the
  elaborator at "``_` is not a constructor of `X```". The default arm changes
  no token and steals no name.
- **An arm's binder list is already positional and arity-checked** at four
  independent sites (`inductive.rs:1493`, `forded.rs:967`, `indexed.rs:955`,
  and the two hand-written checks in `elab_match_nat`/`elab_match_fin`). Those
  checks are what the compiled output has to satisfy, and it does, because the
  compiler emits exactly one arm per constructor with exactly the right number
  of binders.

Elaboration has three entry points into arm-shaped work, and all three are in
front of the same preprocessing (`§9`): `elab_check`'s `Match { motive: None }`
(`lib.rs:1671`), `elab_infer`'s `Match { motive: Some(m) }` (`lib.rs:2258`,
which calls `elab_match_forded`/`elab_match_indexed` *directly*), and
`elab_match` itself (`lib.rs:2546`).

Two more facts the design leans on:

- **Arm field binders are aliases, not kernel binders** (`elab_arm`,
  `inductive.rs:1650`; the same in `wf.rs:603`, `indexed.rs:1535`). A field is
  a projection term, so a nested `match` on one has a **non-variable**
  scrutinee, and `synth_motive` (`lib.rs:3105`) falls back to the
  non-dependent motive for it. §10.2 measures what that costs.
- **`shift_local` preserves structural sharing.** `sub_tm`
  (`subst.rs:311-332`) returns `Rc::clone` for a subtree the mapper did not
  change, and `skip_tm` skips whole subtrees the bounds say are unaffected. So
  a *closed* shared body's interior really is one node in the emitted term, and
  not just one elaboration. §5.3 states the caveat about its head.

## 3. Decision 1: deep patterns

### 3.1 Grammar

```
arm     := pat "=>" expr
pat     := "_"                                  -- default arm (head only)
         | ctor ( "(" subpat ("," subpat)* ")" )?
subpat  := ident                                -- binder, or nullary ctor (§3.5)
         | ctor "(" subpat ("," subpat)* ")"
```

`Arm.binders` becomes `Vec<Pat>`:

```rust
pub enum Pat {
    Var { name: String, span: Span },
    Ctor { name: String, args: Vec<Pat>, span: Span },
}
```

and `Arm` gains `default: bool` (`ctor` is `"_"` when it is set). `default`
was preferred over an `ArmHead` enum because a default arm never survives
preprocessing, so making the ~14 downstream readers of `arm.ctor` handle a
second case would have been ceremony for an unreachable branch. The `"_"`
sentinel is a live safety net instead: if a default arm ever *did* leak past
§9, it dies at "``_` is not a constructor of `X``" rather than silently.

### 3.2 What is compiled, and to what

The whole feature is one function: given the match's arms, produce arms whose
patterns are all `Pat::Var` and whose bodies may be freshly built `match`
expressions. Worked example, `step_letmatch`'s tower written flat:

```heather
match lookup(env)(scrut) {
    NoneV => Stuck,
    SomeV(VCon(tag, fields)) => match ev(append(fields, env), pick_arm(arms)(tag)) { … },
    SomeV(_) => Stuck,
}
```

compiles to

```heather
match lookup(env)(scrut) {
    NoneV  => Stuck,
    SomeV(#p0) => match #p0 {
        VCon(#p1, #p2) => { let tag = #p1; let fields = #p2; match ev(…) { … } },
        _ => Stuck,
    },
}
```

Three things to read off it:

- **The inner `match` is ordinary surface syntax**, elaborated by
  `elab_check`'s `Match { motive: None }` path against the arm's expected
  type — which is exactly what the hand-written tower gets.
- **The inner `_` is the feature of §4**, and it is resolved when the *inner*
  match elaborates, where the sub-scrutinee's type is known. The compiler
  carries each column's type only to classify bare identifiers (§3.5); it
  still never enumerates constructors to expand `_`. That remains deferred to
  the generated level that knows it.
- **User pattern variables are bound by `let` aliases at the leaf.** The
  generated binders are `#`-prefixed and so unspellable; the `let`s cost
  nothing (an alias is inlined, `Γ` is unchanged) and they keep the rule
  uniform: a column binder serves several rows, which may name it differently
  or not at all.

### 3.3 Compilation order

The matrix is over *columns* (surface names of scrutinee variables) and *rows*
(one pattern per column, a body, the source span of the originating arm).

- **Column selection: the leftmost column that some row does not have a
  variable at.** Maranget's simplest heuristic. Not chosen for the size of the
  tree it produces — chosen because it makes the emitted nesting the one the
  user would have written, in the order the pattern reads, which is what makes
  a diagnostic inside a generated `match` locatable at all.
- **Row order: first match.** At a leaf (every remaining column a variable in
  some row) the **first** such row in source order wins. This is the only
  order-sensitivity the surface acquires: the existing single-level `match`
  permutes arms into declaration order and is genuinely order-free, and stays
  so, because a match with no deep pattern and no `_` is not compiled at all
  (§9's fast path).
- **Grouping replaces the duplicate-arm check at the top level.** Two rows may
  now share a top-level constructor (`SomeV(VCon(…))` and `SomeV(_)`), which
  the old check called a duplicate. After grouping, the emitted arm set has one
  arm per constructor, so the *downstream* duplicate check is untouched and
  still fires for a genuine `C => …, C => …`.

### 3.4 Exhaustiveness and redundancy

Exhaustiveness is **not** computed by the compiler. Each generated level is a
`match` like any other, so a missing constructor is caught by the existing
"``match` is missing an arm for `C``" check at that level, with the generated
node's span set to the *whole match's* span so the message lands on the user's
`match`. The consequence, stated: a non-exhaustive *inner* column is reported
at the outer `match`, not at the pattern. Recorded as residue (§11).

Redundancy is likewise not computed. A row shadowed by an earlier one simply
never reaches a leaf; its body is never elaborated, which over-counts
`count_holes`'s pre-count by the holes it contains — harmless, since the
pre-count is documented as an upper bound. Filed as its own issue rather than
done (§11): a redundancy *warning* needs a warning channel, and
`check_source` has only errors.

*Amended 2026-08-16* (`docs/elaborator/diagnostic-warnings-design.md` §7): the channel
exists and this is **reported**. Nothing here was recomputed — `Compile.uses`,
the census §5 keeps to choose between sharing and copying a body, is already
"how many leaves this arm reached", so an unreachable row is that number being
zero at a branch `settle` already had. One correction to the paragraph above:
"harmless" is right about the emitted term and wrong about the writer — a body
that reaches no leaf is never elaborated, so it is never **type-checked**
either, and that is the half worth a diagnostic.

That is also why a redundant `_` is **dropped silently** rather than refused:
§3.2's generated inner `_` is redundant exactly when the sub-column's rows
already cover its type (a `Nat` column with both `Zero` and `Succ` rows, say),
and the compiler emits it unconditionally. Making redundancy an error would
have meant marking generated arms, i.e. the preprocessing remembering which
spelling produced it — the thing §6 of the `split` design exists to prevent.

*Amended 2026-08-16*: a written redundant `_` is now **warned about**, and the
marking is done — `generated: bool` on the node, set by this module's emit and
read by diagnostics only. The last clause above conflated two things and is
withdrawn: remembering that WE built a node is not remembering which spelling
the user typed, and §6's tautology is about the *elimination* both spellings
build, which no flag on the node touches. (The spelling is remembered too, and
deliberately — `form: MatchForm`, same field group, same
diagnostics-only rule.) Refusing a redundant `_` outright is still not done and
still should not be: it breaks the refactor that adds a constructor.

### 3.5 A bare identifier in a sub-pattern

`SomeV(NoneV)` is genuinely ambiguous in the grammar: `NoneV` could be a
binder or the nullary constructor. The column type settles it. If `SomeV`'s
field is `Option<A>`, `NoneV` is that declaration's constructor; if the field
is `Nat`, it is a binder. `_` is always a binder.

This is the nested form of the judgment top-level arms have always used: the
scrutinee identifies the declaration before an arm name is read. It is also
the checking-position rule for constructor expressions. The expected type may
shrink an ambiguous name's candidate set; it never consults the global table
and guesses. Consequently, importing a second declaration with the same
constructor name may introduce an ambiguity in synthesis position, but cannot
silently reinterpret a deep pattern.

The implementation reads instantiated field types from the lowering's Sigma
spine. Thus a stored field written `A` in `Outer<A>`, instantiated at
`Outer<Inner>`, is classified at `Inner`; recursive child columns carry the
scrutinee's own type. This type information is used only for classification.
The generated decision tree and every lowerer remain unchanged.

The spine is read from the type as written, and where that is not the
declaration's shape but reduces to it, from the reduced type. The second
reading is not an optimisation. A type that arrives as an application, the
carrier applied to its argument for the variable of a `let x <- t;`, or a
type a function computes (`Maybe(List<Nat>)`), has no spine as written,
and before 2026-11-12 its columns were therefore unknown and every nullary
constructor in them a binder: `Cons(c, Nil)` matched each non-empty list,
with no diagnostic (`issues/deep-pattern-ctor-unknown-column-type.md`).

Where a column's type cannot be read at all, a bare identifier that is a
visible nullary constructor's name is **refused**, not read as a binder:
there is no classification to make, and the wrong guess is silent. The
refusal names the constructor and its type and says to give the scrutinee
its type or to match the field in the arm. A name that is no constructor
stays a binder.

## 4. Decision 2: the `_` arm

```
match e { C₁(x⃗) => b₁, …, _ => d }
```

- **No binders.** `_( … )` is a parse error: "``_` binds no fields``".
- **Last.** A `_` followed by another arm is refused —
  "``a `_` arm must be the last arm``" — because first-match semantics (§3.3)
  would otherwise make every following arm dead, and silently.
- **At most one**, refused by the same check.
- It expands to one arm per constructor of the scrutinee's type that has no
  arm of its own, with `#`-prefixed binders at that constructor's arity.
- If nothing is missing it is dropped (§3.4).
- If the scrutinee's type has no *known* constructor set — a `Fin` at an open
  length, say — a `_` is refused with the reason, since there is nothing to
  expand it to.

The constructor sets come from one new helper mirroring `elab_match`'s own
dispatch order: forded family, indexed family, declared inductive (tier 0 and
tier 1 alike), `Fin(Succ k)`, `Empty`, `Nat`. `Empty` is a real case and
falls out: nothing is missing, the `_` is dropped, and `match e { _ => x }` on
an empty type is `match e { }`, i.e. `elim_Empty`.

## 5. Decision 3: the sharing rule

The issue's cost note is the requirement: expansion must not be eight copies of
a body when one will do, because term size is billed at conversion
(`issues/simulate-conversion-cost.md`).

### 5.1 When a body is shared

A row's body is elaborated **once** and referenced from every arm it lands in,
iff both hold:

1. **The row binds no pattern variables** — every position is `_` or absent.
   The top-level `_` arm always qualifies; a deep row like `SomeV(_)` also
   does; `SomeV(other)` does not, because `other` is bound to a different
   column at different leaves and the shared term would have to mean two
   things.
2. **The motive does not mention the scrutinee.** Tested structurally: with
   `result = M[scrut/z]`, the motive is non-dependent exactly when
   `M == result↑¹` — which is also precisely the term `synth_motive`'s
   non-dependent branch builds, so the test is exact on everything the
   elaborator itself synthesizes and conservative on a hand-written `as`
   motive that is dependent only vacuously.

Otherwise the body is duplicated. A dependent motive gives every arm a
*different* expected type, so there is no single type to elaborate one term at;
this is inherent, not a gap.

### 5.2 The device

The shared body is elaborated in the match's own context `cx` at `result`, and
pushed as an ordinary `Alias` (`lib.rs:5101`) under an unspellable name; each
arm's body becomes a `Var` for it. Alias resolution already does the one thing
that has to happen — "inlined at the use site, shifted across the binders
pushed since it was bound" (`lib.rs:4796`) — so the arms' differing binder
depths, which differ *per arm* in a tier-0 case tree (arm `j` sits under `j`
`#rest` binders), are handled by machinery that already exists and is already
tested.

### 5.3 What sharing actually saves

Honestly, and measured rather than asserted:

- **Always: N elaborations become 1.** One traversal of the body, one set of
  goals raised, one conversion of its type against the expected one.
- **Always: the `?goal` hazard disappears.** A hole is keyed by its source
  span and context; elaborating a duplicated body twice raises
  `internal: a hole was re-elaborated in a different context`. With sharing, a
  `_ => ?g` over a seven-constructor type raises exactly **one** goal, which is
  the observable the acceptance test asserts (§12) — no kernel term is printed
  to see it.
- **When the body is closed w.r.t. the local context: its interior is one node
  in the emitted term, not N.** `shift_local` returns `Rc::clone` for an
  unchanged subtree (§2), so a body mentioning no local — `λ (tag: Nat) =>
  NoArm`, which is `pick_arm`'s whole default — is shared below its head. The
  head itself is re-allocated per arm, because `resolve` hands an alias back as
  a `Term` by value rather than an `Rc` (`lib.rs:4796`); that is one node per
  arm, not one *copy* per arm, and it is what the acceptance test measures
  (`a_shared_default_body_is_one_node_when_it_is_closed`, at the interior). A
  body mentioning a local is rebuilt along the spine of that local's
  occurrences, and its closed subtrees are still shared.
- **Never: a `let` in the kernel.** There is none (`elab_arm`'s comment says
  so), so "one copy in the emitted term regardless of free variables" is not
  reachable from here. The user's own device for that is the one `ir_v1` uses
  everywhere already: bind the body to a `fn` above the match.

## 6. Decision 4: no deep patterns in the decreasing position

A `match` whose scrutinee is one of the enclosing declaration's own parameters
(`descends_on_param`, `lib.rs:2913`) **and** one of whose arms mentions the
declaration's own name refuses deep patterns:

> a deep pattern is not available in this `match`: it descends on `arms`, a
> parameter of `pick_arm`, so its arm binders are what the termination guard
> matches a recursive call's argument against. Match the field in a nested
> `match` inside the arm instead.

The `_` arm is **not** refused there — see §6.2.

### 6.1 Why, precisely

The guard compares a self-call's elaborated argument against the arm's own
binder: by *position* for `Nat` (`matches!(arg_t, Term::Var(LocalVar(i)) if
cx.names.len() - 1 - i as usize == *pred_pos)`) and by *term* for `Wf`
(`children.iter().position(|(c, ..)| c.shift_local(by) == arg_t)`) —
`issues/guard-matches-self-calls-by-term.md`. Both readings are of the binder
this level's elaboration installed. A deep pattern moves the recursive call's
argument one level down: the user writes `f(k)` for `Succ(Succ(k))`, and `k` is
a binder of the *generated inner* match, which the outer guard has never heard
of. The failure is not a wrong answer — it is the guard's own rejection, at a
call site, saying the argument is not the predecessor. That message is true and
useless, so the feature refuses at the pattern instead, where the fix is
visible.

### 6.2 Why the trigger is the self-call, not the parameter

The first implementation refused on `descends_on_param` alone — "the guard
could have been installed here" — and that was measured, immediately, to be
useless: `fn f(o: Opt<Res<A>>)` matching deeply on `o` is the *most common*
shape the feature exists for, and it is not recursive at all. The guard is only
ever read by `elab_self_call`, so the honest test is whether any arm could
reach it, and the honest over-approximation of that is a syntactic mention of
the declaration's own name in an arm body (`expr_mentions`,
`inductive.rs:2841`).

The over-approximation is sound in the direction that matters — every guard
read is a mention — and it costs nothing in the other, because a mention of the
declaration's name that is *not* a saturated guarded call is already an error
("`f` can only be used here as a saturated recursive call"). So a program the
scan refuses is either one that would have hit the guard or one that would not
have elaborated anyway.

### 6.3 Why `_` is exempt

The default arm binds nothing and its expansion introduces no binder the guard
reads: the arms it generates are the constructors the user gave no arm to, and
a self-call in the shared body would be a call from an arm that is not the
recursive one. `pick_arm` is the case — it recurses on `arms` and its `_`
covers the seven constructors with no recursive field at all. Refusing `_`
there would have refused this round's own acceptance demonstration.

## 7. Decision 5: index fields of an indexed or forded family

A deep pattern at a field whose `FieldKind` is `IndexVar` is refused, naming
the family and the field.

### 7.1 Why this is a finding

That binder is not a value binder. For route 1 it is aliased to a component of
the *index pattern* (`indexed.rs:1535` pushes an alias built from
`env.pat[a]`), and for route 2b to a projection of the fording witness. Its
value is determined by the scrutinee's index, not by the scrutinee, so
"case on it" is not an elimination the arm is in a position to perform — and
the guard's `rebind` (an indexed self-call must pass *exactly* the arm's index
variable, `lib.rs`'s `g.rebind` check) reads that same binder by term, so §6.1's
argument applies to it at every declaration, recursive or not.

Payload fields of the same families are unrestricted: they are ordinary field
aliases and a nested `match` on one is what the user writes by hand today.

## 8. Decision 6: deep patterns under `match h : e`

**Accepted, and the equation is about the outer scrutinee**: in the compiled
arm for `C`, `h : e = C(#p₀, …)` — the *generated* binders, not the inner
pattern. The inner levels are separate eliminations with their own synthesized
motives, and an equation for one of them would need a second binder the surface
gives no name to.

This falls out of the ordering rather than being arranged: `elab_convoy`
(`lib.rs:2440`) wraps each arm's surface body in `λ h => body` and then calls
`elab_match`, which is where §9's preprocessing runs. So the λ is already on
the row body when the row is compiled, the outer level is decorated exactly as
it is without deep patterns, and the convoy stays type-transparent.

One consequence, and it is not a regression: the convoy's motive is
`Π (e = z). M`, which mentions `z` **by construction**, so §5.1's condition 2
never holds and a default arm under a convoy is always duplicated. A user who
wants both wants the equation at N different types anyway — that is what the
convoy is for — so there was nothing to share.

`split` inherits everything, since it is the same node: `on _ := b;` is a
default arm (told apart from the goal discharge `on _: P := b;` by one token,
`:=` versus `:`), and `on C(D(x)) := b;` is a deep row. Neither costs the
elaborator a line.

## 9. Where the preprocessing runs

One function, called from the three entry points of §2, and **idempotent** —
its fast path is "no arm has a deep pattern and none is `_`", which is every
match written before this round and every match the compiler itself emits at
the level it emits it. So calling it twice on the way down (once in
`elab_infer`, once in `elab_match`) is free and is not a correctness question.

It runs *after* the scrutinee is elaborated (it needs `scrut_t` for §6 and for
`result`) and *before* the dispatch on the scrutinee's type, except for the one
thing that cannot be: expanding `_` needs the constructor set, so it consults
the same type the dispatch is about to.

## 10. Boundaries this round measured

### 10.1 The compiler needs no type information — except for `_`

Stated as a decision in §3.2, but it is worth recording as a *finding*, because
the obvious design (compile the whole decision tree eagerly, looking up each
sub-column's constructor set from the inductive table) needs field types at
every level, instantiated at type arguments, for six different family
encodings. The lazy design needs none of that, and it needs none of it because
the default arm exists. **The two features are not independent: feature 2 is
what makes feature 1 cheap.**

### 10.2 A nested match on a field has a non-dependent motive

Field binders are aliases, so an inner scrutinee is a *projection*, not a
`Term::Var`, and `synth_motive` returns the weakened expected type for it. So a
deep pattern cannot be used to prove something *about* the field it matched:
the inner arms are all checked at the same type. This is inherited, not
introduced — a hand-written nested match on a field has had it since tier 0 —
and it is why deep patterns are a *programming* convenience in v1 and not a
proving one. The route for the proving case is unchanged: an explicit `as`
motive on the inner match, which the user writes and the compiler never
synthesizes.

### 10.3 A duplicated body cannot contain a goal

§5.3. Under a dependent motive the sharing device is unavailable, and a `?goal`
in a body that lands in more than one arm hits the hole machinery's
context-keying. Refused with a message that says which arm and why, instead of
`internal:`.

## 11. Residue, with owners

- ~~**Redundancy and reachability are not reported** (§3.4). Needs a warning
  channel; filed as its own issue.~~ **Paid 2026-08-16**: the channel is
  `docs/elaborator/diagnostic-warnings-design.md` and this was its first customer. An
  unreachable row and a `_` that stands for nothing are reported as warnings,
  off `Compile.uses`; a generated level's own `_` is not (§7.1 there).
- **A non-exhaustive inner column reports at the outer `match`** (§3.4). Same
  class as the `split` design's §6 wart — the message is true and the span is
  coarse — and the fix is the same one (thread a form/site name), still not
  worth five message sites.
  *Amended 2026-08-16* (`issues/diagnostics-name-the-written-form.md`): the
  **form** half is paid and the **span** half is not, and they turned out to
  be separable rather than one fix. A generated level now inherits the written
  form, so an inner column of a `split` says `split`; what it still cannot do
  is point at the column, because a generated level has no source text —
  which is this bullet's own observation and is untouched.
  *Amended again 2026-08-16*: that amendment recorded the inheritance as
  honest but **unobservable**, on the ground that a `split` arm's binders are
  plain names. They are not — an `on` arm's binders are read by the same
  `pat_args` a `match` arm's are, so a deep pattern is writable in a `split`
  and the generated level is reachable from one. The inheritance is
  observable, is correct, and is now pinned
  (`a_splits_deep_patterns_name_split`), along with this section's own two
  refusals, which named `match` at a `split` until the same day. The span half
  now has its own owner, `issues/inner-column-diagnostic-span.md`.
- **§6's rejection is on a *syntactic* mention of the declaration's own name**
  (§6.2), so a deep pattern in an arm that merely shadows that name is
  refused. Nothing in the corpus does, and narrowing it means resolving the
  name, which the pass runs too early to do.

## 12. Acceptance

`crates/elab/tests/nested_match_patterns.rs`, against
`docs/testing-generated-terms.md`:

- **Axis 6 × axis 2 throughout**: the fixture inductives have ≥ 3 constructors
  and an open (type-parameter) payload, so every generated case tree's inner
  node meets an ambient variable.
- **Axis 1**: a deep match on a *literal* scrutinee that must **compute** to
  the expected reduct, and the same on a **neutral** one.
- **Axis 3**: a deep match and a `_` arm in *checking* position under a
  dependent `as` motive (a theorem), where the annotations must convert.
- **Axis 4**, one per decision: a wrong-arm body is refuted; a non-exhaustive
  match without `_` is rejected; a `_` that is not last is rejected; a deep
  pattern in the decreasing position is rejected with §6's message; a deep
  pattern at an index field is rejected with §7's; a duplicated body with a
  goal is rejected with §10.3's.
- **Nonzero level**: a deep match whose result is a `Type<1>`-level payload.
- **Sharing, observably**: `_ => ?g` over a seven-constructor type raises
  **exactly one** goal and is discharged by one `on ?g := …`. Nothing is
  `Debug`-formatted.
- **The library**: `pick_arm`, `step_letmatch` and `step_loopiter` in
  `lib/certgen/ir_v1.hthr` rewritten, under the full `scripts/test` (§13.1).

26 tests, all passing.

---

## 13. Addendum: the implementing round, 2026-08-05

### 13.1 What was measured

**The acceptance demonstration went further than `pick_arm`.** All three
hand-written towers named in the issue were rewritten, and all of
`lib/certgen/ir_v1.hthr`'s downstream proofs — `step_letmatch_unfolds`,
`step_loopiter_unfolds`, `k_bind_inv`, `step_mono`'s convoy — still check
against them unchanged:

| declaration | before | after |
|---|---|---|
| `pick_arm` | 8 arms, 7 of them `λ (tag: Nat) => NoArm` | 2 arms, one `_` |
| `step_letmatch` | 2 nested `match`es, 5 arms | 1 deep row + `_` |
| `step_loopiter` | 4 nested `match`es, 11 arms | 3 rows + `_` |

`lib/certgen/ir_v1.hthr` is 58 lines changed, net −11. Capped release checks
(`ulimit -v 8388608 -t 300`):

| | run 1 | run 2 |
|---|---|---|
| before | 60.3 s | 60.0 s |
| after (all three) | 59.6 s | 59.4 s |

Inside the noise, which is the predicted result and the point: the elaborator
emits the term the user was writing, so the feature moves who writes it and
not what it costs. Full `scripts/test`: 1093 passed, 0 failed (1067 before).

### 13.2 The one defect the round found, and what it says about the design

**The generated column names shadowed each other across levels.** The pass
runs again on every level it emits (§9), and the first implementation gave
each *call* a fresh-name counter starting at zero. So a re-prepared inner
`match` minted `#p0`, `#p1` — rebinding the outer level's columns — and a leaf
that referred to a column bound two levels up silently got the wrong one. The
symptom was a wrong answer, not a rejection: `VCons(VCon(Zero, ff), c) => c`
returned `ff`.

Two things are worth recording about it.

**(a) The test that caught it is axis 1 done properly.** A literal scrutinee
that must *compute* — `theorem carries(): loopiter(Out(VCons(VCon(0, VNil),
VCons(VNil, VNil)))) = Out(VCons(VNil, VNil))` — is the only kind of test that
can see it. Every typing test passed: both columns have type `Val`, so
substituting one for the other is perfectly well typed. This is
`docs/testing-generated-terms.md`'s axis 1 and axis 3 crossing exactly as that
document says they should, and it is the first defect in this codebase that a
*wrong variable* produced rather than a wrong annotation.

**(b) The fix is local because the names are checkable.** Rather than adding
elaborator state, the counter starts past every `#p⟨k⟩` already visible — in
`cx.names`, in `cx.aliases`, and in the arms' own patterns. That set is
provably a superset of what a generated name could collide with, and it needs
no interior mutability on an `&self` method.

**A second, smaller finding in the same place: the first-match rule is also an
optimization.** If a constructor group's *first* row has all-variable
patterns, every row behind it is unreachable under that constructor, so there
is nothing to compile — emit the plain arm. That is what keeps a `match` that
only gained a `_` arm emitting byte-identically to one that spells its arms
out, and it is also what stops the pass from re-generating columns for the
inner levels it just emitted.

### 13.3 Corrections to the sections above

- **§6's trigger changed during implementation**, from "the scrutinee is a
  parameter" to "…and an arm mentions the declaration's own name". §6.2 is
  the new section; the old rule refused `fn deep(o: Opt<Res<A>>)`, which is the
  feature's most common shape.
- **§5.3's sharing claim is one node weaker than first written.** The shared
  body's *interior* is one node; its head is re-allocated per arm, because
  alias resolution returns a `Term` by value.
- **§5.1's condition 1 is vacuous for the `_` arm** and load-bearing only for
  a *deep* fallthrough row: a surface `_` binds nothing by grammar, and the
  bindings a generated `_` needs are emitted as `let` aliases *inside* its
  body, where they are the same at every arm it expands to.
