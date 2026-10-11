---
title: "Named arguments at call sites (landed); defaults at binders (staged)"
status: open
labels: [frontend,syntax,design]
created: 2026-07-27
updated: 2026-10-10
---

**Status (2026-08-18): the call-site half is LANDED**
(`docs/named-arguments-design.md`, narrative in the log below). This issue
stays open for **half 2 only** — *default argument values declared at the
binder*, re-homed here from [[true-prop-trivial-hypotheses]]. Everything about
that half except one question is settled and pinned in design §9; the open
question is design §9.4, **where a default's free names resolve**. See the
last paragraph of the 2026-08-18 log entry.

The sketch below is kept as filed. Where it and the design disagree, the
design won and the log entry says why — most sharply at "type parameters":
the sketch expected named arguments to subsume `<…>`, and §5.3 declined.

**Sketch, not scheduled.** Raised by the user while
[[at-and-type-arguments]] was being settled, and filed because it is a third
knob on the same axis rather than a separate idea.

```heather
sym(p)                       // everything inferred
sym(p, a := x)               // one implicit pinned by name
map(xs := ys, f := g)        // explicit arguments, order-free
```

## Why it belongs next to the `@` work

[[surface-polymorphism]] and [[at-and-type-arguments]] left the surface with
two *positional* overrides — `@` for value implicits, `<…>` for type
parameters — and both are all-or-nothing. `@sym(a, b, p)` exists only because
there is no way to say "infer `a`, but let me give `b`". Named arguments
subsume both cases and are finer-grained:

- `@f(…)` becomes sugar for "every implicit given, positionally", and would
  arguably stop earning its own syntax.
- `f<T>(…)` likewise, for the type parameters specifically.
- The `calc` desugaring emits `@trans(a, b, c, p, q)` (`parser.rs`'s
  `calc_expr`) purely to force the endpoints; named arguments would let it
  name the two it cares about and leave the rest alone. That desugaring has
  now been fragile twice.

## The reason it is cheaper here than in Rust

Rust has postponed named arguments for a decade, and the reason that bites
hardest there **is already paid for here**: in Rust a parameter *name* is
private to the body — documentation, not interface — so making names callable
would retroactively turn every rename into a breaking change across the whole
ecosystem.

In Heather parameter names are **already API**, deliberately and in writing:
[[goal-holes]] names an argument-position goal after the callee's parameter
("proof-parameter names are API precisely so this reads",
`crates/elab/src/lib.rs`'s `ParamMeta`), `on ?bound := …` discharges by that
name, and `ParamMeta` carries it for exactly this purpose. So the semver
question that stalls Rust does not arise; the names are load-bearing already.

The other Rust obstacles are worth checking against this design rather than
assuming they transfer:

1. **Trait methods.** An `impl` may name its parameters differently from the
   trait declaration, so it is genuinely ambiguous which names a caller at a
   generic type may use. Lands here with [[compile-typeclass-design]] /
   [[surface-records]], not before — but the answer should be decided *with*
   that round, since a record of operations is where it first bites.
2. **Indirect calls.** A function *value* has a `Type::Pi`, and `Type::Pi` has
   no names — the same structural gap
   [[implicit-binders-in-function-types]] documents for implicitness. So
   named arguments would work on named callees and not on λ-bound ones, which
   is a two-tier rule and wants a decision, not a silent restriction.
3. **Default arguments.** Rust has repeatedly bundled the two and stalled on
   the pair. **Keep them apart.** Defaults are a separate feature with their
   own evaluation-order and elaboration questions, and nothing here needs
   them.

## Design questions

1. **Spelling.** `f(a := x)` reuses `:=`, which already means "discharge" in
   `on ?g := e` — arguably the same idea (fill this named slot). `f(a: x)`
   collides with type ascription; `f(a = x)` collides with the equality type
   former, which is the one `=` Heather deliberately merged onto
   ([[surface-syntax]]). `:=` looks right for that reason.
2. **Mixing with positional.** The usual rule — positional first, named after,
   no gaps — or fully order-free? Order-free is harder for the elaborator only
   because the Π spine is ordered; the arguments still have to be *elaborated*
   in dependency order, since a later parameter's type mentions an earlier
   argument. That is the real constraint and it should be stated, not
   discovered.
3. **Does naming an implicit make it explicit?** `sym(p, a := x)` gives `a`
   and leaves `b` inferred, which is the whole point. `apply_implicit` already
   carries a per-parameter mask; this is that mask with a third state
   (`inferred` / `positional` / `given-by-name`).
4. **Constructors and `match` arms.** `Cons(head := x, tail := xs)` is natural
   and the field names already exist (`FieldDecl.name`). Whether *patterns*
   get the same (`Cons(head, tail)` by name rather than position) is
   [[surface-records]]' question too, and the two should agree.

## Out of scope for the sketch

Default arguments, variadics, and any form of overloading.

## Log

- 2026-07-27: Filed as a sketch after [[at-and-type-arguments]] landed. Not
  scheduled: it wants [[surface-records]] first, because the trait/record
  layer is both where argument lists get long enough to need it and where the
  trait-method naming question has to be answered anyway.
- 2026-07-27: **[[surface-records]] landed, and it added a second payoff —
  worth pulling this forward for.** A record's constructor is an ordinary
  constructor, so `Monoid(unit: 0, op: f)` would be an ordinary *call* with
  named arguments, saying exactly what the braced literal
  `Monoid { unit: 0, op: f }` says. The braced form is now marked provisional
  (docs/surface-records.md §6), because retiring it in favour of this would
  delete a whole ambiguity class: `{` after an expression collides with every
  position where a *block* follows one (`match m { … }`, a declaration's
  result type), which currently needs a Rust-style suppression flag lifted
  inside brackets. That flag is a standing hazard rather than a one-time cost
  — every future block-preceding construct has to remember it, and
  [[effects-direction]] will bring more of them. A call is in parentheses, so
  it has none of that.

  Concretely, this issue now buys: finer-grained `@`/`<…>` overrides (the
  original motivation), `calc`'s fragile fully-explicit `@trans` desugaring,
  and the record-literal ambiguity. Open question 4 above ("constructors and
  `match` arms") is no longer a nice-to-have but the load-bearing case.

  Also relevant to open question 4, from the same round: [[method-receiver-position]]
  argues the receiver should stop being positional at all, which is the same
  observation one layer up.
- 2026-08-16: Adjacent feature ratified in principle (2026-08-16, from the true-prop-trivial-hypotheses discussion): default argument values declared at the binder (x: T := e), the chosen mechanism for discharging definitionally-trivial hypotheses on generated refines signatures, and per the user a wanted general tool — including defaults that run a tactic search over the surrounding context, not just a stored term. Defaults are half the reason named arguments exist, so the two likely design together; this issue is the natural home.
- 2026-08-16: One-line follow-up (2026-08-16): [[true-prop-trivial-hypotheses]] half 1 landed and that issue CLOSED, so this one is now half 2's only home. Concrete first customer, spelled the way the round left it: a generated `refines`/law signature binds `h0: True` (the prelude proposition over kernel `Unit^0`) and every consumer passes `trivial` explicitly — the binder that a default at the declaration would let a caller omit. Nothing here was built.
- 2026-08-18: **CALL-SITE HALF LANDED** (managed round; `docs/named-arguments-design.md`). Defaults-at-binders (half 2) is **staged with its shape pinned** in design §9, so this issue stays open for it alone.

  **The spelling is `f(x := e)`.** Two disqualifications and one positive reason. `f(a = x)` is unavailable, not merely ugly: `=` is the identity-**type** former (the one `=` this surface deliberately merged binding and equality onto), so `f(a = x)` is *already* a legal one-argument call passing the proposition `a = x` — choosing it would silently change existing programs. `f(a: e)` parses (a survey finding: `:` never *continues* an expression, so `call_args` simply dies at the `)`, and the real estate is free) and is refused anyway: `:` introduces a **type** in every binding position in this grammar, and `docs/types-as-expressions.md` means a type *is* an expression where both are legal, so `f(A: Nat)` has two well-formed readings and a reader cannot pick. The codebase had already made this call next door — the parser's error at an instance literal field says "`:=` (an instance's literal field is `op := e`; `:` is the record literal's spelling and would be ambiguous here)". Positively: `:=` is this language's operator for **filling a named slot** (`on ?g := e`, `op := e`, `abs := e`, and `hx: P := infer` at a binder), and the last of those is why §9 is a *continuation* of this design rather than a second one — the binder's default and the caller's override are the same operator on two sides of one slot.

  **The four open questions, answered.** (1) *Order*: **written order free, elaboration order is the declaration's** — forced, not chosen, because a later parameter's type mentions an earlier argument, and `apply_implicit` in particular *depends* on it (an argument's domain is zonked against the solutions learned before it, and a checking-only argument is only in checking position because earlier arguments solved its metas). Same rule as the record literal's, which is the precedent. (2) *Mixing*: **positional first, then named**, enforced **in the parser**, so the interleaving is unrepresentable in the AST and no elaborator path has to define it. (3) *Implicits*: **yes**, and it is the whole feature — the predicted "third state of the mask" is exactly right and is literally one bit flipped from `true` to `false`, after which the slot travels `apply_implicit`'s ordinary explicit-argument path unchanged. Solver parameters too, which is strictly finer than `@f(…)`. (4) *Constructors*: **yes**, by field name, sharing **one** permutation function with the record literal (`record_lit_args` generalized to `permute_by_name`), so `Monoid(unit := 0)` and `Monoid { unit: 0 }` cannot drift into disagreeing about what is unknown, duplicated or missing. **Patterns are deliberately not decided**, and not for scheduling reasons: a pattern *binds* rather than *fills*, so `:=` would point the wrong way — filed as [[named-patterns-by-field]] for [[surface-records]] to answer with it.

  **Type parameters are NOT nameable**, and this is the one place the sketch's "subsumes `@` and `<…>`" framing was too optimistic. A type argument is a *type*, parsed by `ty()` and lowered by `elab_ty`; a named argument's payload is an expression. The overlap is large but **proper** — `Nat`, `List<Nat>`, `Type<0>` and `a = b` read both ways via `expr_as_ty`, while `[Nat; 3]`, `Nat -> Nat` and `Code(Δ |- T)` have no expression spelling at all — so naming one is a *second reading* of the payload, available for some types and not others. And it is the reading [[at-and-type-arguments]] deliberately killed ("the coercion is now DEAD … it had existed only to paper over this collision"). Refused with a message naming `f<…>`; the gain given up is filed as [[partial-type-application]], where the likelier answer is a hole in the **type**-argument list, `zip<_, Bool>(xs)`, which needs no second reading of anything.

  **Where the `@` payoff was actually paid.** This issue advertised finer `@` overrides and the record-literal ambiguity as library payoffs. The survey found **neither has a library site today**: there are no `@`-spelled calls left in `lib/` at all (the 2026-08-17 argument-type-reduction round removed the last of them) and no braced record literals either. So the `@` payoff was paid at **`calc`**, which this issue also named: it now emits `trans(p1, p2, a := a, b := b, c := c)` rather than `@trans(a, b, c, p1, p2)`. `@` forced every value implicit positionally, so a *parser* desugaring encoded how many implicits `trans` has and in what order — a property of a library declaration, and the fragility recorded above as having bitten twice. Naming depends only on what they are *called*, which `ParamMeta` already treats as API. A shipped test was changed on purpose and says so.

  **What the library did have**, which neither this issue nor the design predicted: a record whose two fields have the **same type**, where a transposition typechecks. Seven adopted sites in `lib/std` — `and_swap`, `iff_refl`, `iff_sym`, `iff_trans`, `lt_succ_iff_le`, `le_iff_exists_add`, `mem_append_iff`. `iff_refl`'s `Iff<P, P>` is the sharpest: both fields are `P -> P`, so **no** type error could catch a swap, and until now nothing but position said which lambda was `mp`.

  **Findings from doing it** (design §12 has all seven; three matter). *(a) The value-head tier is narrower than the design wrote.* It said `let g: (x: Nat) -> Nat = …; g(x := 3)` would work. It does not: `skel_of_ty` is deliberately **sparse** and stores a skeleton only when the written type carries an *implicit mark*, so a markless function type keeps no binder names even though the writer visibly wrote one. The real boundary is "nameable exactly when the type carries an implicit mark"; both halves are tests, and the strange line is filed as [[skel-of-ty-drops-binder-names]]. *(b) The method-call interaction is positional, not nominal.* The design worried about naming the **receiver's** parameter, which is a "given twice" and takes care of itself. The real one: `resolve_dot` splices the receiver into the argument list at `subject_index`, an index among the **written** arguments, so naming a parameter *before* the subject would place the receiver one slot early and silently mean a different call. Refused with its own message — a wrong-term bug, not a diagnostic wart, and nothing in the design had seen it. *(c) The audit's two worst sites were not the one it predicted.* The prediction (zero-positional-argument recognizers like `is_naive_call`, where `repr::naive(x := 1)` would read as `repr::naive()`) was real. The two it missed are both **walkers**, where dropping a subterm is silent by construction: the **goal pre-count**, whose own doc comment says under-counting is the one thing the goal mechanism cannot survive — a `?hole` inside a named argument would have been uncounted, and is now a test — and **`scan_splices`**, i.e. a `$u` inside a named argument inside a **quotation**, which is the quotation-payload interaction the design listed and did not resolve. Seven further traversals were threaded for the same reason; the remaining ~20 reading sites are fixed-arity shape recognizers left alone deliberately, since a named call has a different positional arity and they *decline*, which is the safe direction. Two **renderers** chose oppositely and both are right: `traits::render_expr` renders `x := e` as written per [[diagnostics-name-the-written-form]]; `datarepr::spell_expr` **declines**, because its output is re-parsed as generated source and a permutation that resolves at one callee need not resolve at another.

  **Representation**: a **separate** `named: Vec<NamedArg>` field on `App`/`Dot`, not `args: Vec<Arg>`. It makes positional-then-named unrepresentable; it leaves `args.len()` meaning the positional arity every fragment recognizer keys on; and it cannot desync as a parallel `Vec<Option<String>>` could. Its one cost — that `..` reading sites are *not* audited by the compiler — was paid by hand, and (c) above is the report.

  **The invariant, and the standing control**: **a call with no named argument takes the path it took before, byte for byte.** Both resolution entry points return `None` and clone nothing when nothing is named. `a_call_with_no_named_argument_is_unchanged` pins it — without it, a pass that silently reordered *positional* arguments would pass every other test in the file. Two further things it protects, found by breaking them: partial application through `apply_explicit` (which named arguments deliberately do not compose with) and partially applied **constructors** η-expanded against an expected Π.

  **Tests +25**: `crates/elab/tests/named_arguments.rs` is new (21 — the positives assert `f(named…) = f(positional…)` **by `refl`**, i.e. conversion at the kernel, because a permutation that got the order wrong would still typecheck wherever two parameters share a shape) and 4 in the parser's own module for the grammar; `calc`'s two fold tests were re-spelled rather than added. Suite **1868 → 1893**, full run on the final tree; `scripts/bench --check`: **ok, 106 comparisons within thresholds**. Docs: `docs/named-arguments-design.md` (new); `docs/surface-records.md` §6 marked with the successor spelling and with why the braced form is **not** retired here.

  **Residue, each with an owner**: [[skel-of-ty-drops-binder-names]], [[partial-type-application]], [[retire-braced-record-literal]], [[named-patterns-by-field]].

  **What remains on this issue**: defaults-at-binders, and only the hard half of it. The grammar slot is settled (`p: T := e`, the position `:= infer` already occupies). The semantics are settled: a **defaulted parameter has no positional slot**, taking the solver parameter's own precedent, which is what makes the partial-application ambiguity never arise, makes adding a default backwards-compatible, and makes named arguments the override with no new syntax. The elaborator shape is settled: a `DefaultOb` beside the existing `ResolveOb`, discharged by the same retry-to-fixpoint loop. What is **not** settled, and is the whole of the remaining work, is **where a default's free names resolve**. Lowering once in the declaration's telescope and instantiating at the call is correct and is the only mechanism that can ever support `k: Nat := n`, but the elaborator has no path today for a stored *open surface* default. Splicing the surface expression into the call and elaborating it there is trivial and is **dynamically scoped** — a caller with a local named `trivial` would change what the default means — which is a defect to file rather than a limitation to document. Mechanism 1 is the one to build; and the user's further want, *defaults that run a tactic search over the surrounding context*, is mechanism 1 with the stored term replaced by a stored **goal**, which is a second reason not to build the version that cannot grow into it.
- 2026-08-20: Audited after the issue checker questioned the preceding entry.
  Keep this issue open: call-site naming is finished, but binder defaults are
  real remaining scope. In particular, the elaborator still lacks a stored
  open default lowered in the declaration telescope; elaborating stored
  surface text at the caller would be the rejected dynamically scoped
  substitute. [[named-patterns-by-field]] consumes only the finished
  call-site `field := value` convention and does not change that status.
- 2026-10-01: 2026-10-01: Record field defaults landed (docs/named-arguments-design.md §9.5; [[automatic-author-surface]]). §9.2's no-positional-slot rule holds, and the default is checked in the declaring scope against the instantiated field type, in an empty local context. Running a default under locals is [[field-defaults-under-locals]]. Parameter defaults remain §9's.
- 2026-10-10: Parameter defaults (`h: 0 < n := omega`) are wanted by [[positivity-evidence]] for positivity; Minus asked that they parse (2026-10-10).
