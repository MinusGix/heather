---
title: An annotated `let` at a non-equality type does not parse
status: closed
labels: [frontend,syntax,parser]
created: 2026-07-26
updated: 2026-08-02
---

```heather
fn f() -> Nat { let n: Nat = 3; n }
```

```
parse error: expected `=`, found Semi
```

**Pre-existing**, confirmed by running the same input against the parser as of
`13dd25d` (before [[surface-function-types]]); it is not a regression from
that round, which is only how it was found.

## Why

`let_stmt` parses the annotation with `ty()`, and `ty()`'s equality case takes
the first `=` it sees:

```
let  n  :  Nat  =  3  ;
            └─ ty() ─┘        annotation parsed as the type `Nat = 3`
                        ^ let_stmt now wants `=`, finds `;`
```

This is deliberate for the *other* reading and is tested
(`parser::tests::let_binds_with_and_without_an_annotation`,
`let p: a = b = pf;`), which the comment on `let_stmt` spells out: "`=` is not
an expression operator, so `ty()` stops after `a = b`". What nobody wrote down
is that the same greed makes a **non**-equality annotation unparseable, because
there is then no second `=` for the statement.

So `let` is currently usable either *unannotated* (`let n = 3;`, which infers
and is what every test in the suite does) or annotated at an equality type
(`let p: a = b = pf;`). The middle case — annotated at any other type — is the
hole, and it is exactly the spelling [[goal-holes]] recommends in its own
diagnostic ("annotate it (`let p: T = ?;`)").

## Why it is not a one-line fix

`let x: T = e;` and `let p: (a = b) = pf;` are genuinely ambiguous under a
greedy `ty()`. Resolving it is a grammar decision, not a typo fix:

- **Scan for the last top-level `=`** before the `;` and treat that as the
  binder's `=`, everything before it as the annotation. Handles both, and is a
  single lookahead pass in the style of `parser.rs::group_is_type`. Fails on a
  `let` whose *value* contains a top-level `=`, which today nothing can.
- **Require parentheses** on an equality annotation (`let p: (a = b) = pf;`).
  Simplest rule, breaks the existing spelling and its test.
- **A different binder token** for `let`, e.g. `:=` (already lexed, and used
  by `on` discharge). Clean separation, and it is the one that composes with
  [[effects-direction]]'s eventual assignment `=`. Breaks the existing
  spelling too.

The first is the least disruptive; the third is arguably the most principled
given [[surface-syntax]]'s settled story that `=` is binding *and* equality.

## Log

- 2026-07-26: Found while probing hole-under-lambda behaviour for
  [[surface-function-types]]; confirmed pre-existing rather than a regression
  by re-running the input against the previous commit's parser. Not fixed in
  that round because choosing between the three options above is a grammar
  decision that should not ride along inside a function-types commit.
- 2026-07-27: Option 1 (scan for the last top-level '=') is INVALIDATED by [[surface-universe]] phase 3, which made '=' an expression former. That option's own escape clause was 'fails on a let whose VALUE contains a top-level '=', which today nothing can' -- as of 2026-07-27 something can: 'let x: Type<0> = 0 = 0;' is a well-formed binding whose value is an equation, and the last-top-level-'=' scan splits it as annotation 'Type<0> = 0' with value '0'. So the least-disruptive option is now the wrong one, and the choice is between option 2 (parenthesise an equality annotation) and option 3 (':=' as the let binder, which composes with [[effects-direction]]'s eventual assignment). Note also that the mechanism for either is now cheap and already present: the 'no_eq' suppression flag added for calc steps and ty_atom (parser.rs, mirroring no_record_lit) is exactly what an annotation position would set. What it does NOT do on its own is decide the grammar question, which is why that round left this alone.
- 2026-08-01: Interaction from [[comparison-operators]] (2026-08-01): '<=' joined '=' on the non-associative comparison rung, so 'let h: n <= m = pf;' now parses and works — accidentally the second annotated-let shape that survives this issue. It is also why 'a <= b = c' cannot get the good chain diagnostic: the parser cannot tell that shape from the let binder '=' without this issue deciding the binder token (':=' would dissolve both).
- 2026-08-02: Bitten again in the fold_code port (in_language_fold.rs): 'let s: Nat = xs.fold(...)' fails to parse — the type parser eats 'Nat = <expr>' as an equality type. Worked around with a vector-typed annotated let plus an argument position; second live sighting, raises the priority a notch.
- 2026-08-02: Confirmed general and now load-bearing (2026-08-02): it falsifies surface-fin-indexing-design.md §3.2's claim that an annotated let is an available checking position — 'let i: Fin(k) = FZ;' cannot be written, and FZ/FS are checking-only, so argument position and xs[i]'s index slot are the only ways to build an index today. Raises the priority of this parse gap a notch.
- 2026-08-02: RESOLVED by docs/let-and-blocks-design.md §3, option 2 (parenthesise an equality annotation). Three findings first, because this issue was the wrong SIZE and had the wrong CAUSE. (1) THE STATED CAUSE IS WRONG. This issue, docs/surface-function-types.md:507-513, docs/surface-value-parameters.md:133-137 and crates/elab/tests/value_parameters.rs:143-148 all say 'ty()'s equality case takes the first = it sees'. True of `let n: Nat = 3;` and false as a general account: ty_atom bottoms out at parser.rs:915-916 in self.expr(), and it is EXPR()'S COMPARISON RUNG that eats the binder. So the gap was every annotation reaching that fall-through, not the ones that look like equations -- `let q: P = p;` at a declared record, `let g: Nat -> Nat = fun x => x;` and `let x: (Nat) = 3;` all failed identically. What worked was exactly the ty_atom productions that RETURN EARLY (Type<n>, [T; n], D<A>, Ctx, TyCode(g), Code(g |- T), $a), which is why in_language_fold.rs:71 could work around it with a vector-typed annotation and why nobody noticed how wide it was. All four documents corrected. (2) OPTION 2'S OWN SPELLING DID NOT PARSE EITHER. `let p: (a = b) = pf;` failed with 'expected =, found Semi': the parenthesised group fell through group_is_type to expr(), which ate the binder just the same. So 'require parentheses' was not a spelling that already worked and merely needed making mandatory; it had to be CREATED. (3) no_eq's DOCUMENTED PARENTHESIS ESCAPE HATCH WAS NOT IMPLEMENTED, and one live diagnostic was lying about it: parser.rs:93-94 promised it, there was no with_eq(false, …) call site anywhere, neither bracketed context cleared the flag, and so the CHAIN message's advice ('parenthesise the one that is meant to be an operand') was FALSE -- `a = (b = c)` was a parse error. Fixed as a side effect and tested. What landed, three changes all in parser.rs: atom's `(` arm and ty_atom's clear no_eq (the escape hatch made real); let_stmt's annotation is read inside with_eq(true, …); comparison's trailing-operator check gains TokKind::Eq and its doc comment's trailing-= exemption is deleted. Blast radius exactly as surveyed: SIX executable sites (parser.rs:1907, goal_holes.rs:146, lib/certgen/ir_v1.hthr:972/975/994/997) migrated to `(a = b)`; the <=-annotated shape had ZERO executable sites. lib/certgen/ir_v1.hthr re-checks in 70s with no change other than those four annotations, which was §7.3's prediction 1 and is CONFIRMED. Option 3 (:= as the let binder) was rejected on three counts, and this issue's argument for it was stale: it claimed := 'composes with [[effects-direction]]'s eventual assignment =', which reads that issue's 2026-07-24 log BACKWARDS -- that log records that = is NOT available for assignment, which is exactly why := is being held. Spending := on `let` would make it mean goal discharge, a calc step proof, a local binding and later an assignment: four things against the two = carries. Blast radius ~40 sites against 6. What option 3 genuinely had going for it -- the good `a <= b = c` chain diagnostic -- option 2 delivers too, since once the annotation suppresses the rung a = after a completed comparison is always a chain; docs/comparison-operators.md:95-110's prediction that the exception 'will disappear when that issue picks :=' is FALSIFIED and corrected in place. Beyond the reported bug this makes `let x: T = e;` writable at EVERY T, makes [[goal-holes]]'s own recommended spelling `let p: T = ?;` writable at a non-equality T, and makes docs/surface-fin-indexing-design.md §3.2's claim that an annotated let is an available checking position TRUE -- crates/elab/tests/surface_fin.rs's recorded caveat is retired and replaced with the axis-3 test it wanted (`let i: Fin(Succ(n)) = FZ;`, at an open length). The migration break is survivable because the elaborator's let-annotation path gained a hint: an annotation that resolves to a TERM now says so and names the parenthesised spelling.
