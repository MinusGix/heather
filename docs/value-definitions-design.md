# Value definitions and declaration-prefix generators

Status: **built, 2026-11-01** (issues `value-definitions` and
`declaration-prefix-generators`). Written for the DSL frontends of
`docs/compilation-vision.md` §3.3 and §6.1, whose motivating line is

```heather
regex def is_hex = "[0-9a-f]+";
```

That line needs two things this note describes: a proper `def` (§2), and a
declaration prefix whose generator may rewrite the declaration it prefixes
(§3). §4 is the first customer, a small regular-expression language, and §6
is what is left open.

## 1. What this builds on

- **`generate g(args);`** (`docs/host-elaboration-interface-design.md` §19):
  a generator is an ordinary library function returning
  `tactic::Tac<List<tactic::Decl>>`; its arguments are elaborated with quoting
  on (an `Expr` parameter receives a quoted term, any other parameter the
  value); its group is checked in the run and then elaborated member by member
  as the same declarations written in source, published all or none.
- **The prefix spelling** (`docs/runtime-fn-setups-design.md` §9.1): `runtime
  fn f` resolves `runtime` in scope; no keyword is reserved.
- **Frontends** (`docs/compilation-vision.md` §6.1): a *definitional*
  frontend (`regex def`) defines the declared name as the term's meaning, so
  the tie between name and term costs nothing; a *reflective* one (`runtime
  fn`) pins an ordinary body to its reflected term.

## 2. `def`

### 2.1 The form

```heather
def five: Nat = 5;
def six = Succ(five);                 // type inferred
def empty<A>: List<A> = Nil;          // type parameters are implicit
def add_five: Nat → Nat = λ x => x + five;
def five_is: (five = 5) = refl;       // an equation type is parenthesised
```

`def` is contextual: only `def` followed by a name, at an item's head. A
`def` takes no written parameter list (refused with the two spellings it could
have meant: `fn name(…) -> T { … }`, or a function-typed value) and no
`requires` list (an inline constraint `<A: Monoid>` is allowed, since it is
implicit). Its annotation stops at its `=`, as a `let`'s does, so an equation
type is written in parentheses.

Kernel-side a `def` **is** a nullary `fn`: the parser builds a
`DeclKind::Fn` with no written parameters, the body `{ e }`, and the new
`Decl::value` flag. So it is elaborated, gated, imaged, and δ-unfolded exactly
as a nullary `fn` is, and closed verdicts by `refl` keep working through it.
What the flag changes is only what a reader of the surface sees (§2.3, §2.4).
A nullary `fn` was already a global of type `T` (not of `() → T`), so
`five` and `five()` both elaborated before this round; `def` is the form that
says which one is meant.

A value does not refer to itself: its own name in its value is refused as
"refers to itself, and a value is not recursive" (a parameterless `fn` gets the
same sentence instead of "only a saturated recursive call").

### 2.2 The inferred type

`def x = e;` has the result type `TyKind::TypeOf(e)`, a surface type with no
spelling (only the parser makes it). `check_decl` recognises the pair (result
`TypeOf(e)`, body exactly `{ e }`) and infers `e` **once**: the inferred type
is the statement and the inferred term the body. Every other reader of the
stored declaration (a `datarepr` re-lowering, say) elaborates `TypeOf(e)` by
inferring `e` again, which is correct and costs one more elaboration of the
value. A value whose type inference cannot find (`def amb = Nil;`) is refused
with the inference error plus "write it as `def amb: T = …;`".

### 2.3 Use sites

A value is used bare: `five`, `six + 1`, `add_five(1)` (applying a
function-typed value is a call with arguments, unaffected). A polymorphic value
is used bare too; its type parameters are implicit and inference fills them.
The empty call `five()` is refused: "`five` is a value (a `def`), not a
function: write `five`, without `()`". The check (`refuse_value_call`) sits at
the two funnels, inference and checking, and reads the flag off the layer that
registered the global, so it holds across modules and never consults a
same-named declaration of another module. A `def` whose section inherited an
explicit parameter is a function outside the section and is not refused.

### 2.4 Diagnostics, image, tools

- The module image keeps the flag in the declaration-kind byte (tag 3, a `Fn`
  with the flag) and `TypeOf` as surface-type tag 13. An image written before
  `def` existed never holds either tag, so it still decodes; the round-trip
  unit test (`module_image_is_deterministic_roundtrips_and_replays`) carries a
  `def` of each kind.
- The language server lists a `def` as a constant (symbol kind 14).
- `tree-sitter-heather` has `value_declaration` and `prefixed_declaration`,
  with a corpus case; the keyword is in `syntax-inventory.json`.
- `mono_carriers` (`lib/std/tactic/mono.hthr`) was the migrated example: a list
  constant read by the tactic, `def mono_carriers: List<MonoCarrier> = …;`.
  Since 2026-11-08 its rows are `register def`s in the carriers' modules
  (docs/registered-values-design.md).

## 3. Declaration-prefix generators

### 3.1 Syntax

```heather
P fn f(…) → T { … }            P(args) fn f(…) → T { … }
P theorem t(…): S { … }        P(args) theorem t(…): S { … }
P def x = e;                   P(args) def x: T = e;
```

An identifier before `fn`, `theorem` or `def` (or before `(`), at an item's
head, after the keywords (`import`, `inductive`, `class`, `generate`, …) have
been matched, is a prefix. Nothing that parsed before parses differently: an
identifier was not otherwise a valid item start. The parser refuses:

- two prefixes (`a b fn f`): how generators compose is open
  (`scoped-declaration-generators`);
- a prefix over an `axiom`, a `meta fn` or an `evidence theorem`;
- a prefixed declaration in a `section` or under `assuming`, for the reason a
  `generate` is: the generator runs at the module's empty context.

### 3.2 The calling convention

The elaborator calls the generator with what the declaration hands it **in
front of** the written arguments:

| prefixed | call |
|---|---|
| `P(args) fn f …`, `P(args) theorem f …` | `P("f", args)` |
| `P(args) def x = e;` | `P("x", e, args)` |
| `P(args) def x: T = e;` | `P("x", { let x: T = e; x }, args)` |

and runs it as `generate` runs its generator. In front, like a method's
`self`, so the written arguments keep their names and defaults
(`runtime(setup := owned) fn f` is `runtime("f", setup := owned)`).

The declaration arrives **by name**, a `String`, not as the `GlobalRef` the
setups note (§9.1) sketched: a `GlobalRef` is issued by a run, so none exists
before the run starts. A consuming generator calls `lookup(name)` for it (the
declaration is already published, §3.3). A rewriting generator receives the
value at the type its parameter asks for, the rule every generator argument
already follows: a `String` parameter gets the string as data (so the
generator can parse it), an `Expr` parameter a quoted term.

The call is **kernel-checked before it runs**. Elaboration leaves some
mismatches for the kernel to find (a numeral checked at `String`), and a
generator's call is evaluated before anything else reads it, so without the
check a mismatched value reached the generator as a stuck term ("a Nat that
is not a numeral: stuck(…)"). This applies to `generate` too.

### 3.3 Consume and rewrite

- A prefixed **`fn` or `theorem` is consumed**: it is elaborated and published
  as written, then the generator runs over it (`lookup(name)` finds it, and
  its group may cite it), and the group is published beside it.
- A prefixed **`def` is rewritten**: the declaration as written is not
  published. Its value goes to the generator, whose group **must declare the
  name** ("the generator did not declare `x`"). A rewritten `def` cannot have
  type parameters yet. A generator that wants the value published unchanged
  publishes it itself (an `AsValue` member whose body is the value), so
  rewriting subsumes consuming for values.

Either way the item is one transaction: a failing generator, an ill-typed
call, a refused member or a forgotten name publishes nothing, the prefixed
declaration included. An unknown prefix is refused by name before anything
runs: "`runtme` is not a generator in scope". A prefix that resolves to
something that is not a generator is refused at its call, with the convention
of §3.2 spelled out.

### 3.4 Values in a group

`tactic::DeclForm` gains `AsValue`: a member that is a `def` (the `value` flag
set on the declaration the host elaborates from the member's skeleton). A
value takes no parameters; a member with any is refused.

`AsInstance(class, args, index)` (2026-11-04, for `runtime fn`,
docs/runtime-fn-setups-design.md §16.8) is a value that is also registered
as the instance `class<args…>(index…)`: the host elaborates the instance
written in source as `{ field := name.field, … }`, so its key, coherence and
index spelling are the ordinary checks. The type arguments are `Expr`s read
as types; a function type is spelled as an arrow, so it is keyed as one.

## 4. The customer: `regex` (`lib/std/text/regex.hthr`)

```heather
inductive Regex { NoMatch, Eps, Range(lo: Nat, hi: Nat), Seq(a, b: Regex), Alt(a, b: Regex), Star(r: Regex) }
fn Regex::accepts(self r: Regex, s: String) → Bool        // the meaning (Brzozowski derivatives)
fn Regex::parse(s: String) → Option<Regex>                // `|`, juxtaposition, `* + ?`, `( )`, `[a-z_]`, `\c`
fn regex(name: String, source: String) → Tac<List<Decl>>  // the prefix generator

regex def is_hex = "[0-9a-f]+";
// publishes
//   def is_hex: String → Bool = Regex::accepts(<term>)
//   def is_hex::term: Regex = <term>
theorem hex_accepts(): is_hex("c0ffee") = True {}                          // by evaluation
theorem hex_is_its_meaning(s: String): is_hex(s) = is_hex::term.accepts(s) {}  // by definition
```

The generator parses the string in the run (the parser is ordinary Heather,
evaluated by the host between requests), builds the term as an `Expr` from
`Regex`'s constructors (read with `Ctors` at the type it reads off
`Regex::accepts`'s domain), and publishes the meaning and the term. The
meaning is defined as `accepts` of the term, so the tie the compilation vision
asks of a definitional frontend is a definition: `hex_is_its_meaning` is
`refl`. The term is inlined in both members rather than `is_hex` citing
`is_hex::term`, because a member cannot yet cite an earlier member of its own
group (`generate-group-internal-references`). A string that spells no
expression is refused with the generator's reason, and nothing is declared.

What is not here: the language's compiler (a DFA and its soundness, proved
once) and `instance Compile(is_hex)`, which needs the `Compile` class
(setups note §9.3); issue `regex-dfa-compiler`.

## 5. Costs

As shapes. A `def` with a written type costs what the nullary `fn` costs;
an inferred one infers its value once at its declaration. A prefixed
declaration costs the declaration (when consumed), the generator's run
(evaluation between requests dominates, as for every generator), the kernel
check of the call (linear in the call term, which is small: a name, a value,
the written arguments), and each member as the same declaration written in
source. The empty-call check is one name resolution per zero-argument call.

## 6. Left open

- **Rewriting a `fn`'s syntax.** A prefix over a `fn` only consumes it. A
  frontend that lowers a body's syntax first (a `simd` dialect, a parser
  grammar) needs the declaration handed over as structured syntax, which is
  `scoped-declaration-generators`' structured-input acceptance.
- **Composition** (`a b fn f`), **sections** and **`assuming`**: refused, as
  for `generate` (`generate-in-sections`).
- **Group-internal references**: `is_hex` cannot be defined as
  `is_hex::term.accepts` (`generate-group-internal-references`).
- **A rewritten `def` with type parameters**, and a corecursive `def` (write
  a `fn`).
- **`runtime fn f`** itself, publishing `instance Compile(f)`: built
  2026-11-04 (`runtime-fn-default-setup`, setups note §16.8).
