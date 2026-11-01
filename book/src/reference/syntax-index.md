# Syntax index

This page is a compact inventory, not a formal grammar. Ellipses indicate a
repeated list; all forms shown are implemented.

## Files and declarations

```text
file          ::= import-or-export* item*
import        ::= import module ;
                | import module :: { name, ... } ;
                | export module :: { name, ... } ;

item          ::= fn name type-params? requires? params -> type decreases? block
                | theorem name type-params? requires? params : type decreases? block
                | axiom name type-params? requires? params : type ;
                | def name type-params? (: type)? = expr ;
                | generator args? (fn ... | theorem ... | def ...)
                | generate generator args? ;
                | inductive name type-params? value-params? index? { ctors }
                | record name type-params? value-params? { fields }
                | class name <params> value-params? extends? { fields }
                | instance type-params? value-params? class-ref requires? body
                | designation type-params? operator at type := name
                | designation prefix - at type := name
                | meta fn ... for family.slot ...
                | datarepr name for type { clauses }
                | datarepr name for type := route() ;
                | impl operation for representation { clauses }
                | impl operation for representation := route() ;
                | assuming params { item* }
                | section type-params? requires? params? { (fn | theorem | section)* }
```

`fn` uses `->`; theorem-like statements use `:`. A declaration body is a
block. Most apparent keywords are contextual.

## Binders and arguments

```text
type-params   ::= < A, B : Type<n>, A : Class, ... >
params        ::= ( x, y : T, {implicit : U}, self receiver : R, ... )
solver-param  ::= evidence : Proposition := infer
default-param ::= name : T := expression
requires      ::= requires name : Class<A>, Class<B>, ...

call          ::= expression ( positional..., named := expression... )
explicit-call ::= @name ( all-value-arguments... )
type-app      ::= name < type, ... >
```

## Types

```text
type ::= Nat | Type | Type<n> | name | name<type, ...>
       | expression
       | [type; expression] | Fin(expression)
       | type -> type | (x, y: type) -> type | {x: type} -> type
       | expression = expression
       | ∥type∥ | Squash<type>
       | ¬type | type ∧ type | type ∨ type | type ↔ type
       | ∀ x, y: type, type | ∃ x: type, type
       | Ctx | TyCode(context) | Code(context |- type)
       | $type-code-name
```

## Expressions

```text
expr ::= name | qualified::name | numeral | character | string
       | Type | Type<n>
       | f(args) | @f(args) | f<types> | receiver.field
       | receiver.method(args) | receiver[index]
       | λ binders => expr | fun binders => expr
       | ∑ name < expr, expr | ∏ name < expr, expr
       | binders ⊢ expr | binders |- expr
       | apply callee; give expr; ... expr
       | · | ·₀ | ·₁ ...
       | [expr, ...]
       | Constructor { field: expr, ... }
       | ⟨expr, ...⟩ | ⟨expr |⟩ | ⟨| expr⟩
       | { statements* expr }
       | if proposition { expr } else { expr }
       | if let pattern = expr { expr } else { expr }
       | match equation-binder? expr motive? { arms }
       | match code expr as type { code-arms }
       | j(proof, λ endpoint path => motive, case)
       | squash(expr) | squash_ind(expr, motive, case)
       | calc { expr = expr := proof, = expr := proof, ... }
       | calc { expr ≈ expr := proof, ≈ expr := proof, ... }
       | refl | trivial | decide | omega | absurd(proof)
       | ?name | ?
       | code { expr } | $name | ${expr}
```

## Statements

```text
statement ::= let name = expr ;
            | let name : type = expr ;
            | let { field := pattern, field, ... } = expr ;
            | let code name = expr ;
            | split equation-binder? expr ; on arms
            | split_all ; all_goals { block }

discharge ::= on ?name := expr ;
            | on _ : type := expr ;
```

Goal discharges occur after the block's result expression. In a `split`,
`on Constructor(patterns) := expr;` supplies a match arm instead.

## Operators and punctuation

```text
prefix:        -  ¬
multiplicative: *  ∙
additive:      +  -  ++  ⊔
boolean:       &&  ||
comparison:    <  <=  =  ≠
relation:      ≈
logic:         ∧  ∨  ->  ↔  <->
arrows:        ->  →  =>
turnstile:     |-  ⊢
assignment:    :=
qualification: ::
```

`==` is deliberately rejected; equality is `=`. There is no `!=` alias for
`≠`, and `>`/`>=` are not comparison operators. Comments start with `//`.
