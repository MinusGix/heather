//! `let` annotations and block expressions (`docs/let-and-blocks-design.md`).
//!
//! Two decisions share this suite because they share their clients: §3 makes
//! `let x: T = e;` writable at every `T` by reading the annotation with the
//! comparison rung suppressed, and §4 makes `{ stmt* expr }` an expression in
//! prefix position. Neither adds a kernel form — a `let` is an *alias*, not a
//! binder (`lib.rs`'s `elab_stmts`) — so the suite's job is that the terms are
//! the ones the same program without the block already emits.
//!
//! Per `docs/testing-generated-terms.md`, §4 is an elaboration change that
//! emits terms and gets all four axes: a literal scrutinee that must
//! **compute**, a neutral one where nothing reduces, an **open** element type
//! (a declaration's type parameter), a *checking* position under a dependent
//! motive, and negative controls. §3 is grammar and gets its shape assertions
//! in `crates/syntax/src/parser.rs`'s own suite; what is here is what only the
//! elaborator can see.

use heather_elab::{ElabError, Elaborator};
use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{CtxBase, GlobalBinding, LocalCtx, Term, Type};

const ADD: &str =
    "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }\n";

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

/// The type and body of the *last* committed binding.
fn last_body(e: &Elaborator) -> (Term, Type, Level) {
    match e.psi().bindings.last().expect("a binding") {
        GlobalBinding::Tm { ty, level, body: Some(b), .. } => {
            ((**b).clone(), (**ty).clone(), level.clone())
        }
        other => panic!("expected a bodied Tm binding, found {other:?}"),
    }
}

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated:\n{src}"),
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(ElabError::Parse(p)) => p.msg,
        Err(other) => format!("{other}"),
    }
}

// -- §3: the annotation position -------------------------------------------

/// §8 item 1: every `T` that used to fall through `ty_atom` into `expr()`'s
/// comparison rung. The gap was never about equations
/// (`docs/let-and-blocks-design.md` §1.1(1)) — a bare declared type name and
/// a function type were just as unwritable.
#[test]
fn an_annotated_let_takes_any_type() {
    ok("fn f() -> Nat { let n: Nat = 3; n }");
    ok("record P { a: Nat }
        fn f(p: P) -> Nat { let q: P = p; q.a }");
    ok("inductive Opt<A> { None, Some(A) }
        fn f(o: Opt<Nat>) -> Nat { let x: Opt<Nat> = o; 0 }");
    ok("fn f() -> Nat { let g: Nat -> Nat = fun x => x; g(3) }");
    ok("fn f() -> Nat { let x: (Nat) = 3; x }");
    ok("fn f(n: Nat, xs: [Nat; Succ(n)]) -> Nat { let i: Fin(Succ(n)) = FZ; xs[i] }");
}

/// §8 item 2: the annotations that already worked are byte-identical, because
/// each is an early return from `ty_atom` and never sees the flag.
#[test]
fn the_annotations_that_worked_still_work() {
    ok("fn f() -> Nat { let t: Type<0> = Nat; 0 }");
    ok("fn f() -> Nat { let r: [Nat; 3] = [1, 2, 3]; 0 }");
    ok("inductive Opt<A> { None, Some(A) }
        fn f(o: Opt<Nat>) -> Nat { let x: Opt<Nat> = o; 0 }");
}

/// §8 item 3: an equality annotation is *parenthesised* now, and so is a
/// `<=` one — the shape `docs/comparison-operators.md:100` only ever had as
/// prose.
#[test]
fn a_comparison_annotation_is_parenthesised() {
    ok("theorem t(n: Nat): n = n { let p: (n = n) = refl; p }");
    ok("record Le(a: Nat, b: Nat) { w: Nat }
        theorem t(n: Nat, m: Nat, pf: Le(n, m)): Le(n, m) { let h: (n <= m) = pf; h }");
}

/// §8 item 4(a): the negative control, and the hint that makes the migration
/// survivable. `let p: a = b = pf;` now parses as annotation `a` — a *term* —
/// and the elaborator says so and names the spelling that works.
#[test]
fn an_unparenthesised_equality_annotation_is_diagnosed() {
    let m = bad("theorem t(a: Nat, b: Nat, pf: a = b): a = b { let p: a = b = pf; p }");
    assert!(m.contains("is a term, not a type"), "{m}");
    assert!(m.contains("parenthesise it"), "{m}");
}

/// §8 item 4(b): `no_eq` is scoped to the *annotation*, so a `let`'s value may
/// still be an equation. This is the `surface-universe` counterexample that
/// killed the last-`=`-scan option, and it is a control on the scoping.
#[test]
fn a_let_value_may_still_be_an_equation() {
    ok("fn f(a: Nat, b: Nat) -> Nat { let x: Type<0> = a = b; 0 }");
}

/// §8 item 4(c): the parenthesis escape hatch `no_eq`'s doc comment promised.
/// Until this round `a = (b = c)` was a parse error, which made the `CHAIN`
/// diagnostic's own advice false (`docs/let-and-blocks-design.md` §1.1(3)).
#[test]
fn a_parenthesis_is_a_real_escape_hatch() {
    ok("fn f(b: Nat, c: Nat) -> Type<1> { let x: Type<1> = (b = c) = (b = c); x }");
}

// -- §4: the block expression ----------------------------------------------

/// §8 item 5, axis 1 (literal) and axis 3's other half (computing): the
/// motivating shape from `issues/match-arm-blocks.md`, at a **literal**
/// scrutinee, asserted to *compute* rather than merely to type. A `theorem`
/// whose proof is `refl` is the assertion — the two sides must converge.
#[test]
fn a_block_in_an_arm_at_a_literal_scrutinee_computes() {
    ok(&format!(
        "{ADD}
         fn f(n: Nat) -> Nat {{
             match n {{
                 Zero => 0,
                 Succ(k) => {{ let y = add(k, k); add(y, 1) }},
             }}
         }}
         theorem f_computes(): f(3) = 5 {{ refl }}"
    ));
}

/// §8 item 6, axis 1 (neutral): the same block at a scrutinee that never
/// reduces, inside an enclosing `match` arm. Nothing computes here, so the
/// alias has to survive as a term and the emitted `elim_Nat` has to type.
#[test]
fn a_block_in_an_arm_at_a_neutral_scrutinee_types() {
    ok(&format!(
        "{ADD}
         fn f(n: Nat, m: Nat) -> Nat {{
             match n {{
                 Zero => match m {{ Zero => 0, Succ(p) => {{ let y = add(p, p); y }} }},
                 Succ(k) => {{ let y = add(k, m); add(y, k) }},
             }}
         }}"
    ));
}

/// §8 item 7, axis 3: a block in an arm under an **explicit dependent
/// motive**, in a *checking* position — a `theorem`, where the block's value
/// must convert with the goal rather than be reduced away. The block carries
/// an **annotated** `let`, so §3 and §4 are exercised together, and the
/// annotation is at the arm's own equation.
#[test]
fn a_block_checks_under_a_dependent_motive() {
    ok(&format!(
        "{ADD}
         theorem add_zero(n: Nat): add(n, 0) = n {{ refl }}
         theorem t(n: Nat): add(n, 0) = n {{
             match n as \u{3bb} z => add(z, 0) = z {{
                 Zero => {{ let p: (add(0, 0) = 0) = refl; p }},
                 Succ(k) => {{ let p: (add(Succ(k), 0) = Succ(k)) = refl; p }},
             }}
         }}"
    ));
}

/// §8 item 8, axis 2: an **open** element type. The block's `let` binds at
/// `[A; n]` for a declaration type parameter `A` and an ambient length, so
/// nothing about the binding is closed and a de Bruijn shift error in the
/// alias cannot be the identity.
#[test]
fn a_block_binds_at_an_open_type() {
    ok("fn head_or<A>(z: A, n: Nat, xs: [A; Succ(n)]) -> A {
            { let ys: [A; Succ(n)] = xs; ys[FZ] }
        }");
    ok("fn pick<A>(n: Nat, k: Nat, xs: [[A; Succ(n)]; 2]) -> [A; Succ(n)] {
            match k {
                Zero => { let row: [A; Succ(n)] = xs[FZ]; row },
                Succ(p) => { let row: [A; Succ(n)] = xs[FS(FZ)]; row },
            }
        }");
}

/// §8 item 9: the form is **general**, not arm-local — which is the whole
/// argument for it over an arm-local block. A call argument, a `let` value, a
/// lambda body, a vector element, and a `match` scrutinee.
#[test]
fn a_block_is_an_expression_everywhere() {
    ok(&format!(
        "{ADD}
         fn arg(n: Nat) -> Nat {{ add({{ let y = n; y }}, 1) }}
         fn value(n: Nat) -> Nat {{ let m = {{ let y = n; add(y, y) }}; m }}
         fn lam(n: Nat) -> Nat {{ (\u{3bb} (x: Nat) => {{ let y = x; add(y, 1) }})(n) }}
         fn elem(n: Nat) -> [Nat; 2] {{ [{{ let y = n; y }}, 0] }}
         fn scrut(n: Nat) -> Nat {{ match {{ let y = n; y }} {{ Zero => 0, Succ(k) => k }} }}
         theorem arg_computes(): arg(2) = 3 {{ refl }}"
    ));
}

/// §8 item 10, the equivalence control: the same program with and without the
/// block elaborates to **convertible** terms at `Layer::Prog`, plus the
/// vacuity guard `in_language_fold.rs:103-141` established. Without the guard
/// a block that had silently elaborated to the *same* term would make the
/// conversion trivially true and the test would prove nothing — here the guard
/// asserts the opposite: a `let` is an alias, so hoisting it out of the arm
/// must give the **same** term, and that identity is itself the claim.
#[test]
fn a_block_is_the_program_without_it() {
    let with_block = format!(
        "{ADD}fn probe(n: Nat) -> Nat {{ {{ let y = add(n, n); add(y, 1) }} }}"
    );
    let without = format!(
        "{ADD}fn probe(n: Nat) -> Nat {{ let y = add(n, n); add(y, 1) }}"
    );
    let (a, aty, alvl) = last_body(&elab(&with_block));
    let (b, ..) = last_body(&elab(&without));
    // A `let` is an alias, not a binder, so the *identical* term is the
    // expected outcome and inequality would mean the block minted something.
    assert!(a == b, "a block emitted a different term than the hoisted `let`");
    let empty = LocalCtx { base: CtxBase::Nil, entries: vec![] };
    conv_term(Elaborator::with_prelude().expect("prelude").psi(), &empty, Layer::Prog,
              &a, &b, &aty, &alvl, 1_000_000)
        .expect("the two spellings must be convertible");
}

/// §8 item 11, the negative controls. Each has its own message, because each
/// is a different decision (§4.3, §4.5, §4.4, §7.2).
#[test]
fn the_block_rejections_carry_their_messages() {
    // (a) `on` inside a block expression: a nested goal scope, which the
    // declaration-scoped goal machinery cannot serve.
    let m = bad("theorem t(n: Nat): n = n { { ?g on ?g := refl; } }");
    assert!(m.contains("cannot discharge goals"), "{m}");
    assert!(m.contains("nested-goal-discharge"), "{m}");
    // (b) a `let` *after* the result: `block_body`'s all-`let`s-first shape.
    let m = bad("fn f(n: Nat) -> Nat { { n let y = n; } }");
    assert!(!m.is_empty(), "{m}");
    // (c) `let code x` inside a block expression in a non-meta declaration:
    // the existing meta-layer message, now reachable from a second site.
    let m = bad("fn f(n: Nat) -> Nat { { let code x = n; n } }");
    assert!(m.contains("meta-layer syntax"), "{m}");
    // (d) a block as a `code { … }` payload's top level (§7.2).
    let m = bad("meta fn q(g: Ctx) -> Code(g |- Nat) { code { { let y = 1; y } } }");
    assert!(m.contains("one expression, not a block"), "{m}");
    assert!(m.contains("let-inside-quotation"), "{m}");
    // (e) an empty block has no result expression.
    let m = bad("fn f(n: Nat) -> Nat { { } }");
    assert!(m.contains("expected an expression"), "{m}");
}

/// §8 item 12, `count_holes`: a hole inside an arm-level block, discharged by
/// the *declaration's* trailing `on` — the capture §4.3 says is not lost by
/// refusing a block-level `on`. Plus a second hole in a **nested** block, so a
/// shallow walk (one that visited a block's result but not its statements, or
/// did not recurse) is caught too. Without the `count_holes` arm this is
/// `internal: more goals than the pre-count reserved`.
#[test]
fn a_hole_inside_a_block_is_counted() {
    ok(&format!(
        "{ADD}
         theorem add_zero(n: Nat): add(n, 0) = n {{ refl }}
         theorem t(n: Nat): add(n, 0) = n {{
             match n as \u{3bb} z => add(z, 0) = z {{
                 Zero => {{ let p: (add(0, 0) = 0) = ?zero; p }},
                 Succ(k) => {{ let q = {{ let r: (add(Succ(k), 0) = Succ(k)) = ?succ; r }}; q }},
             }}
             on ?zero := refl;
             on ?succ := refl;
         }}"
    ));
}

/// §8 item 13, `scan_splices`: the walk arm is written to `err`, so what is
/// pinned is the **rejection** — a `$x` inside a block inside a payload is
/// declined rather than silently not hoisted. Reached through a block nested
/// deeper than the payload's top level, which the parser rejects on its own.
#[test]
fn a_block_inside_a_quote_payload_is_declined() {
    let m = bad(
        "meta fn q(g: Ctx, c: Code(g |- Nat)) -> Code(g |- Nat) {
             let code x = c;
             code { add({ let y = 1; y }, $x) }
         }",
    );
    assert!(m.contains("not in this slice"), "{m}");
    assert!(m.contains("let-inside-quotation"), "{m}");
}

// -- §5: the binder traps ---------------------------------------------------

/// §8 item 15, **rule 2**: `refl` is nullary, so only the elaborator can buy
/// its name back, and it does with the guard `Fin`/`absurd`/`inj` already use.
/// This was one of the two *silent* traps (§5.1): `let refl = n; refl`
/// elaborated the **use** as `ExprKind::Refl` and died at "`refl` needs an `=`
/// expected type", a message about a form the user never wrote.
#[test]
fn a_bound_refl_is_the_binding() {
    ok("fn f(n: Nat) -> Nat { let refl = n; refl }");
    // A parameter and a declaration shadow it too — `shadowed` sees all four
    // kinds of binding.
    ok("fn f(refl: Nat) -> Nat { refl }");
    ok("fn refl(n: Nat) -> Nat { n }
        fn g(n: Nat) -> Nat { refl(n) }");
    // …and an *unshadowed* `refl` is still the form, in a checking position.
    ok("theorem t(n: Nat): n = n { refl }");
    // Both at once: the binding wins where it exists, and the form is
    // unreachable there — which is the documented cost, not a bug.
    let m = bad("theorem t(n: Nat): n = n { let refl = n; refl }");
    assert!(!m.is_empty(), "a shadowed `refl` cannot also be the form");
}

/// §8 item 14 at the elaborator: rule 1's `j` in the shape that reported the
/// bug — a `Fin` predecessor binder used as an ordinary argument.
#[test]
fn a_bound_j_is_an_ordinary_name() {
    ok("fn f(i: Fin(2)) -> Nat { match i { FZ => 0, FS(j) => 1 } }");
    // The reported shape: a *use* of the binder as an argument, which is
    // where the old message named an eliminator the user never wrote.
    ok("fn f(n: Nat, xs: [Nat; Succ(n)], i: Fin(Succ(Succ(n)))) -> Nat {
            match i { FZ => 0, FS(j) => xs[j] }
        }");
}
