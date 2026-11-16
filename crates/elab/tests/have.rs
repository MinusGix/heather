//! `have x = e;` — a block binding whose value is hidden
//! (`docs/language/have-design.md`).
//!
//! A `have` is the one statement that emits a kernel form, the redex
//! `(λ x: T. rest)(v)`, so per `docs/testing-generated-terms.md` it gets all
//! four axes: a literal argument that must **compute**, a neutral one where
//! nothing reduces, an **open** element type, a *checking* position under a
//! dependent expected type, and negative controls. The last test is the reason
//! the form exists: the kernel's cost for a chain of `have`s is linear where
//! the same chain of `let`s is exponential.

use heather_elab::{ElabError, Elaborator};
use heather_kernel::stats as kstats;

const ADD: &str =
    "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }\n";

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

/// Axis 1 (literal): the redex is an ordinary β-redex, so hiding the value
/// from the rest of the *block* does not hide it from *computation*. A
/// function whose body is a `have` chain still reduces to its value.
#[test]
fn a_have_computes_at_a_literal_argument() {
    ok(&format!(
        "{ADD}
         fn f(n: Nat) -> Nat {{ have m = add(n, 1); have m2 = add(m, m); m2 }}
         theorem f_computes(): f(2) = 6 {{ refl }}"
    ));
}

/// Axis 1 (neutral): at a neutral argument the redex still β-reduces, and
/// the equation holds by computation on both sides.
#[test]
fn a_have_reduces_at_a_neutral_argument() {
    ok(&format!(
        "{ADD}
         fn f(n: Nat) -> Nat {{ have m = add(n, 1); add(m, m) }}
         theorem f_unfolds(n: Nat): f(n) = add(add(n, 1), add(n, 1)) {{ refl }}"
    ));
}

/// Axis 2: an **open** type. The binder's type mentions a declaration type
/// parameter, so a wrong shift of the domain or of the weakened expected type
/// cannot be the identity.
#[test]
fn a_have_binds_at_an_open_type() {
    ok("fn twice<A>(a: A, f: A -> A) -> A { have b: A = f(a); f(b) }");
    ok("fn head_or<A>(n: Nat, xs: [A; Succ(n)]) -> A { have ys: [A; Succ(n)] = xs; ys[FZ] }");
}

/// Axis 3: a *checking* position whose expected type mentions the
/// declaration's parameters and is weakened past the binder (§4), both in a
/// declaration body and in a block under a dependent motive.
#[test]
fn a_have_checks_under_a_dependent_expected_type() {
    ok(&format!(
        "{ADD}
         theorem add_zero(n: Nat): add(n, 0) = n {{ refl }}
         theorem t(n: Nat): add(n, 0) = n {{ have e: (add(n, 0) = n) = add_zero(n); e }}
         theorem u(n: Nat): add(n, 0) = n {{
             match n as \u{3bb} z => add(z, 0) = z {{
                 Zero => {{ have p: (add(0, 0) = 0) = refl; p }},
                 Succ(k) => {{ have p = add_zero(Succ(k)); let q = p; q }},
             }}
         }}"
    ));
}

/// Inference position: a block with a `have` in a `let` value is inferred,
/// and its type is the rest's with the value substituted back — `x = x` at
/// `x := 2` is `2 = 2`, which the statement then has to accept.
#[test]
fn an_inferred_block_substitutes_the_value_into_its_type() {
    ok("theorem refl_at(a: Nat): a = a { refl }
        theorem u(): 2 = 2 { let p = { have x = 2; refl_at(x) }; p }");
}

/// The negative control, and the whole meaning of the form: the rest of the
/// block does not see the value. The same proof with `let` goes through.
#[test]
fn a_have_hides_its_value_from_the_rest_of_the_block() {
    // `p` is used, so it reaches the kernel: an unused alias never does.
    const USE: &str = "fn use_eq(a: Nat, q: a = 3) -> Nat { a }\n";
    ok(&format!("{USE}fn f() -> Nat {{ let x = 3; let p: (x = 3) = refl; use_eq(x, p) }}"));
    let m = bad(&format!("{USE}fn f() -> Nat {{ have x = 3; let p: (x = 3) = refl; use_eq(x, p) }}"));
    assert!(m.contains("NotConvertible") || m.contains("refl"), "{m}");
}

/// `have` and `let` interleave, shadow each other like any binders, and a
/// `let` after a `have` may mention it.
#[test]
fn have_and_let_interleave_and_shadow() {
    ok(&format!(
        "{ADD}
         fn f(n: Nat) -> Nat {{ let a = n; have x = add(a, 1); let y = add(x, x); have x = add(y, 1); x }}
         theorem f_computes(): f(1) = 5 {{ refl }}"
    ));
}

/// A self-call after a `have` in a structurally recursive arm: the guard's
/// induction hypothesis is found under the extra binder exactly as under a λ.
/// The arm says `Succ(k)`, not `n`: naming the scrutinee there is
/// issues/recursive-arm-reads-outer-scrutinee.md, with or without a `have`.
#[test]
fn a_self_call_after_a_have_is_still_guarded() {
    ok(&format!(
        "{ADD}
         fn sum(n: Nat) -> Nat {{
             match n {{ Zero => 0, Succ(k) => {{ have r = sum(k); have s = sum(k); add(add(r, s), Succ(k)) }} }}
         }}
         theorem sum_computes(): sum(3) = 11 {{ refl }}"
    ));
}

/// Holes on either side of the binder are counted and discharged. The one
/// after it lives in a context that lists the `have` as a plain local.
#[test]
fn holes_around_a_have_are_goals() {
    ok(&format!(
        "{ADD}
         theorem t(n: Nat): add(n, 0) = n {{ have e: (add(n, 0) = n) = ?g; have m = n; e on ?g := refl; }}
         theorem u(n: Nat): n = n {{ have m = add(n, 0); ?h on ?h := refl; }}"
    ));
}

/// A `have`-bound function carries its written implicit binder: the
/// skeleton rides on the binder as it does on an alias.
#[test]
fn a_have_bound_lambda_keeps_its_skeleton() {
    ok("fn f(n: Nat) -> Nat { have id = \u{3bb} {A: Type} (a: A) => a; id(n) }");
}

/// `have` is contextual: only `have` followed by a name is a statement, so a
/// value named `have` still works, at a block's result included.
#[test]
fn have_is_still_an_ordinary_name() {
    ok("fn f(n: Nat) -> Nat { let have = n; have }");
    ok("fn have(n: Nat) -> Nat { n }
        fn g(n: Nat) -> Nat { have(n) }");
}

/// The forms `have` does not take, each refused rather than read as
/// something else (§2).
#[test]
fn the_have_refusals_carry_their_messages() {
    let m = bad("fn f(n: Nat) -> Nat { have { a } = n; a }");
    assert!(!m.is_empty(), "{m}");
    let m = bad("meta fn q(g: Ctx) -> Code(g |- Nat) { have x = 1; code { 0 } }");
    assert!(m.contains("`have` is not part of the meta slice"), "{m}");
}

/// The acceptance family of `issues/proof-let-substitution-cost.md`: a chain
/// in which each binding uses the previous one twice. As `have`s its kernel
/// cost is linear. The counters are exact, so the assertion is on them and
/// not on time. As `let`s it was 2^k (the number of paths) until the
/// kernel's typing memo (`issues/kernel-typing-memo-on-node-identity.md`)
/// judged each shared link once; it is linear too now, and `let_and_blocks.rs`
/// holds that side.
#[test]
fn a_fan_out_chain_of_haves_checks_in_linear_time() {
    fn chain(keyword: &str, k: usize) -> String {
        let mut body = String::from("    KW s0 = mix(a, a);\n");
        for i in 1..=k {
            body.push_str(&format!("    KW s{i} = mix(s{j}, s{j});\n", j = i - 1));
        }
        format!(
            "fn mix(x, y: Nat) -> Nat {{ x }}\nfn chain(a: Nat) -> Nat {{\n{}    s{k}\n}}\n",
            body.replace("KW", keyword)
        )
    }
    fn queries(src: &str) -> u64 {
        let mut e = Elaborator::with_prelude().expect("prelude");
        let before = kstats::snapshot();
        if let Err(err) = e.elab_source(src) {
            panic!("expected success, got: {}", err.render(src));
        }
        let d = kstats::snapshot().since(&before);
        d.conv_shortcut_hits + d.conv_memo_hits + d.conv_misses
    }
    let short = queries(&chain("have", 10));
    let long = queries(&chain("have", 40));
    assert!(long < 6 * short, "k = 10 → 40 grew {short} → {long}: not linear");
}
