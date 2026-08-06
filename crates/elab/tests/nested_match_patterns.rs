//! Deep patterns and the `_` arm (`docs/nested-match-patterns-design.md`).
//!
//! Two sugarings, one preprocessing pass. A deep pattern compiles by the
//! classic pattern matrix into the nested single-level `match`es a user writes
//! by hand today; a `_ =>` arm expands to the constructors with no arm of
//! their own. Neither adds an elimination form, so the suite's job is to show
//! that the *compiled* tree computes what the hand-written tower computes, and
//! that the boundaries the design refuses are refused by name.
//!
//! Per `docs/testing-generated-terms.md`:
//!
//! - **axis 1** — a literal scrutinee that must **compute** (`refl` against
//!   the expected reduct, at every branch of the tree including the
//!   fallthrough ones) and a **neutral** one, where nothing reduces and the
//!   compiled tree has to be *convertible* with the hand-written tower;
//! - **axis 2** — every fixture is parameterized, so the payload type is an
//!   ambient variable and a shift error in a generated level is visible;
//! - **axis 3** — a deep match and a `_` arm in **checking** position under a
//!   dependent `as` motive, where the annotation must convert with a goal;
//! - **axis 4** — one negative control per decision of §1;
//! - **axis 6** — `Res3` has three constructors and an open payload, crossed
//!   with the 2026-08-05 refinement: a **dependent** motive, so the inner
//!   `Case` node's annotations are not substituted away before the kernel
//!   sees them.
//!
//! Plus a nonzero-level test (§12) and the sharing observable: a `_ => ?g`
//! over a three-constructor type raises **exactly one** goal, asserted off
//! `ElabError::UnsolvedGoals` rather than by printing a kernel term.

use heather_elab::{ElabError, Elaborator};
use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::term::{GlobalBinding, LocalCtx, Term};
use heather_kernel::typing::DEFAULT_FUEL;

/// Axis 6 × axis 2: three constructors and a type-parameter payload, plus a
/// nested family so a pattern can actually be *deep*, plus a recursive
/// (tier-1) inductive with eight constructors — `pick_arm`'s shape, which is
/// what motivates the `_` arm at all.
const PREAMBLE: &str = r#"
inductive Res3<A> { Stuck, OutOfFuel, Out(v: A) }
inductive Opt<A> { NoneV, SomeV(v: A) }
inductive Val { VNil, VCon(tag: Nat, fs: Val), VCons(h: Val, t: Val) }

inductive Ir {
    Ret(rs: Nat),
    LetCon(tag: Nat, rest: Ir),
    LetMatch(scrut: Nat, rest: Ir),
    Arm(body: Ir, next: Ir),
    NoArm,
    LetLoop(body: Ir, rest: Ir),
    LoopIter(body: Ir),
    LetCall(callee: Nat, rest: Ir),
}

fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k) => Succ(add(k, n)),
    }
}
"#;

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(PREAMBLE).unwrap_or_else(|err| panic!("preamble: {}", err.render(PREAMBLE)));
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn ok(src: &str) {
    elab(src);
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(PREAMBLE).expect("preamble");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated:\n{src}"),
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(ElabError::Parse(p)) => p.msg,
        Err(other) => format!("{other}"),
    }
}

/// The goals a declaration leaves undischarged — the sharing observable (§5.3).
fn unsolved(src: &str) -> usize {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(PREAMBLE).expect("preamble");
    match e.elab_source(src) {
        Err(ElabError::UnsolvedGoals { goals, .. }) => goals.len(),
        other => panic!("expected unsolved goals, got {other:?}"),
    }
}

/// The body of the last committed binding.
fn last_body(e: &Elaborator) -> Term {
    match e.psi().bindings.last().expect("a binding") {
        GlobalBinding::Tm { body: Some(b), .. } => (**b).clone(),
        other => panic!("expected a bodied Tm binding, found {other:?}"),
    }
}

fn empty_ctx() -> LocalCtx {
    LocalCtx::nil()
}

// ---------------------------------------------------------------------------
// Axis 1 — a literal scrutinee, and it must COMPUTE.
//
// `loopiter` is `lib/ir_v1.hthr`'s `step_loopiter` written flat: three levels
// deep, and the middle level carries a column (`carried`) *past* a split,
// which is the case a single-column compiler gets wrong.
// ---------------------------------------------------------------------------

const LOOPITER: &str = r#"
fn loopiter(r: Res3<Val>) -> Res3<Val> {
    match r {
        Out(VCons(VCon(Zero, ffields), carried)) => Out(carried),
        Out(VCons(VCon(Succ(f2), ffields), carried)) => OutOfFuel,
        Stuck => Stuck,
        _ => Stuck,
    }
}
"#;

#[test]
fn a_deep_match_computes_at_a_literal_scrutinee() {
    ok(&format!(
        "{LOOPITER}
         // The two deep rows, each reached through three levels.
         theorem stop(): loopiter(Out(VCons(VCon(0, VNil), VNil))) = Out(VNil) {{ refl }}
         theorem go(): loopiter(Out(VCons(VCon(1, VNil), VNil))) = OutOfFuel {{ refl }}
         // The column carried past the split really is the outer one.
         theorem carries(): loopiter(Out(VCons(VCon(0, VNil), VCons(VNil, VNil))))
             = Out(VCons(VNil, VNil)) {{ refl }}
         // A top-level arm of its own, and the three ways to fall through:
         // at the outermost level, at the middle one, at the innermost one.
         theorem shallow(): loopiter(Stuck) = Stuck {{ refl }}
         theorem fall_top(): loopiter(OutOfFuel) = Stuck {{ refl }}
         theorem fall_mid(): loopiter(Out(VNil)) = Stuck {{ refl }}
         theorem fall_deep(): loopiter(Out(VCons(VNil, VNil))) = Stuck {{ refl }}"
    ));
}

// ---------------------------------------------------------------------------
// Axis 1 again — a NEUTRAL scrutinee, where nothing reduces and the compiled
// tree has to agree with the hand-written tower as a term.
// ---------------------------------------------------------------------------

#[test]
fn a_deep_match_agrees_with_the_hand_written_tower_at_a_neutral_scrutinee() {
    let e = elab(
        r#"
        fn deep<A>(o: Opt<Res3<A>>, d: A) -> A {
            match o {
                SomeV(Out(v)) => v,
                _ => d,
            }
        }
        fn tower<A>(o: Opt<Res3<A>>, d: A) -> A {
            match o {
                NoneV => d,
                SomeV(w) => match w {
                    Stuck => d,
                    OutOfFuel => d,
                    Out(v) => v,
                },
            }
        }
        "#,
    );
    // Both bodies are closed (their parameters are λ-bound), so the two
    // committed terms are compared at the declaration's own type in the empty
    // context. Convertible, not necessarily identical: the compiled tree binds
    // its columns through `let` aliases, which are inlined, and the arm order
    // is the declaration's on both sides.
    let bindings = &e.psi().bindings;
    let n = bindings.len();
    let (deep, tower) = (&bindings[n - 2], &bindings[n - 1]);
    let (GlobalBinding::Tm { body: Some(d), ty, level, .. }, GlobalBinding::Tm { body: Some(t), .. }) =
        (deep, tower)
    else {
        panic!("expected two bodied bindings")
    };
    conv_term(&e.psi(), &empty_ctx(), Layer::Prog, d, t, ty, level, DEFAULT_FUEL)
        .expect("the compiled decision tree and the hand-written tower agree");
}

#[test]
fn a_deep_match_computes_under_an_open_element_type() {
    // Axis 2: the payload is an ambient variable, so every annotation the
    // generated levels carry mentions it.
    ok(
        r#"
        fn deep<A>(o: Opt<Res3<A>>, d: A) -> A {
            match o { SomeV(Out(v)) => v, _ => d }
        }
        theorem hit<A>(v: A, d: A): deep(SomeV(Out(v)), d) = v { refl }
        theorem miss_inner<A>(d: A): deep(SomeV(Stuck<A>()), d) = d { refl }
        theorem miss_outer<A>(d: A): deep(NoneV<Res3<A>>(), d) = d { refl }
        "#,
    );
}

// ---------------------------------------------------------------------------
// Axis 3 — checking position under a dependent motive. `z` really occurs in
// the motive, which is the 2026-08-05 refinement of axis 6: at a
// non-dependent one the case tree's injections are substituted away before
// the kernel is shown them.
// ---------------------------------------------------------------------------

#[test]
fn a_default_arm_checks_under_a_dependent_motive() {
    ok(
        r#"
        fn idr<A>(r: Res3<A>) -> Res3<A> { match r { Out(v) => Out(v), _ => Stuck } }
        theorem idr_idem<A>(r: Res3<A>): idr(idr(r)) = idr(r) {
            match r as fun z => idr(idr(z)) = idr(z) {
                Out(v) => refl,
                _ => refl,
            }
        }
        "#,
    );
}

#[test]
fn a_deep_match_checks_under_a_dependent_motive() {
    ok(
        r#"
        fn flat<A>(o: Opt<Res3<A>>) -> Opt<Res3<A>> {
            match o { SomeV(Out(v)) => SomeV(Out(v)), _ => NoneV }
        }
        theorem flat_idem<A>(o: Opt<Res3<A>>): flat(flat(o)) = flat(o) {
            match o as fun z => flat(flat(z)) = flat(z) {
                NoneV => refl,
                SomeV(w) => match w as fun y => flat(flat(SomeV(y))) = flat(SomeV(y)) {
                    Stuck => refl,
                    OutOfFuel => refl,
                    Out(v) => refl,
                },
            }
        }
        "#,
    );
}

// ---------------------------------------------------------------------------
// The `_` arm really expands — over the eight-constructor recursive family
// that motivated it.
// ---------------------------------------------------------------------------

#[test]
fn a_default_arm_expands_over_every_missing_constructor() {
    ok(
        r#"
        fn pick(arms: Ir) -> Nat {
            match arms {
                Arm(body, next) => 1,
                _ => 0,
            }
        }
        // The arm it names.
        theorem p_arm(): pick(Arm(NoArm, NoArm)) = 1 { refl }
        // Every one of the seven it does not, so each expanded arm exists and
        // carries the shared body. Nullary, unary and binary alike.
        theorem p_noarm(): pick(NoArm) = 0 { refl }
        theorem p_ret(): pick(Ret(3)) = 0 { refl }
        theorem p_loopiter(): pick(LoopIter(NoArm)) = 0 { refl }
        theorem p_letcon(): pick(LetCon(1, NoArm)) = 0 { refl }
        theorem p_letmatch(): pick(LetMatch(1, NoArm)) = 0 { refl }
        theorem p_letloop(): pick(LetLoop(NoArm, NoArm)) = 0 { refl }
        theorem p_letcall(): pick(LetCall(1, NoArm)) = 0 { refl }
        "#,
    );
}

#[test]
fn a_default_arm_is_dropped_when_nothing_is_missing() {
    // §3.4: redundancy is silent, because the pattern compiler emits
    // redundant `_` arms itself (a `Nat` column covered by `Zero` and `Succ`).
    ok(
        r#"
        fn allthree<A>(r: Res3<A>, d: A) -> Nat {
            match r { Stuck => 0, OutOfFuel => 1, Out(v) => 2, _ => 3 }
        }
        theorem at_s<A>(d: A): allthree(Stuck<A>(), d) = 0 { refl }
        theorem at_o<A>(v: A, d: A): allthree(Out(v), d) = 2 { refl }
        "#,
    );
}

#[test]
fn a_default_arm_on_a_recursive_argument_keeps_the_guard() {
    // §6.2: `_` binds nothing the guard reads, so it is available in the
    // decreasing position — which is `pick_arm`'s whole shape.
    ok(
        r#"
        fn depth(arms: Ir) -> Nat {
            match arms {
                Arm(body, next) => Succ(depth(next)),
                _ => 0,
            }
        }
        theorem d0(): depth(NoArm) = 0 { refl }
        theorem d2(): depth(Arm(NoArm, Arm(NoArm, NoArm))) = 2 { refl }
        "#,
    );
}

// ---------------------------------------------------------------------------
// §5 — sharing, observably.
// ---------------------------------------------------------------------------

#[test]
fn a_shared_default_body_raises_exactly_one_goal() {
    // Three constructors, two of them expanded from the `_`. Duplicating the
    // body would raise the goal twice — and, worse, re-elaborate one hole in
    // two contexts. Asserted off the goal listing: no kernel term is printed.
    assert_eq!(
        unsolved(
            r#"
            fn sh<A>(r: Res3<A>, d: A) -> A {
                match r { Out(v) => v, _ => ?fallback }
            }
            "#
        ),
        1,
        "the `_` body must be elaborated once, not once per expanded arm"
    );
}

#[test]
fn a_shared_default_body_is_discharged_once() {
    ok(
        r#"
        fn sh<A>(r: Res3<A>, d: A) -> A {
            { let x: A = match r { Out(v) => v, _ => ?fallback }; x }
            on ?fallback := d;
        }
        theorem sh_hit<A>(v: A, d: A): sh(Out(v), d) = v { refl }
        theorem sh_miss<A>(d: A): sh(Stuck<A>(), d) = d { refl }
        "#,
    );
}

#[test]
fn a_shared_default_body_is_one_node_when_it_is_closed() {
    // §5.3's strongest claim: `shift_local` returns the same `Rc` for a
    // subtree it does not change, so a *closed* shared body is literally one
    // node in the emitted term rather than one copy per arm. Measured by
    // pointer identity between two of the expanded arms' occurrences — the
    // term is walked, never formatted.
    let e = elab(
        r#"
        fn pick(arms: Ir) -> Nat {
            match arms { Arm(body, next) => 1, _ => Succ(Succ(Succ(Succ(Zero)))) }
        }
        "#,
    );
    let body = last_body(&e);
    let mut seen: Vec<*const Term> = Vec::new();
    count_shared(&body, &mut seen);
    // The default body is `4`. Its *interior* — the `Succ(Succ(Succ(Zero)))`
    // under the head — is what `shift_local` hands back untouched, so sharing
    // makes it one pointer where seven independent elaborations would make it
    // seven. The head itself is re-allocated per use, because `resolve`
    // returns a `Term` by value (§5.3).
    let copies = seen.len();
    assert_eq!(copies, 1, "expected one shared `Succ(Succ(Succ(Zero)))`, found {copies}");
}

/// Collect the distinct identities of every `Succ(Succ(Succ(Zero)))` subterm.
/// Structural walk, no formatting.
fn count_shared(t: &Term, seen: &mut Vec<*const Term>) {
    fn depth3(t: &Term) -> bool {
        let mut cur = t;
        for _ in 0..3 {
            match cur {
                Term::Succ(k) => cur = k,
                _ => return false,
            }
        }
        matches!(cur, Term::Zero)
    }
    if depth3(t) {
        let p = t as *const Term;
        if !seen.contains(&p) {
            seen.push(p);
        }
        return;
    }
    for c in children(t) {
        count_shared(c, seen);
    }
}

fn children(t: &Term) -> Vec<&Term> {
    match t {
        Term::Succ(k) => vec![k],
        Term::Lam { body, .. } => vec![body],
        Term::App { fun, arg, .. } => vec![fun, arg],
        Term::Pair { fst, snd, .. } => vec![fst, snd],
        Term::Fst { pair, .. } | Term::Snd { pair, .. } => vec![pair],
        Term::Inl { val, .. } | Term::Inr { val, .. } => vec![val],
        Term::Case { case_l, case_r, scrut, .. } => vec![case_l, case_r, scrut],
        Term::ElimNat { base, step, scrut, .. } => vec![base, step, scrut],
        Term::ElimEmpty { scrut, .. } => vec![scrut],
        Term::ElimWf { scrut, step, .. } => vec![scrut, step],
        _ => vec![],
    }
}

// ---------------------------------------------------------------------------
// A nonzero level (§12).
// ---------------------------------------------------------------------------

#[test]
fn a_deep_match_at_a_type_valued_result() {
    // The motive is at level 1, so every level of the compiled tree carries a
    // `Level::Succ` where the level-0 fixtures carry `Zero`.
    ok(
        r#"
        fn tsel(o: Opt<Res3<Nat>>) -> Type<0> {
            match o {
                SomeV(Out(v)) => Nat,
                _ => Nat -> Nat,
            }
        }
        theorem t_hit(v: Nat): tsel(SomeV(Out(v))) = Nat { refl }
        theorem t_inner(): tsel(SomeV(Stuck)) = (Nat -> Nat) { refl }
        theorem t_outer(): tsel(NoneV) = (Nat -> Nat) { refl }
        "#,
    );
}

// ---------------------------------------------------------------------------
// §8 — the equation binding and `split` inherit both features.
// ---------------------------------------------------------------------------

#[test]
fn a_deep_match_may_carry_an_equation_binding() {
    ok(
        r#"
        fn cv<A>(o: Opt<Res3<A>>, d: A) -> A {
            match h : o {
                SomeV(Out(v)) => v,
                _ => d,
            }
        }
        theorem cv_hit<A>(v: A, d: A): cv(SomeV(Out(v)), d) = v { refl }
        theorem cv_miss<A>(d: A): cv(NoneV<Res3<A>>(), d) = d { refl }
        "#,
    );
}

#[test]
fn a_split_takes_a_default_arm_and_a_deep_one() {
    ok(
        r#"
        fn spl<A>(o: Opt<Res3<A>>, d: A) -> A {
            split o;
            on SomeV(Out(v)) := v;
            on _ := d;
        }
        theorem spl_hit<A>(v: A, d: A): spl(SomeV(Out(v)), d) = v { refl }
        theorem spl_miss<A>(d: A): spl(SomeV(OutOfFuel<A>()), d) = d { refl }
        "#,
    );
}

// ---------------------------------------------------------------------------
// §7 — indexed families: index fields are refused, payload fields are not.
// ---------------------------------------------------------------------------

const TG: &str = r#"
inductive Col { CZ, CS(n: Nat) }
inductive Tg : (c: Col) -> Type {
    TZ                 : Tg(CZ),
    TS(n: Nat, x: Nat) : Tg(CS(n)),
}
"#;

#[test]
fn an_indexed_family_takes_a_deep_pattern_at_a_payload_field() {
    ok(&format!(
        "{TG}
         fn pl(c: Col, t: Tg(c)) -> Nat {{ match t {{ TS(n, Succ(m)) => m, _ => 0 }} }}
         theorem pl_hit(): pl(CS(3), TS(3, 7)) = 6 {{ refl }}
         theorem pl_zero(): pl(CS(3), TS(3, 0)) = 0 {{ refl }}
         theorem pl_tz(): pl(CZ, TZ) = 0 {{ refl }}
         // The same, in inference position with the two-binder motive.
         fn pl2(c: Col, t: Tg(c)) -> Nat {{
             match t as fun i z => Nat {{ TS(n, Succ(m)) => m, _ => 0 }}
         }}
         theorem pl2_hit(): pl2(CS(3), TS(3, 7)) = 6 {{ refl }}"
    ));
}

// ---------------------------------------------------------------------------
// Axis 4 — one negative control per decision of §1.
// ---------------------------------------------------------------------------

#[test]
fn a_wrong_arm_body_is_refuted() {
    // The positive tests above cannot tell a decision tree from a tree that
    // routes two branches to the same leaf. This one can: it asserts a
    // *false* equation between the two deep rows' results.
    let msg = bad(&format!(
        "{LOOPITER}
         theorem wrong(): loopiter(Out(VCons(VCon(1, VNil), VNil))) = Out(VNil) {{ refl }}"
    ));
    assert!(msg.contains("NotConvertible"), "{msg}");
}

#[test]
fn a_match_with_no_default_must_still_be_exhaustive() {
    let msg = bad("fn f<A>(r: Res3<A>, d: A) -> A { match r { Out(v) => v } }");
    assert!(msg.contains("missing an arm"), "{msg}");
    assert!(msg.contains("Stuck") && msg.contains("OutOfFuel"), "{msg}");
}

#[test]
fn a_deep_match_with_no_fallthrough_is_not_exhaustive() {
    // The inner column is the one that is short, and §3.4 says the message
    // lands on the outer `match`. Recorded here so a future span improvement
    // has to change a test deliberately.
    let msg = bad(
        "fn f<A>(o: Opt<Res3<A>>, d: A) -> A {
             match o { NoneV => d, SomeV(Out(v)) => v, SomeV(Stuck) => d }
         }",
    );
    assert!(msg.contains("missing an arm for `OutOfFuel`"), "{msg}");
}

#[test]
fn a_default_arm_must_be_last() {
    let msg = bad("fn f<A>(r: Res3<A>, d: A) -> A { match r { _ => d, Out(v) => v } }");
    assert!(msg.contains("must be the last arm"), "{msg}");
}

#[test]
fn a_default_arm_binds_nothing() {
    let msg = bad("fn f<A>(r: Res3<A>, d: A) -> A { match r { Out(v) => v, _(x) => d } }");
    assert!(msg.contains("`_` binds no fields"), "{msg}");
}

#[test]
fn a_deep_pattern_in_the_decreasing_position_is_refused() {
    let msg = bad(
        "fn f(arms: Ir) -> Nat {
             match arms { Arm(body, Arm(b2, n2)) => f(n2), _ => 0 }
         }",
    );
    assert!(msg.contains("deep pattern is not available in this `match`"), "{msg}");
    assert!(msg.contains("descends on `arms`"), "{msg}");
    assert!(msg.contains("termination guard"), "{msg}");
}

#[test]
fn a_deep_pattern_at_an_index_field_is_refused() {
    let msg = bad(&format!(
        "{TG}
         fn ix(c: Col, t: Tg(c)) -> Nat {{ match t {{ TS(Succ(m), x) => m, _ => 0 }} }}"
    ));
    assert!(msg.contains("index* pattern variable"), "{msg}");
    assert!(msg.contains("`Tg` is an indexed family"), "{msg}");
}

#[test]
fn a_copied_body_with_a_goal_is_refused_by_name() {
    // §10.3: a dependent motive makes sharing impossible, and a hole cannot be
    // elaborated in two contexts. The message says which, rather than the
    // `internal:` one the hole machinery would raise.
    let msg = bad(
        "theorem t<A>(r: Res3<A>): r = r {
             match r as fun z => z = z { Out(v) => refl, _ => ?g }
             on ?g := refl;
         }",
    );
    assert!(msg.contains("cannot be elaborated more than once"), "{msg}");
    assert!(msg.contains("the motive mentions the scrutinee"), "{msg}");
}

#[test]
fn an_arity_mismatch_inside_a_deep_pattern_is_named() {
    let msg = bad(
        "fn f<A>(o: Opt<Res3<A>>, d: A) -> A {
             match o { SomeV(Out(v, w)) => d, _ => d }
         }",
    );
    assert!(msg.contains("binds 1 field(s), found 2"), "{msg}");
}

#[test]
fn a_default_arm_needs_a_known_constructor_set() {
    // §4: at an open `Fin` length there is nothing to expand to.
    let msg = bad("fn f(n: Nat, i: Fin(n)) -> Nat { match i { _ => 0 } }");
    assert!(msg.contains("known set of constructors"), "{msg}");
}

// ---------------------------------------------------------------------------
// §3.5 — a bare identifier that names a constructor is that constructor.
// ---------------------------------------------------------------------------

#[test]
fn a_nullary_constructor_reads_as_a_pattern_not_a_binder() {
    ok(
        r#"
        fn nz<A>(o: Opt<Res3<A>>, d: A) -> Nat {
            match o { SomeV(Stuck) => 1, SomeV(OutOfFuel) => 2, _ => 0 }
        }
        theorem nz_s<A>(d: A): nz(SomeV(Stuck<A>()), d) = 1 { refl }
        theorem nz_o<A>(d: A): nz(SomeV(OutOfFuel<A>()), d) = 2 { refl }
        theorem nz_v<A>(v: A, d: A): nz(SomeV(Out(v)), d) = 0 { refl }
        theorem nz_n<A>(d: A): nz(NoneV<Res3<A>>(), d) = 0 { refl }
        "#,
    );
    // And the level-0 spelling: `Zero` in a sub-pattern is the numeral's
    // constructor, not a name for the field.
    ok(
        r#"
        fn tz(v: Val) -> Nat {
            match v { VCon(Zero, fs) => 1, _ => 0 }
        }
        theorem tz_hit(): tz(VCon(0, VNil)) = 1 { refl }
        theorem tz_miss(): tz(VCon(1, VNil)) = 0 { refl }
        "#,
    );
}
