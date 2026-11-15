//! Acceptance for issues/decreases-unfolding-equations.md
//! (docs/language/recursion/decreases-unfolding-design.md): the generated unfolding equation
//! `f_unfold(x̄): f(x̄) = body`, and the two lifted helpers it is proved
//! through. The whole point is the customer proof — a theorem *about* a
//! `decreases`-defined function at an **open** argument, which is refused
//! outright without the equation — so that is what the positives are.
//!
//! What they vary (docs/testing-generated-terms.md): the equation at a
//! literal and at a neutral argument; an **open** element type (`List<A>`,
//! not `List<Nat>`); a by-hand `on` obligation and one left to `omega` (§4's
//! lifting is what puts the second in reach); a member, whose equation is
//! read under its qualified name; the equation used in a *checking* position
//! inside a larger goal rather than as a whole proof; and negative controls
//! for each way §3's walk declines a body, plus §7's `fn`-only rule.

use std::sync::OnceLock;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/num/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/tactic/omega.hthr");

/// The same prefix, in the same order, as `semantic_omega_warmup.rs`, so the
/// on-disk image keys this file reads are the ones the warmup wrote.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", ALGEBRA),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", INT),
    ("omega", OMEGA),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn load_image() -> SemanticImage {
    // Built once per process (`BASE` is a process-wide `OnceLock`; the other
    // tests wait for it): see `support`'s note on per-test threads.
    support::semantic_test_base(MODULES).semantic_image()
}

/// A fresh elaborator over the checked library prefix. The semantic image is
/// the committed-state boundary: every call forks its own attempt, report and
/// gate state, so a test's module never leaks into the next one's base.
fn base() -> Elaborator {
    BASE.get_or_init(load_image).elaborator()
}

const IMPORTS: &str = "import logic;\nimport nat;\nimport list;\nimport int;\nimport omega;\n";

fn ok(src: &str) {
    let mut e = base();
    e.elab_module_source("m", &format!("{IMPORTS}{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err}"));
}

fn elab_err(src: &str) -> String {
    let mut e = base();
    match e.elab_module_source("m", &format!("{IMPORTS}{src}")) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

/// `halve`, the running example of the design doc's §1 and of its end-to-end
/// probe. The obligation is discharged by hand, per §4's note.
const HV: &str = r#"
fn hv(n: Nat) -> Nat decreases n {
    match n { Zero => 0, Succ(k) => Succ(hv(k)) }
    on ?dec1 := nat::Nat::lt_succ_self(k);
}
"#;

#[test]
fn the_customer_theorem_goes_through_at_an_open_argument_and_at_a_literal() {
    // §1's `hv_id`, refused outright before this round: the `Zero` arm cites
    // the equation at the **literal** `0`, the `Succ` arm at the **neutral**
    // `Succ(k)`, and §6 is what makes one equation serve both — the
    // right-hand side of `hv_unfold(0)` reduces to the arm.
    ok(&format!(
        "{HV}\n\
         theorem hv_id(n: Nat): hv(n) = n {{\n\
         \x20   match n {{\n\
         \x20       Zero => hv_unfold(0),\n\
         \x20       Succ(k, ih) => j(ih, λ y _ => hv(Succ(k)) = Succ(y), hv_unfold(Succ(k))),\n\
         \x20   }}\n\
         }}"
    ));
}

#[test]
fn the_equation_mentions_no_generated_binder() {
    // §5: the right-hand side is the body *as written* — plain `match`, plain
    // `hv(m)`, no convoy — so a proof may state it in the user's own spelling
    // and have it accepted.
    ok(&format!(
        "{HV}\n\
         theorem spelled(n: Nat): hv(n) = match n {{ Zero => 0, Succ(m) => Succ(hv(m)) }} {{\n\
         \x20   hv_unfold(n)\n\
         }}"
    ));
}

#[test]
fn gcd_carries_its_by_hand_obligation_into_the_companions() {
    // §4: the `on ?dec1` is copied verbatim onto `f#ext` and `f_unfold`, and
    // resolves there because the walk re-binds `k` in the same place. The
    // measure is refined by the convoy, so this also exercises §3's
    // "instantiate each `__dec_eqN` to `refl` at its arm's pattern".
    ok(r#"
        fn gcd(a, b: Nat) -> Nat decreases b {
            match b {
                Zero => a,
                Succ(k) => gcd(Succ(k), nat::Nat::mod(a, Succ(k))),
            }
            on ?dec1 := nat::Nat::mod_lt(a, Succ(k));
        }

        theorem gcd_step(a, k: Nat): gcd(a, Succ(k)) = gcd(Succ(k), nat::Nat::mod(a, Succ(k))) {
            gcd_unfold(a, Succ(k))
        }

        theorem gcd_12_8(): gcd(12, 8) = 4 { refl }
    "#);
}

#[test]
fn an_open_element_type_and_a_checking_position() {
    // Two axes at once (docs/testing-generated-terms.md): the element type is
    // the **open** `A` rather than `Nat`, and `eo_len` uses the equation by
    // rewriting *inside* a larger goal rather than as the whole proof. The
    // nested `match xt` is the second refinement stage of §3.
    ok(r#"
        fn every_other<A>(xs: List<A>) -> List<A> decreases xs.len() {
            match xs {
                Nil => Nil,
                Cons(x, xt) => match xt {
                    Nil => Cons(x, Nil),
                    Cons(y, yt) => Cons(x, every_other(yt)),
                },
            }
            on ?dec1 := nat::Nat::le_succ_r(Succ(yt.len()), Succ(yt.len()),
                                       nat::Nat::le_refl(Succ(yt.len())));
        }

        theorem eo_step<A>(x, y: A, yt: List<A>):
            every_other(Cons(x, Cons(y, yt))) = Cons(x, every_other(yt)) {
            every_other_unfold(Cons(x, Cons(y, yt)))
        }

        theorem eo_len<A>(x, y: A, yt: List<A>):
            every_other(Cons(x, Cons(y, yt))).len() = Succ(every_other(yt).len()) {
            j(sym(every_other_unfold(Cons(x, Cons(y, yt)))),
              λ w _ => w.len() = Succ(every_other(yt).len()),
              refl)
        }
    "#);
}

// -- negative controls --------------------------------------------------------
//
// §3: a refusal is never an error on `f` — `f` checks exactly as it did — and
// is reported only where `f_unfold` is *cited*, naming the shape that stopped
// the walk.

#[test]
fn a_theorem_by_measure_gets_no_unfolding_equation() {
    // §7: a `theorem` is opaque, so `f(ȳ)` in the right-hand side would never
    // unfold, and nothing rewrites with a proof's value anyway.
    let msg = elab_err(
        r#"
        theorem le_self(n: Nat): nat::Nat::Le(n, n) decreases n {
            match n { Zero => nat::Nat::le_refl(0), Succ(k) => nat::Nat::le_refl(Succ(k)) }
        }
        theorem cite(n: Nat): nat::Nat::Le(n, n) { le_self_unfold(n) }
        "#,
    );
    assert!(msg.contains("no unfolding equation for `le_self`"), "{msg}");
    assert!(msg.contains("`theorem`"), "{msg}");
    assert!(msg.contains("decreases-unfolding-design.md §3"), "{msg}");
}

#[test]
fn a_self_call_under_a_lambda_is_refused_but_the_function_still_checks() {
    // The one shape §3 names outright: it is functional extensionality again.
    // `under_lam` itself is accepted — only the citation reports.
    let msg = elab_err(
        r#"
        fn under_lam(n: Nat) -> Nat decreases n {
            match n {
                Zero => 0,
                Succ(k) => (λ (g: Nat -> Nat) => g(0))(λ (z: Nat) => under_lam(k)),
            }
            on ?dec1 := nat::Nat::lt_succ_self(k);
        }
        theorem cite(n: Nat): under_lam(n) = under_lam(n) { under_lam_unfold(n) }
        "#,
    );
    assert!(msg.contains("under a `λ`"), "{msg}");
    ok(r#"
        fn under_lam(n: Nat) -> Nat decreases n {
            match n {
                Zero => 0,
                Succ(k) => (λ (g: Nat -> Nat) => g(0))(λ (z: Nat) => under_lam(k)),
            }
            on ?dec1 := nat::Nat::lt_succ_self(k);
        }
    "#);
}

#[test]
fn a_match_on_a_computed_scrutinee_is_spelled_on_both_sides() {
    // `merge`'s `match nat::Nat::le_dec(x, y)`: the anchors do not reduce past
    // a stuck scrutinee, so the walk spells the match on both sides at a
    // motive generalizing the scrutinee (§3's second amendment;
    // issues/decreases-unfold-convoy-scrutinee.md). Outside the walk before.
    ok(r#"
        theorem succ_add_le(a, b: Nat): Succ(a + b) <= Succ(a) + b {
            match b { Zero => nat::Nat::le_refl(Succ(a)), Succ(k) => succ_add_le(a, k) }
        }
        fn merge(xs, ys: List<Nat>) -> List<Nat> decreases xs.len() + ys.len() {
            match xs {
                Nil => ys,
                Cons(x, xt) => match ys {
                    Nil => Cons(x, xt),
                    Cons(y, yt) => match nat::Nat::le_dec(x, y) {
                        Inl(_) => Cons(x, merge(xt, Cons(y, yt))),
                        Inr(_) => Cons(y, merge(Cons(x, xt), yt)),
                    },
                },
            }
            on ?dec1 := succ_add_le(xt.len(), yt.len());
            on ?dec2 := nat::Nat::le_refl(Succ(xt.len()) + yt.len());
        }
        theorem cite(x, y: Nat, xt, yt: List<Nat>): merge(Cons(x, xt), Cons(y, yt)) = match nat::Nat::le_dec(x, y) {
            Inl(_) => Cons(x, merge(xt, Cons(y, yt))),
            Inr(_) => Cons(y, merge(Cons(x, xt), yt)),
        } { merge_unfold(Cons(x, xt), Cons(y, yt)) }
    "#);
}

#[test]
fn a_convoy_on_a_computed_scrutinee_gets_its_equation() {
    // `match h: c`, the loop test of every measured `runtime fn`: the
    // obligation reads `h`, whose type names the walk's alias of `c`; the
    // lifted obligation states it about `c` itself, and the walk spells the
    // convoy on both sides (issues/decreases-unfold-convoy-scrutinee.md).
    ok(r#"
        fn cd(n, acc: Nat) -> Nat decreases n {
            match h: n.leb(0) {
                True => acc,
                False => cd(n - 1, acc + n),
            }
        }
        theorem cite(n, acc: Nat): cd(n, acc) = match h: n.leb(0) { True => acc, False => cd(n - 1, acc + n) } {
            cd_unfold(n, acc)
        }
    "#);
}

// -- back inside the walk -----------------------------------------------------

#[test]
fn an_obligation_left_to_omega_is_lifted_and_carries_the_equation() {
    // §4's refutation and its fix, pinned together: `halve_steps` writes no
    // `on`, so its obligation is `omega`'s — and `omega` reconstructs against
    // the *context*, so the body and the two companions must reference one
    // lifted `halve_steps#obl_1` rather than each re-run it. The customer is
    // the equation at an **open** argument, which is what the whole round is
    // for; `halve_three` next door pins that the literal still computes.
    ok(r#"
        fn halve_steps(n: Nat) -> Nat decreases n {
            match n { Zero => 0, Succ(k) => Succ(halve_steps(k)) }
        }
        theorem hs_id(n: Nat): halve_steps(n) = n {
            match n {
                Zero => halve_steps_unfold(0),
                Succ(k, ih) =>
                    j(ih, λ y _ => halve_steps(Succ(k)) = Succ(y), halve_steps_unfold(Succ(k))),
            }
        }
        theorem hs_three(): halve_steps(3) = 3 { refl }
    "#);
}

#[test]
fn a_member_by_measure_gets_its_equation_under_the_qualified_name() {
    // §5's last paragraph: a member recurses under its **base** name, and the
    // equation is read outside the body, so its right-hand side spells the
    // self-call qualified. Two refinement stages over two different
    // scrutinees, one of them the measure's — and the arm binders the lifted
    // obligation quantifies are typed from `List<A>`, not from `Nat`.
    ok(r#"
        import option;
        fn List::nth2<A>(xs: List<A>, i: Nat) -> Option<A> decreases i {
            match xs {
                Nil => None,
                Cons(x, xt) => match i { Zero => Some(x), Succ(k) => nth2(xt, k) },
            }
        }

        theorem nth2_step<A>(x: A, xt: List<A>, k: Nat):
            List::nth2(Cons(x, xt), Succ(k)) = List::nth2(xt, k) {
            List::nth2_unfold(Cons(x, xt), Succ(k))
        }
    "#);
}

const MERGE: &str = r#"
theorem succ_add_le(a, b: Nat): Succ(a + b) <= Succ(a) + b {
    match b { Zero => nat::Nat::le_refl(Succ(a)), Succ(k) => succ_add_le(a, k) }
}
fn merge(xs, ys: List<Nat>) -> List<Nat> decreases xs.len() + ys.len() {
    match xs {
        Nil => ys,
        Cons(x, xt) => match ys {
            Nil => Cons(x, xt),
            Cons(y, yt) => match nat::Nat::le_dec(x, y) {
                Inl(_) => Cons(x, merge(xt, Cons(y, yt))),
                Inr(_) => Cons(y, merge(Cons(x, xt), yt)),
            },
        },
    }
    on ?dec1 := succ_add_le(xt.len(), yt.len());
    on ?dec2 := nat::Nat::le_refl(Succ(xt.len()) + yt.len());
}
"#;

#[test]
fn a_match_on_a_computed_scrutinee_is_walked_through_its_own_eliminator() {
    // `merge`'s `match nat::Nat::le_dec(x, y)` reduces neither anchor, so the
    // walk spells both sides of the match out at a fresh scrutinee and
    // re-matches on it (docs/language/matching/dependent-match-compiler-design.md §8). It was
    // this file's negative control until then. The customer is the
    // `Cons`/`Cons` case at open lists, whose right-hand side is the
    // computed match with the self-calls as written.
    ok(&format!("{MERGE}{}", r#"
        theorem merge_cons(x, y: Nat, xt, yt: List<Nat>):
            merge(Cons(x, xt), Cons(y, yt)) = (match nat::Nat::le_dec(x, y) {
                Inl(_) => Cons(x, merge(xt, Cons(y, yt))),
                Inr(_) => Cons(y, merge(Cons(x, xt), yt)),
            }) { merge_unfold(Cons(x, xt), Cons(y, yt)) }
    "#));
    // Negative control: the equation is about the body, not a restatement of
    // the call, so citing it for `merge(xs, ys) = merge(xs, ys)` at open
    // lists is the kernel's refusal (the two sides are not convertible
    // there, which is why the equation exists).
    support::assert_refused(
        &mut base(),
        "m",
        &format!("{IMPORTS}{MERGE}{}", r#"
            theorem cite(xs, ys: List<Nat>): merge(xs, ys) = merge(xs, ys) { merge_unfold(xs, ys) }
        "#),
        support::Refusal::Kernel,
    );
}

const CD_LOOP: &str = r#"
record CdState { m: Nat, out: List<Nat> }
fn cd_loop(s: CdState) -> CdState decreases s.m {
    match h: Nat::leb(s.m, 0) {
        True => s,
        False => cd_loop(CdState(s.m - 1, Cons(s.m, s.out))),
    }
}
"#;

#[test]
fn a_match_with_an_equation_binding_is_walked_and_its_obligation_takes_the_equation() {
    // The `while … decreases` shape (docs/language/sequencing-surface-design.md §7.3):
    // the obligation is `omega`'s and reads the arm's equation, so the lifted
    // `cd_loop#obl_1` quantifies it, stated about `Nat::leb(s.m, 0)` and not
    // about the `__dec_scrut_N` name the body binds it to; and the walk goes
    // through the convoy.
    ok(&format!("{CD_LOOP}{}", r#"
        theorem cd_stmt(s: CdState): cd_loop(s) = (match h: Nat::leb(s.m, 0) {
            True => s,
            False => cd_loop(CdState(s.m - 1, Cons(s.m, s.out))),
        }) { cd_loop_unfold(s) }
        theorem cd_three(): cd_loop(CdState(3, Nil)) = CdState(0, [1, 2, 3]) { refl }
    "#));
    // The same equation binding on a variable scrutinee, which reduces into
    // its arms, is the convoy rule too.
    ok(r#"
        fn hv2(n: Nat) -> Nat decreases n {
            match h: n {
                Zero => 0,
                Succ(k) => Succ(hv2(k)),
            }
        }
        theorem hv2_succ(k: Nat): hv2(Succ(k)) = Succ(hv2(k)) { hv2_unfold(Succ(k)) }
    "#);
}

#[test]
fn a_computed_scrutinee_at_an_open_element_type() {
    // The other axes for the convoy rule: an **open** `A`, the computed
    // scrutinee `p(x)` under a variable refinement of `xs`, and the equation
    // transported along the arm's guard rather than cited as the whole proof.
    ok(r#"
        import bool;
        fn keep_while<A>(xs: List<A>, p: A -> Bool) -> List<A> decreases xs.len() {
            match xs {
                Nil => Nil,
                Cons(x, xt) => match h: p(x) {
                    True => Cons(x, keep_while(xt, p)),
                    False => Nil,
                },
            }
        }
        theorem kw_true<A>(x: A, xt: List<A>, p: A -> Bool, h: p(x) = True):
            keep_while(Cons(x, xt), p) = Cons(x, keep_while(xt, p)) {
            j(h,
              λ b _ => keep_while(Cons(x, xt), p) = (match e: b as λ _ => List<A> {
                  True => Cons(x, keep_while(xt, p)),
                  False => Nil,
              }),
              keep_while_unfold(Cons(x, xt), p))
        }
    "#);
}

#[test]
fn a_recursive_call_in_a_scrutinee_is_refused_but_the_function_still_checks() {
    let src = r#"
        fn nest(n: Nat) -> Nat decreases n {
            match n {
                Zero => 0,
                Succ(k) => match nest(k) { Zero => 0, Succ(_) => 1 },
            }
            on ?dec1 := nat::Nat::lt_succ_self(k);
        }
    "#;
    ok(src);
    let msg = elab_err(&format!("{src}{}", r#"
        theorem cite(n: Nat): nest(n) = nest(n) { nest_unfold(n) }
    "#));
    assert!(msg.contains("a recursive call in a `match` scrutinee"), "{msg}");
}

#[test]
fn a_plain_match_on_a_computed_scrutinee_gets_its_equation_where_an_obligation_reads_it() {
    // No `h:` written: `half`'s obligation `n - 2 < n` needs the guard, so
    // the lowering binds the arm's equation for the lifted obligation alone
    // (docs/language/matching/dependent-match-compiler-design.md §4, §13), and the companions
    // walk the convoy it leaves in `half#body`. The unfolding equation states
    // the match as written.
    ok(r#"
        import bool;
        fn half(n: Nat) -> Nat decreases n {
            match Nat::leb(n, 1) {
                True => 0,
                False => Succ(half(n - 2)),
            }
        }
        theorem half_stmt(n: Nat): half(n) = (match Nat::leb(n, 1) {
            True => 0,
            False => Succ(half(n - 2)),
        }) { half_unfold(n) }
        theorem half_seven(): half(7) = 3 { refl }
    "#);
    // An open element type, the candidate nested under an arm that recurses
    // through a second match, and the equation read by `omega` there.
    ok(r#"
        import bool;
        fn take_n<A>(n: Nat, xs: List<A>) -> List<A> decreases n {
            match Nat::leb(n, 0) {
                True => Nil,
                False => match xs {
                    Nil => Nil,
                    Cons(x, xt) => Cons(x, take_n(n - 1, xt)),
                },
            }
        }
        theorem take_n_stmt<A>(n: Nat, xs: List<A>): take_n(n, xs) = (match Nat::leb(n, 0) as λ _ => List<A> {
            True => Nil,
            False => match xs { Nil => Nil, Cons(x, xt) => Cons(x, take_n(n - 1, xt)) },
        }) { take_n_unfold(n, xs) }
        theorem take_two(): take_n<Nat>(2, [7, 8, 9]) = [7, 8] { refl }
    "#);
    // A candidate no obligation reads keeps its plain match, and unfolds the
    // same way.
    ok(r#"
        import bool;
        fn walk(n: Nat) -> Nat decreases n {
            match n {
                Zero => 0,
                Succ(k) => match Nat::leb(k, 3) { True => walk(k), False => Succ(walk(k)) },
            }
        }
        theorem walk_succ(k: Nat): walk(Succ(k)) =
            (match Nat::leb(k, 3) { True => walk(k), False => Succ(walk(k)) }) { walk_unfold(Succ(k)) }
    "#);
}

#[test]
fn an_obligation_the_guard_does_not_give_is_still_refused() {
    // Negative control: the equation is `n.leb(1) = False`, which does not
    // give `n - 1 + 1 < n`; the lifted obligation fails, the un-lifted
    // fallback fails with it, and the declaration is refused.
    let msg = elab_err(r#"
        import bool;
        fn bad(n: Nat) -> Nat decreases n {
            match Nat::leb(n, 1) {
                True => 0,
                False => Succ(bad(n - 1 + 1)),
            }
        }
    "#);
    assert!(msg.contains("omega"), "{msg}");
}

// -- back inside the walk -----------------------------------------------------

