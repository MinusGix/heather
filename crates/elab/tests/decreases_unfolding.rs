//! Acceptance for issues/decreases-unfolding-equations.md
//! (docs/decreases-unfolding-design.md): the generated unfolding equation
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

use std::cell::OnceCell;
use std::sync::Mutex;

use heather_elab::{ElabError, Elaborator, SemanticImage};

mod support;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/omega.hthr");

/// The same prefix, in the same order, as `semantic_omega_warmup.rs`, so the
/// on-disk image keys this file reads are the ones the warmup wrote.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("algebra", ALGEBRA),
    ("int", INT),
    ("omega", OMEGA),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn load_image() -> SemanticImage {
    // Two libtest workers otherwise miss the cold image store together and
    // each spends the process's CPU rail checking the same arithmetic
    // prefix. The first worker fills it; the second waits and replays it.
    let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    support::semantic_test_base(MODULES).semantic_image()
}

/// A fresh elaborator over the checked library prefix. The semantic image is
/// the committed-state boundary: every call forks its own attempt, report and
/// gate state, so a test's module never leaks into the next one's base.
fn base() -> Elaborator {
    BASE.with(|base| base.get_or_init(load_image).elaborator())
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
    on ?dec1 := nat::lt_succ_self(k);
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
                Succ(k) => gcd(Succ(k), nat::mod(a, Succ(k))),
            }
            on ?dec1 := nat::mod_lt(a, Succ(k), trivial);
        }

        theorem gcd_step(a, k: Nat): gcd(a, Succ(k)) = gcd(Succ(k), nat::mod(a, Succ(k))) {
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
            on ?dec1 := nat::le_succ_r(Succ(yt.len()), Succ(yt.len()),
                                       nat::le_refl(Succ(yt.len())));
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
        theorem le_self(n: Nat): nat::Le(n, n) decreases n {
            match n { Zero => nat::le_refl(0), Succ(k) => nat::le_refl(Succ(k)) }
        }
        theorem cite(n: Nat): nat::Le(n, n) { le_self_unfold(n) }
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
            on ?dec1 := nat::lt_succ_self(k);
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
            on ?dec1 := nat::lt_succ_self(k);
        }
    "#);
}

#[test]
fn a_match_on_a_computed_scrutinee_is_outside_the_walk() {
    // `merge`'s `match nat::le_dec(x, y)`: the anchors do not reduce past a
    // stuck scrutinee, and equating the arms would need the body rendered
    // into the motive. Amends §3, which had claimed `merge`.
    let msg = elab_err(
        r#"
        theorem succ_add_le(a, b: Nat): Succ(a + b) <= Succ(a) + b {
            match b { Zero => nat::le_refl(Succ(a)), Succ(k) => succ_add_le(a, k) }
        }
        fn merge(xs, ys: List<Nat>) -> List<Nat> decreases xs.len() + ys.len() {
            match xs {
                Nil => ys,
                Cons(x, xt) => match ys {
                    Nil => Cons(x, xt),
                    Cons(y, yt) => match nat::le_dec(x, y) {
                        Inl(_) => Cons(x, merge(xt, Cons(y, yt))),
                        Inr(_) => Cons(y, merge(Cons(x, xt), yt)),
                    },
                },
            }
            on ?dec1 := succ_add_le(xt.len(), yt.len());
            on ?dec2 := nat::le_refl(Succ(xt.len()) + yt.len());
        }
        theorem cite(xs, ys: List<Nat>): merge(xs, ys) = merge(xs, ys) { merge_unfold(xs, ys) }
        "#,
    );
    assert!(msg.contains("scrutinee is not a variable"), "{msg}");
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
