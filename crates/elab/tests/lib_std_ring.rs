//! `lib/std/tactic/ring.hthr` and the `ring` tactic — commutative-ring
//! normalization by reflection (`issues/ring-normalization.md`,
//! `docs/ring-normalization-design.md`).
//!
//!  1. identities at `Int` and `Nat`, over neutral atoms and closed
//!     numerals, in checking positions (`let`, a `calc` step, a match arm,
//!     under a binder that shadows a hypothesis's variable);
//!  2. `ring(h, …)`: hypotheses combined with polynomial multipliers the
//!     tactic finds, a chain of substitutions among them, a defined
//!     proposition as goal and as hypothesis;
//!  3. composition: a `ring` fact handed to `omega`;
//!  4. negative controls: a non-identity, a combination that does not exist,
//!     a goal that is not an equation, a carrier mismatch, a missing import,
//!     and a local named `ring` that shadows the tactic.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
    ("ring", include_str!("../../../lib/std/tactic/ring.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn check(name: &str, src: &str) {
    let mut e = base();
    if let Err(err) = e.elab_module_source(name, src) {
        panic!("{}", err.render(src));
    }
}

fn refused(name: &str, src: &str, needle: &str) {
    let mut e = base();
    match e.elab_module_source(name, src) {
        Ok(_) => panic!("{name} should be refused"),
        Err(err) => {
            let rendered = err.render(src);
            assert!(rendered.contains(needle), "{name}: expected `{needle}` in\n{rendered}");
        }
    }
}

const IMPORTS: &str = "import logic; import nat; import int; import ring;\n";

#[test]
fn identities_at_int() {
    check(
        "ring_int",
        &format!(
            "{IMPORTS}
            theorem squares(a, b: Int): (a + b) * (a - b) = a * a - b * b {{ ring }}
            theorem negation(a, b: Int): -(a - b) * -b = a * b + -(b * b) {{ ring }}
            theorem seven(a, c, r, p, q: Int):
                (a * (c * r)) * ((p * q) * (p * r)) = ((a * c) * (p * r)) * (p * (q * r)) {{ ring }}
            // Closed numerals fold; a neutral factor beside them stays an atom.
            theorem literal(): OfNat(2) * OfNat(3) - OfNat(7) = NegSucc(0) {{ ring }}
            theorem scaled(a: Int): (a + OfNat(2)) * OfNat(3) = OfNat(3) * a + OfNat(6) {{ ring }}
            // Atoms are whatever is not ring syntax, here applications that
            // mention a function parameter.
            theorem applied(f: Int → Int, x, y: Int): (f(x) + f(y)) * f(x) = f(x) * f(x) + f(y) * f(x) {{ ring }}
            "
        ),
    );
}

#[test]
fn identities_at_nat() {
    check(
        "ring_nat",
        &format!(
            "{IMPORTS}
            theorem square(x, y: Nat): (x + y) * (x + y) = x * x + 2 * (x * y) + y * y {{ ring }}
            // `Succ(x)` is read as `x + 1`, and computes back to it.
            theorem succ(x: Nat): Succ(x) * Succ(x) = x * x + 2 * x + 1 {{ ring }}
            theorem closed(): 3 * 4 + 1 = 13 {{ ring }}
            "
        ),
    );
}

#[test]
fn ring_in_checking_positions() {
    check(
        "ring_positions",
        &format!(
            "import list; {IMPORTS}
            theorem by_let(a, b: Int): a * b * a = a * a * b {{
                let swapped: (a * b * a = b * (a * a)) = ring;
                trans(swapped, b.mul_comm(a * a))
            }}
            theorem by_calc(a, b: Int): (a + b) * (a + b) = a * a + (a * b + a * b) + b * b {{
                calc {{
                    (a + b) * (a + b)
                        = a * (a + b) + b * (a + b) := ring,
                        = a * a + (a * b + a * b) + b * b := ring,
                }}
            }}
            // In a match arm the atoms are the pattern's variables.
            theorem by_arm(xs: List<Int>): List<Int> → OfNat(0) = OfNat(0) {{
                match xs {{
                    Nil => λ ys => refl,
                    Cons(h, t) => λ ys => {{
                        let fact: (h * h - h * h = OfNat(0)) = ring;
                        refl
                    }},
                }}
            }}
            // The binder `x` shadows the parameter `x` the hypothesis is
            // about; the certificate still names both.
            theorem shadowed(x, y: Int, h: x = y): (w: Int) → w * x = w * y {{
                λ x => ring(h)
            }}
            "
        ),
    );
}

#[test]
fn hypotheses_with_found_multipliers() {
    check(
        "ring_hypotheses",
        &format!(
            "{IMPORTS}
            theorem substituted(a, b, c: Int, h: a = b + c): a * a = b * b + OfNat(2) * b * c + c * c {{ ring(h) }}
            // Cross-multiplication: each hypothesis is scaled by the other
            // side's factors.
            theorem crossed(a, p, q, a2, p2, q2: Int, h: a * p2 = a2 * p):
                (a * q) * (p2 * q2) = (a2 * q2) * (p * q) {{ ring(h) }}
            // A chain: `d` is `p·e`, and `e` is `q·r`; one link per round.
            theorem chained(s, d, e, p, q, r: Int, h1: d = p * e, h2: e = q * r): s * d = s * p * q * r {{
                ring(h1, h2)
            }}
            // A hypothesis that is not needed is not used.
            theorem unused(a, b: Int, h: a = b): a * b = b * a {{ ring(h) }}
            // A hypothesis may be any proof, not only a name.
            theorem by_lemma(a, b, c: Int): a * (b * c) = c * (b * a) {{ ring(a.mul_comm(b)) }}
            theorem at_nat(x, y: Nat, h: x = y + 1): x * x = y * y + 2 * y + 1 {{ ring(h) }}
            "
        ),
    );
}

#[test]
fn defined_propositions_are_unfolded() {
    check(
        "ring_defined",
        &format!(
            "{IMPORTS}
            fn Square(a, b: Int) → Type {{ a * a = b }}
            theorem goal(x, y: Int): Square(x + y, x * x + OfNat(2) * x * y + y * y) {{ ring }}
            theorem hypothesis(x, y: Int, h: Square(x, y)): x * x * x = y * x {{ ring(h) }}
            "
        ),
    );
}

#[test]
fn ring_facts_compose_with_omega() {
    check(
        "ring_omega",
        "import logic; import nat; import int; import omega; import ring;
        theorem mixed(a, b, c: Int, h: a * b * c <= OfNat(5)): c * (b * a) + OfNat(1) <= OfNat(6) {
            let same: (c * (b * a) = a * b * c) = ring;
            omega
        }",
    );
}

#[test]
fn a_non_identity_is_refused_with_its_residual() {
    refused(
        "ring_not_identity",
        &format!("{IMPORTS} theorem bad(a, b: Int): (a + b) * (a + b) = a * a + b * b {{ ring }}"),
        "differ by `2 * a * b`",
    );
    refused(
        "ring_nat_not_identity",
        &format!("{IMPORTS} theorem bad(x: Nat): Succ(x) * x = x * x {{ ring }}"),
        "differ by `x`",
    );
}

#[test]
fn a_missing_combination_is_refused() {
    refused(
        "ring_no_combination",
        &format!("{IMPORTS} theorem bad(a, b: Int, h: a = b): a * a = b {{ ring(h) }}"),
        "no combination",
    );
    // Hypotheses are equations: a proof of something else is named.
    refused(
        "ring_hypothesis_not_equation",
        &format!("{IMPORTS} theorem bad(a, b: Int, h: a <= b): a = b {{ ring(h) }}"),
        "`ring` combines equations; `h` is",
    );
    refused(
        "ring_carrier_mismatch",
        &format!("{IMPORTS} theorem bad(a: Int, x, y: Nat, h: x = y): a = a {{ ring(h) }}"),
        "is an equation at `Nat`",
    );
}

#[test]
fn only_equations_at_int_or_nat() {
    refused(
        "ring_order_goal",
        &format!("{IMPORTS} theorem bad(a: Int): a <= a {{ ring }}"),
        "`ring` proves an equation at `Int` or `Nat`",
    );
    refused(
        "ring_bool_goal",
        &format!("import bool; {IMPORTS} theorem bad(b: Bool): b = b {{ ring }}"),
        "`ring` proves an equation at `Int` or `Nat`",
    );
}

#[test]
fn ring_needs_its_library_and_yields_to_a_local() {
    refused(
        "ring_no_import",
        "import logic; import nat; import int; theorem bad(a: Int): a * a = a * a { ring }",
        "add `import ring;`",
    );
    // A local named `ring` is the local.
    check(
        "ring_shadowed",
        &format!("{IMPORTS} theorem ok(a: Int, ring: a = a): a = a {{ ring }}"),
    );
}
