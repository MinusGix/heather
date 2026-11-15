//! Round 4 of `docs/metaprogramming/host-elaboration-interface-design.md` (§19): `generate
//! g(args);` runs a `Tac<List<Decl>>` at a module's top level and publishes
//! the declarations it builds. The library's probes
//! (`lib/_tests/std/tactic/derive_tests.hthr`) pin what Heather can state:
//! the generated lemmas at their statements and the refusals of malformed
//! output. These are what it cannot: generated declarations crossing a module
//! boundary, the parser's refusals, and forged references.

use std::sync::OnceLock;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("char", include_str!("../../../lib/std/text/char.hthr")),
    ("string", include_str!("../../../lib/std/text/string.hthr")),
    ("tactic", include_str!("../../../lib/std/tactic/tactic.hthr")),
    ("derive", include_str!("../../../lib/std/tactic/derive.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn elaborator() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn message(error: ElabError) -> String {
    match error {
        ElabError::Elab { msg, .. } => msg,
        other => other.to_string(),
    }
}

const PRELUDE: &str = "import logic;\nimport bool;\nimport nat;\nimport list;\nimport char;\nimport string;\nimport tactic;\nimport derive;\n";

/// A generated lemma is an ordinary declaration of its module: another
/// module imports it like any other, at its statement.
#[test]
fn generated_declarations_cross_modules() {
    let mut e = elaborator();
    let tm = format!("{PRELUDE}inductive Tm {{ Var(n: Nat), App(f: Tm, a: Tm) }}\ngenerate congruences(Tm);\n");
    e.elab_module_source("terms", &tm).unwrap_or_else(|err| panic!("{}", err.render(&tm)));
    let client = "import logic;
         import nat;
         import terms;
         theorem app(f, g, a, b: Tm, hf: f = g, ha: a = b): Tm::App(f, a) = Tm::App(g, b) { Tm::cong_App(hf, ha) }
         theorem var(n: Nat): Tm::Var(n + 0) = Tm::Var(n) { Tm::cong_Var(refl) }";
    e.elab_source(client).unwrap_or_else(|err| panic!("{}", err.render(client)));
}

/// A generator runs at the module's empty context; a section's or an
/// `assuming` block's head would be a context it has no way to see, so the
/// parser refuses both rather than run it outside them.
#[test]
fn generate_stays_at_top_level() {
    let in_section = format!("{PRELUDE}inductive Tm {{ Var(n: Nat) }}\nsection(n: Nat) {{ generate congruences(Tm); }}\n");
    let why = message(elaborator().elab_source(&in_section).expect_err("a generate in a section"));
    assert!(why.contains("a `generate` cannot be in a section yet"), "{why}");
    let assuming = format!("{PRELUDE}inductive Tm {{ Var(n: Nat) }}\nassuming n: Nat {{ generate congruences(Tm); }}\n");
    let why = message(elaborator().elab_source(&assuming).expect_err("a generate under assuming"));
    assert!(why.contains("a `generate` cannot yet inherit an `assuming` telescope"), "{why}");
}

/// Without the protocol there is nothing to run.
#[test]
fn generate_needs_the_protocol() {
    let src = "fn g(n: Nat) → Nat { n }\ngenerate g(3);\n";
    let why = message(elaborator().elab_source(src).expect_err("no protocol"));
    assert!(why.contains("add `import tactic;`"), "{why}");
}

/// Parameters, statements and bodies refer to locals the run introduced;
/// a reference to one it never issued is refused, not trusted.
#[test]
fn forged_parameters_are_refused() {
    let src = format!(
        "{PRELUDE}inductive Tm {{ Var(n: Nat) }}
         fn forged(t: Expr) → Tac<List<Decl>> {{
             Pure([Decl(AsFunction, \"f\", [Param(LocalRef(7), False)], t, Local(LocalRef(7)))])
         }}
         generate forged(Tm);"
    );
    let why = message(elaborator().elab_source(&src).expect_err("a forged parameter"));
    assert!(why.contains("`generate forged(…)`") && why.contains("`f`"), "{why}");
}

/// A declaration's name must be one a source declaration could have.
#[test]
fn names_are_checked() {
    let src = format!(
        "{PRELUDE}inductive Tm {{ Var(n: Nat) }}
         fn badly_named(t: Expr) → Tac<List<Decl>> {{ Pure([Decl(AsFunction, \"no good\", [], t, t)]) }}
         generate badly_named(Tm);"
    );
    let why = message(elaborator().elab_source(&src).expect_err("a bad name"));
    assert!(why.contains("`no good` is not a declaration's name"), "{why}");
}
