//! Modules: imports, per-file namespaces, and the §4 name regime
//! (docs/modules-design.md, issues/modules.md).
//!
//! The claim under test is not "a second file can be read" — it is that the
//! name layer is **honest**: a name that resolves uniquely works unqualified,
//! a name declared in two visible modules is an error *at the use* naming
//! both origins, a file's own declaration beats an unlisted import, and
//! import order decides nothing. Every positive here has the negative that
//! distinguishes it from a first-match `open`, because a first-match system
//! passes every positive in this file.
//!
//! The loader (search paths, cycles, the DAG) is the CLI's; this file feeds
//! the modules to one elaborator directly, in the order a loader would.

use heather_elab::{ElabError, Elaborator};
use heather_syntax::parse_file;

/// Elaborate a list of modules in order, into one accumulator — the shape of
/// one `heather check` run.
fn run(mods: &[(&str, &str)]) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in mods {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
        }
    }
    Ok(e)
}

fn ok(mods: &[(&str, &str)]) -> Elaborator {
    run(mods).unwrap_or_else(|e| panic!("expected these modules to check, got: {e}"))
}

fn bad(mods: &[(&str, &str)]) -> String {
    match run(mods) {
        Err(e) => e,
        Ok(_) => panic!("expected a refusal, but the modules checked"),
    }
}

// ---------------------------------------------------------------------------
// Phase 1: the syntax.

#[test]
fn import_forms_parse() {
    let f = parse_file("import nat;\nimport option::{Option, map};\nfn f() -> Nat { 0 }")
        .expect("parses");
    assert_eq!(f.items.len(), 3);
}

#[test]
fn an_import_after_a_declaration_is_a_parse_error() {
    let e = parse_file("fn f() -> Nat { 0 }\nimport nat;").expect_err("must not parse");
    assert!(e.msg.contains("before the first declaration"), "{}", e.msg);
}

#[test]
fn there_is_no_glob_import() {
    let e = parse_file("import nat::{*};").expect_err("must not parse");
    assert!(e.msg.contains("no glob import"), "{}", e.msg);
}

#[test]
fn a_qualified_name_cannot_be_a_binder() {
    // The name regime's other half: `m::n` is a *reference*, so nothing is
    // ever declared or bound under one.
    let e = parse_file("fn f(nat::x: Nat) -> Nat { 0 }").expect_err("must not parse");
    assert!(e.msg.contains("qualified name"), "{}", e.msg);
}

#[test]
fn qualified_names_parse_in_both_positions() {
    parse_file("fn f(o: option::Option<Nat>) -> Nat { nat::add(1, 2) }").expect("parses");
}

// ---------------------------------------------------------------------------
// Phase 2: the regime.

const A: &str = "fn f() -> Nat { 1 }
fn only_in_a() -> Nat { 7 }";
const B: &str = "fn f() -> Nat { 2 }";

#[test]
fn an_import_brings_names_in_unqualified() {
    ok(&[("a", A), ("user", "import a;\ntheorem t(): only_in_a() = 7 { refl }")]);
}

#[test]
fn without_the_import_the_name_is_not_there() {
    // The negative that makes the positive above mean something: visibility
    // is the import, not the accumulator.
    let e = bad(&[("a", A), ("user", "theorem t(): only_in_a() = 7 { refl }")]);
    assert!(e.contains("only_in_a"), "{e}");
}

#[test]
fn a_qualified_name_resolves_through_the_module() {
    ok(&[("a", A), ("user", "import a;\ntheorem t(): a::only_in_a() = 7 { refl }")]);
}

#[test]
fn qualifying_by_a_module_that_is_not_imported_is_an_error() {
    let e = bad(&[("a", A), ("user", "theorem t(): a::only_in_a() = 7 { refl }")]);
    assert!(e.contains("neither an imported module nor a type"), "{e}");
}

#[test]
fn a_name_declared_in_two_imports_is_ambiguous_at_use() {
    // Not shadowed by import order — an error naming BOTH origins. This is
    // the one test a first-match `open` system cannot pass.
    let e = bad(&[("a", A), ("b", B), ("user", "import a;\nimport b;\ntheorem t(): f() = 1 { refl }")]);
    assert!(e.contains("ambiguous"), "{e}");
    assert!(e.contains("`a`") && e.contains("`b`"), "both origins must be named: {e}");
}

#[test]
fn ambiguity_is_fixed_by_qualifying() {
    ok(&[
        ("a", A),
        ("b", B),
        ("user", "import a;\nimport b;\ntheorem t(): a::f() = 1 { refl }\ntheorem u(): b::f() = 2 { refl }"),
    ]);
}

#[test]
fn ambiguity_is_fixed_by_listing_it_in_the_import() {
    // A listed name is a standing disambiguation: it binds unqualified and
    // beats the collision, and it beats it in whichever order the imports are
    // written.
    ok(&[
        ("a", A),
        ("b", B),
        ("user", "import a::{f};\nimport b;\ntheorem t(): f() = 1 { refl }"),
    ]);
    ok(&[
        ("a", A),
        ("b", B),
        ("user", "import b;\nimport a::{f};\ntheorem t(): f() = 1 { refl }"),
    ]);
}

#[test]
fn two_imports_cannot_list_one_name() {
    let e = bad(&[
        ("a", A),
        ("b", B),
        ("user", "import a::{f};\nimport b::{f};\nfn g() -> Nat { f() }"),
    ]);
    assert!(e.contains("listed by two imports"), "{e}");
}

#[test]
fn listing_a_name_the_module_does_not_declare_is_an_error() {
    let e = bad(&[("a", A), ("user", "import a::{nope};")]);
    assert!(e.contains("declares no `nope`"), "{e}");
}

#[test]
fn a_local_declaration_beats_an_unlisted_import() {
    // The one precedence in the system: the file you are reading beats the
    // file you are not. `f` is `1` in `a` and `3` here, and `refl` decides
    // which one the body meant.
    ok(&[("a", A), ("user", "import a;\nfn f() -> Nat { 3 }\ntheorem t(): f() = 3 { refl }")]);
}

#[test]
fn a_local_declaration_does_not_beat_a_listed_import() {
    // …and the negative: asking for `a`'s `f` by name and then declaring one
    // is a contradiction, not a precedence.
    let e = bad(&[("a", A), ("user", "import a::{f};\nfn f() -> Nat { 3 }")]);
    assert!(e.contains("listed"), "{e}");
}

#[test]
fn the_local_declaration_is_still_reachable_from_the_other_side() {
    // Locals winning must not make the import unreachable: qualification is
    // the escape hatch, and it is what makes "locals win" a *naming* rule
    // rather than a hiding one.
    ok(&[("a", A), ("user", "import a;\nfn f() -> Nat { 3 }\ntheorem t(): a::f() = 1 { refl }")]);
}

#[test]
fn a_module_cannot_import_itself() {
    let e = bad(&[("a", "import a;")]);
    assert!(e.contains("cannot import itself"), "{e}");
}

#[test]
fn importing_a_module_that_is_not_in_the_run_is_an_error() {
    let e = bad(&[("user", "import nowhere;")]);
    assert!(e.contains("unknown module"), "{e}");
}

#[test]
fn the_prelude_is_imported_implicitly_and_locals_beat_it() {
    // `sym` is the prelude's. A module may declare its own without an error,
    // because the prelude is an ordinary unlisted import.
    ok(&[("user", "theorem t({a: Nat}, {b: Nat}, p: a = b): b = a { sym(p) }")]);
    ok(&[("user", "fn sym(n: Nat) -> Nat { n }\ntheorem t(): sym(3) = 3 { refl }")]);
}

// ---------------------------------------------------------------------------
// Constructors: qualified by TYPE, in both modes.

const OPT: &str = "inductive Option<A> { None, Some(v: A) }
fn unwrap_or<A>(o: Option<A>, d: A) -> A { match o { None => d, Some(v) => v } }";

#[test]
fn a_qualified_constructor_checks_and_synthesizes() {
    // Checking position: the expected type supplies the instantiation.
    // Synthesis position: `Option::Some(3)` is inferred from its field, and
    // the `let` has no annotation to lean on.
    ok(&[
        ("opt", OPT),
        (
            "user",
            "import opt;
             fn none_nat() -> Option<Nat> { Option::None }
             fn some_three() -> Nat { { let x = Option::Some(3); unwrap_or(x, 0) } }
             theorem t(): some_three() = 3 { refl }
             theorem u(): unwrap_or(none_nat(), 9) = 9 { refl }",
        ),
    ]);
}

#[test]
fn a_qualified_constructor_of_the_wrong_type_is_an_error() {
    let e = bad(&[
        ("opt", OPT),
        ("user", "import opt;\nfn f() -> Option<Nat> { Option::Nope }"),
    ]);
    assert!(e.contains("Option::Nope") || e.contains("Nope"), "{e}");
}

#[test]
fn a_constructor_declared_in_two_modules_is_ambiguous_until_qualified() {
    const OPT2: &str = "inductive Maybe<A> { None, Just(v: A) }";
    let mods = |body: &str| {
        [
            ("opt".to_string(), OPT.to_string()),
            ("opt2".to_string(), OPT2.to_string()),
            (
                "user".to_string(),
                format!("import opt;\nimport opt2;\nfn f() -> Option<Nat> {{ {body} }}"),
            ),
        ]
    };
    let m = mods("None");
    let borrowed: Vec<(&str, &str)> =
        m.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect();
    let e = bad(&borrowed);
    assert!(e.contains("ambiguous"), "{e}");
    assert!(e.contains("`opt`") && e.contains("`opt2`"), "{e}");

    // …and the type qualifies it, which is the whole v1 answer for
    // constructors: by TYPE name, not by module.
    let m = mods("Option::None");
    let borrowed: Vec<(&str, &str)> =
        m.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect();
    ok(&borrowed);
}

// ---------------------------------------------------------------------------
// Cross-module inductives: the generated artifacts (μ_D and friends) are
// keyed on nominal tags, so an import must not disturb them.
//
// The axes of docs/testing-generated-terms.md, where they apply: the element
// type is **open** (`A`, not `Nat`), there is a *neutral* scrutinee as well as
// a literal one, and the neutral case is a **proof** — a computing test would
// never compare the lowering's annotations against a goal.

const LIST: &str = "inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
fn append<A>(xs: List<A>, ys: List<A>) -> List<A> {
    match xs { Nil => ys, Cons(h, t) => Cons(h, append(t, ys)) }
}";

#[test]
fn a_recursive_inductive_is_matched_and_proved_about_across_a_module_boundary() {
    ok(&[
        ("l", LIST),
        (
            "user",
            // Literal scrutinee: computes.
            "import l;
             fn one() -> List<Nat> { Cons(1, Nil) }
             theorem lit(): append(one(), Nil) = one() { refl }
             // Neutral scrutinee at an OPEN element type, in a proof: nothing
             // reduces, so the lowering's annotations carry it.
             theorem cong_cons<A>(h: A, {t1: List<A>}, {t2: List<A>}, p: t1 = t2):
                 Cons(h, t1) = Cons(h, t2)
             { j(p, λ y q => Cons(h, t1) = Cons(h, y), refl) }
             theorem append_nil<A>(xs: List<A>): append(xs, Nil) = xs {
                 match xs {
                     Nil => refl,
                     Cons(h, t) => cong_cons(h, append_nil(t)),
                 }
             }",
        ),
    ]);
}

#[test]
fn an_imported_inductive_is_still_a_nominal_type() {
    // The negative control for the round's assumption (issues/modules.md,
    // §10.6 of issues/indexed-families.md): qualification changes spelling,
    // never identity. Two *structurally identical* declarations in two
    // modules are two types — nominal tags are per declaration — so one does
    // not check at the other, and imports have not quietly made them one.
    let e = bad(&[
        ("s1", "record Box { v: Nat }"),
        ("s2", "record Crate { v: Nat }"),
        ("user", "import s1;\nimport s2;\nfn f() -> Box { Crate { v: 1 } }"),
    ]);
    assert!(!e.is_empty(), "{e}");

    // …and each is buildable at its own type, so the refusal above is about
    // identity and not about either declaration being unusable.
    ok(&[
        ("s1", "record Box { v: Nat }"),
        ("s2", "record Crate { v: Nat }"),
        (
            "user",
            "import s1;\nimport s2;
             fn f() -> Box { Box { v: 1 } }
             fn g() -> Crate { Crate { v: 1 } }",
        ),
    ]);
}

#[test]
fn stored_field_types_keep_their_declaration_module_scope() {
    // `a::Box` meant `base::Item` when it was declared. Importing an
    // unrelated second `Item` must not make the stored field type ambiguous
    // when `.value` is lowered in `user`.
    ok(&[
        ("base", "record Item { n: Nat }"),
        ("a", "import base;\nrecord Box { value: Item }"),
        ("b", "record Item { flag: Nat }"),
        (
            "user",
            "import a;\nimport base;\nimport b;\nfn read(w: a::Box) -> Nat { w.value.n }",
        ),
    ]);

    // The recursive form is the original motivating case. Match-arm
    // lowering reads `a`'s stored `tail: List<A>` while both `List`s are
    // visible in `user`; the self-reference must still mean `a::List`.
    ok(&[
        ("a", "inductive List<A> { Nil, Cons(head: A, tail: List<A>) }"),
        ("b", "inductive List<A> { Empty, Push(head: A, tail: List<A>) }"),
        (
            "user",
            "import a;\nimport b;\nfn step(n: Nat) -> Nat { Succ(n) }\n\
             fn len<A>(xs: a::List<A>) -> Nat {\n\
                 match xs { Nil => 0, Cons(h, t) => step(len(t)) }\n}",
        ),
    ]);
}

#[test]
fn stored_value_parameter_types_keep_their_declaration_module_scope() {
    ok(&[
        ("base", "record Item { n: Nat }"),
        ("a", "import base;\nrecord Holds(x: Item) { proof: x = x }"),
        ("b", "record Item { flag: Nat }"),
        (
            "user",
            "import a;\nimport base;\nimport b;\n\
             fn make() -> base::Item { base::Item { n: 0 } }\n\
             fn hold() -> a::Holds(make()) { a::Holds { proof: refl } }",
        ),
    ]);
}

#[test]
fn stored_forded_indices_keep_their_declaration_module_scope() {
    // Route 2b retains each constructor's result-index expression. Building
    // the family in `user` must resolve `bump` through `a`'s import, not
    // against the two `bump`s visible at the use site.
    ok(&[
        ("ops", "fn bump(n: Nat) -> Nat { Succ(n) }"),
        (
            "a",
            "import ops;\ninductive F : (n: Nat) -> Type {\n\
                 Z : F(0),\nS(n: Nat, t: F(n)) : F(bump(n)),\n}",
        ),
        ("b", "fn bump(n: Nat) -> Nat { n }"),
        (
            "user",
            "import a;\nimport ops;\nimport b;\nfn zero() -> a::F(0) { Z }",
        ),
    ]);
}

// ---------------------------------------------------------------------------
// `meta_slots` stays global: one template per slot across the whole program,
// and a second claim through an import is an error that names both modules.

const TEMPLATE: &str = "meta fn map_code(g: Ctx) for vec.map
    -> Code(g |- (A: Type<0>) -> (B: Type<0>) -> (f: A -> B) -> (k: Nat) -> (v: [A; k]) -> [B; k])
{
    code {
        fun (A: Type<0>) => fun (B: Type<0>) => fun (f: A -> B) => fun (k: Nat) =>
            match k as λ z => [A; z] -> [B; z] {
                Zero => fun (v: [A; 0]) => [],
                Succ(zk, ih) => fun (v: [A; Succ(zk)]) =>
                    cons(f(head(v)), ih(tail(v))),
            }
    }
}";

#[test]
fn a_template_declared_in_one_module_dispatches_in_another() {
    let e = ok(&[
        ("t", TEMPLATE),
        (
            "user",
            "import t;
             fn double(n: Nat) -> Nat { Succ(Succ(n)) }
             fn go(v: [Nat; 2]) -> [Nat; 2] { v.map(double) }",
        ),
    ]);
    let _ = e;
}

#[test]
fn two_modules_cannot_claim_one_slot() {
    let e = bad(&[("t", TEMPLATE), ("t2", TEMPLATE)]);
    assert!(e.contains("already elaborated by"), "{e}");
    assert!(e.contains("module `t`"), "the error must name the other module: {e}");
}

#[test]
fn a_match_arm_resolves_its_constructors_through_the_scrutinee() {
    // The free win of docs/modules-design.md §8: an arm never consults the
    // global constructor table, so two visible `None`s do not make an arm
    // ambiguous — the scrutinee's type already said which constructors exist.
    // The qualified spelling is accepted too, and only for the right type.
    ok(&[
        ("opt", OPT),
        ("opt2", "inductive Maybe<A> { None, Just(v: A) }"),
        (
            "user",
            "import opt;
             import opt2;
             fn get(o: Option<Nat>) -> Nat { match o { None => 0, Some(v) => v } }
             fn get2(o: Option<Nat>) -> Nat {
                 match o { Option::None => 0, Option::Some(v) => v }
             }
             theorem t(): get(Option::Some(4)) = 4 { refl }
             theorem u(): get2(Option::None) = 0 { refl }",
        ),
    ]);
}

#[test]
fn an_arm_qualified_by_the_wrong_type_is_an_error() {
    let e = bad(&[
        ("opt", OPT),
        ("opt2", "inductive Maybe<A> { None, Just(v: A) }"),
        (
            "user",
            "import opt;\nimport opt2;
             fn get(o: Option<Nat>) -> Nat { match o { Maybe::None => 0, Some(v) => v } }",
        ),
    ]);
    assert!(e.contains("not a constructor of `Option`"), "{e}");
}
