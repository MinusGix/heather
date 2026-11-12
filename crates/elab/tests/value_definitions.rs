//! `def` and declaration-prefix generators
//! (docs/value-definitions-design.md). The library's probes
//! (`lib/_tests/std/core/value_definition_tests.hthr`,
//! `lib/_tests/std/tactic/prefix_generator_tests.hthr`,
//! `lib/_tests/std/text/regex/regex_tests.hthr`) pin what Heather can state. These
//! are what it cannot: the parser's refusals, and a value and a generated
//! group crossing a module boundary.

use heather_elab::Elaborator;

use crate::support::{self, Refusal};

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
    ("regex", include_str!("../../../lib/std/text/regex/regex.hthr")),
];

fn elaborator() -> Elaborator {
    support::semantic_test_base(MODULES)
}

const PRELUDE: &str = "import logic;\nimport bool;\nimport nat;\nimport list;\nimport option;\nimport char;\nimport string;\nimport tactic;\n";

/// A value, its inferred type and the empty-call refusal all cross a module
/// boundary: the importer reads the `def` flag off the exporter's
/// registration.
#[test]
fn values_cross_modules() {
    let mut e = elaborator();
    let consts = "import nat;\nimport list;\ndef five: Nat = 5;\ndef six = Succ(five);\ndef empty<A>: List<A> = Nil;\n";
    e.elab_module_source("consts", consts).unwrap_or_else(|err| panic!("{}", err.render(consts)));
    let client = "import nat;\nimport list;\nimport consts;\n\
                  theorem six_is(): six = 6 {}\n\
                  def none: List<Nat> = empty;\n\
                  theorem none_len(): none.len() = 0 {}\n";
    e.elab_module_source("client", client).unwrap_or_else(|err| panic!("{}", err.render(client)));
    let called = "import nat;\nimport consts;\ntheorem called(): five() = 5 {}\n";
    support::assert_refused(&mut e, "called", called, Refusal::Says("`five` is a value (a `def`), not a function"));
}

/// A generated value is used from another module like a written one: the
/// `regex` generator's `is_hex` and `is_hex::term`.
#[test]
fn generated_values_cross_modules() {
    let mut e = elaborator();
    let hex = format!("{PRELUDE}import regex;\nregex def is_hex = \"[0-9a-f]+\";\n");
    e.elab_module_source("hex", &hex).unwrap_or_else(|err| panic!("{}", err.render(&hex)));
    let client = format!(
        "{PRELUDE}import regex;\nimport hex;\n\
         theorem ok(): is_hex(\"0ff\") = True {{}}\n\
         theorem tie(s: String): is_hex(s) = is_hex::term.accepts(s) {{}}\n"
    );
    e.elab_module_source("hex_client", &client).unwrap_or_else(|err| panic!("{}", err.render(&client)));
}

fn parse_refusal(src: &str) -> String {
    match heather_syntax::parse_file(src) {
        Ok(_) => panic!("expected a parse refusal:\n{src}"),
        Err(e) => e.msg,
    }
}

/// A `def` takes no written parameters and no `requires` list, and its value
/// follows `=`; each is refused with the spelling that was meant.
#[test]
fn def_shapes_are_refused_by_the_parser() {
    let why = parse_refusal("def f(x: Nat) = x;");
    assert!(why.contains("a `def` names a value and takes no parameters"), "{why}");
    let why = parse_refusal("def f requires m: M<Nat> = 0;");
    assert!(why.contains("a `def` takes no `requires` list"), "{why}");
    let why = parse_refusal("def f: Nat { 0 }");
    assert!(why.contains("a `def`'s value follows `=`"), "{why}");
    let why = parse_refusal("meta def f: Nat = 0;");
    assert!(why.contains("`meta` marks a `fn`"), "{why}");
}

/// An annotation stops at its `=`, as a `let`'s does: an equation type is
/// written in parentheses, and the value is not swallowed into the type.
#[test]
fn a_def_annotation_stops_at_its_equals() {
    let file = heather_syntax::parse_file("def p: (1 = 1) = refl;\ndef n: Nat = 5;").expect("parses");
    assert_eq!(file.items.len(), 2);
    for item in file.items {
        let d = item.into_decl();
        assert!(d.value && d.params.is_empty(), "{}", d.name);
    }
}

/// One prefix per declaration, over a `fn`, `theorem` or `def`, at the top
/// level: stacking, an `axiom` or `meta fn` under a prefix, and a prefix in
/// a section or under `assuming` are refused by the parser.
#[test]
fn prefixes_are_refused_where_they_have_no_meaning() {
    let why = parse_refusal("a b fn f(n: Nat) -> Nat { n }");
    assert!(why.contains("one generator prefixes a declaration"), "{why}");
    let why = parse_refusal("p axiom a(): 0 = 0;");
    assert!(why.contains("not an `axiom`"), "{why}");
    let why = parse_refusal("p meta fn m(g: Ctx) -> Nat { 0 }");
    assert!(why.contains("not a `meta fn`"), "{why}");
    let why = parse_refusal("section(k: Nat) { p fn f(n: Nat) -> Nat { n } }");
    assert!(why.contains("a prefixed declaration cannot be in a section yet"), "{why}");
    let why = parse_refusal("assuming k: Nat { p fn f(n: Nat) -> Nat { n } }");
    assert!(why.contains("a prefixed declaration cannot yet inherit an `assuming` telescope"), "{why}");
}

/// A `record` takes a prefix, with arguments or without; the other type
/// declarations are refused as what they are, and two prefixes as two.
#[test]
fn a_prefix_before_a_record_parses() {
    let file = heather_syntax::parse_file("laid record P { a: Nat }").expect("parses");
    let [heather_syntax::Item::PrefixedRecord(p)] = &file.items[..] else { panic!("one prefixed record") };
    assert!(matches!(&p.generator.kind, heather_syntax::ExprKind::Var(n) if n == "laid"));
    assert!(p.record.is_record);
    assert_eq!(p.record.name, "P");
    let file = heather_syntax::parse_file("laid(endian := Big) record P { a: Nat }\nfn f(n: Nat) -> Nat { n }").expect("parses");
    let [heather_syntax::Item::PrefixedRecord(p), heather_syntax::Item::Decl(_)] = &file.items[..] else { panic!("a prefixed record, then a fn") };
    let heather_syntax::ExprKind::App { args, named, .. } = &p.generator.kind else { panic!("a call") };
    assert_eq!((args.len(), named.len()), (0, 1));
    let why = parse_refusal("p inductive T { A, B }");
    assert!(why.contains("a generator prefixes a `fn`, a `theorem`, a `def` or a `record`, not an `inductive`"), "{why}");
    let why = parse_refusal("p(1) class C<A> { f: A }");
    assert!(why.contains("not a `class`"), "{why}");
    let why = parse_refusal("a b record P { a: Nat }");
    assert!(why.contains("one generator prefixes a declaration"), "{why}");
    let why = parse_refusal("section(k: Nat) { p record P { a: Nat } }");
    assert!(why.contains("a prefixed declaration cannot be in a section yet"), "{why}");
}

/// A prefix's arguments are written after its name, as a call's are.
#[test]
fn a_prefix_with_arguments_parses_as_a_call() {
    let file = heather_syntax::parse_file("runtime(owned, budget := 3) fn f(n: Nat) -> Nat { n }").expect("parses");
    let [heather_syntax::Item::Prefixed(p)] = &file.items[..] else { panic!("one prefixed item") };
    let heather_syntax::ExprKind::App { args, named, .. } = &p.generator.kind else { panic!("a call") };
    assert_eq!((args.len(), named.len()), (1, 1));
    assert_eq!(p.decl.name, "f");
}
