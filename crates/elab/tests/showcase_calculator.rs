//! The realized calculator and its token parser are checked artifacts, not
//! documentation snippets that can drift away from the language.
use heather_elab::Elaborator;

mod support;

fn base() -> Elaborator {
    support::semantic_test_base(&[
        ("logic", include_str!("../../../lib/std/logic.hthr")),
        ("bool", include_str!("../../../lib/std/bool.hthr")),
        ("nat", include_str!("../../../lib/std/nat.hthr")),
        ("option", include_str!("../../../lib/std/option.hthr")),
        ("pair", include_str!("../../../lib/std/pair.hthr")),
        ("list", include_str!("../../../lib/std/list.hthr")),
        ("algebra", include_str!("../../../lib/std/algebra.hthr")),
        ("int", include_str!("../../../lib/std/int.hthr")),
        ("omega", include_str!("../../../lib/std/omega.hthr")),
        ("result", include_str!("../../../lib/std/result.hthr")),
    ])
}

#[test]
fn calculator_parser_and_compiler_check_and_reject_wrong_answers() {
    let mut e = base();
    for (name, src) in [
        ("calc", include_str!("../../../docs/showcase/calc.hthr")),
        ("calc_parser", include_str!("../../../docs/showcase/calc_parser.hthr")),
    ] {
        e.elab_module_source(name, src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    }
    // Each control starts from the same checked modules. A failed attempt
    // cannot influence the next one. These must fail at their proof body.
    let image = e.semantic_image();
    for statement in [
        "parse([TNum(2), TPlusSym, TNum(3), TStarSym, TNum(4)]) = Ok(Times(Plus(Lit(2), Lit(3)), Lit(4)))",
        "parse([TNum(1), TPlusSym, TNum(2), TPlusSym, TNum(3)]) = Ok(Plus(Plus(Lit(1), Lit(2)), Lit(3)))",
        "execute([TNum(2), TPlusSym, TNum(3), TStarSym, TNum(4)]) = Ok(Some([20]))",
        "parse([TNum(2), TNum(3)]) = Ok(Lit(2))",
        "parse([TPlusSym, TOpen]) = Err(BadParen)",
    ] {
        let src = format!("import calc; import calc_parser; import result; import option; import list;\ntheorem wrong(): {statement} {{ refl }}");
        let mut control = image.elaborator();
        let err = control.elab_module_source("wrong", &src).expect_err("false calculator theorem");
        let message = err.render(&src);
        assert!(message.contains("the kernel rejected `wrong`: NotConvertible"), "{message}");
    }
}
