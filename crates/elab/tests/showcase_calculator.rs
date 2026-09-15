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
    // The proof-carrying grammar is a large checked artifact; keep its gate
    // serial within the per-process memory rail.
    e.set_kernel_workers(1);
    support::parser::load(&mut e);
    for (name, src) in [
        ("calc", include_str!("../../../docs/showcase/calc.hthr")),
        ("calc_parser", include_str!("../../../docs/showcase/calc_parser.hthr")),
    ] {
        e.elab_module_source(name, src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    }
    let mixed = r#"
        import calc_parser; import list; import result; import option;
        fn list_map<A,B>(xs: List<A>, f: A → B) -> List<B> { xs.map(f) }
        fn vector_map<A,B>(xs: [A;2], f: A → B) -> [B;2] { xs.map(f) }
        theorem list_result(): list_map<Nat,Nat>([2,3],Succ) = [3,4] { refl }
        theorem vector_result(): vector_map<Nat,Nat>([2,3],Succ) = [3,4] { refl }
        theorem result_result(): (Ok<Nat,Nat>(2)).map(Succ) = Ok(3) { refl }
        theorem option_result(): (Some(2)).map(Succ) = Some(3) { refl }
    "#;
    e.elab_module_source("mixed", mixed).unwrap_or_else(|err| panic!("{}", err.render(mixed)));
    let grammar_client = r#"
        import calc_parser; import calc; import list; import result; import logic; import parser; import nat;
        // These witnesses use the specification constructors, independently
        // of the parser. The variable numeral exercises an open payload.
        fn literal_witness(n: Nat) -> WholeGrammar([TNum(n)],Lit(n)) {
            WholeGrammar(FactorExpr(AtomFactor(Number(n))),And(refl,And(refl,trivial)),refl,refl,refl)
        }
        fn parenthesized_witness(n: Nat) -> WholeGrammar([TOpen,TNum(n),TClose],Lit(n)) {
            WholeGrammar(FactorExpr(AtomFactor(Parenthesized(FactorExpr(AtomFactor(Number(n)))))),
                And(refl,And(refl,And(refl,And(refl,And(refl,trivial))))),refl,refl,refl)
        }
        fn literal_span(n: Nat, tail: List<PTok>) -> Grammar(2,Cons(TNum(n),tail),parser::start(Cons(TNum(n),tail)),
            Cursor(refl,1,nat::zero_le(list_len(tail))),Lit(n)) {
            Grammar(Number(n),trivial,refl,refl,list::cong_cons(TNum(n),sym(parser::initial_rest(tail))))
        }
        theorem open_success(tokens: List<PTok>, value: Expr, success: parse(tokens) = Ok(value)):
            WholeGrammar(tokens,value) { parse_sound(tokens,value,success) }
        theorem open_span(source: List<PTok>, begin: Cursor<PTok>(source), s: Success<PTok,Expr>(source,begin), success: parse_expr(source,begin) = Ok(s)):
            Grammar(0,source,begin,s.end,s.value) { expression_sound(source,begin,s,success) }
    "#;
    e.elab_module_source("grammar_client", grammar_client).unwrap_or_else(|err| panic!("{}", err.render(grammar_client)));
    for name in ["calc_parser::checked_expr", "calc_parser::checked_factor", "calc_parser::checked_atom",
        "calc_parser::parse_sound", "calc_parser::expression_sound", "calc_parser::grammar_sound",
        "calc_parser::factor_sound", "calc_parser::atom_sound", "grammar_client::open_success",
        "parser::complete_post", "parser::certified_finish_forget", "parser::recognized_head"] {
        assert!(e.axiom_report(name).unwrap().axioms.is_empty(), "{name} used an axiom");
    }
    // Each control starts from the same checked modules. A failed attempt
    // cannot influence the next one. These must fail at their proof body.
    let image = e.semantic_image();
    check_nested_parser_costs(&image);
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
    // Refuse malformed derivations as well as wrong executable answers.
    for body in [
        "fn bad() -> Grammar(2,[TNum(7),TNum(8)],parser::start([TNum(7),TNum(8)]),Cursor(refl,2,nat::le_refl(2)),Lit(7)) { Grammar(Number(7),trivial,refl,refl,refl) }",
        "fn bad() -> WholeGrammar([TNum(8)],Lit(7)) { WholeGrammar(FactorExpr(AtomFactor(Number(7))),And(refl,And(refl,trivial)),refl,refl,refl) }",
        "fn bad() -> WholeGrammar([TNum(7)],Lit(8)) { WholeGrammar(FactorExpr(AtomFactor(Number(7))),And(refl,And(refl,trivial)),refl,refl,refl) }",
        "fn bad() -> WellFormed(Sum(Sum(AtomFactor(Number(1)),FactorExpr(AtomFactor(Number(2)))),FactorExpr(AtomFactor(Number(3))))) { And(And(refl,And(And(refl,And(refl,trivial)),And(refl,And(refl,And(refl,trivial))))),And(refl,And(refl,And(refl,trivial)))) }",
        "fn bad() -> WellFormed(Product(Sum(AtomFactor(Number(1)),FactorExpr(AtomFactor(Number(2)))),AtomFactor(Number(3)))) { And(And(refl,And(And(refl,And(refl,trivial)),And(refl,And(refl,And(refl,trivial))))),And(refl,And(refl,trivial))) }",
        "fn bad() -> WholeGrammar([TOpen,TNum(7)],Lit(7)) { WholeGrammar(FactorExpr(AtomFactor(Parenthesized(FactorExpr(AtomFactor(Number(7)))))),And(refl,And(refl,And(refl,And(refl,And(refl,trivial))))),refl,refl,refl) }",
    ] {
        let src = format!("import calc; import calc_parser; import list; import logic; import parser; import nat; {body}");
        let mut control = image.elaborator();
        let err = control.elab_module_source("bad_grammar", &src).expect_err("invalid grammar derivation");
        let message = err.render(&src);
        assert!(message.contains("the kernel rejected `bad`: NotConvertible"), "{message}");
    }

}

fn check_nested_parser_costs(image: &heather_elab::SemanticImage) {
    for depth in [1,2,4,8] {
        let mut expression = "parser::token<Nat>(1)".to_string();
        for _ in 1..depth { expression = format!("parser::then(parser::token<Nat>(1),{expression})"); }
        let tokens = vec!["7";depth].join(",");
        let source = format!("import parser; import list; import result; fn p() -> Parser<Nat,Nat> {{ {expression} }} theorem correct(): parser::run<Nat,Nat>(parser::complete(p(),99),[{tokens}]) = Ok<Nat,ErrorView>(7) {{ refl }}");
        measure(image,"composition",depth,&source);
        let mut tokens = vec!["TOpen";depth]; tokens.push("TNum(7)"); tokens.extend(vec!["TClose";depth]);
        let source = format!("import calc; import calc_parser; import result; import list; theorem correct(): parse([{}]) = Ok<Expr,ParseError>(Lit(7)) {{ refl }}",tokens.join(","));
        measure(image,"parentheses",depth,&source);
    }
    fn measure(image: &heather_elab::SemanticImage, family: &str, depth: usize, source: &str) {
        let mut e = image.elaborator();
        e.set_kernel_workers(1);
        e.enable_item_timings();
        e.take_item_timings();
        let delta = e.elab_module_delta("cost",source,Default::default()).unwrap_or_else(|err| panic!("{}",err.render(source)));
        let rows = e.take_item_timings();
        let steps: u64 = rows.iter().map(|r| r.kernel.eval_steps).sum();
        let nanos: u64 = rows.iter().map(|r| r.total_ns).sum();
        // Serialized checked deltas include syntax and registry metadata as
        // well as proof terms. They are a growth proxy, not an exact node count.
        println!("parser-cost {family} depth={depth} bytes={} eval_steps={steps} ms={}",delta.to_image_bytes().len(),nanos / 1_000_000);
    }
}
