//! Checked representation and composition prototype for the parser library.
use heather_elab::{Elaborator, SemanticImage};
use std::sync::OnceLock;
use crate::support;
const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra/algebra.hthr")),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", include_str!("../../../lib/std/num/int.hthr")),
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
    ("result", include_str!("../../../lib/std/core/result.hthr")),
];

/// Standard library and parser library alike come back as replayed semantic
/// images (`support::parser::MODULES` is the same list the calculator
/// showcase replays, so the two binaries share one store). Before 2026-09-17
/// the parser modules were re-elaborated from source here on every run: the
/// binary took 19.3 s alone at width one, and 1.35 s warm after.
fn base() -> Elaborator {
    let modules: Vec<(&str, &str)> = MODULES.iter().chain(support::parser::MODULES).copied().collect();
    support::semantic_test_base_with(&modules, |e| e.set_kernel_workers(1))
}

#[test]
fn parser_library_checks() {
    let _ = library();
}

fn library() -> Elaborator {
    // Check the library once in this process. Each client gets independent
    // attempt and diagnostic state over the same kernel-checked declarations.
    // Rebuilding it for all four tests exceeds the full lane's process budget.
    static IMAGE: OnceLock<SemanticImage> = OnceLock::new();
    let image = IMAGE.get_or_init(|| base().semantic_image());
    let mut e = image.elaborator();
    e.set_kernel_workers(1);
    e
}

#[test]
fn deferred_parser_map_reports_the_selected_callee_and_rough_types() {
    // Selecting the visible parser `map` explicitly exercises the deferred
    // path. Result's type-owned member now wins for the original r.map form.
    let source = r#"
        import parser_core; import parser_combinators; import list; import result;
        fn map<T,A,B>(self p: Parser<T,A>, f: A -> B) -> Parser<T,B> {
            parser_combinators::map(p,f)
        }
        fn lookahead_at<T,A>(source: List<T>, begin: Cursor<T>(source),
            r: Reply<T,A>(source,begin)) -> Reply<T,A>(source,begin) {
            map(r,λ s => pure_at(source,begin,s.value))
        }
    "#;
    let msg = library().elab_module_source("deferred_parser", source)
        .expect_err("parser map cannot map a Reply").render(source);
    assert!(msg.contains("was deferred"), "{msg}");
    assert!(msg.contains("selected callee: `deferred_parser::map`"), "{msg}");
    assert!(msg.contains("`p: Parser<") && msg.contains("`f:") && msg.contains("->"), "{msg}");
    assert!(!msg.contains("GlobalTm") && !msg.contains("LocalSubst") && !msg.contains("El("), "{msg}");

    // Selecting Result::map reveals the nested Result returned by the callback;
    // binding the callback result with and_then is the well-typed correction.
    for call in [
        "result::Result::map(r,λ s => pure_at(source,begin,s.value))",
        "r.map(λ s => pure_at(source,begin,s.value))",
        "r.and_then(λ s => pure_at(source,begin,s.value))",
    ] {
        let source = format!(r#"
            import parser_core; import parser_combinators; import list; import result;
            fn map<T,A,B>(self p: Parser<T,A>, f: A -> B) -> Parser<T,B> {{
                parser_combinators::map(p,f)
            }}
            fn lookahead_at<T,A>(source: List<T>, begin: Cursor<T>(source),
                r: Reply<T,A>(source,begin)) -> Reply<T,A>(source,begin) {{ {call} }}
        "#);
        let result = library().elab_module_source("qualified_parser", &source);
        if !call.starts_with("r.and_then") {
            let msg = result.expect_err("map nests the callback's Result").render(&source);
            assert!(msg.contains("has type `Result<") && msg.contains("Success<"), "{msg}");
            assert!(msg.contains("expected here") && !msg.contains("was deferred"), "{msg}");
        } else {
            result.unwrap_or_else(|err| panic!("{}", err.render(&source)));
        }
    }
}

#[test]
fn generic_combinators_progress_and_error_semantics() {
    let mut e = library();
    let source = r#"
        import parser; import nat; import logic; import list; import result; import option; import pair;
        fn zero(n: Nat) -> Option<Nat> { match n { Zero => Some(0), Succ(k) => None } }
        fn zeros() -> Parser<Nat,List<Nat>> { parser::many(parser::recognize(zero,10),parser::recognize_consumes(zero,10)) }
        theorem receiver_composition(): parser::Parser::run_start(parser::token<Nat>(1).map(Succ).before(parser::eof<Nat>(99)),[2]) = Ok<Nat,ErrorView>(3) { refl }
        theorem repetition(): parser::Parser::run_start(zeros(),[0,0,1]) = Ok<List<Nat>,ErrorView>([0,0]) { refl }
        theorem vacuous_progress(): parser::Parser::run_start(parser::many(parser::fail<Nat,Nat>(1),parser::fail_consumes<Nat,Nat>(1,1)),[]) = Ok<List<Nat>,ErrorView>([]) { refl }
        theorem some_progress(): parser::Parser::run_start(parser::many(parser::some(parser::recognize(zero,10),parser::recognize_consumes(zero,10)),parser::some_consumes(parser::recognize(zero,10),parser::recognize_consumes(zero,10))),[0,0,1]) = Ok<List<List<Nat>>,ErrorView>([[0,0]]) { refl }
        theorem empty_repetition(): parser::Parser::run_start(zeros(),[]) = Ok<List<Nat>,ErrorView>([]) { refl }
        theorem finite_nullable(): parser::Parser::run_start(parser::map(parser::repeatN(3,parser::pure<Nat,Nat>(7)),λ (c: Counted<Nat>(3)) => c.values),[]) = Ok<List<Nat>,ErrorView>([7,7,7]) { refl }
        theorem open_tokens<A>(x,y: A): parser::Parser::run_start<A,List<A>>(parser::many(parser::token<A>(1),parser::token_consumes<A>(1)),[x,y]) = Ok<List<A>,ErrorView>([x,y]) { refl }
        theorem mapped_progress(): parser::Parser::run_start(parser::many(parser::map(parser::token<Nat>(1),Succ),parser::map_consumes(parser::token<Nat>(1),Succ,1,parser::token_consumes<Nat>(1))),[1,2]) = Ok<List<Nat>,ErrorView>([2,3]) { refl }
        fn consumed_failure() -> Parser<Nat,Nat> { parser::then(parser::token<Nat>(1),parser::fail<Nat,Nat>(2)) }
        theorem committed_failure(): parser::Parser::run_start(consumed_failure(),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Committed)) { refl }
        theorem no_fallback(): parser::Parser::run_start(parser::choice(consumed_failure(),parser::pure<Nat,Nat>(8)),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Committed)) { refl }
        theorem rewind(): parser::Parser::run_start(parser::choice(parser::attempt(consumed_failure()),parser::token<Nat>(3)),[7]) = Ok<Nat,ErrorView>(7) { refl }
        theorem farther_error(): parser::Parser::run_start(parser::choice(parser::attempt(consumed_failure()),parser::fail<Nat,Nat>(3)),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Retryable)) { refl }
        theorem tied_errors(): parser::Parser::run_start(parser::choice(parser::fail<Nat,Nat>(2),parser::choice(parser::fail<Nat,Nat>(3),parser::fail<Nat,Nat>(2))),[]) = Err<Nat,ErrorView>(ErrorView(0,[2,3],Retryable)) { refl }
        theorem explicit_commit(): parser::Parser::run_start(parser::choice(parser::commit(parser::fail<Nat,Nat>(2)),parser::pure<Nat,Nat>(8)),[]) = Err<Nat,ErrorView>(ErrorView(0,[2],Committed)) { refl }
        theorem optional_absent(): parser::Parser::run_start(parser::optional(parser::fail<Nat,Nat>(2)),[]) = Ok<Option<Nat>,ErrorView>(None) { refl }
        theorem optional_malformed(): parser::Parser::run_start(parser::optional(consumed_failure()),[7]) = Err<Option<Nat>,ErrorView>(ErrorView(1,[2],Committed)) { refl }
        theorem complete_error(): parser::Parser::run_start(parser::complete(parser::pure<Nat,Nat>(7),99),[1]) = Err<Nat,ErrorView>(ErrorView(0,[99],Retryable)) { refl }
        theorem lookahead_restored(): parser::observe<Nat,Nat>([7],parser::Cursor::start<Nat>([7]),parser::lookahead(parser::token<Nat>(1)).run([7],parser::Cursor::start<Nat>([7]))) = Ok<Pair<Nat,Nat>,ErrorView>(Pair(7,0)) { refl }
        theorem lookahead_failure(): parser::Parser::run_start(parser::lookahead(consumed_failure()),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Committed)) { refl }
    "#;
    e.elab_module_source("client",source).unwrap_or_else(|err| panic!("{}",err.render(source)));
}
#[test]
fn false_progress_and_source_forgery_are_rejected() {
    let e = library();
    let image = e.semantic_image();
    for program in [
        "fn bad() -> Consumes<Nat,Nat>(parser::pure<Nat,Nat>(7),1) { Consumes(λ source begin => trivial) }",
        "fn bad() -> Parser<Nat,List<Nat>> { parser::many(parser::pure<Nat,Nat>(7),parser::token_consumes<Nat>(1)) }",
        "fn bad() -> Parser<Nat,List<Nat>> { parser::many(parser::lookahead(parser::token<Nat>(1)),parser::token_consumes<Nat>(1)) }",
        "fn bad() -> Counted<Nat>(3) { Counted([1,2],refl) }",
        "fn impossible(source: List<Nat>, begin,end: Cursor<Nat>(source), value: Nat) -> Type { False } fn bad() -> Sound<Nat,Nat>(parser::token<Nat>(1),impossible) { Sound(λ source begin => trivial) }",
        "fn bad() -> Cursor<Nat>([1]) { parser::Cursor::start<Nat>([2]) }",
        "fn bad() -> CachedCursor<Nat>([1]) { CachedCursor(parser::Cursor::start<Nat>([1]),[2],refl) }",
        "theorem bad(): parser::Parser::run_start(parser::many(parser::token<Nat>(1),parser::token_consumes<Nat>(1)),[1,2]) = Ok<List<Nat>,ErrorView>([2,1]) { refl }",
    ] {
        let source = format!("import parser; import list; import nat; import result; import logic; {program}");
        let mut e = image.elaborator();
        let error = e.elab_module_source("bad",&source).expect_err(program).render(&source);
        assert!(!error.contains("panicked"),"{error}");
        e.elab_module_source("after","theorem clean(n: Nat): n = n { refl }").unwrap();
    }
}

#[test]
fn soundness_certificates_are_first_class() {
    let mut e = library();
    let source = r#"
        import parser; import nat; import list; import result; import option; import logic;
        fn pick(n: Nat) -> Option<Nat> { Some(n) }
        fn second(n: Nat) -> Parser<Nat,Nat> { parser::token<Nat>(2) }
        fn pairs() -> Parser<Nat,Nat> { parser::bind(parser::token<Nat>(1),second) }
        fn pairs_progress() -> Consumes<Nat,Nat>(pairs(),1) {
            parser::weaken_consumes(pairs(),1,2,nat::Nat::le_succ_r(1,1,nat::Nat::le_refl(1)),
                parser::bind_consumes(parser::token<Nat>(1),second,1,1,parser::token_consumes<Nat>(1),λ n => parser::token_consumes<Nat>(2)))
        }
        theorem composed_progress(): parser::Parser::run_start(parser::many(pairs(),pairs_progress()),[1,2,3,4]) = Ok<List<Nat>,ErrorView>([2,4]) { refl }
        theorem committed_repetition(): parser::Parser::run_start(parser::many(pairs(),pairs_progress()),[1,2,3]) = Err<List<Nat>,ErrorView>(ErrorView(3,[2],Committed)) { refl }
        fn recognition() -> Sound<Nat,Nat>(parser::recognize(pick,1),Recognized<Nat,Nat>(pick)) { parser::recognize_sound(pick,1) }
        fn open_head<T>(value: T, tail: List<T>) -> SelectedHead<T,T>(λ token => Some(token),Cons(value,tail),value) {
            parser::selected_head<T,T>(λ token => Some(token),Cons(value,tail),value,refl)
        }
        fn complete_recognition() -> Sound<Nat,Nat>(parser::complete(parser::recognize(pick,1),9),CompleteSpec<Nat,Nat>(Recognized<Nat,Nat>(pick))) {
            parser::complete_sound(parser::recognize(pick,1),9,Recognized<Nat,Nat>(pick),recognition())
        }
        theorem recognized(source: List<Nat>, begin: Cursor<Nat>(source), s: Success<Nat,Nat>(source,begin), shape: parser::recognize(pick,1).run(source,begin) = Ok(s)):
            Recognized(pick,source,begin,s.end,s.value) {
            parser::post_on_success(source,begin,Recognized<Nat,Nat>(pick),parser::recognize(pick,1).run(source,begin),recognition().law(source,begin),s,shape)
        }
        fn certified(source: List<Nat>, begin: Cursor<Nat>(source)) -> Result<Certified<Nat,Nat>(source,begin,Recognized<Nat,Nat>(pick)),Failure<Nat>(source)> {
            parser::certify_at(parser::recognize(pick,1),Recognized<Nat,Nat>(pick),recognition(),source,begin)
        }
    "#;
    e.elab_module_source("certificates",source).unwrap_or_else(|err| panic!("{}",err.render(source)));
    for name in ["parser::many_at", "parser::bind_associativity", "parser::recognize_post", "parser::recognized_head", "parser::complete_post", "parser::certified_finish_forget", "parser::certified_map_forget", "certificates::recognized"] {
        assert!(e.axiom_report(name).unwrap().axioms.is_empty(),"{name} used an axiom");
    }
}
