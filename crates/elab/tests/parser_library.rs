//! Checked representation and composition prototype for the parser library.
use heather_elab::{Elaborator, SemanticImage};
use std::sync::OnceLock;
mod support;
fn base() -> Elaborator {
    let mut e = support::semantic_test_base(&[
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
    ]);
    e.set_kernel_workers(1);
    e
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
    let image = IMAGE.get_or_init(|| {
        let mut e = base();
        support::parser::load(&mut e);
        e.semantic_image()
    });
    let mut e = image.elaborator();
    e.set_kernel_workers(1);
    e
}
#[test]
fn generic_combinators_progress_and_error_semantics() {
    let mut e = library();
    let source = r#"
        import parser; import parser_contracts; import parser_diagnostics; import parser_combinators; import parser_primitives; import parser_recursion; import parser_repetition; import nat; import logic; import list; import result; import option; import pair;
        fn zero(n: Nat) -> Option<Nat> { match n { Zero => Some(0), Succ(k) => None } }
        fn zeros() -> Parser<Nat,List<Nat>> { parser_repetition::many(parser_primitives::recognize(zero,10),parser_primitives::recognize_consumes(zero,10)) }
        theorem receiver_composition(): parser::run(parser_primitives::token<Nat>(1).map(Succ).before(parser_primitives::eof<Nat>(99)),[2]) = Ok<Nat,ErrorView>(3) { refl }
        theorem repetition(): parser::run(zeros(),[0,0,1]) = Ok<List<Nat>,ErrorView>([0,0]) { refl }
        theorem vacuous_progress(): parser::run(parser_repetition::many(parser_primitives::fail<Nat,Nat>(1),parser_primitives::fail_consumes<Nat,Nat>(1,1)),[]) = Ok<List<Nat>,ErrorView>([]) { refl }
        theorem some_progress(): parser::run(parser_repetition::many(parser_repetition::some(parser_primitives::recognize(zero,10),parser_primitives::recognize_consumes(zero,10)),parser_repetition::some_consumes(parser_primitives::recognize(zero,10),parser_primitives::recognize_consumes(zero,10))),[0,0,1]) = Ok<List<List<Nat>>,ErrorView>([[0,0]]) { refl }
        theorem empty_repetition(): parser::run(zeros(),[]) = Ok<List<Nat>,ErrorView>([]) { refl }
        theorem finite_nullable(): parser::run(parser_combinators::map(parser_repetition::repeatN(3,parser_combinators::pure<Nat,Nat>(7)),λ (c: Counted<Nat>(3)) => c.values),[]) = Ok<List<Nat>,ErrorView>([7,7,7]) { refl }
        theorem open_tokens<A>(x,y: A): parser::run<A,List<A>>(parser_repetition::many(parser_primitives::token<A>(1),parser_primitives::token_consumes<A>(1)),[x,y]) = Ok<List<A>,ErrorView>([x,y]) { refl }
        theorem mapped_progress(): parser::run(parser_repetition::many(parser_combinators::map(parser_primitives::token<Nat>(1),Succ),parser_combinators::map_consumes(parser_primitives::token<Nat>(1),Succ,1,parser_primitives::token_consumes<Nat>(1))),[1,2]) = Ok<List<Nat>,ErrorView>([2,3]) { refl }
        fn consumed_failure() -> Parser<Nat,Nat> { parser_combinators::then(parser_primitives::token<Nat>(1),parser_primitives::fail<Nat,Nat>(2)) }
        theorem committed_failure(): parser::run(consumed_failure(),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Committed)) { refl }
        theorem no_fallback(): parser::run(parser_combinators::choice(consumed_failure(),parser_combinators::pure<Nat,Nat>(8)),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Committed)) { refl }
        theorem rewind(): parser::run(parser_combinators::choice(parser_diagnostics::attempt(consumed_failure()),parser_primitives::token<Nat>(3)),[7]) = Ok<Nat,ErrorView>(7) { refl }
        theorem farther_error(): parser::run(parser_combinators::choice(parser_diagnostics::attempt(consumed_failure()),parser_primitives::fail<Nat,Nat>(3)),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Retryable)) { refl }
        theorem tied_errors(): parser::run(parser_combinators::choice(parser_primitives::fail<Nat,Nat>(2),parser_combinators::choice(parser_primitives::fail<Nat,Nat>(3),parser_primitives::fail<Nat,Nat>(2))),[]) = Err<Nat,ErrorView>(ErrorView(0,[2,3],Retryable)) { refl }
        theorem explicit_commit(): parser::run(parser_combinators::choice(parser_diagnostics::commit(parser_primitives::fail<Nat,Nat>(2)),parser_combinators::pure<Nat,Nat>(8)),[]) = Err<Nat,ErrorView>(ErrorView(0,[2],Committed)) { refl }
        theorem optional_absent(): parser::run(parser_combinators::optional(parser_primitives::fail<Nat,Nat>(2)),[]) = Ok<Option<Nat>,ErrorView>(None) { refl }
        theorem optional_malformed(): parser::run(parser_combinators::optional(consumed_failure()),[7]) = Err<Option<Nat>,ErrorView>(ErrorView(1,[2],Committed)) { refl }
        theorem complete_error(): parser::run(parser_primitives::complete(parser_combinators::pure<Nat,Nat>(7),99),[1]) = Err<Nat,ErrorView>(ErrorView(0,[99],Retryable)) { refl }
        theorem lookahead_restored(): parser::observe<Nat,Nat>([7],parser::start<Nat>([7]),parser_combinators::lookahead(parser_primitives::token<Nat>(1)).run([7],parser::start<Nat>([7]))) = Ok<Pair<Nat,Nat>,ErrorView>(Pair(7,0)) { refl }
        theorem lookahead_failure(): parser::run(parser_combinators::lookahead(consumed_failure()),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Committed)) { refl }
    "#;
    e.elab_module_source("client",source).unwrap_or_else(|err| panic!("{}",err.render(source)));
}
#[test]
fn false_progress_and_source_forgery_are_rejected() {
    let e = library();
    let image = e.semantic_image();
    for program in [
        "fn bad() -> Consumes<Nat,Nat>(parser_combinators::pure<Nat,Nat>(7),1) { Consumes(λ source begin => trivial) }",
        "fn bad() -> Parser<Nat,List<Nat>> { parser_repetition::many(parser_combinators::pure<Nat,Nat>(7),parser_primitives::token_consumes<Nat>(1)) }",
        "fn bad() -> Parser<Nat,List<Nat>> { parser_repetition::many(parser_combinators::lookahead(parser_primitives::token<Nat>(1)),parser_primitives::token_consumes<Nat>(1)) }",
        "fn bad() -> Counted<Nat>(3) { Counted([1,2],refl) }",
        "fn impossible(source: List<Nat>, begin,end: Cursor<Nat>(source), value: Nat) -> Type { False } fn bad() -> Sound<Nat,Nat>(parser_primitives::token<Nat>(1),impossible) { Sound(λ source begin => trivial) }",
        "fn bad() -> Cursor<Nat>([1]) { parser::start<Nat>([2]) }",
        "fn bad() -> CachedCursor<Nat>([1]) { CachedCursor(parser::start<Nat>([1]),[2],refl) }",
        "theorem bad(): parser::run(parser_repetition::many(parser_primitives::token<Nat>(1),parser_primitives::token_consumes<Nat>(1)),[1,2]) = Ok<List<Nat>,ErrorView>([2,1]) { refl }",
    ] {
        let source = format!("import parser; import parser_contracts; import parser_diagnostics; import parser_combinators; import parser_primitives; import parser_recursion; import parser_repetition; import list; import nat; import result; import logic; {program}");
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
        import parser; import parser_contracts; import parser_diagnostics; import parser_combinators; import parser_primitives; import parser_recursion; import parser_repetition; import nat; import list; import result; import option; import logic;
        fn pick(n: Nat) -> Option<Nat> { Some(n) }
        fn second(n: Nat) -> Parser<Nat,Nat> { parser_primitives::token<Nat>(2) }
        fn pairs() -> Parser<Nat,Nat> { parser_combinators::bind(parser_primitives::token<Nat>(1),second) }
        fn pairs_progress() -> Consumes<Nat,Nat>(pairs(),1) {
            parser_contracts::weaken_consumes(pairs(),1,2,nat::le_succ_r(1,1,nat::le_refl(1)),
                parser_combinators::bind_consumes(parser_primitives::token<Nat>(1),second,1,1,parser_primitives::token_consumes<Nat>(1),λ n => parser_primitives::token_consumes<Nat>(2)))
        }
        theorem composed_progress(): parser::run(parser_repetition::many(pairs(),pairs_progress()),[1,2,3,4]) = Ok<List<Nat>,ErrorView>([2,4]) { refl }
        theorem committed_repetition(): parser::run(parser_repetition::many(pairs(),pairs_progress()),[1,2,3]) = Err<List<Nat>,ErrorView>(ErrorView(3,[2],Committed)) { refl }
        fn recognition() -> Sound<Nat,Nat>(parser_primitives::recognize(pick,1),Recognized<Nat,Nat>(pick)) { parser_primitives::recognize_sound(pick,1) }
        fn open_head<T>(value: T, tail: List<T>) -> SelectedHead<T,T>(λ token => Some(token),Cons(value,tail),value) {
            parser_primitives::selected_head<T,T>(λ token => Some(token),Cons(value,tail),value,refl)
        }
        fn complete_recognition() -> Sound<Nat,Nat>(parser_primitives::complete(parser_primitives::recognize(pick,1),9),CompleteSpec<Nat,Nat>(Recognized<Nat,Nat>(pick))) {
            parser_primitives::complete_sound(parser_primitives::recognize(pick,1),9,Recognized<Nat,Nat>(pick),recognition())
        }
        theorem recognized(source: List<Nat>, begin: Cursor<Nat>(source), s: Success<Nat,Nat>(source,begin), shape: parser_primitives::recognize(pick,1).run(source,begin) = Ok(s)):
            Recognized(pick,source,begin,s.end,s.value) {
            parser_contracts::post_on_success(source,begin,Recognized<Nat,Nat>(pick),parser_primitives::recognize(pick,1).run(source,begin),recognition().law(source,begin),s,shape)
        }
        fn certified(source: List<Nat>, begin: Cursor<Nat>(source)) -> Result<Certified<Nat,Nat>(source,begin,Recognized<Nat,Nat>(pick)),Failure<Nat>(source)> {
            parser_contracts::certify_at(parser_primitives::recognize(pick,1),Recognized<Nat,Nat>(pick),recognition(),source,begin)
        }
    "#;
    e.elab_module_source("certificates",source).unwrap_or_else(|err| panic!("{}",err.render(source)));
    for name in ["parser_repetition::many_at", "parser_combinators::bind_associativity", "parser_primitives::recognize_post", "parser_primitives::recognized_head", "parser_primitives::complete_post", "parser_combinators::certified_finish_forget", "parser_combinators::certified_map_forget", "certificates::recognized"] {
        assert!(e.axiom_report(name).unwrap().axioms.is_empty(),"{name} used an axiom");
    }
}

