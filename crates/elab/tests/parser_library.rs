//! Checked representation and composition prototype for the parser library.
use heather_elab::Elaborator;
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
    let source = include_str!("../../../lib/std/parser.hthr");
    base().elab_module_source("parser",source).unwrap_or_else(|e| panic!("{}",e.render(source)));
}

fn library() -> Elaborator {
    let mut e = base();
    let source = include_str!("../../../lib/std/parser.hthr");
    e.elab_module_source("parser",source).unwrap_or_else(|e| panic!("{}",e.render(source)));
    e
}
#[test]
fn generic_combinators_progress_and_error_semantics() {
    let mut e = library();
    let source = r#"
        import parser; import nat; import logic; import list; import result; import option; import pair;
        fn zero(n: Nat) -> Option<Nat> { match n { Zero => Some(0), Succ(k) => None } }
        fn zeros() -> Parser<Nat,List<Nat>> { parser::many(parser::recognize(zero,10),parser::recognize_consumes(zero,10)) }
        theorem receiver_composition(): parser::run(parser::token<Nat>(1).map(Succ).before(parser::eof<Nat>(99)),[2]) = Ok<Nat,ErrorView>(3) { refl }
        theorem repetition(): parser::run(zeros(),[0,0,1]) = Ok<List<Nat>,ErrorView>([0,0]) { refl }
        theorem vacuous_progress(): parser::run(parser::many(parser::fail<Nat,Nat>(1),parser::fail_consumes<Nat,Nat>(1,1)),[]) = Ok<List<Nat>,ErrorView>([]) { refl }
        theorem some_progress(): parser::run(parser::many(parser::some(parser::recognize(zero,10),parser::recognize_consumes(zero,10)),parser::some_consumes(parser::recognize(zero,10),parser::recognize_consumes(zero,10))),[0,0,1]) = Ok<List<List<Nat>>,ErrorView>([[0,0]]) { refl }
        theorem empty_repetition(): parser::run(zeros(),[]) = Ok<List<Nat>,ErrorView>([]) { refl }
        theorem finite_nullable(): parser::run(parser::map(parser::repeatN(3,parser::pure<Nat,Nat>(7)),λ (c: Counted<Nat>(3)) => c.values),[]) = Ok<List<Nat>,ErrorView>([7,7,7]) { refl }
        theorem open_tokens<A>(x,y: A): parser::run<A,List<A>>(parser::many(parser::token<A>(1),parser::token_consumes<A>(1)),[x,y]) = Ok<List<A>,ErrorView>([x,y]) { refl }
        theorem mapped_progress(): parser::run(parser::many(parser::map(parser::token<Nat>(1),Succ),parser::map_consumes(parser::token<Nat>(1),Succ,1,parser::token_consumes<Nat>(1))),[1,2]) = Ok<List<Nat>,ErrorView>([2,3]) { refl }
        fn consumed_failure() -> Parser<Nat,Nat> { parser::then(parser::token<Nat>(1),parser::fail<Nat,Nat>(2)) }
        theorem committed_failure(): parser::run(consumed_failure(),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Committed)) { refl }
        theorem no_fallback(): parser::run(parser::choice(consumed_failure(),parser::pure<Nat,Nat>(8)),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Committed)) { refl }
        theorem rewind(): parser::run(parser::choice(parser::attempt(consumed_failure()),parser::token<Nat>(3)),[7]) = Ok<Nat,ErrorView>(7) { refl }
        theorem farther_error(): parser::run(parser::choice(parser::attempt(consumed_failure()),parser::fail<Nat,Nat>(3)),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Retryable)) { refl }
        theorem tied_errors(): parser::run(parser::choice(parser::fail<Nat,Nat>(2),parser::choice(parser::fail<Nat,Nat>(3),parser::fail<Nat,Nat>(2))),[]) = Err<Nat,ErrorView>(ErrorView(0,[2,3],Retryable)) { refl }
        theorem explicit_commit(): parser::run(parser::choice(parser::commit(parser::fail<Nat,Nat>(2)),parser::pure<Nat,Nat>(8)),[]) = Err<Nat,ErrorView>(ErrorView(0,[2],Committed)) { refl }
        theorem optional_absent(): parser::run(parser::optional(parser::fail<Nat,Nat>(2)),[]) = Ok<Option<Nat>,ErrorView>(None) { refl }
        theorem optional_malformed(): parser::run(parser::optional(consumed_failure()),[7]) = Err<Option<Nat>,ErrorView>(ErrorView(1,[2],Committed)) { refl }
        theorem complete_error(): parser::run(parser::complete(parser::pure<Nat,Nat>(7),99),[1]) = Err<Nat,ErrorView>(ErrorView(0,[99],Retryable)) { refl }
        theorem lookahead_restored(): parser::observe<Nat,Nat>([7],parser::start<Nat>([7]),parser::lookahead(parser::token<Nat>(1)).run([7],parser::start<Nat>([7]))) = Ok<Pair<Nat,Nat>,ErrorView>(Pair(7,0)) { refl }
        theorem lookahead_failure(): parser::run(parser::lookahead(consumed_failure()),[7]) = Err<Nat,ErrorView>(ErrorView(1,[2],Committed)) { refl }
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
        "fn bad() -> Cursor<Nat>([1]) { parser::start<Nat>([2]) }",
        "fn bad() -> CachedCursor<Nat>([1]) { CachedCursor(parser::start<Nat>([1]),[2],refl) }",
        "theorem bad(): parser::run(parser::many(parser::token<Nat>(1),parser::token_consumes<Nat>(1)),[1,2]) = Ok<List<Nat>,ErrorView>([2,1]) { refl }",
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
            parser::weaken_consumes(pairs(),1,2,nat::le_succ_r(1,1,nat::le_refl(1)),
                parser::bind_consumes(parser::token<Nat>(1),second,1,1,parser::token_consumes<Nat>(1),λ n => parser::token_consumes<Nat>(2)))
        }
        theorem composed_progress(): parser::run(parser::many(pairs(),pairs_progress()),[1,2,3,4]) = Ok<List<Nat>,ErrorView>([2,4]) { refl }
        theorem committed_repetition(): parser::run(parser::many(pairs(),pairs_progress()),[1,2,3]) = Err<List<Nat>,ErrorView>(ErrorView(3,[2],Committed)) { refl }
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

