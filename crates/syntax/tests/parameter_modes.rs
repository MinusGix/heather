//! Parse-level facts of a parameter's mode
//! (docs/language/sequencing-surface-design.md §24): the mode the AST keeps
//! for `x: T`, `x: &T`, `x: &mut T` and `mut self x: T`, the result type a
//! live path gives, and the refusals a whole file's parse owns, which a
//! Heather probe cannot state (a parse error refuses the file). What the
//! forms mean is probed in Heather, `lib/_tests/std/core/parameter_modes_tests.hthr`.
use heather_syntax::{parse_file, Decl, Item, ParamMode, Ty, TyKind};

fn decl(src: &str) -> Decl {
    let file = parse_file(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg));
    file.items
        .into_iter()
        .find_map(|i| match i { Item::Decl(d) => Some(d), _ => None })
        .expect("a declaration")
}

fn refused(src: &str, says: &str) {
    match parse_file(src) {
        Ok(_) => panic!("{src}: parsed, but should be refused with `{says}`"),
        Err(e) => assert!(e.msg.contains(says), "{src}: refused with `{}`, not `{says}`", e.msg),
    }
}

/// `Mutated<A, Mutated<B, …>>` as the names of its type arguments, outermost first.
fn nest(ty: &Ty) -> Vec<String> {
    match &ty.kind {
        TyKind::Named { name, args } if name == "Mutated" => {
            let mut out = vec![format!("{:?}", args[0].kind)];
            out.extend(nest(&args[1]));
            out
        }
        other => vec![format!("{other:?}")],
    }
}

#[test]
fn each_parameter_keeps_its_mode() {
    let d = decl("fn f(a: A, b: &B, c: &mut C, mut d: D) -> R { a }");
    let modes: Vec<ParamMode> = d.params.iter().map(|p| p.mode).collect();
    assert_eq!(modes, [ParamMode::Owned, ParamMode::View, ParamMode::Path, ParamMode::Owned]);
    // The type is the one after the mode.
    assert!(matches!(&d.params[1].ty.kind, TyKind::Named { name, .. } if name == "B"));
    assert!(matches!(&d.params[2].ty.kind, TyKind::Named { name, .. } if name == "C"));
    // A run of names shares the mode with the type.
    let d = decl("fn f(a, b: &mut N) -> R { a }");
    assert!(d.params.iter().all(|p| p.mode == ParamMode::Path));
}

#[test]
fn mut_self_is_a_live_path_and_its_result_is_unchanged() {
    for src in ["fn T::m(mut self t: T, n: N) -> R { n }", "fn T::m(self t: &mut T, n: N) -> R { n }"] {
        let d = decl(src);
        assert_eq!(d.params[0].mode, ParamMode::Path, "{src}");
        assert!(d.params[0].is_self, "{src}");
        assert_eq!(nest(&d.result).len(), 2, "{src}: {:?}", d.result);
    }
    // The two spellings give one body.
    let a = format!("{:?}", decl("fn T::m(mut self t: T, n: N) -> R { t := g(t); n }").body);
    let b = format!("{:?}", decl("fn T::m(self t: &mut T, n: N) -> R { t := g(t); n }").body);
    assert_eq!(strip_spans(&a), strip_spans(&b));
}

/// A `Debug` rendering with its spans removed, so two spellings compare.
fn strip_spans(s: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find("span: Span {") {
        out.push_str(&rest[..i]);
        let tail = &rest[i..];
        let end = tail.find('}').expect("a span closes");
        rest = &tail[end + 1..];
    }
    out.push_str(rest);
    out
}

#[test]
fn live_paths_nest_in_parameter_order() {
    let d = decl("fn f(a: &mut A, n: N, b: &mut B) -> R { n }");
    let shown = nest(&d.result);
    assert_eq!(shown.len(), 3, "{shown:?}");
    assert!(shown[0].contains("\"A\"") && shown[1].contains("\"B\"") && shown[2].contains("\"R\""), "{shown:?}");
    // A frozen view leaves the result alone.
    let d = decl("fn f(a: &A) -> R { a }");
    assert_eq!(nest(&d.result).len(), 1);
}

#[test]
fn a_designation_reference_keeps_its_ampersand() {
    // `(&, …)` and `(&)` between delimiters are designation references, not
    // a lent place.
    decl("fn f() -> R { g(&) }");
    decl("fn f() -> R { g(&, x) }");
}

#[test]
fn a_call_that_lends_places_leaves_no_argument_marker() {
    for src in [
        "fn f(x: N) -> N { let mut p = x; g(&mut p); p }",
        "fn f(x: N) -> N { let mut p = x; let r = g(&mut p, 1); r }",
        "fn f(x: N) -> N { let mut p = x; let mut r = g(&mut p); r }",
        "fn f(x: N) -> N { let mut p = x; g(&mut p) }",
        "fn f(t: T) -> N { let mut u = t; g(&mut u.a, &mut u.b); u.a }",
    ] {
        let parsed = format!("{:?}", parse_file(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg)));
        assert!(!parsed.contains("\\0assign"), "{src} keeps an assignment");
        // Each lent argument stands inside the one call that lends it.
        assert_eq!(parsed.matches("\\0mutarg").count(), src.matches("&mut").count(), "{src}");
        assert!(parsed.contains("\\0pathcall"), "{src}");
    }
}

#[test]
fn only_a_place_is_lent() {
    refused("fn f(x: N) -> N { g(&mut h(x)) }", "`&mut` lends a place");
    refused("fn f(x: N) -> N { g(&mut (x + 1)) }", "`&mut` lends a place");
    refused("fn f(x: N) -> N { g(n := &mut x) }", "a `&mut` argument is positional");
}

#[test]
fn a_lent_place_is_mutable() {
    for src in [
        // A parameter that is not `mut`.
        "fn f(x: N) -> N { g(&mut x); x }",
        // A `let` that is not `mut`.
        "fn f() -> N { let x = 1; let r = g(&mut x); r }",
        // A field of an immutable local.
        "fn f(t: T) -> N { g(&mut t.a); 0 }",
        // Through a λ.
        "fn f() -> N { let mut x = 1; let h = λ (u: N) => { g(&mut x) }; x }",
    ] {
        refused(src, "is not mutable");
    }
}

#[test]
fn the_places_of_one_call_are_apart() {
    refused("fn f() -> N { let mut x = 1; g(&mut x, &mut x); x }", "`x` is passed to two `&mut` parameters");
    refused("fn f(t: T) -> N { let mut u = t; g(&mut u, &mut u.a); 0 }", "overlap, one inside the other");
    refused("fn f(t: T) -> N { let mut u = t; g(&mut u.a.b, &mut u.a); 0 }", "overlap, one inside the other");
    refused(
        "fn f(t: T, i: N, j: N) -> N { let mut u = t; g(&mut u[i], &mut u[j]); 0 }",
        "differ only by an index",
    );
    refused(
        "fn f(t: T, i: N, j: N) -> N { let mut u = t; g(&mut u.a[i].b, &mut u.a[j].c); 0 }",
        "differ only by an index",
    );
    // A method call on a mutable place may rebind its receiver, which is then
    // one of the call's places.
    refused("fn f(t: T) -> N { let mut u = t; u.a.g(&mut u.a); 0 }", "`u.a` is passed to two `&mut` parameters");
    refused("fn f(t: T) -> N { let mut u = t; u.g(&mut u.a); 0 }", "overlap, one inside the other");
    decl("fn f(t: T) -> N { let mut u = t; u.a.g(&mut u.b); 0 }");
    // On a receiver that is not mutable, the receiver is no place of the call.
    decl("fn f(t: T) -> N { let mut u = t; t.g(&mut u); 0 }");
    // Different fields, and different roots, are apart.
    decl("fn f(t: T) -> N { let mut u = t; g(&mut u.a, &mut u.b); 0 }");
    decl("fn f(t: T) -> N { let mut u = t; let mut v = t; g(&mut u.a, &mut v.a); 0 }");
}

#[test]
fn a_mode_is_written_where_an_argument_is_lent() {
    refused("fn f({x: &mut N}) -> N { 0 }", "an implicit parameter cannot be `&mut`");
    refused("fn f({x: &N}) -> N { 0 }", "an implicit parameter cannot be `&`");
    refused("fn f(mut x: &mut N) -> N { 0 }", "written both `mut` and `&mut`");
    refused("fn f(mut x: &N) -> N { 0 }", "asks a frozen view to be reassigned");
    refused("fn f(x: &mut N := 1) -> N { 0 }", "a `&mut` parameter takes no default");
    refused("theorem t(x: &mut N): P { p }", "only a `fn` takes `mut` parameters");
    // A `mut self` receiver beside other live paths stands first among them,
    // so its value is the outermost `Mutated` a method call rebinds it from.
    refused("fn T::m(b: &mut N, mut self t: T) -> R { 0 }", "a `mut self` receiver comes first among the `&mut` parameters");
    let d = decl("fn T::m(mut self t: T, n: N, b: &mut B) -> R { n }");
    let shown = nest(&d.result);
    assert!(shown.len() == 3 && shown[0].contains("\"T\"") && shown[1].contains("\"B\""), "{shown:?}");
    // A frozen view is a theorem's parameter as well as a function's.
    decl("theorem t(x: &N): P { p }");
}

#[test]
fn a_call_inside_an_expression_runs_first() {
    // Each lent argument still stands inside the one call that lends it,
    // and none is left in the expression around it.
    for src in [
        "fn f(x: N) -> N { let mut p = x; let r = g(&mut p) + 1; r }",
        "fn f(x: N) -> N { let mut p = x; let mut q = x; let r = g(&mut p, g(&mut q)); r }",
        "fn f(x: N, b: B) -> N { let mut p = x; if b { return g(&mut p); } p }",
        "fn f(x: N, b: B) -> N { let mut p = x; match b { T => g(&mut p), F => p } }",
        "fn f(x: N) -> N { let mut p = x; let mut q = x; q := g(&mut p); q }",
        "fn f(x: N) -> N { let mut p = x; let r <- g(&mut p); r }",
    ] {
        let parsed = format!("{:?}", parse_file(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg)));
        assert_eq!(parsed.matches("\\0mutarg").count(), src.matches("&mut").count(), "{src}");
        assert_eq!(parsed.matches("\\0pathcall").count(), src.matches("&mut").count(), "{src}");
    }
}

#[test]
fn a_place_lent_inside_an_expression_is_read_nowhere_else_in_it() {
    // The call now runs before the whole expression, so a read of the place
    // beside it would mean its value after the call.
    refused("fn f(x: N) -> N { let mut p = x; let r = p + g(&mut p); r }", "`p` is lent `&mut` by a call inside this expression and read elsewhere in it");
    refused("fn f(x: N) -> N { let mut p = x; g(&mut p, g(&mut p)); p }", "read elsewhere in it");
    refused("fn f(x: N) -> N { let mut p = x; return h(p, g(&mut p)); }", "read elsewhere in it");
    // The call's own arguments are read before it runs, as at a statement.
    decl("fn f(x: N) -> N { let mut p = x; let r = g(&mut p, p) + 1; r }");
    // Two calls lending one place run left to right.
    decl("fn f(x: N) -> N { let mut p = x; let r = g(&mut p) + g(&mut p); r }");
}

#[test]
fn an_arm_in_value_position_cannot_rebind_a_lent_place() {
    // The arm lends the place, which only an arm of a branch that ends its
    // block may rebind (§19.1).
    refused("fn f(x: N, b: B) -> N { let mut p = x; let r = match b { T => g(&mut p), F => 0 }; r }", "is not mutable");
}
