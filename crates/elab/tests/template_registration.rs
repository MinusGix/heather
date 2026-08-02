//! The registration seam (docs/meta-def-registration-design.md §8): what a
//! `meta fn` has to declare before the elaborator will route a use site
//! through it, and what happens when it declares it badly.
//!
//! The per-family suites (in_language_map.rs, in_language_fold.rs) test what a
//! template *computes*. This one tests the seam itself: the `for` clause is
//! the contract, a template's own signature carries the Π order, and every
//! shape failure is loud at the declaration rather than at some later use
//! site. Two controls moved here from those suites when that became true.

use heather_elab::Elaborator;
use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{CtxBase, GlobalBinding, LocalCtx, Term, Type};

const LIB: &str = include_str!("../../../lib/vec_code.hthr");

const ADD: &str = "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
";

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

/// The diagnostic `src` is refused with, panicking if it elaborates.
fn refusal(src: &str, what: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a refusal ({what}), but this elaborated:\n{src}"),
        Err(err) => format!("{err:?}"),
    }
}

/// The body of the last committed binding — the fixture each cross-check
/// declares last, as in the two family suites.
fn last_body(e: &Elaborator) -> (Term, Type, Level) {
    match e.psi().bindings.last().expect("a binding") {
        GlobalBinding::Tm { ty, level, body: Some(b), .. } => {
            ((**b).clone(), (**ty).clone(), level.clone())
        }
        other => panic!("expected a bodied Tm binding, found {other:?}"),
    }
}

/// A `meta fn` declaration for `vec.map`, with `clause` between the parameter
/// list and the arrow and `sig` as the payload type. The body is always the
/// real map template, so every rejection below is about the *signature*.
fn map_template(clause: &str, sig: &str) -> String {
    format!(
        "meta fn map_code(g: Ctx) {clause} -> Code(g |- {sig}) {{
    code {{
        fun (A: Type<0>) => fun (B: Type<0>) => fun (f: A -> B) => fun (k: Nat) =>
            match k as λ z => [A; z] -> [B; z] {{
                Zero => fun (v: [A; 0]) => [],
                Succ(zk, ih) => fun (v: [A; Succ(zk)]) =>
                    cons(f(head(v)), ih(tail(v))),
            }}
    }}
}}
"
    )
}

const MAP_SIG: &str =
    "(A: Type<0>) -> (B: Type<0>) -> (f: A -> B) -> (k: Nat) -> (v: [A; k]) -> [B; k]";

const BUMP: &str = "fn bump(xs: [Nat; 2]) -> [Nat; 2] { xs.map(λ (n: Nat) => Succ(n)) }";

// -- the clause is the contract ---------------------------------------------

/// The retirement of "the name is the contract" (design doc §8 item 2). A
/// `meta fn` named `map_code`, with exactly the right signature and body, is
/// registered as a meta definition and **not** dispatched: without the `for`
/// clause the elaborator has no reason to believe it elaborates anything.
#[test]
fn a_template_without_a_for_clause_is_never_dispatched() {
    let no_clause = map_template("", MAP_SIG);
    let with_clause = map_template("for vec.map", MAP_SIG);

    let src = format!("{no_clause}{BUMP}");
    let undeclared = elab(&format!("{no_clause}"));
    let _ = undeclared; // the declaration itself is fine; it just does nothing
    let (silent, _, _) = last_body(&elab(&src));
    let (rust, _, _) = last_body(&elab(BUMP));
    assert_eq!(
        silent, rust,
        "a `meta fn` with no `for` clause must not route `.map`: the term differs \
         from the Rust schema's, so the name is still being treated as a contract"
    );

    // The same file *with* the clause does route it — the control that says
    // the comparison above tested something.
    let (hooked, _, _) = last_body(&elab(&format!("{with_clause}{BUMP}")));
    assert_ne!(hooked, rust, "the `for` clause did not route `.map`");
}

/// An unknown slot is a registration error that names the vocabulary, not a
/// silently ignored clause.
#[test]
fn an_unknown_slot_is_rejected_with_the_list() {
    let err = refusal(&map_template("for vec.zip", MAP_SIG), "`vec.zip` is not a slot");
    assert!(err.contains("no elaboration slot"), "wrong failure: {err}");
    assert!(err.contains("vec.tabulate"), "the diagnostic should list the slots: {err}");
}

/// `for` on an ordinary declaration is a parse error: only a template
/// elaborates something other than itself.
#[test]
fn a_for_clause_needs_a_meta_fn() {
    let err = refusal("fn f(n: Nat) for vec.map -> Nat { n }", "not a `meta fn`");
    assert!(err.contains("meta fn"), "wrong failure: {err}");
}

// -- the signature is checked, at the declaration ---------------------------

/// Moved from in_language_map.rs. A template that binds too few of the slot's
/// ingredients used to register happily and blow up at the first use site
/// ("its Π spine ran out of parameters"); now it never registers, and the
/// diagnostic says how many of what it was supposed to bind.
#[test]
fn a_short_template_is_rejected_at_its_declaration() {
    // Its own body, not the map one: the point is that a *well-typed* meta fn
    // of the wrong arity is refused, not that a mismatched body is.
    let short = "meta fn map_code(g: Ctx) for vec.map -> Code(g |-
    (A: Type<0>) -> (k: Nat) -> (v: [A; k]) -> [A; k]
) {
    code { fun (A: Type<0>) => fun (k: Nat) => fun (v: [A; k]) => v }
}
";
    let err = refusal(short, "a short template must not register");
    assert!(err.contains("3 of the slot's 5"), "wrong failure: {err}");
}

/// The binder names are the argument protocol, so a template cannot leave one
/// anonymous — even though the *type* would be perfectly well formed.
#[test]
fn an_anonymous_binder_is_rejected() {
    let err = refusal(
        &map_template(
            "for vec.map",
            "(A: Type<0>) -> (B: Type<0>) -> (A -> B) -> (k: Nat) -> (v: [A; k]) -> [B; k]",
        ),
        "an anonymous binder must not register",
    );
    assert!(err.contains("no name"), "wrong failure: {err}");
}

/// A binder named outside the slot's vocabulary: the use site would have
/// nothing to put there.
#[test]
fn a_binder_outside_the_vocabulary_is_rejected() {
    let err = refusal(
        &map_template(
            "for vec.map",
            "(A: Type<0>) -> (B: Type<0>) -> (f: A -> B) -> (n: Nat) -> (v: [A; n]) -> [B; n]",
        ),
        "`n` is not an ingredient of `vec.map`",
    );
    assert!(err.contains("`n` is not an ingredient"), "wrong failure: {err}");
    assert!(err.contains("`k`"), "the diagnostic should list the ingredients: {err}");
}

/// One ingredient, one parameter: a name bound twice means some ingredient is
/// unbound, whatever the type says.
#[test]
fn a_duplicated_binder_is_rejected() {
    let dup = "meta fn map_code(g: Ctx) for vec.map -> Code(g |-
    (A: Type<0>) -> (A: Type<0>) -> (f: A -> A) -> (k: Nat) -> (v: [A; k]) -> [A; k]
) {
    code {
        fun (A: Type<0>) => fun (A: Type<0>) => fun (f: A -> A) => fun (k: Nat) =>
            match k as λ z => [A; z] -> [A; z] {
                Zero => fun (v: [A; 0]) => [],
                Succ(zk, ih) => fun (v: [A; Succ(zk)]) =>
                    cons(f(head(v)), ih(tail(v))),
            }
    }
}
";
    let err = refusal(dup, "`A` is bound twice");
    assert!(err.contains("bound twice"), "wrong failure: {err}");
}

/// The type check proper (design doc §2.2 step 3): names in the vocabulary,
/// arity right, and still not the slot's type — here the result is `[A; k]`
/// where `vec.map` returns `[B; k]`. The body is the identity on the vector,
/// so this is a *well-typed* `meta fn` that simply does not fit the site.
#[test]
fn a_wrong_shape_is_rejected_by_conversion() {
    let wrong = "meta fn map_code(g: Ctx) for vec.map -> Code(g |-
    (A: Type<0>) -> (B: Type<0>) -> (f: A -> B) -> (k: Nat) -> (v: [A; k]) -> [A; k]
) {
    code {
        fun (A: Type<0>) => fun (B: Type<0>) => fun (f: A -> B) => fun (k: Nat) =>
            fun (v: [A; k]) => v
    }
}
";
    let err = refusal(wrong, "the identity is not `vec.map`'s type");
    assert!(err.contains("does not have `vec.map`'s type"), "wrong failure: {err}");
}

/// A template is applied to the use site's context and then to the slot's
/// ingredients, so there is no argument position a `Code` parameter could
/// occupy — and no context for a template with no `Ctx` binder.
#[test]
fn a_template_takes_one_ctx_binder_and_no_code_parameters() {
    let extra = format!(
        "meta fn map_code(g: Ctx, c: Code(g |- Nat)) for vec.map -> Code(g |- {MAP_SIG}) {{
    code {{
        fun (A: Type<0>) => fun (B: Type<0>) => fun (f: A -> B) => fun (k: Nat) =>
            match k as λ z => [A; z] -> [B; z] {{
                Zero => fun (v: [A; 0]) => [],
                Succ(zk, ih) => fun (v: [A; Succ(zk)]) =>
                    cons(f(head(v)), ih(tail(v))),
            }}
    }}
}}
"
    );
    let err = refusal(&extra, "a `Code` parameter has no argument to take");
    assert!(err.contains("exactly one `Ctx` binder"), "wrong failure: {err}");
}

/// One slot takes one template: a second claim is an error naming the first,
/// never a shadowing. (The positive half — two templates for two *different*
/// slots — is `map_and_fold_route_independently` in in_language_fold.rs, and
/// the lib file itself.)
#[test]
fn two_templates_cannot_claim_one_slot() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(LIB).expect("the lib registers");
    let second = "meta fn other_map(g: Ctx) for vec.map -> Code(g |-
    (A: Type<0>) -> (B: Type<0>) -> (f: A -> B) -> (k: Nat) -> (v: [A; k]) -> [B; k]
) {
    code {
        fun (A: Type<0>) => fun (B: Type<0>) => fun (f: A -> B) => fun (k: Nat) =>
            match k as λ z => [A; z] -> [B; z] {
                Zero => fun (v: [A; 0]) => [],
                Succ(zk, ih) => fun (v: [A; Succ(zk)]) =>
                    cons(f(head(v)), ih(tail(v))),
            }
    }
}
";
    let err = format!("{:?}", e.elab_source(second).expect_err("`vec.map` is taken"));
    assert!(err.contains("already elaborated by `map_code`"), "wrong failure: {err}");
}

// -- the order lives in the signature ---------------------------------------

/// **The crux** (design doc §3, §4.3, §8 item 4). Two legal permutations of
/// `vec.fold`'s signature, neither of them the one the call site used to
/// hard-code, both routed correctly with no call-site change:
///
/// 1. the type binders swapped — which is what in_language_fold.rs used to
///    call the "swapped template" negative control, and which is *not* a
///    negative at all once the names carry the order;
/// 2. the length bound **first**, ahead of both type binders — the one that
///    could not work under the old two-code prefix, since the codes are no
///    longer a prefix at all.
#[test]
fn a_permuted_template_is_the_same_template() {
    let swapped = "meta fn fold_code(g: Ctx) for vec.fold -> Code(g |-
    (B: Type<0>) -> (A: Type<0>) -> (z: B) -> (f: A -> B -> B) -> (k: Nat) -> (v: [A; k]) -> B
) {
    code {
        fun (B: Type<0>) => fun (A: Type<0>) => fun (z: B) =>
            fun (f: A -> B -> B) => fun (k: Nat) =>
                match k as λ w => [A; w] -> B {
                    Zero => fun (v: [A; 0]) => z,
                    Succ(zk, ih) => fun (v: [A; Succ(zk)]) =>
                        f(head(v), ih(tail(v))),
                }
    }
}
";
    let length_first = "meta fn fold_code(g: Ctx) for vec.fold -> Code(g |-
    (k: Nat) -> (A: Type<0>) -> (B: Type<0>) -> (z: B) -> (f: A -> B -> B) -> (v: [A; k]) -> B
) {
    code {
        fun (k: Nat) => fun (A: Type<0>) => fun (B: Type<0>) => fun (z: B) =>
            fun (f: A -> B -> B) =>
                match k as λ w => [A; w] -> B {
                    Zero => fun (v: [A; 0]) => z,
                    Succ(zk, ih) => fun (v: [A; Succ(zk)]) =>
                        f(head(v), ih(tail(v))),
                }
    }
}
";
    // An `A ≠ B` instance at a neutral length: the axis that would notice the
    // arguments arriving in the wrong holes, and the fixture the old
    // "swapped" control asserted must *fail*.
    let probe = "fn probe(m: Nat, n: Nat, xs: [[Nat; Succ(m)]; n]) -> Nat {
                     xs.fold(0, λ (v: [Nat; Succ(m)]) (b: Nat) => Succ(b))
                 }";
    let rust = elab(probe);
    let (rt, _, _) = last_body(&rust);

    for template in [swapped, length_first] {
        let hooked = elab(&format!("{template}{probe}"));
        let (ht, hty, hl) = last_body(&hooked);
        assert_ne!(ht, rt, "the hook declined — the cross-check below would be vacuous");
        let empty = LocalCtx { base: CtxBase::Nil, entries: vec![] };
        conv_term(hooked.psi(), &empty, Layer::Prog, &ht, &rt, &hty, &hl, 1_000_000)
            .unwrap_or_else(|e| {
                panic!("a permuted template is not the same template:\n{template}\n{e:?}")
            });
    }
}

/// The literal instance too, where computation decides rather than
/// conversion: a permuted `fold_code` still sums.
#[test]
fn a_permuted_template_still_computes() {
    let length_first = "meta fn fold_code(g: Ctx) for vec.fold -> Code(g |-
    (k: Nat) -> (A: Type<0>) -> (B: Type<0>) -> (z: B) -> (f: A -> B -> B) -> (v: [A; k]) -> B
) {
    code {
        fun (k: Nat) => fun (A: Type<0>) => fun (B: Type<0>) => fun (z: B) =>
            fun (f: A -> B -> B) =>
                match k as λ w => [A; w] -> B {
                    Zero => fun (v: [A; 0]) => z,
                    Succ(zk, ih) => fun (v: [A; Succ(zk)]) =>
                        f(head(v), ih(tail(v))),
                }
    }
}
";
    let src = format!(
        "{length_first}{ADD}
         fn total(xs: [Nat; 3]) -> Nat {{ xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b)) }}
         theorem t(): total([1, 2, 3]) = 6 {{ refl }}"
    );
    elab(&src);
}

// -- the loud use-site paths, and why they have no tests --------------------
//
// The design doc's test plan (§8 item 7) asked for one test each of the two
// loud use-site failures. Both turn out to be **unreachable from the surface**
// once registration checks the signature, and that is a finding rather than an
// omission — the same status as the uncovered-former diagnostic in
// docs/types-as-expressions.md §2.
//
// - *Short Π spine*: the payload is checked against the declared code type,
//   and that type is checked against the slot's, so a registered template's
//   spine has exactly the slot's arity. The guard stays in `try_code_template`
//   because it is what keeps that reasoning from becoming an `unwrap`.
// - *Evaluation goes neutral*: a template takes one `Ctx` binder and no `Code`
//   parameters, so its body is a quote under a closed letbox chain — every
//   scrutinee is a literal `box`, and `CtxApp` of a `CtxLam` always fires. A
//   stuck head needs a code *argument*, which no slot has.
//
// The corresponding failures now happen at the declaration, and every one of
// them is tested above.
//
// A third status, recorded by the surface indexing round
// (docs/surface-fin-indexing-design.md §7 item 15): `vec.tabulate` and
// `vec.nth` now have live *use sites* — `elab_container_ih` and `xs[i]` — and
// still no template, so the only path they exercise is the silent decline
// below. A `for vec.nth` template whose payload disagrees with the slot is
// already rejected by the registration check above, exactly as `vec.map`'s is;
// that path first becomes *reachable* when the port round writes one
// (`issues/quotation-stage-artifacts.md`), and the suite grows a case then.

// -- declines stay silent ---------------------------------------------------

/// An ingredient the level-0 template cannot take is an **honest decline**
/// (design doc §5): the Rust schema serves it, the file elaborates, and the
/// emitted term is the one a file with no template at all would get. Here the
/// element type is `Type<0>` itself, which lives at level 1.
#[test]
fn a_level_one_element_type_declines_to_the_rust_path() {
    let fixture = "fn ids(ts: [Type<0>; 2]) -> [Type<0>; 2] { ts.map(λ (A: Type<0>) => A) }";
    let with_template = elab(&format!("{}{fixture}", map_template("for vec.map", MAP_SIG)));
    let rust = elab(fixture);
    let (dt, _, _) = last_body(&with_template);
    let (rt, _, _) = last_body(&rust);
    assert_eq!(
        dt, rt,
        "a level-1 element type must decline to the Rust schema, silently and \
         with the same term"
    );
}
