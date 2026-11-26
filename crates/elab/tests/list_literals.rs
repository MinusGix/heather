//! Expected-type-directed `[…]` construction through the canonical
//! `CollectionLiteral` protocol. Literals use a primitive vector as their
//! bootstrap representation and add no kernel form.

use heather_elab::{ElabError, Elaborator};

const LIST_DECL: &str = "inductive List<A> { Nil, Cons(head: A, tail: List<A>) }\n";
const LIST: &str = r#"
inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
instance<A>(n: Nat) CollectionLiteral<List<A>>(n) {
    element := A,
    fromLiteral := λ (xs: [A; n]) =>
        xs.fold(Nil<A>, λ (head: A) (tail: List<A>) => Cons(head, tail)),
}
"#;

fn elab(body: &str) -> Elaborator {
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    elaborator.elab_module_source("list", LIST).expect("canonical list module");
    let source = format!("import list;\n{body}");
    elaborator
        .elab_module_source("list_literal_test", &source)
        .unwrap_or_else(|error| panic!("{}", error.render(&source)));
    elaborator
}

fn elab_err(body: &str) -> (String, String) {
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    elaborator.elab_module_source("list", LIST).expect("canonical list module");
    let source = format!("import list;\n{body}");
    let error = elaborator
        .elab_module_source("list_literal_error", &source)
        .expect_err("expected elaboration to fail");
    let message = match &error {
        ElabError::Elab { msg, .. } | ElabError::Parse(heather_syntax::ParseError { msg, .. }) => {
            msg.clone()
        }
        other => other.to_string(),
    };
    (message, error.render_snippet(&source, "test.hthr"))
}

#[test]
fn empty_nonempty_and_trailing_comma_literals_lower_to_list_constructors() {
    elab(
        r#"
        fn empty() -> List<Nat> { [] }
        fn three() -> List<Nat> { [1, 2, 3,] }
        fn pass(xs: List<Nat>) -> List<Nat> { xs }

        theorem empty_lowers(): empty() = Nil { refl }
        theorem three_lowers(): three() = Cons(1, Cons(2, Cons(3, Nil))) { refl }
        theorem argument_gets_container_context():
            pass([4, 5]) = Cons(4, Cons(5, Nil)) { refl }
        "#,
    );
}

#[test]
fn computed_nonvector_carriers_keep_the_collection_protocol() {
    elab(r#"
        record Bag { tag: Nat }
        fn Carrier() -> Type { Bag }
        instance(n: Nat) CollectionLiteral<Carrier()>(n) {
            element := Nat,
            fromLiteral := λ (xs: [Nat; n]) => Bag(7),
        }
        fn empty() -> Carrier() { [] }
        fn two() -> Carrier() { [1, 2] }
        theorem empty_value(): empty() = Bag(7) { refl }
        theorem two_values(): two() = Bag(7) { refl }
        fn generic<C> requires literal: CollectionLiteral<C>(2) (x: literal.element) -> C { [x, x] }
    "#);
}

#[test]
fn list_literals_are_checking_only_because_the_container_is_ambiguous() {
    elab(
        r#"
        fn checked() -> List<Nat> {
            let xs: List<Nat> = [1, 2];
            xs
        }
        theorem checked_lowers(): checked() = Cons(1, Cons(2, Nil)) { refl }
        "#,
    );

    let (message, _) = elab_err("fn f() -> Nat { let xs = [1, 2]; 0 }");
    assert!(message.contains("collection literal needs an expected container type"), "{message}");
}

#[test]
fn list_and_vector_brackets_remain_distinct() {
    elab(
        r#"
        fn list() -> List<Nat> { [1, 2] }
        fn vector() -> [Nat; 2] { [1, 2] }
        fn adjacent_index(List: [Nat; 1]) -> Nat { List[FZ] }
        theorem list_lowers(): list() = Cons(1, Cons(2, Nil)) { refl }
        "#,
    );
}

#[test]
fn empty_and_heterogeneous_literals_have_local_diagnostics() {
    let (message, _) = elab_err("fn f() -> Nat { let xs = []; 0 }");
    assert!(message.contains("collection literal needs an expected container type"), "{message}");

    let (message, rendered) = elab_err(
        r#"
        inductive Bool { False, True }
        fn f() -> List<Nat> { [1, True, 3] }
        "#,
    );
    assert!(message.contains("not the expected type"), "{message}");
    assert!(rendered.contains("[1, True, 3]"), "{rendered}");
    assert!(rendered.lines().any(|line| line.contains("^^^^") && !line.contains("^^^^^^^^^^")), "the element, not the whole literal, should be highlighted: {rendered}");
}

#[test]
fn a_collection_literal_requires_an_instance() {
    let (message, _) = elab_err("fn f() -> Nat { [1] }");
    assert!(message.contains("no instance for `CollectionLiteral<Nat>(1)`"), "{message}");

    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    let malformed = "inductive List<A> { Empty, Push(A, List<A>) }";
    elaborator
        .elab_module_source("list", malformed)
        .expect("the declaration itself is a valid inductive");
    let source = "import list; fn f() -> List<Nat> { [1] }";
    let error = elaborator
        .elab_module_source("malformed_list_user", source)
        .expect_err("an unregistered container must be refused");
    assert!(error.to_string().contains("no instance for"), "{error}");
}

#[test]
fn opt_in_is_by_instance_not_a_hard_coded_list_identity() {
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    elaborator.elab_module_source("list", LIST).expect("canonical list module");
    elaborator.elab_module_source("other", LIST_DECL).expect("unrelated list module");

    let rejected = "import other; fn f() -> other::List<Nat> { [1, 2] }";
    let error = elaborator
        .elab_module_source("impostor_user", rejected)
        .expect_err("structural imitation must not opt in");
    assert!(error.to_string().contains("no instance for"), "{error}");

    let accepted = r#"
        import list;
        import other;
        fn f() -> list::List<Nat> { [1, 2] }
        theorem lowers(): f() = list::Cons(1, list::Cons(2, list::Nil)) { refl }
    "#;
    elaborator
        .elab_module_source("qualified_standard_user", accepted)
        .unwrap_or_else(|error| panic!("{}", error.render(accepted)));
}

#[test]
fn an_unrelated_container_can_opt_in_with_its_own_element_type() {
    elab(
        r#"
        inductive Bag<A> { Empty, Push(head: A, tail: Bag<A>) }
        instance<A>(n: Nat) CollectionLiteral<Bag<A>>(n) {
            element := A,
            fromLiteral := λ (xs: [A; n]) =>
                xs.fold(Empty<A>, λ (head: A) (tail: Bag<A>) => Push(head, tail)),
        }
        fn bag() -> Bag<Nat> { [7, 8] }
        theorem bag_lowers(): bag() = Push(7, Push(8, Empty)) { refl }
        "#,
    );
}

#[test]
fn a_same_named_local_class_cannot_hijack_bracket_syntax() {
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    let source = r#"
        class CollectionLiteral<C>(n: Nat) { tag: Nat }
        instance(n: Nat) CollectionLiteral<Nat>(n) { tag := 0 }
        fn vector_still_uses_prelude() -> [Nat; 1] { [1] }
        fn not_a_collection() -> Nat { [1] }
    "#;
    let error = elaborator
        .elab_module_source("shadow_protocol", source)
        .expect_err("syntax must consult the canonical prelude class");
    assert!(
        error.to_string().contains("no instance for `CollectionLiteral<Nat>(1)`"),
        "{error}"
    );
}

#[test]
fn the_standard_list_protocol_path_does_not_mint_a_derived_dictionary() {
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    elaborator.elab_module_source("list", LIST).expect("canonical list module");
    let before = elaborator.psi().bindings.len();
    elaborator
        .elab_module_source("literal_user", "import list; fn xs() -> List<Nat> { [1, 2] }")
        .expect("literal checks");
    assert_eq!(elaborator.psi().bindings.len(), before + 1);
}

/// A literal's spine is read back a child at a time, and each child holds
/// the rest of the literal's vector; reading a child back must not walk that
/// rest. It did: a closed subtree that mentions a global is never skipped by
/// a local substitution (its `u^δ` tail is rewritten unconditionally), and
/// the readback applied the closure's identity substitution anyway, so a
/// literal of `k` such elements cost `k²` node visits — the byte pieces of a
/// `write-elf` certificate, a hundred bytes each, spent most of their
/// elaboration there. Counted on the exact `local_subst_nodes` counter, at a
/// top-level definition (an empty Γ) and under a parameter (the closure
/// captured over Γ's identity environment); quadrupling `k` quadruples a
/// linear count and multiplies a quadratic one by sixteen. It was 11×; it is
/// under 4× once the debug build's re-check of a readback by the reducer
/// (`readback::verify_term`, one readback in sixteen) is set aside, and about
/// 6× with it, since the reducer's own β-step still copies the rest. Under
/// `long-checks` every readback is re-checked that way, so the count there
/// is the reducer's and is not this test's claim.
#[test]
fn a_literal_spine_is_read_back_in_time_linear_in_its_length() {
    use heather_kernel::checks::{skip_verification, SkipVerification};
    use heather_kernel::stats as kstats;
    if skip_verification() == SkipVerification::Full {
        return;
    }
    fn visits(k: usize, under_parameter: bool) -> u64 {
        let elements: Vec<String> = (0..k).map(|i| format!("w({i})")).collect();
        let body = if under_parameter {
            format!("fn w(n: Nat) -> Nat {{ n }}\nfn xs(a: Nat) -> List<Nat> {{ [{}, a] }}\n", elements.join(", "))
        } else {
            format!("fn w(n: Nat) -> Nat {{ n }}\nfn xs() -> List<Nat> {{ [{}] }}\n", elements.join(", "))
        };
        let mut elaborator = Elaborator::with_prelude().expect("prelude");
        elaborator.elab_module_source("list", LIST).expect("canonical list module");
        let source = format!("import list;\n{body}");
        let before = kstats::snapshot();
        elaborator
            .elab_module_source("list_literal_spine", &source)
            .unwrap_or_else(|error| panic!("{}", error.render(&source)));
        kstats::snapshot().since(&before).local_subst_nodes
    }
    for under_parameter in [false, true] {
        let (small, large) = (visits(64, under_parameter), visits(256, under_parameter));
        assert!(large < 8 * small, "under a parameter: {under_parameter}: {small} → {large} node visits for k = 64 → 256");
    }
}

/// Reading a closed literal costs evaluation steps linear in its length, no
/// more than the same list written as a `Cons` spine. A two-valued element
/// type packs the vector's last (up to 64) elements into one `VecLit`, and
/// the elaborator's spine walk did not read a projection off it: each element
/// past the packing point stayed a projection chain from the literal's root
/// as deep as its position, which the kernel walked once per element, so a
/// literal of 64 cost about ten times its spine
/// (issues/list-literal-evaluation-quadratic.md). Counted on the exact
/// `eval_steps` of a `refl` verdict that reads every element, the list
/// elaborated in an earlier module so only its evaluation is counted, at
/// three doubling lengths; a wrong verdict is refused as the control. At
/// these lengths the quadratic term was not yet the larger one (2.5× and
/// 2.9× per doubling), so the claims are the spine bound and an increment
/// per doubling that at most doubles, not a ratio of totals.
#[test]
fn a_packed_literal_is_read_in_evaluation_steps_linear_in_its_length() {
    use heather_elab::stats;
    const BITS: &str = "import list;
inductive Bit { Off, On }
fn all(xs: List<Bit>) -> Bit { match xs { Nil => On, Cons(b, rest) => match b { Off => Off, On => all(rest) } } }
";
    fn steps(k: usize, spine: bool) -> u64 {
        let elements: Vec<&str> = (0..k).map(|i| if i + 1 == k { "Off" } else { "On" }).collect();
        let list = if spine {
            elements.iter().rev().fold("Nil".to_string(), |rest, e| format!("Cons({e}, {rest})"))
        } else {
            format!("[{}]", elements.join(", "))
        };
        let mut elaborator = Elaborator::with_prelude().expect("prelude");
        elaborator.set_kernel_workers(1);
        elaborator.elab_module_source("list", LIST).expect("canonical list module");
        let source = format!("{BITS}fn xs() -> List<Bit> {{ {list} }}\n");
        elaborator
            .elab_module_source("bits", &source)
            .unwrap_or_else(|error| panic!("{}", error.render(&source)));
        elaborator.enable_item_timings();
        let verdict = "import list; import bits;\ntheorem verdict(): all(xs()) = Off { refl }\n";
        elaborator
            .elab_module_source("verdict", verdict)
            .unwrap_or_else(|error| panic!("{}", error.render(verdict)));
        let rows = elaborator.take_item_timings();
        stats::disable();
        let wrong = "import list; import bits;\ntheorem wrong(): all(xs()) = On { refl }\n";
        assert!(elaborator.elab_module_source("wrong", wrong).is_err(), "a wrong verdict was accepted");
        rows.into_iter().find(|r| r.item.ends_with("verdict")).expect("the verdict's row").kernel.eval_steps
    }
    let lengths = [16, 32, 64];
    let literal: Vec<u64> = lengths.into_iter().map(|k| steps(k, false)).collect();
    let spine: Vec<u64> = lengths.into_iter().map(|k| steps(k, true)).collect();
    eprintln!("verdict steps at 16/32/64: literal {literal:?}, spine {spine:?}");
    assert!(literal[0] > 0);
    for (l, s) in literal.iter().zip(&spine) {
        assert!(l <= s, "a literal's read cost more than its spine's: literal {literal:?}, spine {spine:?}");
    }
    assert!(
        literal[2] - literal[1] <= 2 * (literal[1] - literal[0]),
        "a literal's read grew faster than linearly: {literal:?}"
    );
}
