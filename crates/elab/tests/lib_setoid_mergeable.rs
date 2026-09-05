//! Manual relation-indexed algebra: generic clients, two equality choices,
//! heterogeneous function relations, canonical parents, and refusal controls.

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
        ("relation", include_str!("../../../lib/std/relation.hthr")),
        (
            "relation_props",
            include_str!("../../../lib/std/relation_props.hthr"),
        ),
        (
            "algebra_rel",
            include_str!("../../../lib/std/algebra_rel.hthr"),
        ),
        (
            "relation_context",
            include_str!("../../../lib/std/relation_context.hthr"),
        ),
        (
            "list_setoid",
            include_str!("../../../lib/std/list_setoid.hthr"),
        ),
    ])
}

#[test]
fn composed_context_showcase_checks() {
    let mut e = base();
    check(
        &mut e,
        "relational_contexts",
        include_str!("../../../docs/showcase/relational-contexts.hthr"),
    );
}

#[test]
fn application_rule_allows_heterogeneous_carriers_and_fixed_values() {
    let mut e = base();
    check(
        &mut e,
        "heterogeneous_application",
        r#"
import bool;
import nat;
import list;
import relation;
import relation_props;
import relation_context;

fn ElementIn(n: Nat, xs: List<Nat>) -> Type { Mem(n, xs) }
fn advance(xs: List<Nat>) -> List<Nat> { map(xs, Succ) }

theorem application(n: Nat, xs: List<Nat>, h: Mem(n, xs)):
    Mem(Succ(n), advance(xs))
{
    let functions = respectful_const(ElementIn, Respectful(ElementIn, ElementIn),
        Succ, advance, λ n xs h => mem_map(xs, n, Succ, h));
    respectful_ap(ElementIn, ElementIn, ElementIn,
        λ n => Succ, λ xs => advance, λ n => n, λ xs => xs,
        functions, respectful_id(ElementIn))(n, xs, h)
}

// Even constant values may inhabit different carriers and be non-identical.
theorem constants(n: Nat, xs: List<Nat>, h: Mem(n, xs)): Mem(0, [0]) {
    respectful_const(ElementIn, ElementIn, 0, [0], mem_head(0, []))(n, xs, h)
}

fn Evidence(x, y: Nat) -> Type { Bool }
theorem keeps_exact_evidence(p: Bool):
    respectful_const<Nat, Nat, Nat, Nat>(RelId<Nat>, Evidence, 0, 0, p)(1, 1, refl) = p
{ refl }
"#,
    );
}

#[test]
fn constant_context_does_not_invent_reflexivity() {
    let mut e = base();
    let src = r#"
import logic;
import nat;
import relation;
import relation_props;
import relation_context;
fn Never(x, y: Nat) -> Type { False }
theorem invalid(): Respectful(RelId<Nat>, Never, λ x => 0, λ x => 0) {
    respectful_const(RelId<Nat>, Never, 0, 0, refl)
}
"#;
    let err = e
        .elab_module_source("invalid_constant", src)
        .expect_err("a fixed output still needs evidence in its output relation");
    let message = err.render(src);
    assert!(
        message.contains("`refl` needs an `=` expected type"),
        "{message}"
    );
}

#[test]
fn manual_showcase_checks_with_identity_and_membership_instances() {
    let mut e = base();
    let src = include_str!("../../../docs/showcase/mergeable.hthr");
    if let Err(err) = e.elab_module_source("mergeable_showcase", src) {
        panic!("{}", err.render(src));
    }
}

fn check(e: &mut Elaborator, name: &str, src: &str) {
    if let Err(err) = e.elab_module_source(name, src) {
        panic!("{}", err.render(src));
    }
}

#[test]
fn function_relator_composes_across_different_carriers() {
    let mut e = base();
    check(
        &mut e,
        "heterogeneous",
        r#"
import nat;
import list;
import relation_props;

fn ElementIn(n: Nat, xs: List<Nat>) -> Type { Mem(n, xs) }
fn advance(xs: List<Nat>) -> List<Nat> { map(xs, Succ) }

theorem advance_related():
    Respectful(ElementIn, ElementIn, Succ, advance)
{ λ n xs h => mem_map(xs, n, Succ, h) }

theorem twice_related(n: Nat, xs: List<Nat>, h: Mem(n, xs)):
    Mem(Succ(Succ(n)), advance(advance(xs)))
{
    respectful_compose(ElementIn, ElementIn, ElementIn,
        Succ, advance, Succ, advance, advance_related(), advance_related())(n, xs, h)
}

theorem id_related(n: Nat, xs: List<Nat>, h: Mem(n, xs)): Mem(n, xs) {
    respectful_id(ElementIn, n, xs, h)
}

theorem application_related(n: Nat, xs: List<Nat>, h: Mem(n, xs)):
    Mem(Succ(n), advance(xs))
{
    respectful_apply(ElementIn, ElementIn, Succ, advance, advance_related(), n, xs, h)
}
"#,
    );
}

#[test]
fn named_law_parent_reuses_the_exact_registered_proof() {
    let mut e = base();
    check(
        &mut e,
        "parent_view",
        r#"
import list;
import algebra_rel;
import list_setoid;

fn commute<A: Commutative(same, op)>(same: A -> A -> Type,
    op: A -> A -> A, x, y: A) -> same(op(x,y), op(y,x))
{ A.comm(x,y) }

theorem exact_parent<A>(xs, ys: List<A>):
    commute(SameMembers<A>, append<A>, xs, ys) = append_comm_same_members(xs, ys)
{ refl }

// Also exercises use of an open child dictionary through the named parent.
fn commute_from_child<A: Mergeable(same, op)>(same: A -> A -> Type,
    op: A -> A -> A, x, y: A) -> same(op(x,y), op(y,x))
{ commute(same, op, x, y) }
"#,
    );
}

#[test]
fn membership_laws_cannot_supply_identity_laws() {
    let mut e = base();
    check(
        &mut e,
        "needs_commutative",
        r#"
import algebra_rel;
fn commute<A: Commutative(same, op)>(same: A -> A -> Type,
    op: A -> A -> A, x, y: A) -> same(op(x,y), op(y,x))
{ A.comm(x,y) }
"#,
    );
    let src = r#"
import nat;
import list;
import relation;
import list_setoid;
import needs_commutative;
theorem invalid(): append<Nat>([0], [1]) = append<Nat>([1], [0]) {
    commute(RelId<List<Nat>>, append<Nat>, [0], [1])
}
"#;
    let err = e
        .elab_module_source("invalid_identity", src)
        .expect_err("SameMembers commutativity must not answer an identity goal");
    let message = err.render(src);
    assert!(message.contains("Commutative"), "{message}");
}

fn generation_request() -> heather_elab::relational_context::Request {
    use heather_elab::relational_context::{Fixed, Operation, Request};
    Request {
        function: "receive".into(),
        variable: "incoming".into(),
        input: "SameMembers<A>".into(),
        output: "SameMembers<A>".into(),
        generated_name: "receive_generated".into(),
        operations: vec![Operation {
            head: "++".into(),
            function: "append<A>".into(),
            inputs: vec!["SameMembers<A>".into(), "SameMembers<A>".into()],
            output: "SameMembers<A>".into(),
            certificate: Some("append_same_members<A>".into()),
        }],
        fixed: vec![Fixed {
            term: "known".into(),
            relation: "SameMembers<A>".into(),
            evidence: "same_members_refl(known)".into(),
        }],
    }
}

const GENERATOR_SOURCE: &str = r#"
import list;
import nat;
import relation;
import relation_props;
import list_setoid;
fn receive<A>(known, incoming: List<A>) -> List<A> {
    known ++ (incoming ++ incoming)
}
"#;

#[test]
fn generator_emits_a_checked_reusable_definition_without_mutating_the_session() {
    use heather_elab::relational_context::{Outcome, derive};
    let mut e = base();
    let request = generation_request();
    let Outcome::Checked { source } = derive(&e, "generated", GENERATOR_SOURCE, &request).unwrap()
    else {
        panic!("expected a certificate");
    };
    assert!(source.contains("preserves_relation_binary"));
    assert!(source.contains("respectful_const"));
    assert!(!source.contains('?'));
    // The name is still vacant in the caller's session, and rechecking the
    // emitted source does not require the generator to be installed.
    check(&mut e, "generated", &source);
    check(
        &mut e,
        "consumer",
        r#"
import list;
import list_setoid;
import generated;
theorem rewrite<A>(known, xs, ys: List<A>, h: SameMembers(xs, ys)):
    SameMembers(receive(known, xs), receive(known, ys))
{ receive_generated(known, xs, ys, h) }
"#,
    );
    let Outcome::Checked { source: again } =
        derive(&base(), "generated", GENERATOR_SOURCE, &request).unwrap()
    else {
        panic!()
    };
    assert_eq!(source, again);
}

#[test]
fn generator_reports_the_observer_contract_and_resumes_with_evidence() {
    use heather_elab::relational_context::{Operation, Outcome, derive};
    let e = base();
    let mut request = generation_request();
    let source = GENERATOR_SOURCE
        .replace(
            "fn receive",
            "fn observe<A>(xs: List<A>) -> List<A> { xs }\nfn receive",
        )
        .replace(
            "known ++ (incoming ++ incoming)",
            "observe(known ++ (incoming ++ incoming))",
        );
    request.operations.push(Operation {
        head: "observe".into(),
        function: "observe<A>".into(),
        inputs: vec!["SameMembers<A>".into()],
        output: "SameMembers<A>".into(),
        certificate: None,
    });
    let Outcome::Blocked { obligations } = derive(&e, "observer", &source, &request).unwrap()
    else {
        panic!()
    };
    assert_eq!(obligations.len(), 1);
    assert_eq!(
        obligations[0].goal,
        "PreservesRelation(SameMembers<A>, SameMembers<A>, observe<A>)"
    );
    assert!(obligations[0].declaration.contains("known: List<A>"));
    request.operations.last_mut().unwrap().certificate =
        Some("preserves_relation_id(SameMembers<A>)".into());
    assert!(matches!(
        derive(&e, "observer", &source, &request).unwrap(),
        Outcome::Checked { .. }
    ));
}

#[test]
fn generator_leaves_length_unproved_and_rejects_a_wrong_certificate() {
    use heather_elab::relational_context::{Operation, Outcome, derive};
    let e = base();
    let mut request = generation_request();
    request.output = "RelId<Nat>".into();
    request.operations.push(Operation {
        head: "list_len".into(),
        function: "list_len<A>".into(),
        inputs: vec!["SameMembers<A>".into()],
        output: "RelId<Nat>".into(),
        certificate: None,
    });
    let source = GENERATOR_SOURCE
        .replace("incoming: List<A>) -> List<A>", "incoming: List<A>) -> Nat")
        .replace(
            "known ++ (incoming ++ incoming)",
            "list_len(known ++ (incoming ++ incoming))",
        );
    let Outcome::Blocked { obligations } = derive(&e, "length", &source, &request).unwrap() else {
        panic!()
    };
    assert_eq!(obligations.len(), 1);
    assert_eq!(
        obligations[0].goal,
        "PreservesRelation(SameMembers<A>, RelId<Nat>, list_len<A>)"
    );
    request.operations.last_mut().unwrap().certificate =
        Some("preserves_relation_id(SameMembers<A>)".into());
    let error = derive(&e, "length", &source, &request).unwrap_err();
    assert!(
        error.contains("generated certificate did not check"),
        "{error}"
    );
    // Its actual impossibility has an independent checked refutation.
    check(
        &mut e.clone(),
        "length_counterexample",
        include_str!("../../../docs/showcase/mergeable.hthr"),
    );
}

#[test]
fn generator_refuses_a_misidentified_operation_and_reports_missing_fixed_evidence() {
    use heather_elab::relational_context::{Outcome, derive};
    let e = base();
    let mut request = generation_request();
    request.fixed.clear();
    let Outcome::Blocked { obligations } = derive(&e, "fixed", GENERATOR_SOURCE, &request).unwrap()
    else {
        panic!()
    };
    assert_eq!(obligations[0].goal, "SameMembers<A>(known, known)");
    request = generation_request();
    request.operations[0].function = "(λ x y => x)".into();
    request.operations[0].certificate = Some("(λ x y h a b k => h)".into());
    let error = derive(&e, "wrong_operation", GENERATOR_SOURCE, &request).unwrap_err();
    assert!(
        error.contains("generated certificate did not check"),
        "{error}"
    );
}

#[test]
fn generator_declines_ambiguous_rules_and_unsupported_bodies() {
    use heather_elab::relational_context::derive;
    let e = base();
    let mut request = generation_request();
    request.operations.push(request.operations[0].clone());
    assert!(
        derive(&e, "ambiguous", GENERATOR_SOURCE, &request)
            .unwrap_err()
            .contains("ambiguous")
    );
    request.operations.pop();
    let source = GENERATOR_SOURCE.replace(
        "known ++ (incoming ++ incoming)",
        "let copy = incoming; known ++ copy",
    );
    assert!(
        derive(&e, "local_let", &source, &request)
            .unwrap_err()
            .contains("fragment")
    );
}

#[test]
fn generator_keeps_intermediate_relations_explicit_and_bounds_its_walk() {
    use heather_elab::relational_context::{Operation, Outcome, derive};
    let e = base();
    let mut request = generation_request();
    request.output = "RelId<List<A>>".into();
    request.operations.push(Operation {
        head: "observe".into(),
        function: "observe<A>".into(),
        inputs: vec!["RelId<List<A>>".into()],
        output: request.output.clone(),
        certificate: Some("preserves_relation_id(RelId<List<A>>)".into()),
    });
    let source = GENERATOR_SOURCE
        .replace(
            "fn receive",
            "fn observe<A>(xs: List<A>) -> List<A> { xs }\nfn receive",
        )
        .replace("known ++ (incoming ++ incoming)", "observe(incoming)");
    let Outcome::Blocked { obligations } = derive(&e, "intermediate", &source, &request).unwrap()
    else {
        panic!()
    };
    assert_eq!(obligations.len(), 1);
    assert!(
        obligations[0]
            .goal
            .contains("SameMembers<A>, RelId<List<A>>")
    );
    request = generation_request();
    let nested = (0..34).fold("incoming".to_string(), |inside, _| {
        format!("known ++ ({inside})")
    });
    let source = GENERATOR_SOURCE.replace("known ++ (incoming ++ incoming)", &nested);
    assert!(
        derive(&e, "bounded", &source, &request)
            .unwrap_err()
            .contains("bound")
    );
}

fn rewrite_request() -> heather_elab::relational_context::RewriteRequest {
    let rules = generation_request();
    heather_elab::relational_context::RewriteRequest {
        theorem: "rewrite_receive".into(),
        proof: "h".into(),
        operations: rules.operations,
        fixed: rules.fixed,
    }
}

const REWRITE_SOURCE: &str = r#"
import list;
import nat;
import relation;
import relation_props;
import list_setoid;
theorem rewrite_receive<A>(known, xs, ys: List<A>, h: SameMembers<A>(xs, ys)):
    SameMembers<A>(known ++ (xs ++ xs), known ++ (ys ++ ys))
{ ?rewrite }
"#;

#[test]
fn contextual_rewrite_recovers_repeated_occurrences_and_emits_an_ordinary_proof() {
    use heather_elab::relational_context::{Outcome, rewrite};
    let mut e = base();
    let result = rewrite(&e, "rewritten", REWRITE_SOURCE, &rewrite_request()).unwrap();
    assert_eq!(result.occurrences, 2);
    assert!(result.context.contains("known ++"));
    let Outcome::Checked { source } = result.outcome else {
        panic!()
    };
    assert!(!source.contains("?rewrite"));
    assert!(source.contains("preserves_relation_binary"));
    assert!(source.contains("(xs, ys, h)"));
    check(&mut e, "rewritten", &source);
    check(
        &mut e,
        "rewrite_user",
        r#"
import list;
import list_setoid;
import rewritten;
theorem use_rewrite<A>(known, xs, ys: List<A>, h: SameMembers<A>(xs, ys)):
    SameMembers<A>(known ++ (xs ++ xs), known ++ (ys ++ ys))
{ rewrite_receive(known, xs, ys, h) }
"#,
    );
}

#[test]
fn contextual_rewrite_preserves_unchanged_occurrences_and_avoids_capture() {
    use heather_elab::relational_context::{Fixed, Outcome, rewrite};
    let e = base();
    let mut request = rewrite_request();
    request.fixed.push(Fixed {
        term: "xs".into(),
        relation: "SameMembers<A>".into(),
        evidence: "same_members_refl(xs)".into(),
    });
    let partial = REWRITE_SOURCE.replace("known ++ (ys ++ ys)", "known ++ (ys ++ xs)");
    let result = rewrite(&e, "partial", &partial, &request).unwrap();
    assert_eq!(result.occurrences, 1);
    assert!(result.context.contains("++ xs"));
    assert!(matches!(result.outcome, Outcome::Checked { .. }));
    // A user parameter with the generator's usual fresh-name spelling remains fixed.
    let collision = REWRITE_SOURCE.replace("known", "__context_input_0");
    request = rewrite_request();
    request.fixed[0].term = "__context_input_0".into();
    request.fixed[0].evidence = "same_members_refl(__context_input_0)".into();
    let result = rewrite(&e, "capture", &collision, &request).unwrap();
    assert!(result.context.starts_with("λ (__context_input_1:"));
    assert!(matches!(result.outcome, Outcome::Checked { .. }));
}

#[test]
fn contextual_rewrite_reports_an_observer_obligation_then_resumes() {
    use heather_elab::relational_context::{Operation, Outcome, rewrite};
    let e = base();
    let mut request = rewrite_request();
    let source = REWRITE_SOURCE
        .replace(
            "theorem rewrite_receive",
            "fn observe<A>(xs: List<A>) -> List<A> { xs }\ntheorem rewrite_receive",
        )
        .replace(
            "known ++ (xs ++ xs), known ++ (ys ++ ys)",
            "observe(known ++ (xs ++ xs)), observe(known ++ (ys ++ ys))",
        );
    request.operations.push(Operation {
        head: "observe".into(),
        function: "observe<A>".into(),
        inputs: vec!["SameMembers<A>".into()],
        output: "SameMembers<A>".into(),
        certificate: None,
    });
    let result = rewrite(&e, "missing_observer", &source, &request).unwrap();
    assert_eq!(result.occurrences, 2);
    let Outcome::Blocked { obligations } = result.outcome else {
        panic!()
    };
    assert_eq!(obligations.len(), 1);
    assert_eq!(
        obligations[0].goal,
        "PreservesRelation(SameMembers<A>, SameMembers<A>, observe<A>)"
    );
    assert_eq!(
        &source[obligations[0].at.start..obligations[0].at.end],
        "observe"
    );
    request.operations.last_mut().unwrap().certificate =
        Some("preserves_relation_id(SameMembers<A>)".into());
    assert!(matches!(
        rewrite(&e, "missing_observer", &source, &request)
            .unwrap()
            .outcome,
        Outcome::Checked { .. }
    ));
}

#[test]
fn contextual_rewrite_rejects_unmatched_changes_reversal_and_false_proofs() {
    use heather_elab::relational_context::rewrite;
    let e = base();
    let request = rewrite_request();
    let unrelated = REWRITE_SOURCE
        .replace("known, xs, ys", "known, other, xs, ys")
        .replace("known ++ (ys ++ ys)", "other ++ (ys ++ ys)");
    let error = rewrite(&e, "unmatched", &unrelated, &request).unwrap_err();
    assert!(
        error.contains("context mismatch at goal, argument 1"),
        "{error}"
    );
    let reverse = REWRITE_SOURCE.replace("h: SameMembers<A>(xs, ys)", "h: SameMembers<A>(ys, xs)");
    assert!(
        rewrite(&e, "reversed", &reverse, &request)
            .unwrap_err()
            .contains("context mismatch")
    );
    let mut invalid = request;
    invalid.operations[0].certificate = Some("same_members_refl".into());
    let error = rewrite(&e, "false_certificate", REWRITE_SOURCE, &invalid).unwrap_err();
    assert!(error.contains("generated rewrite did not check"), "{error}");
}

#[test]
fn contextual_rewrite_does_not_turn_membership_into_identity() {
    use heather_elab::relational_context::{Operation, Outcome, rewrite};
    let e = base();
    let mut request = rewrite_request();
    request.operations.push(Operation {
        head: "list_len".into(),
        function: "list_len<A>".into(),
        inputs: vec!["SameMembers<A>".into()],
        output: "RelId<Nat>".into(),
        certificate: None,
    });
    let source = REWRITE_SOURCE.replace(
        "SameMembers<A>(known ++ (xs ++ xs), known ++ (ys ++ ys))",
        "RelId<Nat>(list_len(known ++ (xs ++ xs)), list_len(known ++ (ys ++ ys)))",
    );
    let Outcome::Blocked { obligations } = rewrite(&e, "length_rewrite", &source, &request)
        .unwrap()
        .outcome
    else {
        panic!()
    };
    assert_eq!(obligations.len(), 1);
    assert_eq!(
        obligations[0].goal,
        "PreservesRelation(SameMembers<A>, RelId<Nat>, list_len<A>)"
    );
}

#[test]
fn contextual_rewrite_zero_occurrences_and_fragment_refusals() {
    use heather_elab::relational_context::{Outcome, rewrite};
    let e = base();
    let source = REWRITE_SOURCE.replace("known ++ (xs ++ xs), known ++ (ys ++ ys)", "known, known");
    let result = rewrite(&e, "constant_context", &source, &rewrite_request()).unwrap();
    assert_eq!(result.occurrences, 0);
    assert!(matches!(result.outcome, Outcome::Checked { .. }));
    let no_hole = REWRITE_SOURCE.replace("?rewrite", "same_members_refl(known)");
    assert!(
        rewrite(&e, "no_hole", &no_hole, &rewrite_request())
            .unwrap_err()
            .contains("single hole")
    );
    let under_binder = REWRITE_SOURCE.replace("known ++ (xs ++ xs)", "(λ x => x)(xs)");
    assert!(
        rewrite(&e, "under_binder", &under_binder, &rewrite_request())
            .unwrap_err()
            .contains("binder-free")
    );
    let complex_witness = REWRITE_SOURCE.replace(
        "h: SameMembers<A>(xs, ys)",
        "h: SameMembers<A>(xs ++ xs, ys)",
    );
    assert!(
        rewrite(&e, "complex_witness", &complex_witness, &rewrite_request())
            .unwrap_err()
            .contains("named value parameters")
    );
}

#[test]
fn contextual_rewrite_specializes_to_identity_and_enforces_its_bound() {
    use heather_elab::relational_context::{Operation, Outcome, RewriteRequest, rewrite};
    let e = base();
    let request = RewriteRequest {
        theorem: "successor_rewrite".into(),
        proof: "h".into(),
        fixed: vec![],
        operations: vec![Operation {
            head: "Succ".into(),
            function: "Succ".into(),
            inputs: vec!["RelId<Nat>".into()],
            output: "RelId<Nat>".into(),
            certificate: Some("(λ x y p => cong(p))".into()),
        }],
    };
    let source = r#"
import nat;
import relation;
theorem successor_rewrite(xs, ys: Nat, h: RelId<Nat>(xs, ys)):
    RelId<Nat>(Succ(Succ(xs)), Succ(Succ(ys)))
{ ?rewrite }
"#;
    let result = rewrite(&e, "identity_rewrite", source, &request).unwrap();
    assert_eq!(result.occurrences, 1);
    assert!(matches!(result.outcome, Outcome::Checked { .. }));
    let nested = |base: &str| (0..34).fold(base.to_string(), |inner, _| format!("Succ({inner})"));
    let deep = source
        .replace("Succ(Succ(xs))", &nested("xs"))
        .replace("Succ(Succ(ys))", &nested("ys"));
    assert!(
        rewrite(&e, "rewrite_bound", &deep, &request)
            .unwrap_err()
            .contains("bound")
    );
    let equal_proof =
        REWRITE_SOURCE.replace("h: SameMembers<A>(xs, ys)", "h: SameMembers<A>(xs, xs)");
    assert!(
        rewrite(&e, "equal_proof", &equal_proof, &rewrite_request())
            .unwrap_err()
            .contains("context mismatch")
    );
}

#[test]
fn context_generation_adds_helper_imports_without_duplicating_existing_ones() {
    use heather_elab::relational_context::{Outcome, Request, derive, rewrite};
    let e = base();
    let source =
        "import nat; import relation; import relation_context; fn id(xs: Nat) -> Nat { xs }";
    let request = Request {
        function: "id".into(),
        variable: "xs".into(),
        input: "RelId<Nat>".into(),
        output: "RelId<Nat>".into(),
        generated_name: "id_preserves".into(),
        operations: vec![],
        fixed: vec![],
    };
    let Outcome::Checked { source } = derive(&e, "helper_imports", source, &request).unwrap()
    else {
        panic!()
    };
    assert_eq!(source.matches("import relation_context;").count(), 1);
    assert_eq!(source.matches("import relation_props;").count(), 1);
    // The parser rejects imports after the first declaration.
    let file = heather_syntax::parse_file(REWRITE_SOURCE).unwrap();
    let mut imports = String::new();
    let mut body = String::new();
    for item in file.items {
        match item {
            heather_syntax::Item::Import(i) => {
                imports.push_str(&REWRITE_SOURCE[i.span.start..i.span.end]);
                imports.push('\n');
            }
            heather_syntax::Item::Decl(d) => {
                body.push_str(&REWRITE_SOURCE[d.span.start..d.span.end])
            }
            _ => panic!(),
        }
    }
    assert!(
        rewrite(
            &e,
            "late_imports",
            &format!("{body}\n{imports}"),
            &rewrite_request()
        )
        .unwrap_err()
        .contains("`import` must come before")
    );
}

#[test]
fn proof_position_merge_twice_uses_local_laws() {
    let mut e = base();
    check(
        &mut e,
        "proof_position",
        r#"
import relation_props;
import algebra_rel;
theorem merge_twice_auto<A: Mergeable(same, merge)>(
    same: A → A → Type, merge: A → A → A, state, incoming: A):
    same(merge(merge(state, incoming), incoming), merge(state, incoming))
{
    A.rel_trans(
        merge(merge(state, incoming), incoming),
        merge(state, merge(incoming, incoming)), merge(state, incoming),
        A.assoc(state, incoming, incoming),
        rel_cong(A.idem(incoming)))
}
"#,
    );
}

const PROOF_OBSERVER: &str = r#"
import relation_props;
import algebra_rel;
theorem observer<A>(same: A → A → Type, observe: A → A, xs, ys: A,
    h: same(xs, ys), certificate: PreservesRelation(same, same, observe)):
    same(observe(xs), observe(ys))
{
    rel_cong(h)
}
"#;

#[test]
fn proof_position_observer_uses_local_evidence_and_resumes_goals() {
    let mut e = base();
    check(&mut e, "local_observer", PROOF_OBSERVER);
    let missing =
        PROOF_OBSERVER.replace(", certificate: PreservesRelation(same, same, observe)", "");
    let error = e
        .elab_module_source("missing_observer", &missing)
        .unwrap_err();
    let message = error.render(&missing);
    assert!(message.contains("compatibility"), "{message}");
    assert!(
        message.contains("PreservesRelation")
            && message.contains("observe")
            && !message.contains("«Π"),
        "{message}"
    );
    let resumed = PROOF_OBSERVER
        .replace(
            "certificate: PreservesRelation(same, same, observe)",
            "supply: (u: A) → PreservesRelation(same, same, observe)",
        )
        .replace(
            "rel_cong(h)",
            "rel_cong(h)\n    on ?compatibility := supply(xs);",
        );
    check(&mut e, "resumed_observer", &resumed);
}

#[test]
fn proof_position_repeated_partial_and_zero_occurrences() {
    let mut e = base();
    check(
        &mut e,
        "occurrences",
        r#"
import relation_props;
import algebra_rel;
theorem repeated<A: Mergeable(same, op)>(same: A → A → Type, op: A → A → A,
    x, y: A, h: same(x, y)): same(op(x, x), op(y, y)) { rel_cong(h) }
theorem partial<A: Mergeable(same, op)>(same: A → A → Type, op: A → A → A,
    x, y: A, h: same(x, y)): same(op(x, x), op(y, x)) { rel_cong(h) }
theorem constant<A: Reflexive(same)>(same: A → A → Type,
    x, y, z: A, h: same(x, y)): same(z, z) { rel_cong(h) }
"#,
    );
}

#[test]
fn proof_position_fixed_evidence_is_a_real_goal() {
    let mut e = base();
    let source = r#"
import relation_props;
import algebra_rel;
theorem fixed<A>(same: A → A → Type, x, y, z: A, h: same(x, y),
    supply: (u: A) → same(z, z)): same(z, z) {
    rel_cong(h)
    on ?fixed := supply(x);
}
"#;
    check(&mut e, "fixed_resumed", source);
    let missing = source.replace("    on ?fixed := supply(x);", "");
    let error = e.elab_module_source("fixed_missing", &missing).unwrap_err();
    assert!(error.render(&missing).contains("fixed"));
}

#[test]
fn proof_position_rejects_unexplained_changes_and_wrong_relations() {
    let mut e = base();
    let source = r#"
import relation_props;
import algebra_rel;
theorem mismatch<A: Mergeable(same, op)>(same: A → A → Type, op: A → A → A,
    x, y, z: A, h: same(x, y)): same(op(z, x), op(x, y)) { rel_cong(h) }
"#;
    let error = e.elab_module_source("mismatch", source).unwrap_err();
    assert!(
        error.render(source).contains("context mismatch"),
        "{}",
        error.render(source)
    );
    let reversed = source.replace("same(op(z, x), op(x, y))", "same(op(y, y), op(x, x))");
    let error = e.elab_module_source("reversed", &reversed).unwrap_err();
    assert!(error.render(&reversed).contains("context mismatch"));
    let other = PROOF_OBSERVER
        .replace(
            "same: A → A → Type",
            "same: A → A → Type, other: A → A → Type",
        )
        .replace(
            "same(observe(xs), observe(ys))",
            "other(observe(xs), observe(ys))",
        );
    let error = e.elab_module_source("other_relation", &other).unwrap_err();
    assert!(error.render(&other).contains("same resolved relation"));
}

#[test]
fn proof_position_name_can_be_shadowed() {
    let mut e = base();
    check(
        &mut e,
        "shadowed_congruence",
        r#"
import nat;
fn rel_cong(n: Nat) -> Nat { n }
fn client(n: Nat) -> Nat { rel_cong(n) }
"#,
    );
}

#[test]
fn proof_position_preserves_computational_evidence() {
    let mut e = base();
    check(
        &mut e,
        "evidence_content",
        r#"
import nat;
import bool;
import relation_props;
import algebra_rel;
fn lift<A: Mergeable(same, op)>(same: A → A → Type, op: A → A → A,
    x, y, fixed: A, h: same(x, y)) -> same(op(fixed, x), op(fixed, y))
{ rel_cong(h) }
fn Evidence(x, y: Nat) -> Type { Bool }
instance Mergeable<Nat>(Evidence, add) {
    rel_refl := λ x => True,
    rel_sym := λ x y h => h,
    rel_trans := λ x y z h k => k,
    respects2 := λ x x2 hx y y2 hy => hy,
    assoc := λ x y z => True,
    comm := λ x y => True,
    idem := λ x => True,
}
theorem retained(): lift(Evidence, add, 0, 1, 2, False) = False { refl }
"#,
    );
}

#[test]
fn proof_position_bad_resumption_does_not_register_a_theorem() {
    let mut e = base();
    let source = PROOF_OBSERVER
        .replace(", certificate: PreservesRelation(same, same, observe)", "")
        .replace("rel_cong(h)", "rel_cong(h)\n    on ?compatibility := h;");
    assert!(e.elab_module_source("bad_resumption", &source).is_err());
    // The same module/declaration can be checked afterward with valid evidence.
    check(&mut e, "bad_resumption", PROOF_OBSERVER);
}

#[test]
fn proof_position_binary_dictionary_can_be_supplied_by_on() {
    let mut e = base();
    check(
        &mut e,
        "binary_on",
        r#"
import relation_props;
import algebra_rel;
theorem binary<A>(same: A → A → Type, op: A → A → A,
    x, y: A, h: same(x, y),
    supply: (u: A) → Respects2<A, A, A>(same, same, same, op)):
    same(op(x, x), op(y, y)) {
    rel_cong(h)
    on ?compatibility := supply(x);
}
"#,
    );
}

#[test]
fn proof_position_multiple_calls_have_independent_goals() {
    let mut e = base();
    check(
        &mut e,
        "multiple_goals",
        r#"
import logic;
import relation_props;
import algebra_rel;
theorem twice<A>(same: A → A → Type, observe: A → A,
    x, y: A, h: same(x, y),
    supply: (u: A) → PreservesRelation(same, same, observe)):
    And<same(observe(x), observe(y)), same(observe(x), observe(y))> {
    And(rel_cong(h), rel_cong(h))
    on ?compatibility := supply(x);
    on ?compatibility.1 := supply(y);
}
"#,
    );
}

#[test]
fn proof_position_is_bounded_and_needs_a_goal() {
    let mut e = base();
    let mut left = "xs".to_owned();
    let mut right = "ys".to_owned();
    for _ in 0..34 {
        left = format!("observe({left})");
        right = format!("observe({right})");
    }
    let deep = PROOF_OBSERVER.replace(
        "same(observe(xs), observe(ys))",
        &format!("same({left}, {right})"),
    );
    let error = e.elab_module_source("deep_context", &deep).unwrap_err();
    assert!(
        error.render(&deep).contains("depth-32"),
        "{}",
        error.render(&deep)
    );
    let inference = PROOF_OBSERVER.replace("rel_cong(h)", "let p = rel_cong(h); p");
    let error = e.elab_module_source("needs_goal", &inference).unwrap_err();
    assert!(error.render(&inference).contains("expected relation goal"));
    let annotated = PROOF_OBSERVER.replace(
        "rel_cong(h)",
        "let p: same(observe(xs), observe(ys)) = rel_cong(h); p",
    );
    check(&mut e, "annotated_proof", &annotated);
}

#[test]
fn proof_position_showcase_checks_deterministically() {
    let source = include_str!("../../../docs/showcase/relational_proof.hthr");
    let mut first = base();
    let mut second = base();
    check(&mut first, "native_showcase", source);
    check(&mut second, "native_showcase", source);
    assert_eq!(
        support::psi_hash(first.psi()),
        support::psi_hash(second.psi())
    );
}

#[test]
fn relational_notation_infers_scoped_and_concrete_indices() {
    let mut e = base();
    check(
        &mut e,
        "notation_showcase",
        include_str!("../../../docs/showcase/relational_proof.hthr"),
    );
    check(
        &mut e,
        "scoped_notation_client",
        r#"
import algebra_rel;
import notation_showcase;
theorem receive<A: Mergeable(same, merge)>(same: A → A → Type,
    merge: A → A → A, state, incoming: A):
    same(merge(merge(state, incoming), incoming), merge(state, incoming))
{ merge_twice_auto(state, incoming) }
"#,
    );
    let source = r#"
import list;
import list_setoid;
import notation_showcase;
theorem receive<A>(known, incoming: List<A>):
    SameMembers<A>((known ++ incoming) ++ incoming, known ++ incoming)
{ merge_twice_auto(known, incoming) }
"#;
    check(&mut e, "notation_client", source);
}

#[test]
fn relational_indices_follow_the_goal_with_two_structures_in_scope() {
    let mut e = base();
    check(
        &mut e,
        "notation_showcase",
        include_str!("../../../docs/showcase/relational_proof.hthr"),
    );
    for (name, relation, operation) in [("first", "r", "f"), ("second", "s", "g")] {
        let source = format!(
            r#"
import algebra_rel;
import notation_showcase;
theorem receive<A: Mergeable(r, f) + Mergeable(s, g)>(
    r, s: A → A → Type, f, g: A → A → A, x, y: A):
    {relation}({operation}({operation}(x, y), y), {operation}(x, y))
{{ merge_twice_auto(x, y) }}
"#
        );
        check(&mut e, name, &source);
    }
}

#[test]
fn relational_inference_accepts_a_recently_declared_relation() {
    let mut e = base();
    check(
        &mut e,
        "recent_relation",
        r#"
import nat;
theorem preserve<A>({r: A → A → Type}, x, y: A, h: r(x, y)): r(x, y) { h }
fn Recent(x, y: Nat) -> Type { x = y }
theorem client(x, y: Nat, h: Recent(x, y)): Recent(x, y) { preserve(x, y, h) }
"#,
    );
}

#[test]
fn relational_indices_are_not_chosen_from_the_carrier() {
    let mut e = base();
    let source = r#"
import list;
import list_setoid;
import algebra_rel;
fn unchanged<A: Mergeable(≈, ⊔)>(x: A) -> A { x }
fn client<A>(xs: List<A>) -> List<A> { unchanged(xs) }
"#;
    let error = e.elab_module_source("underdetermined", source).unwrap_err();
    let message = error.render(source);
    assert!(message.contains("cannot infer"), "{message}");
    assert!(message.contains("Mergeable<A>(≈, ⊔)"), "{message}");
    assert!(
        !message.contains("#op") && !message.contains("#constraint"),
        "{message}"
    );
}

#[test]
fn relational_notation_has_no_implicit_global_meaning() {
    let mut e = base();
    for symbol in ["≈", "⊔"] {
        let source = format!("import nat; fn missing(x: Nat) -> Type {{ x {symbol} x }}");
        let error = e
            .elab_module_source("missing_notation", &source)
            .unwrap_err();
        let message = error.render(&source);
        assert!(message.contains("no fallback name"), "{message}");
    }
    let source = r#"
import relation_props;
theorem local<A>(same as ≈: A → A → Type, x, y: A, h: x ≈ y): x ≈ y { h }
theorem escaped<A>(same: A → A → Type, x, y: A, h: same(x, y)): x ≈ y { h }
"#;
    let error = e
        .elab_module_source("escaped_notation", source)
        .unwrap_err();
    assert!(error.render(source).contains("no fallback name"));
}

const POSITIVE_SUBTYPE: &str = include_str!("../../../docs/showcase/positive_subtype.hthr");

fn positive_subtype_base() -> Elaborator {
    let mut e = base();
    check(&mut e, "positive_subtype", POSITIVE_SUBTYPE);
    e
}

#[test]
fn positive_subtype_transfers_addition_and_semigroup_laws() {
    positive_subtype_base();
}

#[test]
fn positive_subtype_missing_closure_is_a_resumable_goal() {
    let mut e = positive_subtype_base();
    let source = r#"
import nat;
import positive_subtype;
fn add_missing(x, y: PositiveNat) -> PositiveNat {
    PositiveNat(value := x.value + y.value, valid := ?valid)
}
"#;
    let error = e.elab_module_source("missing_closure", source).unwrap_err();
    let message = error.render(source);
    let heather_elab::ElabError::UnsolvedGoals { goals, .. } = &error else {
        panic!("expected a closure goal: {message}");
    };
    assert_eq!(goals.len(), 1, "{message}");
    assert!(goals[0].name.contains("valid"), "{message}");
    assert!(
        goals[0].statement.contains("x.value") && goals[0].statement.contains("y.value"),
        "{message}"
    );
    for input in ["x", "y"] {
        assert!(
            goals[0]
                .context
                .iter()
                .any(|(name, ty)| name == input && ty.contains("PositiveNat")),
            "{message}"
        );
    }
    let repaired = source.replace(
        "valid := ?valid)",
        "valid := ?valid)\n    on ?valid := add_positive(x.value, y.value, x.valid);",
    );
    check(&mut e, "repaired_closure", &repaired);
    let wrong = repaired.replace("add_positive(x.value, y.value, x.valid)", "x.valid");
    assert!(e.elab_module_source("wrong_closure", &wrong).is_err());
}

#[test]
fn positive_subtype_zero_requires_impossible_evidence() {
    let mut e = positive_subtype_base();
    let source = r#"
import positive_subtype;
fn zero_unit() -> PositiveNat { PositiveNat(value := 0, valid := ?valid) }
"#;
    let error = e.elab_module_source("missing_zero", source).unwrap_err();
    let message = error.render(source);
    let heather_elab::ElabError::UnsolvedGoals { goals, .. } = &error else {
        panic!("expected a zero-positivity goal: {message}");
    };
    assert_eq!(goals.len(), 1, "{message}");
    assert!(goals[0].name.contains("valid"), "{message}");
    assert!(
        goals[0].statement.contains("0") || goals[0].statement.contains("False"),
        "{message}"
    );
    let wrong = source.replace("?valid", "trivial");
    assert!(e.elab_module_source("invalid_zero", &wrong).is_err());
}

#[test]
fn positive_subtype_does_not_identify_stored_evidence() {
    let mut e = positive_subtype_base();
    let source = r#"
import nat;
import positive_subtype;
theorem proof_identity(n: Nat, p, q: 0 < n):
    PositiveNat(n, p) = PositiveNat(n, q) { refl }
"#;
    assert!(e.elab_module_source("proof_identity", source).is_err());
}

#[test]
fn positive_subtype_still_requires_an_explicit_constructor() {
    let mut e = positive_subtype_base();
    let source = r#"
import nat;
import positive_subtype;
fn raw_add(x, y: PositiveNat) -> PositiveNat { x.value + y.value }
"#;
    let error = e.elab_module_source("raw_add", source).unwrap_err();
    let message = error.render(source);
    assert!(
        message.contains("Nat") && message.contains("PositiveNat"),
        "{message}"
    );
}
