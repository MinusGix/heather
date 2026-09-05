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
