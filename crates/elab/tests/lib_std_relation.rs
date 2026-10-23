//! `lib/std/relation/relation.hthr` — finitary relational semantics and refinement.

use crate::support;
use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const RELATION: &str = include_str!("../../../lib/std/relation/relation.hthr");
const RELATION_PROPS: &str = include_str!("../../../lib/std/relation/relation_props.hthr");

fn elaborated() -> Elaborator {
    let mut e = support::library(&[
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("relation", RELATION),
        ("relation_props", RELATION_PROPS),
    ]);
    e
}

#[test]
fn the_relation_module_checks() {
    elaborated();
}

#[test]
fn relation_properties_compose_at_concrete_and_open_carriers() {
    let mut e = elaborated();
    let probe = r#"
import relation;
import relation_props;

fn from_reflexive<A: Reflexive(R)>(R: A -> A -> Type, x: A) -> R(x, x) {
    A.rel_refl(x)
}

// The concrete identity instance is `Equivalence`; resolution reaches its
// canonical `Reflexive` parent rather than requiring a second declaration.
theorem nat_identity_from_parent(n: Nat): RelId(n, n) {
    from_reflexive(RelId<Nat>, n)
}

// A bare type variable cannot own a canonical instance, so the open-carrier
// spelling is the explicit generic constructor.
theorem open_identity<A>(x: A): RelId(x, x) {
    relid_equivalence<A>().rel_refl(x)
}

theorem pullback_identity<A, B>(f: A -> B, x: A):
    Pullback(f, RelId<B>, x, x)
{
    pullback_equivalence(f, RelId<B>, relid_equivalence<B>()).rel_refl(x)
}

theorem heterogeneous_composition<A, B, C>(
    RA: A -> A -> Type, RB: B -> B -> Type, RC: C -> C -> Type,
    f: A -> B, g: B -> C,
    hf: PreservesRelation(RA, RB, f), hg: PreservesRelation(RB, RC, g),
    x, y: A, hxy: RA(x, y)): RC(g(f(x)), g(f(y)))
{
    preserves_relation_compose(RA, RB, RC, f, g, hf, hg)(x, y, hxy)
}
"#;
    e.elab_module_source("property_customers", probe)
        .expect("relation properties must compose at concrete and open carriers");

    let unrelated = r#"
import relation;
import relation_props;
inductive Point { Pt }
fn Always(x, y: Point) -> Type { True }
instance Symmetric<Point>(Always) { rel_sym := λ x y h => trivial }
fn needs_reflexive<A: Reflexive(R)>(R: A -> A -> Type, x: A) -> R(x, x) {
    A.rel_refl(x)
}
theorem bad(x: Point): Always(x, x) { needs_reflexive(Always, x) }
"#;
    assert!(
        e.elab_module_source("unrelated_property", unrelated).is_err(),
        "an unrelated relation property was used as reflexivity"
    );
}

#[test]
fn algebra_and_finite_execution_laws_apply_at_open_inputs() {
    let mut e = elaborated();
    let probe = r#"
import relation;
import nat;

theorem assoc<A, B, C, D>(R: A -> B -> Type, S: B -> C -> Type,
    T: C -> D -> Type):
    RelEquivalent(
        Compose(Compose(R, S), T),
        Compose(R, Compose(S, T)))
{ compose_assoc(R, S, T) }

theorem left_unit<A, B>(R: A -> B -> Type):
    RelEquivalent(Compose<A, A, B>(λ a b => RelId(a, b), R), R)
{ compose_left_id(R) }

theorem right_unit<A, B>(R: A -> B -> Type):
    RelEquivalent(Compose<A, B, B>(R, λ a b => RelId(a, b)), R)
{ compose_right_id(R) }

theorem monotone<A, B, C>(R1, R2: A -> B -> Type,
    S1, S2: B -> C -> Type, rr: Included(R1, R2), ss: Included(S1, S2)):
    Included(Compose<A, B, C>(R1, S1), Compose<A, B, C>(R2, S2))
{ compose_monotone(R1, R2, S1, S2, rr, ss) }

theorem concatenate<A>(R: A -> A -> Type, m, n: Nat, a, b, c: A,
    ab: Steps(R, m, a, b), bc: Steps(R, n, b, c)):
    Steps(R, m + n, a, c)
{ steps_concat(R, m, n, a, b, c, ab, bc) }

theorem refine_each_step<A>(R, S: A -> A -> Type, h: Included(R, S),
    fuel: Nat, a, b: A, path: Steps(R, fuel, a, b)):
    Steps(S, fuel, a, b)
{ steps_monotone(R, S, h, fuel, a, b, path) }
"#;
    if let Err(err) = e.elab_module_source("laws", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("open relation laws did not apply: {msg}");
    }
}

#[test]
fn deterministic_and_nonfunctional_customers_check() {
    let mut e = elaborated();
    let probe = r#"
import relation;
import bool;
import list;
import pair;

inductive TinyInstr { Increment, Clear }

fn eval_tiny(instruction: TinyInstr, register: Nat) -> Nat {
    match instruction {
        Increment => Succ(register),
        Clear => Zero,
    }
}

fn TinyStep(instruction: TinyInstr) -> Nat -> Nat -> Type {
    Graph(λ (register: Nat) => eval_tiny(instruction, register))
}

theorem deterministic_increment(): TinyStep(Increment, 2, 3) { refl }

theorem eval_tiny_is_allowed(instruction: TinyInstr, register: Nat):
    TinyStep(instruction, register, eval_tiny(instruction, register))
{ refl }

theorem tiny_program_is_allowed(register: Nat):
    ExecuteSteps(TinyStep, [Increment, Clear], register,
        execute_steps(eval_tiny, [Increment, Clear], register))
{
    execute_steps_are_allowed(eval_tiny, TinyStep, eval_tiny_is_allowed,
        [Increment, Clear], register)
}

fn FlagHavoc(source, target: Pair<Bool, Nat>) -> Type {
    FrameFirst(Havoc<Bool>, source, target)
}

// One source has two distinct permitted targets: this is a relation, not the
// graph of a deterministic evaluator.
theorem havoc_may_choose_false(register: Nat):
    FlagHavoc(Pair(False, register), Pair(False, register))
{ And(trivial, refl) }

theorem havoc_may_choose_true(register: Nat):
    FlagHavoc(Pair(False, register), Pair(True, register))
{ And(trivial, refl) }

theorem havoc_keeps_register(source, target: Pair<Bool, Nat>,
    h: FlagHavoc(source, target)): source.snd = target.snd
{ localized_havoc_preserves_neighbor(source, target, h) }

fn KeepFlag(before, after: Bool) -> Type { before = after }
fn SetFlag(before, after: Bool) -> Type { after = True }

theorem finite_choice_keeps():
    RelChoice(KeepFlag, SetFlag, False, False)
{ Inl(refl) }

theorem finite_choice_sets():
    RelChoice(KeepFlag, SetFlag, False, True)
{ Inr(refl) }
"#;
    if let Err(err) = e.elab_module_source("customers", probe) {
        let msg = match err {
            ElabError::Elab { msg, .. } => msg,
            other => format!("{other}"),
        };
        panic!("relation customers did not check: {msg}");
    }
}

#[test]
fn faults_and_unsupported_coverage_are_distinct() {
    let mut e = elaborated();
    let probe = r#"
import relation;

inductive ToyInstr { ReturnSeven, DivideByZero, Missing }
inductive ToyFault { DivisionByZero }

fn toy_semantics(instruction: ToyInstr) -> Coverage<Nat, ToyFault> {
    match instruction {
        ReturnSeven => Supported(Returned(7)),
        DivideByZero => Supported(Faulted(DivisionByZero)),
        Missing => Unsupported,
    }
}

theorem returns_normally():
    toy_semantics(ReturnSeven) = Supported(Returned(7))
{ refl }

theorem fault_is_supported():
    toy_semantics(DivideByZero) = Supported(Faulted(DivisionByZero))
{ refl }

theorem missing_is_unsupported(): toy_semantics(Missing) = Unsupported { refl }
"#;
    e.elab_module_source("coverage", probe)
        .expect("the outcome/coverage toy model must check");

    let bad = r#"
import relation;
inductive ToyFault { DivisionByZero }
fn unsupported_is_not_a_fault() -> SemanticOutcome<Nat, ToyFault> { Unsupported }
"#;
    assert!(
        e.elab_module_source("bad_coverage", bad).is_err(),
        "Unsupported was accidentally accepted as a semantic outcome"
    );
}
