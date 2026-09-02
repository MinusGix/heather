//! Adversarial probes for composing operation-indexed law-bearing classes.
//!
//! Ordinary diamonds must collapse to one canonical parent. Repeating the
//! same class at two different value indices is instead two structures and
//! must never be silently flattened into one. Until qualified parents land,
//! an explicit dependent record is the honest first-class control.

use heather_elab::Elaborator;

fn ok(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected this composition probe to check: {}", err.render(src));
    }
    e
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected this composition probe to be refused"),
        Err(err) => err.render(src),
    }
}

const BASE: &str = r#"
inductive Bit { Off, On }

fn left(x, y: Bit) -> Bit { x }
fn right(x, y: Bit) -> Bit { y }

class Pointed<A>(op: A -> A -> A) {
    point: A,
}
"#;

#[test]
fn a_repeated_parent_at_distinct_indices_is_refused_not_collapsed() {
    let src = format!(
        "{BASE}
class BiPointed<A>(first, second: A -> A -> A)
    extends Pointed<A>(first), Pointed<A>(second)
{{}}
"
    );
    let message = bad(&src);
    assert!(message.contains("two distinct fibers"), "{message}");
    assert!(message.contains("Pointed<A>(first)"), "{message}");
    assert!(message.contains("Pointed<A>(second)"), "{message}");
}

#[test]
fn distinct_fibers_reached_through_different_parents_are_also_refused() {
    let src = format!(
        "{BASE}
class FirstSide<A>(first: A -> A -> A) extends Pointed<A>(first) {{}}
class SecondSide<A>(second: A -> A -> A) extends Pointed<A>(second) {{}}
class TwoSides<A>(first, second: A -> A -> A)
    extends FirstSide<A>(first), SecondSide<A>(second)
{{}}
"
    );
    let message = bad(&src);
    assert!(message.contains("two distinct fibers"), "{message}");
    assert!(message.contains("Pointed<A>(first)"), "{message}");
    assert!(message.contains("Pointed<A>(second)"), "{message}");
}

#[test]
fn an_identical_index_diamond_still_collapses_definitionally() {
    ok(&format!(
        "{BASE}
class LeftPointed<A>(op: A -> A -> A) extends Pointed<A>(op) {{
    left_mark: A,
}}
class RightPointed<A>(op: A -> A -> A) extends Pointed<A>(op) {{
    right_mark: A,
}}
class Diamond<A>(op: A -> A -> A)
    extends LeftPointed<A>(op), RightPointed<A>(op)
{{}}

instance Diamond<Bit>(left) {{
    point := Off,
    left_mark := On,
    right_mark := Off,
}}

theorem shared_point():
    Bit::LeftPointed(left).point = Bit::RightPointed(left).point
{{ refl }}
theorem shared_root():
    Bit::Pointed(left).point = Bit::Diamond(left).point
{{ refl }}
"
    ));
}

#[test]
fn distinct_parent_families_compose_with_two_operation_indices() {
    ok(&format!(
        "{BASE}
class LeftKit<A>(first: A -> A -> A) {{ left_point: A }}
class RightKit<A>(second: A -> A -> A) {{ right_point: A }}
class Interaction<A>(first, second: A -> A -> A)
    extends LeftKit<A>(first), RightKit<A>(second)
{{ interaction: A }}

instance Interaction<Bit>(left, right) {{
    left_point := Off,
    right_point := On,
    interaction := Off,
}}

theorem left_parent(): Bit::LeftKit(left).left_point = Off {{ refl }}
theorem right_parent(): Bit::RightKit(right).right_point = On {{ refl }}
"
    ));
}

#[test]
fn parent_instances_are_not_assembled_into_an_unwritten_child() {
    let src = format!(
        "{BASE}
class LeftKit<A>(first: A -> A -> A) {{ left_point: A }}
class RightKit<A>(second: A -> A -> A) {{ right_point: A }}
class Interaction<A>(first, second: A -> A -> A)
    extends LeftKit<A>(first), RightKit<A>(second)
{{ interaction: A }}

instance LeftKit<Bit>(left) {{ left_point := Off }}
instance RightKit<Bit>(right) {{ right_point := On }}

fn invented() -> Interaction<Bit>(left, right) {{
    Bit::Interaction(left, right)
}}
"
    );
    let message = bad(&src);
    assert!(message.contains("Interaction"), "{message}");
    assert!(message.contains("no instance"), "{message}");
}

#[test]
fn explicit_parent_packaging_is_a_first_class_control() {
    ok(&format!(
        "{BASE}
record TwoPointed<A>(first, second: A -> A -> A) {{
    first_laws: Pointed<A>(first),
    second_laws: Pointed<A>(second),
}}

fn first_pointed() -> Pointed<Bit>(left) {{ Pointed(Off) }}
fn second_pointed() -> Pointed<Bit>(right) {{ Pointed(On) }}
fn both() -> TwoPointed<Bit>(left, right) {{
    TwoPointed(first_pointed(), second_pointed())
}}

theorem first_survives(): both().first_laws.point = Off {{ refl }}
theorem second_survives(): both().second_laws.point = On {{ refl }}
"
    ));
}
