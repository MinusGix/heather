//! Adversarial probes for composing operation-indexed law-bearing classes.
//!
//! Ordinary diamonds must collapse to one canonical parent. Repeating the
//! same class at two different value indices is instead two structures and
//! must never be silently flattened into one. Tagged parents preserve those
//! structures as named dictionary fields.

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
    stable: (x, y: A) -> op(x, y) = op(x, y),
}
"#;

#[test]
fn the_two_probe_operations_and_direct_indexed_instances_are_distinct() {
    ok(&format!(
        "{BASE}
theorem left_computes(): left(Off, On) = Off {{ refl }}
theorem right_computes(): right(Off, On) = On {{ refl }}
instance Pointed<Bit>(left) {{ point := Off, stable := λ x y => refl }}
instance Pointed<Bit>(right) {{ point := On, stable := λ x y => refl }}
theorem direct_left(): Bit::Pointed(left).point = Off {{ refl }}
theorem direct_right(): Bit::Pointed(right).point = On {{ refl }}
"
    ));
}

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
fn tagged_parents_preserve_both_fibers_and_mint_both_canonical_parents() {
    ok(&format!(
        "{BASE}
class BiPointed<A>(first, second: A -> A -> A)
    extends Pointed<A>(first) as first_laws,
            Pointed<A>(second) as second_laws
{{}}

instance BiPointed<Bit>(left, right) {{
    first_laws := Pointed(Off, λ x y => refl),
    second_laws := Pointed(On, λ x y => refl),
}}

theorem first_component(): Bit::BiPointed(left, right).first_laws.point = Off {{ refl }}
theorem second_component(): Bit::BiPointed(left, right).second_laws.point = On {{ refl }}
class PointedUse<A>(op: A -> A -> A) extends Pointed<A>(op) as laws {{}}
instance PointedUse<Bit>(left) {{}}
instance PointedUse<Bit>(right) {{}}
theorem first_parent(): Bit::PointedUse(left).laws.point = Off {{ refl }}
theorem second_parent(): Bit::PointedUse(right).laws.point = On {{ refl }}
"
    ));
}

#[test]
fn tagged_parent_fields_fill_from_existing_canonical_instances() {
    ok(&format!(
        "{BASE}
class BiPointed<A>(first, second: A -> A -> A)
    extends Pointed<A>(first) as first_laws,
            Pointed<A>(second) as second_laws
{{}}

instance Pointed<Bit>(left) {{ point := Off, stable := λ x y => refl }}
instance Pointed<Bit>(right) {{ point := On, stable := λ x y => refl }}
instance BiPointed<Bit>(left, right) {{}}

theorem first_filled(): Bit::BiPointed(left, right).first_laws.point = Off {{ refl }}
theorem second_filled(): Bit::BiPointed(left, right).second_laws.point = On {{ refl }}
"
    ));
}

#[test]
fn an_index_pinned_goal_upcasts_through_the_matching_tag() {
    ok(&format!(
        "{BASE}
class BiPointed<A>(first, second: A -> A -> A)
    extends Pointed<A>(first) as first_laws,
            Pointed<A>(second) as second_laws
{{}}

fn choose<G> requires p: Pointed<G>(op)
    (op: G -> G -> G, x: G) -> G {{ p.point }}
fn choose_first<G> requires p: BiPointed<G>(first, second)
    (first, second: G -> G -> G, x: G) -> G {{ choose(first, x) }}
fn choose_second<G> requires p: BiPointed<G>(first, second)
    (first, second: G -> G -> G, x: G) -> G {{ choose(second, x) }}
"
    ));
}

#[test]
fn two_tagged_fibers_do_not_pin_an_unqualified_member_request() {
    let src = format!(
        "{BASE}
class BiPointed<A>(first, second: A -> A -> A)
    extends Pointed<A>(first) as first_laws,
            Pointed<A>(second) as second_laws
{{}}

fn ambiguous<G> requires p: BiPointed<G>(first, second)
    (first, second: G -> G -> G, x: G) -> G {{ G.point }}
"
    );
    let message = bad(&src);
    assert!(message.contains("not pinned"), "{message}");
    assert!(message.contains("Pointed"), "{message}");
}

#[test]
fn tags_must_distinguish_fibers_and_canonical_routes() {
    let duplicate_tag = format!(
        "{BASE}
class Bad<A>(first, second: A -> A -> A)
    extends Pointed<A>(first) as laws, Pointed<A>(second) as laws
{{}}
"
    );
    let message = bad(&duplicate_tag);
    assert!(message.contains("two distinct fibers"), "{message}");
    assert!(message.contains("distinct `as` names"), "{message}");

    let duplicate_fiber = format!(
        "{BASE}
class Bad<A>(op: A -> A -> A)
    extends Pointed<A>(op) as one, Pointed<A>(op) as two
{{}}
"
    );
    let message = bad(&duplicate_fiber);
    assert!(message.contains("same `Pointed` fiber"), "{message}");
    assert!(message.contains("canonical parent would be ambiguous"), "{message}");
}

#[test]
fn a_phantom_operation_index_cannot_distinguish_two_parent_dictionaries() {
    let message = bad(
        r#"
class Phantom<A>(op: A -> A -> A) { point: A }
class Bad<A>(first, second: A -> A -> A)
    extends Phantom<A>(first) as one, Phantom<A>(second) as two
{}
"#,
    );
    assert!(message.contains("index does not occur"), "{message}");
    assert!(message.contains("kernel sees the two fibers as convertible"), "{message}");
}

#[test]
fn a_semiring_shaped_hierarchy_keeps_additive_and_multiplicative_layers() {
    ok(&format!(
        "{BASE}
class Magma<A>(op: A -> A -> A) {{
    seed: A,
    stable: (x, y: A) -> op(x, y) = op(x, y),
}}
class Monoid<A>(op: A -> A -> A) extends Magma<A>(op) {{ unit: A }}
class CommMonoid<A>(op: A -> A -> A) extends Monoid<A>(op) {{ comm_mark: A }}
class Semiring<A>(add, mul: A -> A -> A)
    extends CommMonoid<A>(add) as additive,
            Monoid<A>(mul) as multiplicative
{{ distrib_mark: A }}

instance Semiring<Bit>(left, right) {{
    additive := CommMonoid(Off, λ x y => refl, Off, On),
    multiplicative := Monoid(On, λ x y => refl, On),
    distrib_mark := Off,
}}

class MonoidUse<A>(op: A -> A -> A) extends Monoid<A>(op) as laws {{}}
class MagmaUse<A>(op: A -> A -> A) extends Magma<A>(op) as laws {{}}
instance MonoidUse<Bit>(left) {{}}
instance MonoidUse<Bit>(right) {{}}
instance MagmaUse<Bit>(left) {{}}
instance MagmaUse<Bit>(right) {{}}
theorem add_unit(): Bit::MonoidUse(left).laws.unit = Off {{ refl }}
theorem mul_unit(): Bit::MonoidUse(right).laws.unit = On {{ refl }}
theorem add_seed(): Bit::MagmaUse(left).laws.seed = Off {{ refl }}
theorem mul_seed(): Bit::MagmaUse(right).laws.seed = On {{ refl }}
"
    ));
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
    stable := λ x y => refl,
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

fn first_pointed() -> Pointed<Bit>(left) {{ Pointed(Off, λ x y => refl) }}
fn second_pointed() -> Pointed<Bit>(right) {{ Pointed(On, λ x y => refl) }}
fn both() -> TwoPointed<Bit>(left, right) {{
    TwoPointed(first_pointed(), second_pointed())
}}

theorem first_survives(): both().first_laws.point = Off {{ refl }}
theorem second_survives(): both().second_laws.point = On {{ refl }}
"
    ));
}
