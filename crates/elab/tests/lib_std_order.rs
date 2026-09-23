//! `lib/std/order.hthr` — mathematical orders without decidability.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const RELATION: &str = include_str!("../../../lib/std/relation.hthr");
const RELATION_PROPS: &str = include_str!("../../../lib/std/relation_props.hthr");
const ORDER: &str = include_str!("../../../lib/std/order.hthr");

fn elaborated() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("algebra", ALGEBRA),
        ("int", INT),
        ("relation", RELATION),
        ("relation_props", RELATION_PROPS),
        ("order", ORDER),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            let msg = match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            };
            panic!("{name} did not check: {msg}");
        }
    }
    e
}

#[test]
fn the_order_module_checks() {
    elaborated();
}

#[test]
fn linear_instances_supply_every_weaker_layer() {
    let mut e = elaborated();
    let probe = r#"
import order;
import int;
import logic;
import nat;
import relation;
import relation_props;

fn preorder_refl<A: Preorder(R)>(R: A -> A -> Type, x: A) -> R(x, x) {
    A.rel_refl(x)
}

fn partial_antisym<A: PartialOrder(R)>(R: A -> A -> Type, x, y: A,
    hxy: R(x, y), hyx: R(y, x)) -> x = y
{
    A.rel_antisym(x, y, hxy, hyx)
}

fn linear_total<A: LinearOrder(R)>(R: A -> A -> Type, x, y: A)
    -> R(x, y) ∨ R(y, x)
{
    A.rel_total(x, y)
}

theorem nat_parent(n: Nat): nat::Nat::Le(n, n) { preorder_refl(nat::Nat::Le, n) }

theorem int_parent(n: Int): int::Int::Le(n, n) { preorder_refl(int::Int::Le, n) }

theorem nat_child(n, m: Nat): nat::Nat::Le(n, m) ∨ nat::Nat::Le(m, n) {
    linear_total(nat::Nat::Le, n, m)
}
"#;
    e.elab_module_source("order_layers", probe)
        .expect("linear orders must resolve at every declared parent layer");
}

#[test]
fn products_stop_at_partial_order_and_pullbacks_need_injectivity() {
    let mut e = elaborated();
    let probe = r#"
import order;
import int;
import nat;
import pair;
import relation;
import relation_props;

fn nat_int_product_order()
    -> PartialOrder<Pair<Nat, Int>>(ProductOrder(nat::Nat::Le, int::Int::Le))
{
    product_partial_order(nat::Nat::Le, int::Int::Le)
}

theorem product_refl(x: Pair<Nat, Int>):
    ProductOrder(nat::Nat::Le, int::Int::Le, x, x)
{
    nat_int_product_order().rel_refl(x)
}

fn SuccOrder(a, b: Nat) -> Type { Pullback(Succ, nat::Nat::Le, a, b) }

fn succ_injective(x, y: Nat, h: Succ(x) = Succ(y)) -> x = y {
    nat::Nat::succ_inj(x, y, h)
}

fn succ_partial_order() -> PartialOrder<Nat>(SuccOrder) {
    pullback_partial_order(Succ, nat::Nat::Le, succ_injective)
}

theorem succ_order_antisym(x, y: Nat,
    hxy: SuccOrder(x, y), hyx: SuccOrder(y, x)): x = y
{
    succ_partial_order().rel_antisym(x, y, hxy, hyx)
}
"#;
    e.elab_module_source("order_constructions", probe)
        .expect("product and injective-pullback order constructions must check");

    let no_injectivity = r#"
import order;
fn constant(n: Nat) -> Nat { 0 }
fn bad() -> PartialOrder<Nat>(Pullback(constant, nat::Nat::Le)) {
    pullback_partial_order(constant, nat::Nat::Le)
}
"#;
    assert!(
        e.elab_module_source("order_missing_injectivity", no_injectivity).is_err(),
        "partial-order pullback unexpectedly omitted its injectivity evidence"
    );
}
