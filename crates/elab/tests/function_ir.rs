//! The first future-facing FunctionIR slice: raw stable-ID regions, hybrid
//! validation, graph-relational semantics, and modular `add64`.

mod support;

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const BITVEC: &str = include_str!("../../../lib/std/bitvec.hthr");
const FUNCTION_IR: &str = include_str!("../../../lib/function_ir.hthr");

const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("algebra", ALGEBRA),
    ("int", INT),
    ("bitvec", BITVEC),
    ("function_ir", FUNCTION_IR),
];

fn elaborated() -> Elaborator {
    support::semantic_test_base(MODULES)
}

#[test]
fn function_ir_suite() {
    let base = elaborated();
    checked_add64_is_available(&base);
    sum4_schedules_and_result_are_available(&base);
    invalid_region_is_rejected_by_computation(&base);
    wrong_add64_observation_is_refused(&base);
}

fn checked_add64_is_available(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import function_ir;
import bitvec;

fn selected() → CheckedRegion { add64_function() }

theorem selected_is_valid(): RegionValid(selected().raw) { selected().valid }

theorem add64_result(x, y: BitVec(64), values: Valuation(),
    hx: values(64, 0) = x,
    hy: values(64, 1) = y,
    graph: RegionHolds(selected().raw, values)):
    values(64, 2) = bitvec::add(64, x, y)
{
    add64_denotes(x, y, values, hx, hy, graph)
}
"#;
    if let Err(err) = e.elab_module_source("function_ir_acceptance", src) {
        panic!("FunctionIR acceptance did not check: {}", err.render(src));
    }
}

fn sum4_schedules_and_result_are_available(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import function_ir;
import bitvec;

theorem schedule_swap(values: Valuation(),
    graph: RegionHolds(sum4_left_first_raw(), values)):
    RegionHolds(sum4_right_first_raw(), values)
{
    sum4_schedules_equivalent(values).mp(graph)
}

fn selected_left() → CheckedRegion { sum4_left_first_function() }
fn selected_right() → CheckedRegion { sum4_right_first_function() }

theorem selected_left_is_valid(): RegionValid(selected_left().raw) {
    selected_left().valid
}

theorem selected_right_is_valid(): RegionValid(selected_right().raw) {
    selected_right().valid
}

theorem sum4_result(a, b, c, d: BitVec(64), values: Valuation(),
    ha: values(64, 0) = a,
    hb: values(64, 1) = b,
    hc: values(64, 2) = c,
    hd: values(64, 3) = d,
    graph: RegionHolds(sum4_right_first_raw(), values)):
    values(64, 6) = bitvec::add(64,
        bitvec::add(64, a, b), bitvec::add(64, c, d))
{
    sum4_denotes(a, b, c, d, values, ha, hb, hc, hd,
        sum4_schedules_equivalent(values).mpr(graph))
}
"#;
    if let Err(err) = e.elab_module_source("function_ir_sum4_acceptance", src) {
        panic!(
            "FunctionIR sum4 acceptance did not check: {}",
            err.render(src)
        );
    }
}

fn invalid_region_is_rejected_by_computation(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import function_ir;
import list;
import logic;

fn duplicate_result() → Region {
    Region(
        inputs := sum4_inputs(),
        nodes := [
            Add(width := 64, output := 4, left := 0, right := 1),
            Add(width := 64, output := 4, left := 2, right := 3),
        ],
        outputs := Ports([Port(id := 4, width := 64)]))
}

fn undefined_operand() → Region {
    Region(
        inputs := Ports([Port(id := 0, width := 64)]),
        nodes := [Add(width := 64, output := 1, left := 0, right := 9)],
        outputs := Ports([Port(id := 1, width := 64)]))
}

fn width_mismatch() → Region {
    Region(
        inputs := Ports([
            Port(id := 0, width := 32), Port(id := 1, width := 64)]),
        nodes := [Add(width := 64, output := 2, left := 0, right := 1)],
        outputs := Ports([Port(id := 2, width := 64)]))
}

fn undefined_output() → Region {
    Region(
        inputs := Ports([Port(id := 0, width := 64)]),
        nodes := [],
        outputs := Ports([Port(id := 1, width := 64)]))
}

fn duplicate_input() → Region {
    Region(
        inputs := Ports([
            Port(id := 0, width := 64), Port(id := 0, width := 64)]),
        nodes := [],
        outputs := Ports([]))
}

theorem duplicate_result_fails():
    ¬ValidationSucceeded(validate_region(duplicate_result()))
{
    ·
}

theorem undefined_operand_fails():
    ¬ValidationSucceeded(validate_region(undefined_operand())) { · }

theorem width_mismatch_fails():
    ¬ValidationSucceeded(validate_region(width_mismatch())) { · }

theorem undefined_output_fails():
    ¬ValidationSucceeded(validate_region(undefined_output())) { · }

theorem duplicate_input_fails():
    ¬ValidationSucceeded(validate_region(duplicate_input())) { · }
"#;
    if let Err(err) = e.elab_module_source("function_ir_invalid_region", src) {
        panic!("FunctionIR rejection check did not check: {}", err.render(src));
    }
}

fn wrong_add64_observation_is_refused(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import function_ir;
import bitvec;

theorem wrong_result(x, y: BitVec(64), values: Valuation(),
    hx: values(64, 0) = x,
    hy: values(64, 1) = y,
    graph: RegionHolds(add64_raw(), values)):
    values(64, 2) = x
{
    graph.left
}
"#;
    match e.elab_module_source("function_ir_wrong", src) {
        Ok(()) => panic!("wrong FunctionIR result certificate checked"),
        Err(ElabError::Parse(err)) => {
            panic!("negative control failed in the parser: {}", err.msg)
        }
        Err(err) => {
            let message = format!("{err:?}");
            assert!(message.contains("NotConvertible"), "{message}");
        }
    }
}
