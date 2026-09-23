//! FunctionIR's stable-ID regions, compact validity certificates,
//! graph-relational semantics, and modular `add64`.

mod support;

use heather_elab::function_ir_cert::{
    self as cert, BlockArgument, ConditionalJoinRegion, ControlRegion, Node, Port, Region,
};
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
const FUNCTION_IR_CERTIFICATES: &str = include_str!("../../../lib/function_ir_certificates.hthr");

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
    ("function_ir_certificates", FUNCTION_IR_CERTIFICATES),
];

fn elaborated() -> Elaborator {
    support::semantic_test_base(MODULES)
}

#[test]
fn function_ir_suite() {
    let base = elaborated();
    checked_add64_is_available(&base);
    sum4_schedules_and_result_are_available(&base);
    alu_node_semantics_are_available(&base);
    structured_conditional_is_valid_and_selects_one_branch(&base);
    block_arguments_feed_one_shared_continuation(&base);
    wrong_add64_observation_is_refused(&base);
}

fn block_arguments_feed_one_shared_continuation(base: &Elaborator) {
    let p = |id, width| Port { id, width };
    let branch_inputs = vec![p(0, 64), p(1, 64), p(2, 64)];
    let graph = ControlRegion {
        prefix: Region {
            inputs: branch_inputs.clone(),
            nodes: vec![Node::UnsignedLessThan {
                width: 64,
                output: 3,
                left: 0,
                right: 1,
            }],
            outputs: vec![p(3, 1)],
        },
        join: ConditionalJoinRegion {
            inputs: vec![p(0, 64), p(1, 64), p(2, 64), p(3, 1)],
            condition: 3,
            arguments: branch_inputs.clone(),
            when_true: Region {
                inputs: branch_inputs.clone(),
                nodes: vec![],
                outputs: vec![p(1, 64), p(2, 64)],
            },
            true_arguments: vec![
                BlockArgument {
                    width: 64,
                    value: 1,
                    parameter: 4,
                },
                BlockArgument {
                    width: 64,
                    value: 2,
                    parameter: 5,
                },
            ],
            when_false: Region {
                inputs: branch_inputs,
                nodes: vec![],
                outputs: vec![p(0, 64), p(2, 64)],
            },
            false_arguments: vec![
                BlockArgument {
                    width: 64,
                    value: 0,
                    parameter: 4,
                },
                BlockArgument {
                    width: 64,
                    value: 2,
                    parameter: 5,
                },
            ],
            continuation: Region {
                inputs: vec![p(4, 64), p(5, 64)],
                nodes: vec![Node::Add {
                    width: 64,
                    output: 6,
                    left: 4,
                    right: 5,
                }],
                outputs: vec![p(6, 64)],
            },
        },
    };
    let raw = cert::render_control_region_function("max_plus_raw", &graph)
        .expect("render valid block-argument graph");
    let src = format!(
        r#"
import function_ir;
import bitvec;
import list;
import logic;

{raw}
"#,
    );
    let mut e = base.clone();
    if let Err(err) = e.elab_module_source("function_ir_block_arguments", &src) {
        panic!(
            "FunctionIR block arguments did not check: {}",
            err.render(&src)
        );
    }
}

fn structured_conditional_is_valid_and_selects_one_branch(base: &Elaborator) {
    let add = Region {
        inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        nodes: vec![Node::Add {
            width: 64,
            output: 2,
            left: 0,
            right: 1,
        }],
        outputs: vec![Port { id: 2, width: 64 }],
    };
    let sub = Region {
        inputs: add.inputs.clone(),
        nodes: vec![Node::Sub {
            width: 64,
            output: 2,
            left: 0,
            right: 1,
        }],
        outputs: add.outputs.clone(),
    };
    let comparison = Region {
        inputs: add.inputs.clone(),
        nodes: vec![Node::UnsignedLessThan {
            width: 64,
            output: 3,
            left: 0,
            right: 1,
        }],
        outputs: vec![Port { id: 3, width: 1 }],
    };
    let add_raw = cert::render_region_function("conditional_add_raw", &add);
    let sub_raw = cert::render_region_function("conditional_sub_raw", &sub);
    let comparison_raw = cert::render_region_function("conditional_comparison_raw", &comparison);
    let add_valid = cert::generate("conditional_add_valid", "conditional_add_raw()", &add)
        .expect("add branch certificate");
    let sub_valid = cert::generate("conditional_sub_valid", "conditional_sub_raw()", &sub)
        .expect("sub branch certificate");
    let comparison_valid = cert::generate(
        "conditional_comparison_valid",
        "conditional_comparison_raw()",
        &comparison,
    )
    .expect("comparison prefix certificate");
    let src = format!(
        r#"
import function_ir;
import bitvec;
import list;
import logic;
import nat;

{add_raw}
{sub_raw}
{comparison_raw}
{add_certificate}
{sub_certificate}
{comparison_certificate}

fn conditional_inputs() → Ports {{
    Ports([Port(id := 0, width := 64), Port(id := 1, width := 64),
        Port(id := 3, width := 1)])
}}

fn conditional_arguments() → Ports {{
    Ports([Port(id := 0, width := 64), Port(id := 1, width := 64)])
}}

fn conditional_outputs() → Ports {{ Ports([Port(id := 2, width := 64)]) }}

fn selected_conditional() → StructuredRegion {{
    Conditional(conditional_inputs(), 3, conditional_arguments(),
        conditional_outputs(), Dataflow(conditional_add_raw()),
        Dataflow(conditional_sub_raw()))
}}

fn comparison_prefixed_conditional() → StructuredRegion {{
    Sequence(conditional_comparison_raw(), selected_conditional())
}}

theorem conditional_0_ne_1(): 0 ≠ 1 {{ nat::Nat::zero_ne_succ(0) }}
theorem conditional_0_ne_3(): 0 ≠ 3 {{ nat::Nat::zero_ne_succ(2) }}
theorem conditional_1_ne_3(equal: 1 = 3): False
{{ nat::Nat::zero_ne_succ(1)(nat::Nat::succ_inj(0, 2, equal)) }}

theorem conditional_inputs_unique():
    PortEntriesUnique(conditional_inputs().entries)
{{
    ⟨⟨conditional_0_ne_1(), ⟨conditional_0_ne_3(), trivial⟩⟩,
     ⟨⟨conditional_1_ne_3, trivial⟩, ⟨trivial, trivial⟩⟩⟩
}}

theorem conditional_arguments_unique():
    PortEntriesUnique(conditional_arguments().entries)
{{
    ⟨⟨conditional_0_ne_1(), trivial⟩, ⟨trivial, trivial⟩⟩
}}

theorem conditional_condition_available():
    HasInterfacePort(conditional_inputs().entries, 3, 1)
{{ ⟨| ⟨| ⟨⟨refl, refl⟩ |⟩⟩⟩ }}

theorem conditional_arguments_available():
    InterfaceSubset(conditional_arguments().entries,
        conditional_inputs().entries)
{{ ⟨⟨⟨refl, refl⟩ |⟩, ⟨⟨| ⟨⟨refl, refl⟩ |⟩⟩, trivial⟩⟩ }}

theorem selected_conditional_valid(): StructuredRegionValid(selected_conditional())
{{
    ⟨conditional_inputs_unique(),
     ⟨conditional_arguments_unique(),
      ⟨conditional_condition_available(),
       ⟨conditional_arguments_available(),
        ⟨refl, ⟨refl, ⟨refl, ⟨refl,
            ⟨conditional_add_valid(), conditional_sub_valid()⟩⟩⟩⟩⟩⟩⟩⟩⟩
}}

theorem comparison_continuation_available():
    InterfaceSubset(conditional_inputs().entries,
        conditional_comparison_raw().inputs.entries ++
        conditional_comparison_raw().outputs.entries)
{{
    ⟨⟨⟨refl, refl⟩ |⟩,
     ⟨⟨| ⟨⟨refl, refl⟩ |⟩⟩,
      ⟨⟨| ⟨| ⟨⟨refl, refl⟩ |⟩⟩⟩, trivial⟩⟩⟩
}}

theorem comparison_prefixed_conditional_valid():
    StructuredRegionValid(comparison_prefixed_conditional())
{{
    ⟨conditional_comparison_valid(),
     ⟨comparison_continuation_available(), selected_conditional_valid()⟩⟩
}}

theorem comparison_prefixed_conditional_holds(values: Valuation(),
    comparison: RegionHolds(conditional_comparison_raw(), values),
    continuation: StructuredRegionHolds(values, selected_conditional())):
    StructuredRegionHolds(values, comparison_prefixed_conditional())
{{ ⟨comparison, continuation⟩ }}

theorem conditional_takes_false(values: Valuation(),
    condition_false: @bitvec::BitVec::head_bit(0, values(1, 3)) = False,
    false_graph: RegionHolds(conditional_sub_raw(), values)):
    StructuredRegionHolds(values, selected_conditional())
{{
    j(sym(condition_false),
        λ actual _ => match actual {{
            False => RegionHolds(conditional_sub_raw(), values),
            True => RegionHolds(conditional_add_raw(), values),
        }}, false_graph)
}}

theorem conditional_takes_true(values: Valuation(),
    condition_true: @bitvec::BitVec::head_bit(0, values(1, 3)) = True,
    true_graph: RegionHolds(conditional_add_raw(), values)):
    StructuredRegionHolds(values, selected_conditional())
{{
    j(sym(condition_true),
        λ actual _ => match actual {{
            False => RegionHolds(conditional_sub_raw(), values),
            True => RegionHolds(conditional_add_raw(), values),
        }}, true_graph)
}}
"#,
        add_certificate = add_valid.text,
        sub_certificate = sub_valid.text,
        comparison_certificate = comparison_valid.text,
    );
    let mut e = base.clone();
    if let Err(err) = e.elab_module_source("function_ir_structured_conditional", &src) {
        panic!(
            "structured FunctionIR conditional did not check: {}",
            err.render(&src)
        );
    }
}

fn alu_node_semantics_are_available(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import function_ir;
import bitvec;

theorem const8(values: Valuation(),
    equation: NodeHolds(values, Const(8, 2, 255))):
    values(8, 2) = @bitvec::BitVec::ofNat(8, 255)
{
    equation
}

theorem xor64(values: Valuation(),
    equation: NodeHolds(values, BitXor(64, 2, 0, 1))):
    values(64, 2) = @bitvec::BitVec::bxor(64, values(64, 0), values(64, 1))
{
    equation
}

theorem shift8(values: Valuation(),
    equation: NodeHolds(values, LogicalShiftRight(8, 2, 0, 3))):
    values(8, 2) = @bitvec::BitVec::shift_right(8, values(8, 0), 3)
{
    equation
}

theorem signed_compare64(values: Valuation(),
    equation: NodeHolds(values, SignedLessThan(64, 2, 0, 1))):
    values(1, 2) = bitvec::BitVec::ofBool(@bitvec::BitVec::signed_lt_bit(64,
        values(64, 0), values(64, 1)))
{
    equation
}
"#;
    if let Err(err) = e.elab_module_source("function_ir_alu_semantics", src) {
        panic!(
            "FunctionIR ALU semantics did not check: {}",
            err.render(src)
        );
    }
}

fn checked_add64_is_available(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import function_ir;
import function_ir_certificates;
import bitvec;

fn selected() → CheckedRegion { add64_function() }

theorem selected_is_valid(): RegionValid(selected().raw) { selected().valid }

theorem add64_result(x, y: BitVec(64), values: Valuation(),
    hx: values(64, 0) = x,
    hy: values(64, 1) = y,
    graph: RegionHolds(selected().raw, values)):
    values(64, 2) = @bitvec::BitVec::add(64, x, y)
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
import function_ir_certificates;
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
    values(64, 6) = @bitvec::BitVec::add(64,
        @bitvec::BitVec::add(64, a, b), @bitvec::BitVec::add(64, c, d))
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
