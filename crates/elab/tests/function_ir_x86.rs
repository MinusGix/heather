//! FunctionIR `Add` through typed x86 block selection, encoding layout, and
//! relational execution.

mod support;

use heather_elab::function_ir_cert::{AddNode, Port, Region};
use heather_elab::function_ir_x86_lower::{self as lower, Gpr};
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
const RELATION: &str = include_str!("../../../lib/std/relation.hthr");
const LOCATION: &str = include_str!("../../../lib/std/location.hthr");
const CERTIFIED_LOOKUP: &str = include_str!("../../../lib/std/certified_lookup.hthr");
const X86_64: &str = include_str!("../../../lib/std/arch/x86_64/model.hthr");
const X86_64_BLOCK: &str = include_str!("../../../lib/std/arch/x86_64/block.hthr");
const FUNCTION_IR: &str = include_str!("../../../lib/function_ir.hthr");
const FUNCTION_IR_X86_SUPPORT: &str = include_str!("../../../lib/function_ir_x86_support.hthr");
const FUNCTION_IR_X86: &str = include_str!("../../../lib/function_ir_x86.hthr");

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
    ("relation", RELATION),
    ("location", LOCATION),
    ("certified_lookup", CERTIFIED_LOOKUP),
    ("x86_64", X86_64),
    ("x86_64_block", X86_64_BLOCK),
    ("function_ir", FUNCTION_IR),
    ("function_ir_x86_support", FUNCTION_IR_X86_SUPPORT),
    ("function_ir_x86", FUNCTION_IR_X86),
];

#[test]
fn function_ir_x86_suite() {
    let base = support::semantic_test_base(MODULES);
    composed_artifact_is_available(&base);
    wrong_canonical_byte_length_is_refused(&base);
}

#[test]
fn checked_example_x86_lowerings_are_current() {
    let expected = checked_example_lowering_module();
    if std::env::var_os("UPDATE_FUNCTION_IR_X86").is_some() {
        let path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lib/function_ir_x86.hthr");
        std::fs::write(path, &expected).expect("write FunctionIR x86 lowerings");
        return;
    }
    assert_eq!(FUNCTION_IR_X86, expected);
}

#[test]
fn stale_generated_add_dag_lowering_is_rejected() {
    // The control generates its own module; do not pay to check the complete
    // generated golden first merely to prove that a dishonest one fails.
    let base = support::semantic_test_base(&MODULES[..MODULES.len() - 1]);
    stale_lowering_model_is_rejected(&base);
}

#[test]
fn generated_right_first_sum4_checks() {
    let base = support::semantic_test_base(&MODULES[..MODULES.len() - 1]);
    let emission = lower::generate(
        "sum4_right_x86",
        "sum4_right_first_raw()",
        &sum4(false),
        &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx, Gpr::Rcx],
        &[Gpr::Rax, Gpr::R8],
        Gpr::Rax,
    )
    .expect("lower right-first sum4");
    let source = generated_module(&emission.text);
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_right_first_x86", &source) {
        panic!(
            "generated right-first sum4 artifact did not check: {}",
            error.render(&source),
        );
    }
}

fn add64() -> Region {
    Region {
        inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        nodes: vec![AddNode {
            width: 64,
            output: 2,
            left: 0,
            right: 1,
        }],
        outputs: vec![Port { id: 2, width: 64 }],
    }
}

fn sum4(left_first: bool) -> Region {
    let left = AddNode {
        width: 64,
        output: 4,
        left: 0,
        right: 1,
    };
    let right = AddNode {
        width: 64,
        output: 5,
        left: 2,
        right: 3,
    };
    Region {
        inputs: (0..4).map(|id| Port { id, width: 64 }).collect(),
        nodes: if left_first {
            vec![
                left,
                right,
                AddNode {
                    width: 64,
                    output: 6,
                    left: 4,
                    right: 5,
                },
            ]
        } else {
            vec![
                right,
                left,
                AddNode {
                    width: 64,
                    output: 6,
                    left: 4,
                    right: 5,
                },
            ]
        },
        outputs: vec![Port { id: 6, width: 64 }],
    }
}

fn checked_example_lowering_module() -> String {
    let inputs2 = [Gpr::Rdi, Gpr::Rsi];
    let inputs4 = [Gpr::Rdi, Gpr::Rsi, Gpr::Rdx, Gpr::Rcx];
    let temporaries = [Gpr::Rax, Gpr::R8];
    let add = lower::generate(
        "add64_x86",
        "add64_raw()",
        &add64(),
        &inputs2,
        &temporaries,
        Gpr::Rax,
    )
    .expect("lower checked add64");
    let left = lower::generate(
        "sum4_x86",
        "sum4_left_first_raw()",
        &sum4(true),
        &inputs4,
        &temporaries,
        Gpr::Rax,
    )
    .expect("lower checked left-first sum4");
    format!(
        "// Generated by function_ir_x86::checked_example_x86_lowerings_are_current.\n\
         // Regenerate with UPDATE_FUNCTION_IR_X86=1 and the focused test.\n\n\
         import function_ir_x86_support;\n\
         import function_ir;\n\
         import x86_64;\n\
         import x86_64_block;\n\
         import bitvec;\n\
         import list;\n\
         import logic;\n\n{}\n{}",
        add.text, left.text,
    )
}

fn generated_module(body: &str) -> String {
    format!(
        "import function_ir_x86_support;\nimport function_ir;\nimport x86_64;\n\
         import x86_64_block;\nimport bitvec;\nimport list;\nimport logic;\n\n{body}",
    )
}

fn stale_lowering_model_is_rejected(base: &Elaborator) {
    let mut stale = add64();
    stale.nodes[0].output = 3;
    stale.outputs[0].id = 3;
    let emission = lower::generate(
        "dishonest_add64_x86",
        "add64_raw()",
        &stale,
        &[Gpr::Rdi, Gpr::Rsi],
        &[Gpr::Rax],
        Gpr::Rax,
    )
    .expect("the stale model is internally lowerable");
    let source = generated_module(&emission.text);
    let mut e = base.clone();
    match e.elab_module_source("function_ir_stale_x86", &source) {
        Ok(()) => panic!("a lowering certificate generated from a stale model checked"),
        Err(ElabError::Parse(error)) => {
            panic!("stale-model control failed in the parser: {}", error.msg)
        }
        Err(error) => {
            let message = format!("{error:?}");
            assert!(message.contains("NotConvertible"), "{message}");
        }
    }
}

fn composed_artifact_is_available(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import function_ir_x86;
import function_ir;
import x86_64;
import x86_64_block;

theorem selected_add_refines<M>(values: Valuation(), before: MachineState<M>,
    hx: values(64, 0) = read_gpr(Rdi, before.gprs),
    hy: values(64, 1) = read_gpr(Rsi, before.gprs),
    graph: RegionHolds(add64_raw(), values)):
    read_gpr(Rax,
        execute_block_normal(add64_x86_instructions(), before).gprs) =
        values(64, 2)
{
    add64_x86_refines_function_ir(values, before, hx, hy, graph)
}

theorem selected_sum4_refines<M>(values: Valuation(), before: MachineState<M>,
    ha: values(64, 0) = read_gpr(Rdi, before.gprs),
    hb: values(64, 1) = read_gpr(Rsi, before.gprs),
    hc: values(64, 2) = read_gpr(Rdx, before.gprs),
    hd: values(64, 3) = read_gpr(Rcx, before.gprs),
    graph: RegionHolds(sum4_right_first_raw(), values)):
    read_gpr(Rax, sum4_x86_artifact(values, before, ha, hb, hc, hd,
        sum4_schedules_equivalent(values).mpr(graph)).after.gprs) = values(64, 6)
{
    sum4_x86_artifact(values, before, ha, hb, hc, hd,
        sum4_schedules_equivalent(values).mpr(graph)).result_correct
}
"#;
    if let Err(err) = e.elab_module_source("function_ir_x86_acceptance", src) {
        panic!(
            "FunctionIR/x86 composition did not check: {}",
            err.render(src)
        );
    }
}

fn wrong_canonical_byte_length_is_refused(base: &Elaborator) {
    let mut e = base.clone();
    let src = r#"
import function_ir_x86;
import list;

theorem wrong_byte_length(): add64_x86_bytes().len() = 5 { refl }
"#;
    match e.elab_module_source("function_ir_x86_wrong", src) {
        Ok(()) => panic!("wrong x86 canonical byte length checked"),
        Err(ElabError::Parse(err)) => {
            panic!("negative control failed in the parser: {}", err.msg)
        }
        Err(err) => {
            let message = format!("{err:?}");
            assert!(message.contains("NotConvertible"), "{message}");
        }
    }
}
