//! FunctionIR `Add` through typed x86 block selection, encoding layout, and
//! relational execution.

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
const RELATION: &str = include_str!("../../../lib/std/relation.hthr");
const LOCATION: &str = include_str!("../../../lib/std/location.hthr");
const CERTIFIED_LOOKUP: &str = include_str!("../../../lib/std/certified_lookup.hthr");
const X86_64: &str = include_str!("../../../lib/std/arch/x86_64/model.hthr");
const X86_64_BLOCK: &str = include_str!("../../../lib/std/arch/x86_64/block.hthr");
const FUNCTION_IR: &str = include_str!("../../../lib/function_ir.hthr");
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
    ("function_ir_x86", FUNCTION_IR_X86),
];

#[test]
fn function_ir_x86_suite() {
    let base = support::semantic_test_base(MODULES);
    composed_artifact_is_available(&base);
    wrong_canonical_byte_length_is_refused(&base);
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
