//! FunctionIR `Add` through typed x86 block selection, encoding layout, and
//! relational execution.
#![allow(dead_code)]

mod support;

use heather_elab::function_ir_cert::{
    self as cert, BlockArgument, ConditionalJoinRegion, ControlRegion, Node, Port, Region,
    StructuredRegion,
};
use heather_elab::function_ir_source;
use heather_elab::function_ir_x86_lower::{self as lower, Gpr};
use heather_elab::{stats, ElabError, Elaborator, SemanticImage};
use heather_syntax::parse_file;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Write as _;
use std::sync::Mutex;
use std::time::Instant;

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
const X86_64_CONTROL_BLOCK: &str = include_str!("../../../lib/std/arch/x86_64/control_block.hthr");
const X86_64_CONTROL_FLOW: &str = include_str!("../../../lib/std/arch/x86_64/control_flow.hthr");
const FUNCTION_IR: &str = include_str!("../../../lib/function_ir.hthr");
const FUNCTION_IR_X86_SUPPORT: &str = include_str!("../../../lib/function_ir_x86_support.hthr");
const FUNCTION_IR_X86: &str = include_str!("../../../lib/function_ir_x86.hthr");

pub(crate) const MODULES: &[(&str, &str)] = &[
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
    ("x86_64_control_block", X86_64_CONTROL_BLOCK),
    ("x86_64_control_flow", X86_64_CONTROL_FLOW),
    ("function_ir", FUNCTION_IR),
    ("function_ir_x86_support", FUNCTION_IR_X86_SUPPORT),
    ("function_ir_x86", FUNCTION_IR_X86),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    // One kernel-checked semantic image per prefix length this binary asks
    // for, so a test function replays the prefix from the process-local image
    // instead of re-reading the stored module images once per call.
    static BASES: RefCell<HashMap<usize, SemanticImage>> = RefCell::new(HashMap::new());
}

/// A fresh elaborator over the first `n` modules of [`MODULES`].
///
/// `SemanticImage::elaborator` forks new attempt, report, policy, metric and
/// gate state around the shared committed prefix, so a caller may mutate the
/// result (the stale-source control does) without touching the memo. The fill
/// is serialized so two libtest workers do not both replay a cold prefix.
pub(crate) fn base_image(n: usize) -> Elaborator {
    let ready = BASES.with(|bases| bases.borrow().get(&n).map(SemanticImage::elaborator));
    if let Some(elab) = ready {
        return elab;
    }
    let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let image = support::semantic_test_base(&MODULES[..n]).semantic_image();
    let elab = image.elaborator();
    BASES.with(|bases| bases.borrow_mut().insert(n, image));
    elab
}

pub fn run_model_tests() {
    function_ir_x86_suite();
}

pub fn run_lowering_tests() {
    checked_example_x86_lowerings_are_current();
    stale_generated_add_dag_lowering_is_rejected();
}

pub fn run_source_tests() {
    source_bitvec_add_reaches_checked_x86_artifact();
    stale_source_function_ir_certificate_is_rejected();
    source_fragment_declines_nested_expressions();
    structured_source_emission_parses_as_a_complete_module();
    elaborated_full_width_constants_reach_checked_x86_artifact();
}

pub fn run_alu_tests() {
    generated_mixed_binary_alu_dag_checks();
    generated_right_first_sum4_checks();
    generated_commutative_right_reuse_checks();
    generated_constant_add_dag_checks();
}

/// The control-flow group is two processes and the dataflow groups one
/// (`function_ir_x86_dataflow`): a binary pays one ~5 s replay of the
/// 18-module prefix, so a group earns its own process only when its
/// generated suffix is comparable — the linked-conditional items here are
/// (2026-09-12, alone on furnace with the gate at the parent's width:
/// control region 9.9 s, conditionals 10.8 s, both about half replay).
/// The 2026-09-04 seven-way split answered suffixes of 20–84 s that sat at
/// the 300 CPU-second rail under the parallel full lane; a killed shard
/// makes every full run INCOMPLETE, so re-split before that recurs.
pub fn run_control_region_tests() {
    generated_control_region_x86_certificate_checks();
}

pub fn run_conditional_tests() {
    generated_structured_conditional_checks();
    generated_comparison_prefixed_conditional_checks();
}

pub fn run_comparison_tests() {
    generated_mixed_unsigned_comparison_checks();
    generated_signed_comparison_checks();
}

fn function_ir_x86_suite() {
    let base = base_image(MODULES.len());
    composed_artifact_is_available(&base);
    generic_normal_block_execution_is_available(&base);
    dishonest_normal_block_result_is_refused(&base);
    wrong_canonical_byte_length_is_refused(&base);
}

fn generated_mixed_binary_alu_dag_checks() {
    check_generated_mixed_binary_alu_dag(5);
}

fn source_bitvec_add_reaches_checked_x86_artifact() {
    const ADD: &str = "fn source_add(left: BitVec(64), right: BitVec(64)) → BitVec(64) {\n\
         \x20   bitvec::add(64, left, right)\n\
         }";
    let declaration = parse_file(ADD)
        .expect("parse source function")
        .items
        .pop()
        .expect("source declaration")
        .into_decl();
    let emission = function_ir_source::generate_x86(
        "source_add_x86",
        &declaration,
        [Gpr::Rdi, Gpr::Rsi],
        &[Gpr::Rax],
        Gpr::Rax,
    )
    .expect("compile initial source fragment");
    assert_eq!(
        emission.instructions,
        vec![
            lower::Instruction::MovRR {
                destination: Gpr::Rax,
                source: Gpr::Rdi
            },
            lower::Instruction::AddRR {
                destination: Gpr::Rax,
                source: Gpr::Rsi
            },
        ],
    );
    assert!(emission.text.contains("source_add_x86_source_artifact"));

    let base = base_image(MODULES.len() - 1);
    let source = generated_module(&format!("{ADD}\n\n{}", emission.text));
    let mut e = base.fork();
    if let Err(error) = e.elab_module_source("source_add_function_ir_x86", &source) {
        panic!(
            "source-to-x86 artifact did not check: {}",
            error.render(&source),
        );
    }
}

fn stale_source_function_ir_certificate_is_rejected() {
    const ADD: &str = "fn source_add(left: BitVec(64), right: BitVec(64)) → BitVec(64) {\n\
         \x20   bitvec::add(64, left, right)\n\
         }";
    let declaration = parse_file(ADD)
        .expect("parse source function")
        .items
        .pop()
        .expect("source declaration")
        .into_decl();
    let frontend = function_ir_source::generate_function_ir("stale_source_add", &declaration)
        .expect("certify source FunctionIR");
    let stale_source = format!(
        "import function_ir;\nimport bitvec;\nimport list;\nimport logic;\nimport nat;\n\n{ADD}\n\n{}",
        frontend.text,
    )
    .replace(
        "bitvec::add(64, left, right)",
        "bitvec::sub(64, left, right)",
    );
    let mut dishonest = base_image(MODULES.len() - 1);
    match dishonest.elab_module_source("stale_source_add_function_ir_x86", &stale_source) {
        Ok(()) => panic!("a source theorem generated from a stale body checked"),
        Err(ElabError::Parse(error)) => {
            panic!("stale-source control failed in the parser: {}", error.msg)
        }
        Err(error) => {
            // Either refusal is the control passing. Since
            // docs/bitvec-width-bounded-defaults-design.md `bitvec::add` and
            // `bitvec::sub` are both ripples that agree on every sum bit and
            // differ only in the column carry, so at width 64 over open
            // operands the kernel spends the budget before it can say
            // `NotConvertible` — `add_and_sub_differ` in
            // crates/elab/tests/lib_std_bitvec.rs pins both reasons.
            let message = format!("{error:?}");
            assert!(
                message.contains("NotConvertible") || message.contains("OutOfFuel"),
                "{message}",
            );
        }
    }
}

fn source_fragment_declines_nested_expressions() {
    let source = "fn nested(left: BitVec(64), right: BitVec(64)) → BitVec(64) {\n\
        bitvec::add(64, bitvec::add(64, left, right), right)\n}";
    let declaration = parse_file(source)
        .expect("parse nested source")
        .items
        .pop()
        .expect("source declaration")
        .into_decl();
    let message = function_ir_source::reflect(&declaration)
        .unwrap_err()
        .to_string();
    assert!(
        message.contains("operands must be source parameters"),
        "{message}"
    );
}

fn structured_source_emission_parses_as_a_complete_module() {
    const SOURCE: &str = "fn source_xor(left: BitVec(64), right: BitVec(64)) → BitVec(64) {\n\
         \x20   bitvec::bxor(64, left, right)\n\
         }";
    let declaration = parse_file(SOURCE)
        .expect("parse source function")
        .items
        .pop()
        .expect("source declaration")
        .into_decl();
    let emission = function_ir_source::generate_x86(
        "source_xor_x86",
        &declaration,
        [Gpr::Rdi, Gpr::Rsi],
        &[Gpr::Rax],
        Gpr::Rax,
    )
    .expect("emit source artifact");
    let module = generated_module(&format!("{SOURCE}\n\n{}", emission.text));
    if let Err(error) = parse_file(&module) {
        panic!("structured emission did not parse: {}", error.msg);
    }
}

pub fn elaborated_source_reflection_builds_a_shared_dag() {
    const SOURCE: &str = r#"
import bitvec;

fn shared_alu(left: BitVec(64), right: BitVec(64)) → BitVec(64) {
    let shared = bitvec::add(64, left, right);
    bitvec::bxor(64, shared,
        bitvec::add(64, shared, bitvec::ofNat(64, 7)))
}

fn unsupported_shift(left: BitVec(64), right: BitVec(64)) → BitVec(64) {
    bitvec::shift_left(64, left, 1)
}
"#;
    let mut elaborator = base_image(MODULES.len() - 1);
    if let Err(error) = elaborator.elab_module_source("shared_alu_source", SOURCE) {
        panic!("shared source did not elaborate: {}", error.render(SOURCE));
    }
    let reflected = function_ir_source::reflect_elaborated(&elaborator, "shared_alu")
        .expect("reflect checked shared expression");
    assert_eq!(
        reflected,
        function_ir_source::reflect_elaborated(&elaborator, "shared_alu")
            .expect("repeat deterministic reflection"),
    );
    assert_eq!(
        reflected.region.nodes,
        vec![
            Node::Add {
                width: 64,
                output: 2,
                left: 0,
                right: 1
            },
            Node::Const {
                width: 64,
                output: 3,
                value: 7
            },
            Node::Add {
                width: 64,
                output: 4,
                left: 2,
                right: 3
            },
            Node::BitXor {
                width: 64,
                output: 5,
                left: 2,
                right: 4
            },
        ],
    );
    assert_eq!(reflected.region.outputs, vec![Port { id: 5, width: 64 }]);
    let emission = function_ir_source::generate_elaborated_function_ir(
        &elaborator,
        "shared_alu_function_ir",
        "shared_alu",
    )
    .expect("emit staged source denotation");
    let module = format!(
        "import function_ir;\nimport bitvec;\nimport list;\nimport logic;\nimport nat;\n\n{}",
        emission.text,
    );
    if let Err(error) = parse_file(&module) {
        panic!("staged source denotation did not parse: {}", error.msg);
    }
    let message = function_ir_source::reflect_elaborated(&elaborator, "unsupported_shift")
        .unwrap_err()
        .to_string();
    assert!(
        message.contains("outside Add/Sub/AND/OR/XOR/ofNat"),
        "{message}"
    );
}

pub fn elaborated_shared_source_reaches_checked_x86_artifact() {
    const SOURCE: &str = r#"
import bitvec;

fn shared_alu(left: BitVec(64), right: BitVec(64)) → BitVec(64) {
    let shared = bitvec::add(64, left, right);
    bitvec::bxor(64, shared,
        bitvec::add(64, shared, bitvec::ofNat(64, 7)))
}
"#;
    let mut source_base = base_image(MODULES.len() - 1);
    if let Err(error) = source_base.elab_module_source("shared_alu_x86_source", SOURCE) {
        panic!("shared source did not elaborate: {}", error.render(SOURCE));
    }
    let emission = function_ir_source::generate_elaborated_x86(
        &source_base,
        "shared_alu_x86",
        "shared_alu",
        [Gpr::Rdi, Gpr::Rsi],
        &[Gpr::Rax, Gpr::R8],
        Gpr::Rax,
    )
    .expect("compile elaborated shared expression");
    assert_eq!(emission.reflected.region.nodes.len(), 4);
    assert_eq!(emission.instructions.len(), 5);
    assert!(emission.instructions.contains(&lower::Instruction::MovRI {
        destination: Gpr::R8,
        immediate: 7,
    }));
    let source = generated_module(&emission.text);
    let mut checker = source_base;
    if let Err(error) = checker.elab_module_source("shared_alu_x86_artifact", &source) {
        panic!(
            "nested source-to-x86 artifact did not check: {}",
            error.render(&source),
        );
    }
}

/// Full-width constants through the whole source route: the reflector reads
/// the literal, the lowering materializes it as `MovRI`, and the certificate
/// checks under ordinary fuel (issues/bitvec-ofnat-large-literals.md). One
/// asymmetric constant pins byte order; one high-bit constant pins the top.
pub fn elaborated_full_width_constants_reach_checked_x86_artifact() {
    const ASYMMETRIC: u64 = 0x0123_4567_89AB_CDEF;
    const HIGH_BIT: u64 = 0x8000_0000_0000_0001;
    let source = format!(
        r#"
import bitvec;

fn wide_constants(left: BitVec(64), right: BitVec(64)) → BitVec(64) {{
    let shared = bitvec::add(64, left, right);
    bitvec::bxor(64,
        bitvec::add(64, shared, bitvec::ofNat(64, {ASYMMETRIC})),
        bitvec::band(64, shared, bitvec::ofNat(64, {HIGH_BIT})))
}}
"#
    );
    let mut source_base = base_image(MODULES.len() - 1);
    if let Err(error) = source_base.elab_module_source("wide_constants_x86_source", &source) {
        panic!("wide-constant source did not elaborate: {}", error.render(&source));
    }
    let reflected = function_ir_source::reflect_elaborated(&source_base, "wide_constants")
        .expect("reflect wide constants");
    let constants: Vec<u64> = reflected
        .region
        .nodes
        .iter()
        .filter_map(|node| match node {
            Node::Const { value, .. } => Some(*value),
            _ => None,
        })
        .collect();
    assert_eq!(constants, vec![ASYMMETRIC, HIGH_BIT]);
    let emission = function_ir_source::generate_elaborated_x86(
        &source_base,
        "wide_constants_x86",
        "wide_constants",
        [Gpr::Rdi, Gpr::Rsi],
        &[Gpr::Rax, Gpr::R8, Gpr::R9],
        Gpr::Rax,
    )
    .expect("compile wide constants");
    for immediate in [ASYMMETRIC, HIGH_BIT] {
        assert!(
            emission
                .instructions
                .iter()
                .any(|instruction| matches!(instruction,
                    lower::Instruction::MovRI { immediate: found, .. } if *found == immediate)),
            "no MovRI materializes {immediate:#x}: {:?}",
            emission.instructions,
        );
    }
    let artifact = generated_module(&emission.text);
    let mut checker = source_base;
    if let Err(error) = checker.elab_module_source("wide_constants_x86_artifact", &artifact) {
        panic!(
            "wide-constant source-to-x86 artifact did not check: {}",
            error.render(&artifact),
        );
    }
}

pub fn elaborated_source_x86_scaling() {
    let node_count = std::env::var("HEATHER_SOURCE_X86_NODES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(20);
    let frontend_only = std::env::var_os("HEATHER_SOURCE_X86_FRONTEND_ONLY").is_some();
    let source = mixed_source_alu(node_count);

    let module_count = if frontend_only { 15 } else { MODULES.len() - 1 };
    let fixture_started = Instant::now();
    let mut source_base = base_image(module_count);
    let fixture_elapsed = fixture_started.elapsed();
    let source_started = Instant::now();
    if let Err(error) = source_base.elab_module_source("scaled_source_alu", &source) {
        panic!("scaled source did not elaborate: {}", error.render(&source));
    }
    let source_elapsed = source_started.elapsed();

    let reflection_started = Instant::now();
    let reflected = function_ir_source::reflect_elaborated(&source_base, "scaled_alu")
        .expect("reflect scaled checked expression");
    let reflection_elapsed = reflection_started.elapsed();
    assert_eq!(reflected.region.nodes.len(), node_count);

    let frontend_generation_started = Instant::now();
    let frontend = function_ir_source::generate_elaborated_function_ir(
        &source_base,
        "scaled_alu_frontend",
        "scaled_alu",
    )
    .expect("certify scaled elaborated expression");
    let frontend_generation_elapsed = frontend_generation_started.elapsed();

    let generation_started = Instant::now();
    let emission = function_ir_source::generate_elaborated_x86(
        &source_base,
        "scaled_alu_x86",
        "scaled_alu",
        [Gpr::Rdi, Gpr::Rsi],
        &[Gpr::Rax, Gpr::R8, Gpr::R9],
        Gpr::Rax,
    )
    .expect("compile scaled elaborated expression");
    let generation_elapsed = generation_started.elapsed();
    assert_eq!(emission.reflected.region.nodes.len(), node_count);

    let generated = generated_module(&emission.text);
    let parse_started = Instant::now();
    if let Err(error) = parse_file(&generated) {
        panic!("scaled generated artifact did not parse: {}", error.msg);
    }
    let parse_elapsed = parse_started.elapsed();
    eprintln!(
        "source x86 n={node_count} source_bytes={} frontend_bytes={} generated_bytes={} instructions={} fixture={:.3}s source_elab={:.3}s reflection={:.3}s frontend_generation={:.3}s x86_generation={:.3}s parse={:.3}s",
        source.len(),
        frontend.text.len(),
        generated.len(),
        emission.instructions.len(),
        fixture_elapsed.as_secs_f64(),
        source_elapsed.as_secs_f64(),
        reflection_elapsed.as_secs_f64(),
        frontend_generation_elapsed.as_secs_f64(),
        generation_elapsed.as_secs_f64(),
        parse_elapsed.as_secs_f64(),
    );

    if frontend_only {
        let frontend_source = format!(
            "import function_ir;\nimport bitvec;\nimport list;\nimport logic;\nimport nat;\n\n{}",
            frontend.text,
        );
        let mut checker = source_base;
        checker.enable_item_timings();
        stats::reset_kernel_ns();
        let check_started = Instant::now();
        if let Err(error) =
            checker.elab_module_source("scaled_alu_frontend_artifact", &frontend_source)
        {
            panic!(
                "scaled source FunctionIR artifact did not check: {}",
                error.render(&frontend_source),
            );
        }
        report_scaling_timings(
            "source frontend",
            check_started.elapsed(),
            checker.take_item_timings(),
        );
        return;
    }

    if std::env::var_os("HEATHER_SOURCE_X86_SKIP_CHECK").is_some() {
        return;
    }

    let mut checker = source_base;
    checker.enable_item_timings();
    stats::reset_kernel_ns();
    let check_started = Instant::now();
    if let Err(error) = checker.elab_module_source("scaled_alu_x86_artifact", &generated) {
        panic!(
            "scaled source-to-x86 artifact did not check: {}",
            error.render(&generated),
        );
    }
    report_scaling_timings(
        "source x86",
        check_started.elapsed(),
        checker.take_item_timings(),
    );
}

fn mixed_source_alu(node_count: usize) -> String {
    assert!(
        node_count > 0,
        "the source scaling rail needs a result node"
    );
    let mut source = String::from(
        "import bitvec;\n\nfn scaled_alu(left: BitVec(64), right: BitVec(64)) → BitVec(64) {\n",
    );
    let mut created = 0usize;
    let mut value_index = 0usize;
    let mut current = String::from("left");
    while created < node_count {
        let operation = ["add", "sub", "band", "bor", "bxor"][value_index % 5];
        let right = if created + 2 <= node_count && value_index % 7 == 6 {
            let constant = format!("constant_{value_index}");
            writeln!(
                source,
                "    let {constant} = bitvec::ofNat(64, {});",
                value_index + 1,
            )
            .unwrap();
            created += 1;
            constant
        } else if value_index % 2 == 0 {
            String::from("right")
        } else {
            String::from("left")
        };
        let next = format!("value_{value_index}");
        writeln!(
            source,
            "    let {next} = bitvec::{operation}(64, {current}, {right});",
        )
        .unwrap();
        current = next;
        created += 1;
        value_index += 1;
    }
    writeln!(source, "    {current}\n}}").unwrap();
    source
}

/// The one dump (`docs/instrumentation-design.md` §4): `HEATHER_TIMINGS`
/// names a file, and stderr is the default because this rail exists to be
/// read. The old hand-rolled category/top-N roll-up is gone — `scope`,
/// `module` and `item` are columns, so a reader groups them however the
/// question asks.
fn report_scaling_timings(
    label: &str,
    _total: std::time::Duration,
    timings: Vec<heather_elab::ItemTiming>,
) {
    let dest = stats::Dest::from_env().unwrap_or(stats::Dest::Stderr);
    eprintln!("timings: {label}");
    let _ = stats::dump(&dest, &timings);
}

pub fn generated_20_node_mixed_binary_alu_dag_checks() {
    check_generated_mixed_binary_alu_dag(20);
}

pub fn generated_50_node_mixed_binary_alu_dag_checks() {
    check_generated_mixed_binary_alu_dag(50);
}

fn check_generated_mixed_binary_alu_dag(default_node_count: usize) {
    let base = base_image(MODULES.len() - 1);
    let node_count = std::env::var("HEATHER_FUNCTION_IR_X86_NODES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default_node_count);
    let region = mixed_binary_alu(node_count);
    let raw = cert::render_region_function("mixed_binary_alu_raw", &region);
    let emission = lower::generate(
        "mixed_binary_alu_x86",
        "mixed_binary_alu_raw()",
        &region,
        &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx, Gpr::Rcx],
        &[Gpr::Rax, Gpr::R8],
        Gpr::Rax,
    )
    .expect("lower mixed binary ALU DAG");
    assert_eq!(emission.lowered.node_plans.len(), node_count);
    assert_eq!(emission.lowered.instructions.len(), node_count + 2);
    let source = generated_module(&format!("{raw}\n{}", emission.text));
    let mut e = base.fork();
    let report_timings = stats::Dest::from_env().is_some();
    let report_value_metrics = std::env::var_os("HEATHER_FUNCTION_IR_X86_VALUE_METRICS").is_some();
    if report_timings {
        e.enable_item_timings();
        stats::reset_kernel_ns();
    }
    if report_value_metrics {
        e.enable_value_metrics();
        // The emission-slot audit rides with the sampler
        // (issues/emission-spelling-chokepoint.md): a row of the miss table
        // and a slot the chokepoint would respell are the same finding seen
        // from two ends, so they are read together.
        e.enable_emission_walk();
    }
    if let Some(path) = std::env::var_os("HEATHER_FUNCTION_IR_X86_DUMP") {
        std::fs::write(path, &source).expect("dump generated module");
    }
    // `HEATHER_FUNCTION_IR_X86_PERF=<file>` records a `perf` profile of the
    // module check alone (the base's replay is most of this binary's wall).
    let mut perf = std::env::var_os("HEATHER_FUNCTION_IR_X86_PERF").map(|out| {
        let child = std::process::Command::new("perf")
            .args(["record", "-F", "499", "-g", "-o"])
            .arg(out)
            .args(["-p", &std::process::id().to_string()])
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .expect("spawn perf");
        std::thread::sleep(std::time::Duration::from_millis(1500));
        child
    });
    let started = Instant::now();
    if let Err(error) = e.elab_module_source("function_ir_mixed_alu_x86", &source) {
        panic!(
            "generated mixed binary ALU artifact did not check: {}",
            error.render(&source),
        );
    }
    if let Some(child) = perf.as_mut() {
        let _ = std::process::Command::new("kill").args(["-INT", &child.id().to_string()]).status();
        let _ = child.wait();
    }
    if report_timings {
        report_scaling_timings("mixed ALU", started.elapsed(), e.take_item_timings());
    }
    if report_value_metrics {
        eprintln!("mixed ALU value metrics: {:?}", e.value_metrics().unwrap());
        // The typing seam's conversion misses by head pair (needs the
        // `value-metrics` feature; empty otherwise).
        eprint!("{}", e.value_conv_miss_report().unwrap());
        let findings = e.take_emission_findings();
        let mut by_site = std::collections::BTreeMap::<(&str, u32), (usize, String, String)>::new();
        for f in &findings {
            let entry = by_site
                .entry((f.slot, f.depth))
                .or_insert_with(|| (0, f.decl.clone(), format!("{} => {}", f.found, f.emitted)));
            entry.0 += 1;
        }
        eprintln!("mixed ALU emission-walk findings: {}", findings.len());
        for ((slot, depth), (count, decl, what)) in by_site {
            eprintln!(
                "mixed ALU emission slot {slot} depth={depth} count={count} first={decl} {what}"
            );
        }
    }
}

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

fn stale_generated_add_dag_lowering_is_rejected() {
    // The control generates its own module; do not pay to check the complete
    // generated golden first merely to prove that a dishonest one fails.
    let base = base_image(MODULES.len() - 1);
    stale_lowering_model_is_rejected(&base);
}

fn generated_right_first_sum4_checks() {
    let base = base_image(MODULES.len() - 1);
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
    let mut e = base.fork();
    if let Err(error) = e.elab_module_source("function_ir_right_first_x86", &source) {
        panic!(
            "generated right-first sum4 artifact did not check: {}",
            error.render(&source),
        );
    }
}

fn generated_commutative_right_reuse_checks() {
    let base = base_image(MODULES.len() - 1);
    let region = commutative_right_reuse();
    let raw = cert::render_region_function("commutative_right_reuse_raw", &region);
    let emission = lower::generate(
        "commutative_right_reuse_x86",
        "commutative_right_reuse_raw()",
        &region,
        &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx],
        &[Gpr::Rax],
        Gpr::Rax,
    )
    .expect("lower DAG by reusing its dying right operand");
    assert_eq!(emission.lowered.instructions.len(), 3);
    let source = generated_module(&format!("{raw}\n{}", emission.text));
    let mut e = base.fork();
    if let Err(error) = e.elab_module_source("function_ir_commutative_reuse_x86", &source) {
        panic!(
            "generated commutative-reuse artifact did not check: {}",
            error.render(&source),
        );
    }
}

fn generated_constant_add_dag_checks() {
    let base = base_image(MODULES.len() - 1);
    let region = constant_add();
    let raw = cert::render_region_function("constant_add_raw", &region);
    let emission = lower::generate(
        "constant_add_x86",
        "constant_add_raw()",
        &region,
        &[Gpr::Rdi],
        &[Gpr::Rax],
        Gpr::Rax,
    )
    .expect("lower constant/Add DAG");
    assert_eq!(emission.lowered.instructions.len(), 2);
    assert!(emission
        .text
        .contains("byte_length():\n    constant_add_x86_bytes().len() = 13"));
    assert!(emission.text.contains("next_rip(next_rip(start, 10), 3)"));
    let source = generated_module(&format!("{raw}\n{}", emission.text));
    let mut e = base.fork();
    if let Err(error) = e.elab_module_source("function_ir_constant_add_x86", &source) {
        panic!(
            "generated constant/Add artifact did not check: {}",
            error.render(&source),
        );
    }
}

fn generated_mixed_unsigned_comparison_checks() {
    let base = base_image(MODULES.len() - 1);
    let region = mixed_unsigned_comparison();
    let raw = cert::render_region_function("mixed_unsigned_comparison_raw", &region);
    let emission = lower::generate(
        "mixed_unsigned_comparison_x86",
        "mixed_unsigned_comparison_raw()",
        &region,
        &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx],
        &[Gpr::Rax, Gpr::Rbx],
        Gpr::Rax,
    )
    .expect("lower mixed Add/unsigned-comparison DAG");
    assert_eq!(emission.lowered.output_width, 1);
    assert!(emission.text.contains("SetBelow(Bl)"));
    assert!(emission
        .text
        .contains("bitvec::zero_extend(1, 63, values(1, 4))"));
    let source = generated_module(&format!("{raw}\n{}", emission.text));
    let mut e = base.fork();
    if let Err(error) = e.elab_module_source("function_ir_unsigned_comparison_x86", &source) {
        panic!(
            "generated mixed unsigned-comparison artifact did not check: {}",
            error.render(&source),
        );
    }
}

fn generated_signed_comparison_checks() {
    let base = base_image(MODULES.len() - 1);
    let region = signed_comparison();
    let raw = cert::render_region_function("signed_comparison_raw", &region);
    let emission = lower::generate(
        "signed_comparison_x86",
        "signed_comparison_raw()",
        &region,
        &[Gpr::Rdi, Gpr::Rsi],
        &[Gpr::Rax],
        Gpr::Rax,
    )
    .expect("lower signed comparison");
    assert!(emission.text.contains("SetLess(Al)"));
    let source = generated_module(&format!("{raw}\n{}", emission.text));
    let mut e = base.fork();
    if let Err(error) = e.elab_module_source("function_ir_signed_comparison_x86", &source) {
        panic!(
            "generated signed-comparison artifact did not check: {}",
            error.render(&source),
        );
    }
}

fn generated_structured_conditional_checks() {
    let base = base_image(MODULES.len() - 1);
    let branch = |node| Region {
        inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        nodes: vec![node],
        outputs: vec![Port { id: 2, width: 64 }],
    };
    let when_true = branch(Node::Add {
        width: 64,
        output: 2,
        left: 0,
        right: 1,
    });
    let when_false = branch(Node::Sub {
        width: 64,
        output: 2,
        left: 0,
        right: 1,
    });
    let region = StructuredRegion::Conditional {
        inputs: vec![
            Port { id: 0, width: 64 },
            Port { id: 1, width: 64 },
            Port { id: 3, width: 1 },
        ],
        condition: 3,
        arguments: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        outputs: vec![Port { id: 2, width: 64 }],
        when_true: Box::new(StructuredRegion::Dataflow(when_true.clone())),
        when_false: Box::new(StructuredRegion::Dataflow(when_false.clone())),
    };
    let emission = lower::generate_conditional(
        "choose_alu_x86",
        "choose_alu_raw()",
        "choose_add_raw()",
        "choose_sub_raw()",
        &region,
        &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx],
        &[Gpr::Rax],
        Gpr::Rax,
    )
    .expect("lower structured conditional");
    assert!(emission
        .text
        .contains("ConditionalBlock(condition_register := Rdx"));
    assert!(emission.text.contains("bit_value_placed_condition"));
    let raw = format!(
        "{}\n{}\n\
         fn choose_alu_raw() → StructuredRegion {{\n\
             Conditional(\n\
                 Ports([Port(id := 0, width := 64), Port(id := 1, width := 64),\n\
                     Port(id := 3, width := 1)]), 3,\n\
                 Ports([Port(id := 0, width := 64), Port(id := 1, width := 64)]),\n\
                 Ports([Port(id := 2, width := 64)]),\n\
                 Dataflow(choose_add_raw()), Dataflow(choose_sub_raw()))\n\
         }}",
        cert::render_region_function("choose_add_raw", &when_true),
        cert::render_region_function("choose_sub_raw", &when_false),
    );
    let source = generated_module(&format!("{raw}\n{}", emission.text));
    let mut e = base.fork();
    if let Err(error) = e.elab_module_source("function_ir_structured_conditional_x86", &source) {
        panic!(
            "generated structured conditional artifact did not check: {}",
            error.render(&source),
        );
    }
}

fn generated_comparison_prefixed_conditional_checks() {
    let base = base_image(MODULES.len() - 1);
    let comparison = Region {
        inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        nodes: vec![Node::UnsignedLessThan {
            width: 64,
            output: 2,
            left: 0,
            right: 1,
        }],
        outputs: vec![Port { id: 2, width: 1 }],
    };
    let branch = |node| Region {
        inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        nodes: vec![node],
        outputs: vec![Port { id: 3, width: 64 }],
    };
    let when_true = branch(Node::Add {
        width: 64,
        output: 3,
        left: 0,
        right: 1,
    });
    let when_false = branch(Node::Sub {
        width: 64,
        output: 3,
        left: 0,
        right: 1,
    });
    let conditional = StructuredRegion::Conditional {
        inputs: vec![
            Port { id: 0, width: 64 },
            Port { id: 1, width: 64 },
            Port { id: 2, width: 1 },
        ],
        condition: 2,
        arguments: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        outputs: vec![Port { id: 3, width: 64 }],
        when_true: Box::new(StructuredRegion::Dataflow(when_true.clone())),
        when_false: Box::new(StructuredRegion::Dataflow(when_false.clone())),
    };
    let region = StructuredRegion::Sequence {
        prefix: comparison.clone(),
        continuation: Box::new(conditional),
    };
    let emission = lower::generate_prefixed_conditional(
        "minmax_alu_x86",
        "minmax_alu_raw()",
        "minmax_compare_raw()",
        "minmax_conditional_raw()",
        "minmax_add_raw()",
        "minmax_sub_raw()",
        &region,
        &[Gpr::Rdi, Gpr::Rsi],
        Gpr::Rdx,
        &[Gpr::Rax],
        Gpr::Rax,
    )
    .expect("lower comparison-prefixed conditional");
    assert!(emission.text.contains("SetBelow(Dl)"));
    assert!(emission.text.contains("PrefixedConditionalBlock"));
    assert!(emission.text.contains("LinkedConditionalBlock"));
    assert!(emission.text.contains("linked_conditional_bytes"));
    assert!(emission.text.contains("bitvec::ofNat(8, 8)"));
    assert!(emission.text.contains("bitvec::ofNat(8, 6)"));
    assert!(emission.text.contains("LinkedConditionalDecodes"));
    assert!(emission.text.contains("LinkedConditionalLayout"));
    assert!(emission.text.contains("ExecuteLinkedConditionalBlock"));
    assert!(emission.text.contains("_linked_bytes().len() = 35"));
    assert!(emission.text.contains("_gprs_congruent"));
    assert!(emission.text.contains("_linked_refines_function_ir"));
    assert!(emission.text.contains("_linked_reaches_join"));
    assert!(emission.text.contains("graph.left"));
    assert!(emission.text.contains("graph.right"));
    let raw = format!(
        "{}\n{}\n{}\n\
         fn minmax_conditional_raw() → StructuredRegion {{\n\
             Conditional(\n\
                 Ports([Port(id := 0, width := 64), Port(id := 1, width := 64),\n\
                     Port(id := 2, width := 1)]), 2,\n\
                 Ports([Port(id := 0, width := 64), Port(id := 1, width := 64)]),\n\
                 Ports([Port(id := 3, width := 64)]),\n\
                 Dataflow(minmax_add_raw()), Dataflow(minmax_sub_raw()))\n\
         }}\n\n\
         fn minmax_alu_raw() → StructuredRegion {{\n\
             Sequence(minmax_compare_raw(), minmax_conditional_raw())\n\
         }}",
        cert::render_region_function("minmax_compare_raw", &comparison),
        cert::render_region_function("minmax_add_raw", &when_true),
        cert::render_region_function("minmax_sub_raw", &when_false),
    );
    let source = generated_module(&format!("{raw}\n{}", emission.text));
    let mut e = base.fork();
    if let Err(error) =
        e.elab_module_source("function_ir_comparison_prefixed_conditional_x86", &source)
    {
        panic!(
            "generated comparison-prefixed conditional artifact did not check: {}",
            error.render(&source),
        );
    }
}

fn generated_control_region_x86_certificate_checks() {
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
    let emission = lower::generate_control_region(
        "max_plus_x86",
        "max_plus_raw()",
        &graph,
        &[Gpr::Rdi, Gpr::Rsi, Gpr::Rdx],
        Gpr::Rcx,
        &[Gpr::R8, Gpr::Rdx],
        &[Gpr::Rax],
        Gpr::Rax,
    )
    .expect("generate complete ControlRegion x86 certificate");
    assert_eq!(
        emission.lowered.when_true_transfer,
        vec![lower::Instruction::MovRR {
            destination: Gpr::R8,
            source: Gpr::Rsi,
        }],
    );
    assert_eq!(
        emission.lowered.when_false_transfer,
        vec![lower::Instruction::MovRR {
            destination: Gpr::R8,
            source: Gpr::Rdi,
        }],
    );
    assert!(emission.text.contains("LinkedControlBlock"));
    assert!(emission.text.contains("_linked_control_bytes().len() = 35"));
    assert!(emission.text.contains("LinkedConditionalDecodes"));
    assert!(emission.text.contains("CanonicalBlockDecodes"));
    assert!(emission.text.contains("ExecuteLinkedControlBlock"));
    assert!(emission.text.contains("ControlRegionHolds"));

    let raw = cert::render_control_region_function("max_plus_raw", &graph)
        .expect("render max_plus ControlRegion");
    let source = generated_module(&format!("{raw}\n{}", emission.text));
    parse_file(&source).expect("generated complete ControlRegion x86 artifact parses");
    let base = base_image(MODULES.len() - 1);
    let mut e = base.fork();
    e.enable_item_timings();
    stats::reset_kernel_ns();
    let started = Instant::now();
    if let Err(error) = e.elab_module_source("function_ir_control_region_x86", &source) {
        report_scaling_timings(
            "control region x86 failure",
            started.elapsed(),
            e.take_item_timings(),
        );
        panic!(
            "generated complete ControlRegion x86 artifact did not check: {}",
            error.render(&source),
        );
    }
    report_scaling_timings(
        "control region x86",
        started.elapsed(),
        e.take_item_timings(),
    );

    let dishonest_source = generated_module(
        "theorem dishonest_edge_destination():\n\
             MovRR(R9, Rsi) = MovRR(R8, Rsi)\n\
         { refl }",
    );
    parse_file(&dishonest_source).expect("dishonest edge certificate parses");
    let mut dishonest = base;
    match dishonest.elab_module_source(
        "dishonest_function_ir_control_region_x86",
        &dishonest_source,
    ) {
        Err(ElabError::Kernel { .. }) => {}
        Err(error) => panic!(
            "dishonest edge destination failed for the wrong reason: {}",
            error.render(&dishonest_source),
        ),
        Ok(()) => panic!("dishonest edge destination unexpectedly checked"),
    }
}

fn add64() -> Region {
    Region {
        inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        nodes: vec![Node::Add {
            width: 64,
            output: 2,
            left: 0,
            right: 1,
        }],
        outputs: vec![Port { id: 2, width: 64 }],
    }
}

fn commutative_right_reuse() -> Region {
    Region {
        inputs: (0..3).map(|id| Port { id, width: 64 }).collect(),
        nodes: vec![
            Node::BitAnd {
                width: 64,
                output: 3,
                left: 1,
                right: 2,
            },
            Node::Add {
                width: 64,
                output: 4,
                left: 0,
                right: 3,
            },
        ],
        outputs: vec![Port { id: 4, width: 64 }],
    }
}

fn constant_add() -> Region {
    Region {
        inputs: vec![Port { id: 0, width: 64 }],
        nodes: vec![
            Node::Const {
                width: 64,
                output: 1,
                value: 1_u64 << 63,
            },
            Node::Add {
                width: 64,
                output: 2,
                left: 0,
                right: 1,
            },
        ],
        outputs: vec![Port { id: 2, width: 64 }],
    }
}

fn mixed_unsigned_comparison() -> Region {
    Region {
        inputs: (0..3).map(|id| Port { id, width: 64 }).collect(),
        nodes: vec![
            Node::Add {
                width: 64,
                output: 3,
                left: 0,
                right: 1,
            },
            Node::UnsignedLessThan {
                width: 64,
                output: 4,
                left: 3,
                right: 2,
            },
        ],
        outputs: vec![Port { id: 4, width: 1 }],
    }
}

fn signed_comparison() -> Region {
    Region {
        inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        nodes: vec![Node::SignedLessThan {
            width: 64,
            output: 2,
            left: 0,
            right: 1,
        }],
        outputs: vec![Port { id: 2, width: 1 }],
    }
}

fn sum4(left_first: bool) -> Region {
    let left = Node::Add {
        width: 64,
        output: 4,
        left: 0,
        right: 1,
    };
    let right = Node::Add {
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
                Node::Add {
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
                Node::Add {
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

fn mixed_binary_alu(node_count: usize) -> Region {
    assert!(node_count >= 5);
    let mut region = Region {
        inputs: (0..4).map(|id| Port { id, width: 64 }).collect(),
        nodes: vec![
            Node::BitAnd {
                width: 64,
                output: 4,
                left: 0,
                right: 1,
            },
            Node::BitXor {
                width: 64,
                output: 5,
                left: 2,
                right: 3,
            },
            Node::Sub {
                width: 64,
                output: 6,
                left: 4,
                right: 5,
            },
            Node::BitOr {
                width: 64,
                output: 7,
                left: 6,
                right: 1,
            },
            Node::Add {
                width: 64,
                output: 8,
                left: 7,
                right: 2,
            },
        ],
        outputs: Vec::new(),
    };
    let mut left = 8;
    for node_index in 5..node_count {
        let output = 4 + node_index as u64;
        let right = ((node_index - 5) % 4) as u64;
        region.nodes.push(match node_index % 5 {
            0 => Node::Add {
                width: 64,
                output,
                left,
                right,
            },
            1 => Node::Sub {
                width: 64,
                output,
                left,
                right,
            },
            2 => Node::BitAnd {
                width: 64,
                output,
                left,
                right,
            },
            3 => Node::BitOr {
                width: 64,
                output,
                left,
                right,
            },
            _ => Node::BitXor {
                width: 64,
                output,
                left,
                right,
            },
        });
        left = output;
    }
    region.outputs.push(Port {
        id: left,
        width: 64,
    });
    region
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
         import x86_64_control_block;\n\
         import x86_64_control_flow;\n\
         import bitvec;\n\
         import list;\n\
         import logic;\n\n{}\n{}",
        add.text, left.text,
    )
}

fn generated_module(body: &str) -> String {
    format!(
        "import function_ir_x86_support;\nimport function_ir;\nimport x86_64;\n\
         import x86_64_block;\nimport x86_64_control_block;\nimport x86_64_control_flow;\nimport bitvec;\nimport list;\nimport logic;\n\n{body}",
    )
}

fn stale_lowering_model_is_rejected(base: &Elaborator) {
    let mut stale = add64();
    stale.nodes[0] = Node::Add {
        width: 64,
        output: 3,
        left: 0,
        right: 1,
    };
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
    let mut e = base.fork();
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
    let mut e = base.fork();
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

fn generic_normal_block_execution_is_available(base: &Elaborator) {
    let mut e = base.fork();
    let src = r#"
import x86_64;
import x86_64_block;
import list;

theorem normal_test_block_is_allowed<M>(before: MachineState<M>):
    ExecuteBlock([TestRR(Rax, Rbx)], before,
        execute_block_normal([TestRR(Rax, Rbx)], before))
{
    canonical_block_executes_normal([TestRR(Rax, Rbx)], before)
}

theorem alternate_test_af_is_still_allowed<M>(before: MachineState<M>):
    ExecuteBlock([TestRR(Rax, Rbx)], before,
        execute_test(Rax, Rbx, 3, before, True))
{
    ⟨execute_test(Rax, Rbx, 3, before, True),
        ⟨Exists(True, refl), refl⟩⟩
}
"#;
    if let Err(err) = e.elab_module_source("x86_64_normal_block_acceptance", src) {
        panic!(
            "generic normal block theorem did not check: {}",
            err.render(src)
        );
    }
}

fn dishonest_normal_block_result_is_refused(base: &Elaborator) {
    let mut e = base.fork();
    let src = r#"
import x86_64;
import x86_64_block;
import list;

theorem dishonest_add_block<M>(before: MachineState<M>):
    ExecuteBlock([AddRR(Rax, Rbx)], before, before)
{
    canonical_block_executes_normal([AddRR(Rax, Rbx)], before)
}
"#;
    match e.elab_module_source("x86_64_normal_block_dishonest", src) {
        Ok(()) => panic!("canonical block theorem admitted a dishonest final state"),
        Err(ElabError::Parse(error)) => {
            panic!(
                "dishonest-result control failed in the parser: {}",
                error.msg
            )
        }
        Err(error) => {
            let message = format!("{error:?}");
            assert!(message.contains("NotConvertible"), "{message}");
        }
    }
}

fn wrong_canonical_byte_length_is_refused(base: &Elaborator) {
    let mut e = base.fork();
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
