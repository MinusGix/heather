//! FunctionIR `Add` through typed x86 block selection, encoding layout, and
//! relational execution.

mod support;

use heather_elab::function_ir_cert::{self as cert, Node, Port, Region, StructuredRegion};
use heather_elab::function_ir_x86_lower::{self as lower, Gpr};
use heather_elab::{ElabError, Elaborator, stats};
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
    generic_normal_block_execution_is_available(&base);
    dishonest_normal_block_result_is_refused(&base);
    wrong_canonical_byte_length_is_refused(&base);
}

#[test]
fn generated_mixed_binary_alu_dag_checks() {
    check_generated_mixed_binary_alu_dag(5);
}

#[test]
#[ignore = "20-node FunctionIR/x86 scaling rail; run explicitly"]
fn generated_20_node_mixed_binary_alu_dag_checks() {
    check_generated_mixed_binary_alu_dag(20);
}

fn check_generated_mixed_binary_alu_dag(default_node_count: usize) {
    let base = support::semantic_test_base(&MODULES[..MODULES.len() - 1]);
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
    let mut e = base.clone();
    let report_timings = std::env::var_os("HEATHER_FUNCTION_IR_X86_TIMINGS").is_some();
    if report_timings {
        e.enable_item_timings();
        stats::reset_kernel_ns();
    }
    let started = Instant::now();
    if let Err(error) = e.elab_module_source("function_ir_mixed_alu_x86", &source) {
        panic!(
            "generated mixed binary ALU artifact did not check: {}",
            error.render(&source),
        );
    }
    if report_timings {
        let total = started.elapsed();
        let mut timings = e.take_item_timings();
        let mut categories = std::collections::BTreeMap::<&str, (usize, u64, u64)>::new();
        for item in &timings {
            let category = timing_category(&item.item);
            let entry = categories.entry(category).or_default();
            entry.0 += 1;
            entry.1 += item.total_ns;
            entry.2 += item.kernel_ns;
        }
        timings.sort_by_key(|item| std::cmp::Reverse(item.total_ns));
        eprintln!(
            "mixed ALU total={:.3}s kernel={:.3}s frontend={:.3}s",
            total.as_secs_f64(),
            stats::kernel_ns() as f64 / 1e9,
            (total.as_nanos() as u64).saturating_sub(stats::kernel_ns()) as f64 / 1e9,
        );
        for (category, (count, total_ns, kernel_ns)) in categories {
            eprintln!(
                "mixed ALU category {category} count={count} total={:.3}s kernel={:.3}s frontend={:.3}s",
                total_ns as f64 / 1e9,
                kernel_ns as f64 / 1e9,
                total_ns.saturating_sub(kernel_ns) as f64 / 1e9,
            );
        }
        for item in timings.into_iter().take(12) {
            eprintln!(
                "mixed ALU item {} total={:.3}s kernel={:.3}s frontend={:.3}s",
                item.item,
                item.total_ns as f64 / 1e9,
                item.kernel_ns as f64 / 1e9,
                item.total_ns.saturating_sub(item.kernel_ns) as f64 / 1e9,
            );
        }
    }
}

fn timing_category(item: &str) -> &'static str {
    if item.contains("_execute_from_") {
        "execution"
    } else if item.contains("_graph_") || item.contains("_nodes_") {
        "graph"
    } else if item.contains("_step_") && item.contains("_preserves_") {
        "machine-frame"
    } else if item.contains("_step_") && item.contains("_result") {
        "machine-result"
    } else if item.contains("_after_node_") || item.contains("_before_add_node_") {
        "value-placement"
    } else if item.contains("_state_") || item.contains("_after") {
        "machine-state"
    } else {
        "boundary"
    }
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

#[test]
fn generated_commutative_right_reuse_checks() {
    let base = support::semantic_test_base(&MODULES[..MODULES.len() - 1]);
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
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_commutative_reuse_x86", &source) {
        panic!(
            "generated commutative-reuse artifact did not check: {}",
            error.render(&source),
        );
    }
}

#[test]
fn generated_constant_add_dag_checks() {
    let base = support::semantic_test_base(&MODULES[..MODULES.len() - 1]);
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
    assert!(
        emission
            .text
            .contains("byte_length(): constant_add_x86_bytes().len() = 13")
    );
    assert!(emission.text.contains("next_rip(next_rip(start, 10), 3)"));
    let source = generated_module(&format!("{raw}\n{}", emission.text));
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_constant_add_x86", &source) {
        panic!(
            "generated constant/Add artifact did not check: {}",
            error.render(&source),
        );
    }
}

#[test]
fn generated_mixed_unsigned_comparison_checks() {
    let base = support::semantic_test_base(&MODULES[..MODULES.len() - 1]);
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
    assert!(
        emission
            .text
            .contains("bitvec::zero_extend(1, 63, values(1, 4))")
    );
    let source = generated_module(&format!("{raw}\n{}", emission.text));
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_unsigned_comparison_x86", &source) {
        panic!(
            "generated mixed unsigned-comparison artifact did not check: {}",
            error.render(&source),
        );
    }
}

#[test]
fn generated_signed_comparison_checks() {
    let base = support::semantic_test_base(&MODULES[..MODULES.len() - 1]);
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
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_signed_comparison_x86", &source) {
        panic!(
            "generated signed-comparison artifact did not check: {}",
            error.render(&source),
        );
    }
}

#[test]
fn generated_structured_conditional_checks() {
    let base = support::semantic_test_base(&MODULES[..MODULES.len() - 1]);
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
    assert!(
        emission
            .text
            .contains("ConditionalBlock(condition_register := Rdx")
    );
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
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_structured_conditional_x86", &source) {
        panic!(
            "generated structured conditional artifact did not check: {}",
            error.render(&source),
        );
    }
}

#[test]
fn generated_comparison_prefixed_conditional_checks() {
    let base = support::semantic_test_base(&MODULES[..MODULES.len() - 1]);
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
    let mut e = base.clone();
    if let Err(error) =
        e.elab_module_source("function_ir_comparison_prefixed_conditional_x86", &source)
    {
        panic!(
            "generated comparison-prefixed conditional artifact did not check: {}",
            error.render(&source),
        );
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

fn generic_normal_block_execution_is_available(base: &Elaborator) {
    let mut e = base.clone();
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
    let mut e = base.clone();
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
