//! Certifying fast-path emission for concrete FunctionIR regions. The renderer
//! is untrusted: every emitted theorem is checked against the actual Heather
//! region, and a deliberately stale model is rejected.

use crate::support;

use heather_elab::function_ir_cert::{self as cert, Node, Port, Region};
use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/num/int.hthr");
const BITVEC: &str = include_str!("../../../lib/std/bitvec/bitvec.hthr");
const FUNCTION_IR: &str = include_str!("../../../lib/native/function_ir/function_ir.hthr");
const FUNCTION_IR_CERTIFICATES: &str = include_str!("../../../lib/native/function_ir/function_ir_certificates.hthr");

const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("relation", include_str!("../../../lib/std/relation/relation.hthr")),
    ("relation_props", include_str!("../../../lib/std/relation/relation_props.hthr")),
    ("algebra_rel", include_str!("../../../lib/std/algebra/algebra_rel.hthr")),
    ("algebra", ALGEBRA),
    ("morphism", include_str!("../../../lib/std/algebra/morphism.hthr")),
    ("int", INT),
    ("bitvec", BITVEC),
    // A view of a buffer is a window of a list (`list_window`, whose laws are `omega`'s
    // and which says what a window is as a `vector`).
    ("omega", include_str!("../../../lib/std/tactic/omega.hthr")),
    ("vector", include_str!("../../../lib/std/data/vector.hthr")),
    ("list_window", include_str!("../../../lib/std/data/list_window.hthr")),
    // A wide load's word is its bytes read little-endian (`bitvec_bytes`).
    ("bitvec_nat", include_str!("../../../lib/std/bitvec/bitvec_nat.hthr")),
    ("bitvec_resize", include_str!("../../../lib/std/bitvec/bitvec_resize.hthr")),
    ("bitvec_bytes", include_str!("../../../lib/std/bitvec/bitvec_bytes.hthr")),
    ("function_ir", FUNCTION_IR),
];

#[test]
fn function_ir_certificate_generator_suite() {
    let base = support::semantic_test_base(MODULES);
    if std::env::var_os("HEATHER_FUNCTION_IR_SPARSE_ONLY").is_some() {
        generated_sparse_dag_checks(&base);
        return;
    }
    generated_sum4_certificates_check(&base);
    generated_alu_core_checks(&base);
    stale_model_is_rejected(&base);
    generated_sparse_dag_checks(&base);
    generated_chain_checks(&base, 100);
}

fn alu_core() -> Region {
    Region {
        inputs: vec![
            Port { id: 0, width: 8 },
            Port { id: 1, width: 8 },
            Port { id: 10, width: 64 },
            Port { id: 11, width: 64 },
        ],
        nodes: vec![
            Node::Const {
                width: 8,
                output: 2,
                value: 255,
            },
            Node::Add {
                width: 8,
                output: 3,
                left: 0,
                right: 2,
            },
            Node::Sub {
                width: 8,
                output: 4,
                left: 3,
                right: 1,
            },
            Node::BitAnd {
                width: 8,
                output: 5,
                left: 4,
                right: 0,
            },
            Node::BitOr {
                width: 8,
                output: 6,
                left: 5,
                right: 1,
            },
            Node::BitXor {
                width: 8,
                output: 7,
                left: 6,
                right: 2,
            },
            Node::ShiftLeft {
                width: 8,
                output: 8,
                value: 7,
                amount: 2,
            },
            Node::LogicalShiftRight {
                width: 8,
                output: 9,
                value: 8,
                amount: 1,
            },
            Node::ArithmeticShiftRight {
                width: 64,
                output: 12,
                value: 10,
                amount: 3,
            },
            Node::UnsignedLessThan {
                width: 8,
                output: 13,
                left: 9,
                right: 1,
            },
            Node::SignedLessThan {
                width: 64,
                output: 14,
                left: 10,
                right: 11,
            },
            Node::Const {
                width: 64,
                output: 15,
                value: 42,
            },
            Node::Add {
                width: 64,
                output: 16,
                left: 11,
                right: 15,
            },
        ],
        outputs: vec![
            Port { id: 9, width: 8 },
            Port { id: 12, width: 64 },
            Port { id: 13, width: 1 },
            Port { id: 14, width: 1 },
            Port { id: 16, width: 64 },
        ],
    }
}

fn generated_alu_core_checks(base: &Elaborator) {
    let region = alu_core();
    let raw = cert::render_region_function("generated_alu_core_raw", &region);
    let proof = cert::generate(
        "generated_alu_core_valid",
        "generated_alu_core_raw()",
        &region,
    )
    .expect("mixed ALU model");
    let source = format!(
        "import function_ir;\nimport list;\nimport logic;\nimport nat;\n{raw}\n{}",
        proof.text,
    );
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_generated_alu_core", &source) {
        panic!(
            "generated mixed ALU certificate did not check: {}",
            error.render(&source),
        );
    }

    let mut wrong_operand_width = region.clone();
    wrong_operand_width.nodes[3] = Node::BitAnd {
        width: 64,
        output: 5,
        left: 4,
        right: 0,
    };
    let message = cert::generate(
        "wrong_operand_width",
        "generated_alu_core_raw()",
        &wrong_operand_width,
    )
    .unwrap_err();
    assert!(message.contains("not requested width 64"), "{message}");

    let mut wrong_comparison_output = region;
    wrong_comparison_output.outputs[2].width = 8;
    let message = cert::generate(
        "wrong_comparison_output",
        "generated_alu_core_raw()",
        &wrong_comparison_output,
    )
    .unwrap_err();
    assert!(message.contains("not requested width 8"), "{message}");
}

#[test]
fn checked_example_certificates_are_current() {
    let expected = checked_example_certificate_module();
    if std::env::var_os("UPDATE_FUNCTION_IR_CERTIFICATES").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../lib/native/function_ir/function_ir_certificates.hthr");
        std::fs::write(path, &expected).expect("write FunctionIR example certificates");
        return;
    }
    assert_eq!(FUNCTION_IR_CERTIFICATES, expected);
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

/// The generated module, in the same spelling `heather fmt` would leave it in.
///
/// Emitting through the formatter is what keeps generated and hand-written
/// source from disagreeing about whitespace forever: without it, this file is
/// the one thing in `lib/` that `heather fmt --check` can never make clean,
/// because regenerating it would undo the formatting on the next run.
fn checked_example_certificate_module() -> String {
    let add = cert::generate("add64_valid", "add64_raw()", &add64()).expect("add64 model");
    let left = cert::generate(
        "sum4_left_first_valid",
        "sum4_left_first_raw()",
        &sum4(true),
    )
    .expect("left sum4 model");
    let right = cert::generate(
        "sum4_right_first_valid",
        "sum4_right_first_raw()",
        &sum4(false),
    )
    .expect("right sum4 model");
    let body = format!(
        "// Generated by function_ir_cert::checked_example_certificates_are_current.\n\
         // Regenerate with UPDATE_FUNCTION_IR_CERTIFICATES=1 and the focused test.\n\n\
         import function_ir;\n\
         import list;\n\
         import logic;\n\
         import nat;\n\n\
         {}\n{}\n{}\n\
         fn add64_function() → CheckedRegion {{\n\
         \x20   CheckedRegion(raw := add64_raw(), valid := add64_valid())\n\
         }}\n\n\
         fn sum4_left_first_function() → CheckedRegion {{\n\
         \x20   CheckedRegion(raw := sum4_left_first_raw(), valid := sum4_left_first_valid())\n\
         }}\n\n\
         fn sum4_right_first_function() → CheckedRegion {{\n\
         \x20   CheckedRegion(raw := sum4_right_first_raw(), valid := sum4_right_first_valid())\n\
         }}\n",
        add.text, left.text, right.text,
    );
    heather_syntax::fmt::format_source(&body)
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
        inputs: vec![
            Port { id: 0, width: 64 },
            Port { id: 1, width: 64 },
            Port { id: 2, width: 64 },
            Port { id: 3, width: 64 },
        ],
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

fn generated_sum4_certificates_check(base: &Elaborator) {
    let left = cert::generate(
        "sum4_left_generated_valid",
        "sum4_left_first_raw()",
        &sum4(true),
    )
    .expect("left sum4 model");
    let right = cert::generate(
        "sum4_right_generated_valid",
        "sum4_right_first_raw()",
        &sum4(false),
    )
    .expect("right sum4 model");
    let source = format!(
        "import function_ir;\nimport list;\nimport logic;\nimport nat;\n{}\n{}",
        left.text, right.text
    );
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_generated_sum4", &source) {
        panic!(
            "generated sum4 certificates did not check: {}",
            error.render(&source)
        );
    }
}

fn stale_model_is_rejected(base: &Elaborator) {
    let mut stale = sum4(false);
    stale.nodes[2] = Node::Add {
        width: 64,
        output: 6,
        left: 5,
        right: 5,
    };
    let emission = cert::generate("dishonest_sum4_valid", "sum4_right_first_raw()", &stale)
        .expect("the stale model is internally valid");
    let source = format!(
        "import function_ir;\nimport list;\nimport logic;\nimport nat;\n{}",
        emission.text
    );
    let mut e = base.clone();
    match e.elab_module_source("function_ir_stale_certificate", &source) {
        Ok(()) => panic!("a certificate generated from a stale model checked"),
        Err(ElabError::Parse(error)) => panic!("generated text did not parse: {}", error.msg),
        Err(ElabError::Elab { msg, .. }) => assert!(msg.contains("is expected here"), "{msg}"),
        Err(error) => assert!(format!("{error:?}").contains("NotConvertible"), "{error:?}"),
    }
}

fn generated_chain_checks(base: &Elaborator, node_count: u64) {
    let region = chain(node_count);
    let raw = cert::render_region_function("generated_chain_raw", &region);
    let proof = cert::generate("generated_chain_valid", "generated_chain_raw()", &region)
        .expect("chain model");
    let source = format!(
        "import function_ir;\nimport list;\nimport logic;\nimport nat;\n{raw}\n{}",
        proof.text
    );
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_generated_chain", &source) {
        panic!(
            "generated {node_count}-node certificate did not check: {}",
            error.render(&source)
        );
    }
}

fn generated_sparse_dag_checks(base: &Elaborator) {
    // Ordinary runs stay small. The environment override exists specifically
    // for the issue's address-space/time-capped maximum-value probe; do not
    // invoke that probe without the documented process limits.
    let top = std::env::var("HEATHER_FUNCTION_IR_SPARSE_TOP")
        .map(|value| value.parse().expect("numeric sparse top"))
        .unwrap_or(100);
    let region = Region {
        inputs: vec![
            Port {
                id: top - 10,
                width: 8,
            },
            Port {
                id: top - 9,
                width: 8,
            },
            Port { id: 42, width: 64 },
            Port { id: 7, width: 64 },
        ],
        nodes: vec![
            Node::Add {
                width: 8,
                output: top - 8,
                left: top - 10,
                right: top - 9,
            },
            Node::Add {
                width: 64,
                output: 60,
                left: 42,
                right: 7,
            },
            Node::Add {
                width: 64,
                output: 59,
                left: 60,
                right: 42,
            },
            Node::Add {
                width: 64,
                output: 58,
                left: 60,
                right: 7,
            },
        ],
        outputs: vec![Port { id: 59, width: 64 }, Port { id: 58, width: 64 }],
    };
    let raw = cert::render_region_function("generated_sparse_dag_raw", &region);
    let proof = cert::generate(
        "generated_sparse_dag_valid",
        "generated_sparse_dag_raw()",
        &region,
    )
    .expect("sparse mixed-width DAG model");
    let source = format!(
        "import function_ir;\nimport list;\nimport logic;\nimport nat;\n{raw}\n{}",
        proof.text
    );
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_generated_sparse_dag", &source) {
        panic!(
            "generated sparse mixed-width DAG certificate did not check: {}",
            error.render(&source)
        );
    }
}

fn chain(node_count: u64) -> Region {
    let mut region = Region {
        inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        nodes: Vec::new(),
        outputs: Vec::new(),
    };
    let mut previous = 1;
    for output in 2..node_count + 2 {
        region.nodes.push(Node::Add {
            width: 64,
            output,
            left: previous,
            right: 0,
        });
        previous = output;
    }
    region.outputs.push(Port {
        id: previous,
        width: 64,
    });
    region
}
