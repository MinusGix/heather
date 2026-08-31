//! Certifying fast-path emission for concrete FunctionIR regions. The renderer
//! is untrusted: every emitted theorem is checked against the actual Heather
//! region, and a deliberately stale model is rejected.

mod support;

use heather_elab::function_ir_cert::{self as cert, AddNode, Port, Region};
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

#[test]
fn function_ir_certificate_generator_suite() {
    let base = support::semantic_test_base(MODULES);
    generated_sum4_certificates_check(&base);
    stale_model_is_rejected(&base);
    eight_node_certificate_checks(&base);
}

#[test]
fn function_ir_v2_certificate_generator_suite() {
    let base = support::semantic_test_base(MODULES);
    generated_sum4_v2_certificates_check(&base);
    stale_v2_model_is_rejected(&base);
    generated_v2_sparse_dag_checks(&base);
    generated_v2_chain_checks(&base, 100);
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
        "import function_ir;\nimport nat;\n{}\n{}\n\
         fn generated_left() → CheckedRegion {{ CheckedRegion(\
             raw := sum4_left_first_raw(), valid := sum4_left_generated_valid()) }}\n\
         fn generated_right() → CheckedRegion {{ CheckedRegion(\
             raw := sum4_right_first_raw(), valid := sum4_right_generated_valid()) }}\n",
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

fn generated_sum4_v2_certificates_check(base: &Elaborator) {
    let left = cert::generate_v2(
        "sum4_left_generated_valid_v2",
        "sum4_left_first_raw()",
        &sum4(true),
    )
    .expect("left sum4 V2 model");
    let right = cert::generate_v2(
        "sum4_right_generated_valid_v2",
        "sum4_right_first_raw()",
        &sum4(false),
    )
    .expect("right sum4 V2 model");
    let source = format!(
        "import function_ir;\nimport list;\nimport logic;\nimport nat;\n{}\n{}",
        left.text, right.text
    );
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_generated_sum4_v2", &source) {
        panic!(
            "generated sum4 V2 certificates did not check: {}",
            error.render(&source)
        );
    }
}

fn stale_model_is_rejected(base: &Elaborator) {
    let mut stale = sum4(true);
    stale.nodes[2].right = 4;
    let emission = cert::generate("dishonest_sum4_valid", "sum4_left_first_raw()", &stale)
        .expect("the stale model is internally valid");
    let source = format!("import function_ir;\nimport nat;\n{}", emission.text);
    let mut e = base.clone();
    match e.elab_module_source("function_ir_stale_certificate", &source) {
        Ok(()) => panic!("a certificate generated from a stale model checked"),
        Err(ElabError::Parse(error)) => panic!("generated text did not parse: {}", error.msg),
        Err(error) => assert!(format!("{error:?}").contains("NotConvertible"), "{error:?}"),
    }
}

fn stale_v2_model_is_rejected(base: &Elaborator) {
    let mut stale = sum4(false);
    stale.nodes[2].left = 5;
    let emission = cert::generate_v2("dishonest_sum4_valid_v2", "sum4_right_first_raw()", &stale)
        .expect("the stale V2 model is internally valid");
    let source = format!(
        "import function_ir;\nimport list;\nimport logic;\nimport nat;\n{}",
        emission.text
    );
    let mut e = base.clone();
    match e.elab_module_source("function_ir_stale_certificate_v2", &source) {
        Ok(()) => panic!("a V2 certificate generated from a stale model checked"),
        Err(ElabError::Parse(error)) => panic!("generated V2 text did not parse: {}", error.msg),
        Err(error) => assert!(format!("{error:?}").contains("NotConvertible"), "{error:?}"),
    }
}

fn eight_node_certificate_checks(base: &Elaborator) {
    let region = chain(8);

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
            "generated 8-node certificate did not check: {}",
            error.render(&source)
        );
    }
}

fn generated_v2_chain_checks(base: &Elaborator, node_count: u64) {
    let region = chain(node_count);
    let raw = cert::render_region_function("generated_v2_chain_raw", &region);
    let proof = cert::generate_v2(
        "generated_v2_chain_valid",
        "generated_v2_chain_raw()",
        &region,
    )
    .expect("V2 chain model");
    let source = format!(
        "import function_ir;\nimport list;\nimport logic;\nimport nat;\n{raw}\n{}",
        proof.text
    );
    let mut e = base.clone();
    if let Err(error) = e.elab_module_source("function_ir_generated_v2_chain", &source) {
        panic!(
            "generated {node_count}-node V2 certificate did not check: {}",
            error.render(&source)
        );
    }
}

fn generated_v2_sparse_dag_checks(base: &Elaborator) {
    // Keep the ordinary regression sparse without exercising the separate
    // large-closed-Nat comparison performance bug.  IDs near `u64::MAX`
    // made this tiny certificate consume roughly 24 GiB, while 10,000 already
    // overflowed the checker thread's stack.
    let top = 100;
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
            AddNode {
                width: 8,
                output: top - 8,
                left: top - 10,
                right: top - 9,
            },
            AddNode {
                width: 64,
                output: 60,
                left: 42,
                right: 7,
            },
            AddNode {
                width: 64,
                output: 59,
                left: 60,
                right: 42,
            },
            AddNode {
                width: 64,
                output: 58,
                left: 60,
                right: 7,
            },
        ],
        outputs: vec![Port { id: 59, width: 64 }, Port { id: 58, width: 64 }],
    };
    let raw = cert::render_region_function("generated_sparse_dag_raw", &region);
    let proof = cert::generate_v2(
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
        region.nodes.push(AddNode {
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
