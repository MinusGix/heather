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

fn eight_node_certificate_checks(base: &Elaborator) {
    let mut region = Region {
        inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
        nodes: Vec::new(),
        outputs: Vec::new(),
    };
    let mut previous = 1;
    for output in 2..10 {
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

    let raw = cert::render_region_function("generated_chain_raw", &region);
    let proof = cert::generate("generated_chain_valid", "generated_chain_raw()", &region)
        .expect("chain model");
    let source = format!(
        "import function_ir;\nimport list;\nimport nat;\n{raw}\n{}",
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
