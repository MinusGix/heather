use heather_elab::function_ir_cert::{Node, Port, Region, StructuredRegion};

pub fn fixture() -> StructuredRegion {
    let word = |id| Port { id, width: 64 };
    let bit = |id| Port { id, width: 1 };
    let arm = |reverse| StructuredRegion::Dataflow(Region {
        inputs: vec![word(1), word(0)],
        nodes: vec![
            Node::Sub { width: 64, output: 3, left: if reverse { 1 } else { 0 }, right: if reverse { 0 } else { 1 } },
            Node::Add { width: 64, output: 4, left: 0, right: 1 },
        ],
        outputs: vec![word(3), word(4)],
    });
    StructuredRegion::Compose {
        prefix: Box::new(StructuredRegion::Sequence {
            prefix: Region { inputs: vec![word(0), word(1)], nodes: vec![Node::UnsignedLessThan { width: 64, output: 2, left: 0, right: 1 }], outputs: vec![bit(2)] },
            continuation: Box::new(StructuredRegion::Conditional {
                inputs: vec![word(0), word(1), bit(2)], condition: 2,
                arguments: vec![word(1), word(0)], outputs: vec![word(3), word(4)],
                when_true: Box::new(arm(true)), when_false: Box::new(arm(false)),
            }),
        }),
        continuation: Box::new(StructuredRegion::Dataflow(Region {
            inputs: vec![word(4), word(0), word(3)],
            nodes: vec![Node::Sub { width: 64, output: 5, left: 4, right: 3 }, Node::UnsignedLessThan { width: 64, output: 6, left: 3, right: 0 }],
            outputs: vec![word(5), bit(6)],
        })),
    }
}
