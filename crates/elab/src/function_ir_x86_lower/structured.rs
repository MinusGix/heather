//! Recursive selection plans. These are untrusted proposals; structured_cert
//! checks their physical execution, layout, and frames before publication.

use super::*;
use cert::Port;

/// Stable FunctionIR value IDs, independent of interface ordering.
pub type Placements = BTreeMap<u64, Gpr>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredStructured {
    pub inputs: Placements,
    /// First result, retained for scalar API consumers.
    pub output: (cert::Port, Gpr),
    /// All simultaneous results in the region interface order.
    pub outputs: Vec<(cert::Port, Gpr)>,
    pub clobbered: BTreeSet<Gpr>,
    pub byte_length: usize,
    pub body: StructuredPlan,
}

/// What a planned conditional tests (x86_64_structured_block's `BranchTest`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlannedTest {
    /// TEST r, r on a materialised comparison bit.
    NonZero(Gpr),
    /// CMP left, right on the region's comparison of `left_port` with
    /// `right_port`, whose bit is never materialised
    /// (docs/structured-lowering-code-size-design.md §2.2).
    Compare { left: Gpr, right: Gpr, operation: ComparisonOperation, left_port: u64, right_port: u64 },
}

impl PlannedTest {
    /// The Jcc condition code of the edge over the true arm: the test's
    /// failure (`branch_skip`), as the manual numbers it.
    pub fn skip_code(self) -> u8 {
        match self {
            PlannedTest::NonZero(_) => 0x4,
            PlannedTest::Compare { operation: ComparisonOperation::UnsignedLessThan, .. } => 0x3,
            PlannedTest::Compare { operation: ComparisonOperation::SignedLessThan, .. } => 0xd,
        }
    }
    /// The test instruction: TEST r, r or CMP left, right.
    pub fn instruction(self) -> Option<Instruction> {
        match self {
            PlannedTest::NonZero(_) => None,
            PlannedTest::Compare { left, right, .. } => Some(Instruction::CmpRR { left, right }),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StructuredPlan {
    Dataflow(LoweredDag),
    MultiDataflow(Vec<(Region, LoweredDag)>),
    Compose { prefix: Box<LoweredStructured>, continuation: Box<LoweredStructured> },
    Sequence {
        prefix: LoweredDag,
        continuation: Box<LoweredStructured>,
    },
    /// A `Sequence` whose comparison moved into the branch after it: the
    /// prefix computes the comparison's one computed operand, and the
    /// continuation is a `Conditional` testing `Compare`. Its region is the
    /// `Sequence` it replaces.
    FusedSequence {
        operands: LoweredDag,
        continuation: Box<LoweredStructured>,
    },
    Conditional {
        test: PlannedTest,
        when_true: Box<LoweredStructured>,
        when_false: Box<LoweredStructured>,
        /// Short: rel8 JZ/JMP. Near: rel32, when either arm is past rel8's
        /// reach (docs/native-wc-design.md §4.5).
        false_displacement: u32,
        join_displacement: u32,
        near: bool,
    },
}

/// Compatibility entry point for a single result. Leaf instruction widths
/// retain their existing restrictions; no spills or edge copies are implicit.
pub fn lower_structured(
    region: &StructuredRegion,
    inputs: &Placements,
    temporaries: &[Gpr],
    requested_output: Gpr,
) -> Result<LoweredStructured, LoweringError> {
    cert::validate_structured_region(region).map_err(LoweringError::InvalidStructuredRegion)?;
    if region.outputs().len() != 1 { return Err(LoweringError::OutputCount(region.outputs().len())); }
    lower_structured_results(region, inputs, temporaries, &Placements::from([(region.outputs()[0].id, requested_output)]))
}

/// Explicit, simultaneous result placements. Results must occupy distinct
/// scratch registers; both arms of a join use this same interface.
pub fn lower_structured_results(
    region: &StructuredRegion, inputs: &Placements, temporaries: &[Gpr], outputs: &Placements,
) -> Result<LoweredStructured, LoweringError> {
    cert::validate_structured_region(region).map_err(LoweringError::InvalidStructuredRegion)?;
    select(region, inputs, temporaries, outputs, "root")
}

fn select(
    region: &StructuredRegion,
    inputs: &Placements,
    temporaries: &[Gpr],
    requested: &Placements,
    path: &str,
) -> Result<LoweredStructured, LoweringError> {
    select_here(region, inputs, temporaries, requested, path).map_err(|error| {
        if matches!(error, LoweringError::StructuredPath { .. }) { error }
        else { LoweringError::StructuredPath { path: path.into(), reason: Box::new(error) } }
    })
}

fn select_here(
    region: &StructuredRegion,
    inputs: &Placements,
    temporaries: &[Gpr],
    requested: &Placements,
    path: &str,
) -> Result<LoweredStructured, LoweringError> {
    if inputs.len() != region.inputs().len() {
        return Err(LoweringError::InputPlacementCount {
            inputs: region.inputs().len(), registers: inputs.len(),
        });
    }
    let registers = region.inputs().iter().map(|port| {
        inputs.get(&port.id).copied().ok_or(LoweringError::UndefinedValue(port.id))
    }).collect::<Result<Vec<_>, _>>()?;
    let mut assigned = BTreeSet::new();
    for &register in &registers {
        if !assigned.insert(register) { return Err(LoweringError::DuplicateRegister(register)); }
    }
    let mut available = BTreeSet::new();
    for &register in temporaries {
        if assigned.contains(&register) { return Err(LoweringError::InputOverlapsTemporary(register)); }
        if !available.insert(register) { return Err(LoweringError::DuplicateRegister(register)); }
    }
    if requested.len() != region.outputs().len() || requested.is_empty() {
        return Err(LoweringError::OutputPlacementCount { outputs: region.outputs().len(), registers: requested.len() });
    }
    let mut destinations = BTreeSet::new();
    let outputs = region.outputs().iter().map(|port| {
        let register = *requested.get(&port.id).ok_or(LoweringError::UndefinedValue(port.id))?;
        if !available.contains(&register) { return Err(LoweringError::OutputRegisterUnavailable(register)); }
        if !destinations.insert(register) { return Err(LoweringError::DuplicateRegister(register)); }
        Ok((*port, register))
    }).collect::<Result<Vec<_>, LoweringError>>()?;
    let output = outputs[0];
    let requested_output = output.1;
    let (body, clobbered, byte_length) = match region {
        StructuredRegion::Compose { prefix, continuation } => {
            let mut prefix_outputs = Placements::new();
            let mut free = temporaries.iter().copied().filter(|r| !destinations.contains(r)).collect::<Vec<_>>();
            for port in prefix.outputs() {
                // A comparison bit needs a byte register; a wide value leaves
                // those to the comparisons downstream when it can.
                let index = if port.width == 1 { free.iter().position(|r| LowByteGpr::from_gpr(*r).is_some()) }
                    else { free.iter().position(|r| LowByteGpr::from_gpr(*r).is_none()).or_else(|| (!free.is_empty()).then_some(0)) }
                    .ok_or(LoweringError::RegisterPressure { node_index: 0, live_temporaries: inputs.len() + prefix_outputs.len() })?;
                prefix_outputs.insert(port.id, free.remove(index));
            }
            let first = select(prefix, inputs, temporaries, &prefix_outputs, &format!("{path}.prefix"))?;
            let mut carried = inputs.clone();
            carried.extend(prefix_outputs);
            let next_inputs = continuation.inputs().iter().map(|port| {
                carried.get(&port.id).copied().map(|r| (port.id, r)).ok_or(LoweringError::UndefinedValue(port.id))
            }).collect::<Result<Placements, _>>()?;
            let scratch = temporaries.iter().copied().filter(|r| !next_inputs.values().any(|v| v == r)).collect::<Vec<_>>();
            let next = select(continuation, &next_inputs, &scratch, requested, &format!("{path}.continuation"))?;
            let clobbered = first.clobbered.union(&next.clobbered).copied().collect();
            let length = first.byte_length + next.byte_length;
            (StructuredPlan::Compose { prefix: Box::new(first), continuation: Box::new(next) }, clobbered, length)
        }
        StructuredRegion::Dataflow(region) if outputs.len() > 1 => {
            // Each result is a dependency slice of the DAG. Protect completed
            // result registers while selecting later slices. Shared work may
            // be recomputed, but no output can be silently overwritten.
            let mut scratch = temporaries.to_vec();
            let mut parts = Vec::new();
            let mut clobbered = BTreeSet::new();
            let mut length = 0;
            for &(port, register) in &outputs {
                let mut needed = BTreeSet::from([port.id]);
                let mut nodes = Vec::new();
                for (index, node) in region.nodes.iter().enumerate().rev() {
                    if !needed.contains(&node.output().id) { continue; }
                    match selected_node(*node, index)? {
                        SelectedNode::Binary(n) => { needed.insert(n.left); needed.insert(n.right); }
                        SelectedNode::Comparison(n) => { needed.insert(n.left); needed.insert(n.right); }
                        SelectedNode::Constant(_) => {}
                    }
                    nodes.push(*node);
                }
                nodes.reverse();
                let slice = Region { inputs: region.inputs.clone(), nodes, outputs: vec![port] };
                let dag = lower_dag(&slice, &registers, &scratch, register)?;
                length += dag.instructions.iter().map(|i| i.canonical_length()).sum::<usize>();
                clobbered.extend(&dag.clobbered);
                parts.push((slice, dag));
                scratch.retain(|r| *r != register);
            }
            (StructuredPlan::MultiDataflow(parts), clobbered, length)
        }
        StructuredRegion::Dataflow(region) => {
            let dag = lower_dag(region, &registers, temporaries, requested_output)?;
            let length = dag.instructions.iter().map(|i| i.canonical_length()).sum();
            let clobbered = dag.clobbered.clone();
            (StructuredPlan::Dataflow(dag), clobbered, length)
        }
        StructuredRegion::Sequence { prefix, continuation } if fusable(prefix, continuation)?.is_some() => {
            let fused = fusable(prefix, continuation)?.unwrap();
            let StructuredRegion::Conditional { arguments, when_true, when_false, .. } = &**continuation else { unreachable!("fusable checked") };
            let candidates = || temporaries.iter().copied().filter(|r| !destinations.contains(r));
            let operand_register = candidates().find(|r| LowByteGpr::from_gpr(*r).is_none()).or_else(|| candidates().next())
                .ok_or(LoweringError::RegisterPressure { node_index: 0, live_temporaries: inputs.len() })?;
            let operands = Region { inputs: prefix.inputs.clone(), nodes: cone(prefix, fused.computed.id)?, outputs: vec![fused.computed] };
            let dag = lower_dag(&operands, &registers, temporaries, operand_register)?;
            let mut carried = inputs.clone();
            carried.insert(fused.computed.id, dag.output_register);
            let place = |id: u64| carried.get(&id).copied().ok_or(LoweringError::UndefinedValue(id));
            let compare = fused.compare;
            let test = PlannedTest::Compare { left: place(compare.left)?, right: place(compare.right)?, operation: compare.operation,
                left_port: compare.left, right_port: compare.right };
            let next_inputs = fused_inputs(&fused, arguments).iter().map(|port| Ok((port.id, place(port.id)?)))
                .collect::<Result<Placements, LoweringError>>()?;
            let next_temporaries = temporaries.iter().copied()
                .filter(|r| !next_inputs.values().any(|placed| placed == r)).collect::<Vec<_>>();
            let (body, clobbered, length) = branch(test, arguments, when_true, when_false, &next_inputs, &next_temporaries, requested, &format!("{path}.continuation"))?;
            let next_outputs = continuation.outputs().iter().map(|port| (*port, requested[&port.id])).collect::<Vec<_>>();
            let next = LoweredStructured { inputs: next_inputs, output: next_outputs[0], outputs: next_outputs, clobbered, byte_length: length, body };
            let clobbered = dag.clobbered.union(&next.clobbered).copied().collect();
            let length = dag.instructions.iter().map(|i| i.canonical_length()).sum::<usize>() + next.byte_length;
            (StructuredPlan::FusedSequence { operands: dag, continuation: Box::new(next) }, clobbered, length)
        }
        StructuredRegion::Sequence { prefix, continuation } => {
            if prefix.outputs.len() != 1 {
                return select_here(&StructuredRegion::Compose { prefix: Box::new(StructuredRegion::Dataflow(prefix.clone())), continuation: continuation.clone() }, inputs, temporaries, requested, path);
            }
            // Reserve the final result register for the continuation. A low
            // byte register is preferred for a materialized comparison bit.
            let candidates = || temporaries.iter().copied().filter(|r| !destinations.contains(r));
            let prefix_register = if prefix.outputs[0].width == 1 { candidates().find(|r| LowByteGpr::from_gpr(*r).is_some()) }
                else { candidates().find(|r| LowByteGpr::from_gpr(*r).is_none()).or_else(|| candidates().next()) }
                .ok_or(LoweringError::RegisterPressure { node_index: 0, live_temporaries: inputs.len() })?;
            let dag = lower_dag(prefix, &registers, temporaries, prefix_register)?;
            let mut carried = inputs.clone();
            carried.insert(dag.output_id, dag.output_register);
            let next_inputs = continuation.inputs().iter().map(|port| {
                carried.get(&port.id).copied().map(|r| (port.id, r))
                    .ok_or(LoweringError::UndefinedValue(port.id))
            }).collect::<Result<Placements, _>>()?;
            let next_temporaries = temporaries.iter().copied()
                .filter(|r| !next_inputs.values().any(|placed| placed == r)).collect::<Vec<_>>();
            let next = select(continuation, &next_inputs, &next_temporaries,
                requested, &format!("{path}.continuation"))?;
            let clobbered = dag.clobbered.union(&next.clobbered).copied().collect();
            let length = dag.instructions.iter().map(|i| i.canonical_length()).sum::<usize>() + next.byte_length;
            (StructuredPlan::Sequence { prefix: dag, continuation: Box::new(next) }, clobbered, length)
        }
        StructuredRegion::Conditional { condition, arguments, when_true, when_false, .. } =>
            branch(PlannedTest::NonZero(inputs[condition]), arguments, when_true, when_false, inputs, temporaries, requested, path)?,
    };
    Ok(LoweredStructured { inputs: inputs.clone(), output, outputs, clobbered, byte_length, body })
}

/// A conditional's two arms and its jumps, over whichever test decides it.
#[allow(clippy::too_many_arguments)]
fn branch(
    test: PlannedTest, arguments: &[Port], when_true: &StructuredRegion, when_false: &StructuredRegion,
    inputs: &Placements, temporaries: &[Gpr], requested: &Placements, path: &str,
) -> Result<(StructuredPlan, BTreeSet<Gpr>, usize), LoweringError> {
    let branch_inputs = arguments.iter().map(|port| (port.id, inputs[&port.id])).collect();
    // Preserve every inherited register across the branch. A caller
    // may still carry a selector omitted from the branch interface.
    let scratch = temporaries.to_vec();
    let yes = select(when_true, &branch_inputs, &scratch, requested, &format!("{path}.true"))?;
    let no = select(when_false, &branch_inputs, &scratch, requested, &format!("{path}.false"))?;
    // TEST r,r or CMP l,r; Jcc false; true; JMP join; false. Short jumps
    // while both distances fit rel8, near (Jcc rel32, JMP rel32) otherwise.
    let near = yes.byte_length + 2 > 127 || no.byte_length > 127;
    let (jz_length, jmp_length) = if near { (6, 5) } else { (2, 2) };
    let false_distance = yes.byte_length + jmp_length;
    let join_distance = no.byte_length;
    for bytes in [false_distance, join_distance] {
        if bytes > i32::MAX as usize { return Err(LoweringError::ShortBranchOutOfRange { bytes }); }
    }
    let length = 3 + jz_length + yes.byte_length + jmp_length + no.byte_length;
    let clobbered = yes.clobbered.union(&no.clobbered).copied().collect();
    Ok((StructuredPlan::Conditional {
        test, when_true: Box::new(yes), when_false: Box::new(no),
        false_displacement: false_distance as u32, join_displacement: join_distance as u32, near,
    }, clobbered, length))
}

/// A `Sequence` whose prefix ends in a 64-bit comparison that only the
/// `Conditional` after it reads, with exactly one operand computed by the
/// prefix: the comparison can move into the branch
/// (docs/structured-lowering-code-size-design.md §2.2). Otherwise the bit is
/// materialised and tested, which stays the rule for every other shape.
pub(crate) struct Fusable {
    pub(crate) compare: ComparisonNode,
    pub(crate) computed: Port,
}

pub(crate) fn fusable(prefix: &Region, continuation: &StructuredRegion) -> Result<Option<Fusable>, LoweringError> {
    let StructuredRegion::Conditional { condition, arguments, .. } = continuation else { return Ok(None) };
    if prefix.outputs.first().map(|port| port.id) != Some(*condition) || arguments.iter().any(|port| port.id == *condition) {
        return Ok(None);
    }
    let mut compare = None;
    for (index, node) in prefix.nodes.iter().enumerate() {
        match selected_node(*node, index)? {
            SelectedNode::Comparison(n) if n.output == *condition => compare = Some(n),
            SelectedNode::Comparison(n) if n.left == *condition || n.right == *condition => return Ok(None),
            SelectedNode::Binary(n) if n.left == *condition || n.right == *condition => return Ok(None),
            _ => {}
        }
    }
    let Some(compare) = compare else { return Ok(None) };
    if compare.operand_width != 64 { return Ok(None); }
    let input = |id: u64| prefix.inputs.iter().any(|port| port.id == id);
    let computed: BTreeSet<u64> = [compare.left, compare.right].into_iter().filter(|id| !input(*id)).collect();
    if computed.len() != 1 { return Ok(None); }
    let computed = Port { id: *computed.iter().next().unwrap(), width: 64 };
    // The computed operand may also be carried to the arms, as a shared
    // constant is; nothing else leaves the prefix.
    if prefix.outputs[1..].iter().any(|port| *port != computed) { return Ok(None); }
    Ok(Some(Fusable { compare, computed }))
}

/// A constant the fused comparison loads that an arm loads again: the arms
/// take the comparison's register as an argument instead of a load of their
/// own (docs/structured-lowering-code-size-design.md §7.1, V5). Only both
/// arms being dataflow is rewritten, and a constant an arm returns as it is
/// stays its own.
pub(crate) fn share_compared_constant(prefix: &mut Region, branch: &mut StructuredRegion) -> Result<(), LoweringError> {
    let Some(fused) = fusable(prefix, branch)? else { return Ok(()) };
    if prefix.outputs.len() != 1 { return Ok(()); }
    let [Node::Const { width, value, .. }] = cone(prefix, fused.computed.id)?[..] else { return Ok(()) };
    let StructuredRegion::Conditional { inputs, arguments, when_true, when_false, .. } = branch else { return Ok(()) };
    let (StructuredRegion::Dataflow(yes), StructuredRegion::Dataflow(no)) = (&mut **when_true, &mut **when_false) else { return Ok(()) };
    let again = |arm: &Region| arm.nodes.iter().find_map(|node| match *node {
        Node::Const { width: w, value: v, output } if (w, v) == (width, value) && !arm.outputs.iter().any(|port| port.id == output) => Some(output),
        _ => None,
    });
    if again(yes).is_none() && again(no).is_none() { return Ok(()); }
    for arm in [yes, no] {
        if let Some(load) = again(arm) {
            arm.nodes.retain(|node| node.output().id != load);
            for node in &mut arm.nodes { *node = node.renamed(load, fused.computed.id); }
        }
        arm.inputs.push(fused.computed);
    }
    prefix.outputs.push(fused.computed);
    inputs.push(fused.computed);
    arguments.push(fused.computed);
    Ok(())
}

/// The fused branch's interface: its comparison's operands, then the arms'
/// arguments, each once.
pub(crate) fn fused_inputs(fused: &Fusable, arguments: &[Port]) -> Vec<Port> {
    let mut ports = Vec::new();
    for port in [Port { id: fused.compare.left, width: 64 }, Port { id: fused.compare.right, width: 64 }].into_iter().chain(arguments.iter().copied()) {
        if !ports.contains(&port) { ports.push(port); }
    }
    ports
}

/// The nodes `wanted` depends on, in order.
pub(crate) fn cone(region: &Region, wanted: u64) -> Result<Vec<Node>, LoweringError> {
    let mut needed = BTreeSet::from([wanted]);
    let mut nodes = Vec::new();
    for (index, node) in region.nodes.iter().enumerate().rev() {
        if !needed.contains(&node.output().id) { continue; }
        match selected_node(*node, index)? {
            SelectedNode::Binary(n) => { needed.insert(n.left); needed.insert(n.right); }
            SelectedNode::Comparison(n) => { needed.insert(n.left); needed.insert(n.right); }
            SelectedNode::Constant(_) => {}
        }
        nodes.push(*node);
    }
    nodes.reverse();
    Ok(nodes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cert::Node;

    // The branch must be the comparison's only reader, at 64 bits, with one
    // operand the prefix computes; anything else keeps the bit materialised.
    #[test]
    fn only_a_comparison_its_branch_alone_reads_is_fused() {
        let word = |id| Port { id, width: 64 };
        let bit = Port { id: 3, width: 1 };
        let prefix = |width| Region { inputs: vec![word(0)], nodes: vec![Node::Const { width, output: 2, value: 16 },
            Node::UnsignedLessThan { width, output: 3, left: 0, right: 2 }], outputs: vec![bit] };
        let arm = |inputs: Vec<Port>| Box::new(StructuredRegion::Dataflow(Region { inputs, nodes: vec![Node::Const { width: 64, output: 4, value: 0 }], outputs: vec![word(4)] }));
        let branch = |arguments: Vec<Port>| {
            let mut inputs = vec![bit];
            inputs.extend(arguments.iter().copied().filter(|port| *port != bit));
            StructuredRegion::Conditional { inputs, condition: 3, arguments: arguments.clone(), outputs: vec![word(4)],
                when_true: arm(arguments.clone()), when_false: arm(arguments) }
        };
        assert!(fusable(&prefix(64), &branch(vec![word(0)])).unwrap().is_some());
        assert!(fusable(&prefix(64), &branch(vec![word(0), bit])).unwrap().is_none(), "the arms read the bit");
        assert!(fusable(&prefix(32), &branch(vec![word(0)])).unwrap().is_none(), "a narrow comparison");
    }

    // Only a constant the fused comparison loads, loaded again by an arm
    // that computes with it, moves into the arms' arguments.
    #[test]
    fn only_a_constant_the_fused_comparison_loads_is_carried() {
        let word = |id| Port { id, width: 64 };
        let bit = Port { id: 3, width: 1 };
        let prefix = |width| Region { inputs: vec![word(0)], nodes: vec![Node::Const { width, output: 2, value: 16 },
            Node::UnsignedLessThan { width, output: 3, left: 0, right: 2 }], outputs: vec![bit] };
        let reads = |value| StructuredRegion::Dataflow(Region { inputs: vec![word(0)], nodes: vec![Node::Const { width: 64, output: 4, value },
            Node::Sub { width: 64, output: 5, left: 0, right: 4 }], outputs: vec![word(5)] });
        let returns = StructuredRegion::Dataflow(Region { inputs: vec![word(0)], nodes: vec![Node::Const { width: 64, output: 5, value: 16 }], outputs: vec![word(5)] });
        let keeps = StructuredRegion::Dataflow(Region { inputs: vec![word(0)], nodes: vec![Node::Const { width: 64, output: 6, value: 0 },
            Node::BitOr { width: 64, output: 5, left: 6, right: 0 }], outputs: vec![word(5)] });
        let branch = |when_false: StructuredRegion| StructuredRegion::Conditional { inputs: vec![word(0), bit], condition: 3, arguments: vec![word(0)],
            outputs: vec![word(5)], when_true: Box::new(keeps.clone()), when_false: Box::new(when_false) };
        let carried = |width, when_false| {
            let (mut prefix, mut branch) = (prefix(width), branch(when_false));
            share_compared_constant(&mut prefix, &mut branch).unwrap();
            (prefix, branch)
        };
        let (prefix, branch) = carried(64, reads(16));
        cert::validate_structured_region(&StructuredRegion::Sequence { prefix: prefix.clone(), continuation: Box::new(branch.clone()) }).unwrap();
        assert_eq!(prefix.outputs, vec![bit, word(2)]);
        assert!(fusable(&prefix, &branch).unwrap().is_some(), "carrying the constant keeps the branch fused");
        let StructuredRegion::Conditional { arguments, when_true, when_false, .. } = branch else { unreachable!() };
        assert_eq!(arguments, vec![word(0), word(2)]);
        assert_eq!(when_true.inputs(), &[word(0), word(2)]);
        let StructuredRegion::Dataflow(arm) = *when_false else { unreachable!() };
        assert_eq!(arm.nodes, vec![Node::Sub { width: 64, output: 5, left: 0, right: 2 }]);
        for (width, when_false, why) in [(64, reads(17), "another constant"), (64, returns, "an arm returning it"), (32, reads(16), "a narrow comparison")] {
            let (prefix, branch) = carried(width, when_false.clone());
            assert_eq!(prefix.outputs, vec![bit], "{why}");
            let StructuredRegion::Conditional { when_false: kept, .. } = branch else { unreachable!() };
            assert_eq!(*kept, when_false, "{why}");
        }
    }
}
