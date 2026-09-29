//! Recursive selection plans. These are untrusted proposals; structured_cert
//! checks their physical execution, layout, and frames before publication.

use super::*;

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StructuredPlan {
    Dataflow(LoweredDag),
    MultiDataflow(Vec<(Region, LoweredDag)>),
    Compose { prefix: Box<LoweredStructured>, continuation: Box<LoweredStructured> },
    Sequence {
        prefix: LoweredDag,
        continuation: Box<LoweredStructured>,
    },
    Conditional {
        condition_register: Gpr,
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
        StructuredRegion::Conditional { condition, arguments, when_true, when_false, .. } => {
            let condition_register = inputs[condition];
            let branch_inputs = arguments.iter().map(|port| (port.id, inputs[&port.id])).collect();
            // Preserve every inherited register across the branch. A caller
            // may still carry a selector omitted from the branch interface.
            let scratch = temporaries.to_vec();
            let yes = select(when_true, &branch_inputs, &scratch, requested, &format!("{path}.true"))?;
            let no = select(when_false, &branch_inputs, &scratch, requested, &format!("{path}.false"))?;
            // TEST r,r; JZ false; true; JMP join; false. Short jumps while
            // both distances fit rel8, near (JZ rel32, JMP rel32) otherwise.
            let near = yes.byte_length + 2 > 127 || no.byte_length > 127;
            let (jz_length, jmp_length) = if near { (6, 5) } else { (2, 2) };
            let false_distance = yes.byte_length + jmp_length;
            let join_distance = no.byte_length;
            for bytes in [false_distance, join_distance] {
                if bytes > i32::MAX as usize { return Err(LoweringError::ShortBranchOutOfRange { bytes }); }
            }
            let length = 3 + jz_length + yes.byte_length + jmp_length + no.byte_length;
            let clobbered = yes.clobbered.union(&no.clobbered).copied().collect();
            (StructuredPlan::Conditional {
                condition_register, when_true: Box::new(yes), when_false: Box::new(no),
                false_displacement: false_distance as u32, join_displacement: join_distance as u32, near,
            }, clobbered, length)
        }
    };
    Ok(LoweredStructured { inputs: inputs.clone(), output, outputs, clobbered, byte_length, body })
}
