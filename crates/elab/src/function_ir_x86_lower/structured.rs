//! Recursive selection plans. These are untrusted proposals; structured_cert
//! checks their physical execution, layout, and frames before publication.

use super::*;

/// Stable FunctionIR value IDs, independent of interface ordering.
pub type Placements = BTreeMap<u64, Gpr>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredStructured {
    pub inputs: Placements,
    pub output: (cert::Port, Gpr),
    pub clobbered: BTreeSet<Gpr>,
    pub byte_length: usize,
    pub body: StructuredPlan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StructuredPlan {
    Dataflow(LoweredDag),
    Sequence {
        prefix: LoweredDag,
        continuation: Box<LoweredStructured>,
    },
    Conditional {
        condition_register: Gpr,
        when_true: Box<LoweredStructured>,
        when_false: Box<LoweredStructured>,
        false_displacement: u8,
        join_displacement: u8,
    },
}

/// Select arbitrary nesting with one common result register. Leaf selection
/// retains its existing restrictions. Prefix results get a fresh placement;
/// inherited inputs remain protected until the next explicit interface drops
/// them. No spill, edge-copy reconciliation, or multi-result join is implicit.
pub fn lower_structured(
    region: &StructuredRegion,
    inputs: &Placements,
    temporaries: &[Gpr],
    requested_output: Gpr,
) -> Result<LoweredStructured, LoweringError> {
    cert::validate_structured_region(region).map_err(LoweringError::InvalidStructuredRegion)?;
    select(region, inputs, temporaries, requested_output, "root")
}

fn select(
    region: &StructuredRegion,
    inputs: &Placements,
    temporaries: &[Gpr],
    requested_output: Gpr,
    path: &str,
) -> Result<LoweredStructured, LoweringError> {
    select_here(region, inputs, temporaries, requested_output, path).map_err(|error| {
        if matches!(error, LoweringError::StructuredPath { .. }) { error }
        else { LoweringError::StructuredPath { path: path.into(), reason: Box::new(error) } }
    })
}

fn select_here(
    region: &StructuredRegion,
    inputs: &Placements,
    temporaries: &[Gpr],
    requested_output: Gpr,
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
    if !available.contains(&requested_output) {
        return Err(LoweringError::OutputRegisterUnavailable(requested_output));
    }
    if region.outputs().len() != 1 { return Err(LoweringError::OutputCount(region.outputs().len())); }
    let output = (region.outputs()[0], requested_output);
    let (body, clobbered, byte_length) = match region {
        StructuredRegion::Dataflow(region) => {
            let dag = lower_dag(region, &registers, temporaries, requested_output)?;
            let length = dag.instructions.iter().map(|i| i.canonical_length()).sum();
            let clobbered = dag.clobbered.clone();
            (StructuredPlan::Dataflow(dag), clobbered, length)
        }
        StructuredRegion::Sequence { prefix, continuation } => {
            if prefix.outputs.len() != 1 { return Err(LoweringError::OutputCount(prefix.outputs.len())); }
            // Reserve the final result register for the continuation. A low
            // byte register is preferred for a materialized comparison bit.
            let prefix_register = temporaries.iter().copied()
                .filter(|r| *r != requested_output)
                .find(|r| prefix.outputs[0].width != 1 || LowByteGpr::from_gpr(*r).is_some())
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
                requested_output, &format!("{path}.continuation"))?;
            let clobbered = dag.clobbered.union(&next.clobbered).copied().collect();
            let length = dag.instructions.iter().map(|i| i.canonical_length()).sum::<usize>() + next.byte_length;
            (StructuredPlan::Sequence { prefix: dag, continuation: Box::new(next) }, clobbered, length)
        }
        StructuredRegion::Conditional { condition, arguments, when_true, when_false, .. } => {
            let condition_register = inputs[condition];
            let branch_inputs = arguments.iter().map(|port| (port.id, inputs[&port.id])).collect();
            // A consumed selector may become scratch in either successor. All
            // other inherited registers remain protected, even if omitted.
            let mut scratch = temporaries.to_vec();
            if !arguments.iter().any(|port| port.id == *condition) {
                scratch.push(condition_register);
            }
            let yes = select(when_true, &branch_inputs, &scratch, requested_output, &format!("{path}.true"))?;
            let no = select(when_false, &branch_inputs, &scratch, requested_output, &format!("{path}.false"))?;
            // TEST r,r; JZ false; true; JMP join; false.
            let false_distance = yes.byte_length + 2;
            let join_distance = no.byte_length;
            for bytes in [false_distance, join_distance] {
                if bytes > 127 { return Err(LoweringError::ShortBranchOutOfRange { bytes }); }
            }
            let length = 3 + 2 + yes.byte_length + 2 + no.byte_length;
            let clobbered = yes.clobbered.union(&no.clobbered).copied().collect();
            (StructuredPlan::Conditional {
                condition_register, when_true: Box::new(yes), when_false: Box::new(no),
                false_displacement: false_distance as u8, join_displacement: join_distance as u8,
            }, clobbered, length)
        }
    };
    Ok(LoweredStructured { inputs: inputs.clone(), output, clobbered, byte_length, body })
}
