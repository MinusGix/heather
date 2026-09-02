//! Executable, target-independent semantics for the compiler-owned FunctionIR.
//!
//! This is deliberately not trusted.  It is a fast development oracle for the
//! same graph whose logical meaning is checked in `lib/function_ir.hthr`.

use std::collections::BTreeMap;

use crate::function_ir_cert::{
    BlockArgument, ConditionalJoinRegion, ControlRegion, Node, Port, Region,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecutionError {
    InvalidRegion(String),
    DuplicateInput(u64),
    InputWidth { id: u64, expected: u64, actual: u64 },
    MissingValue(u64),
    UnsupportedWidth(u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Value {
    width: u64,
    bits: u64,
}

/// Execute a validated structured region and return its declared outputs.
pub fn interpret(
    region: &ControlRegion,
    inputs: &[(Port, u64)],
) -> Result<Vec<(Port, u64)>, ExecutionError> {
    crate::function_ir_cert::validate_control_region(region)
        .map_err(ExecutionError::InvalidRegion)?;
    let mut values = BTreeMap::new();
    for (port, bits) in inputs {
        if !region.inputs().contains(port) {
            return Err(ExecutionError::InputWidth {
                id: port.id,
                expected: region
                    .inputs()
                    .iter()
                    .find(|candidate| candidate.id == port.id)
                    .map_or(0, |candidate| candidate.width),
                actual: port.width,
            });
        }
        if values
            .insert(
                port.id,
                Value {
                    width: port.width,
                    bits: truncate(port.width, *bits)?,
                },
            )
            .is_some()
        {
            return Err(ExecutionError::DuplicateInput(port.id));
        }
    }
    for port in region.inputs() {
        read(&values, *port)?;
    }
    execute_structured(region, &mut values)?;
    region
        .outputs()
        .iter()
        .map(|port| Ok((*port, read(&values, *port)?.bits)))
        .collect()
}

fn execute_structured(
    region: &ControlRegion,
    values: &mut BTreeMap<u64, Value>,
) -> Result<(), ExecutionError> {
    execute_region(&region.prefix, values)?;
    let ConditionalJoinRegion {
        condition,
        when_true,
        true_arguments,
        when_false,
        false_arguments,
        continuation,
        ..
    } = &region.join;
    let selected = read(
        values,
        Port {
            id: *condition,
            width: 1,
        },
    )?
    .bits
        != 0;
    let (branch, arguments) = if selected {
        (when_true, true_arguments)
    } else {
        (when_false, false_arguments)
    };
    execute_region(branch, values)?;
    transfer(arguments, values)?;
    execute_region(continuation, values)
}

fn execute_region(
    region: &Region,
    values: &mut BTreeMap<u64, Value>,
) -> Result<(), ExecutionError> {
    for node in &region.nodes {
        let output = node.output();
        let result = match *node {
            Node::Const { value, .. } => value,
            Node::Add { left, right, .. } => {
                binary(values, output.width, left, right, u64::wrapping_add)?
            }
            Node::Sub { left, right, .. } => {
                binary(values, output.width, left, right, u64::wrapping_sub)?
            }
            Node::BitAnd { left, right, .. } => {
                binary(values, output.width, left, right, |x, y| x & y)?
            }
            Node::BitOr { left, right, .. } => {
                binary(values, output.width, left, right, |x, y| x | y)?
            }
            Node::BitXor { left, right, .. } => {
                binary(values, output.width, left, right, |x, y| x ^ y)?
            }
            Node::ShiftLeft { value, amount, .. } => read(
                values,
                Port {
                    id: value,
                    width: output.width,
                },
            )?
            .bits
            .checked_shl(amount as u32)
            .unwrap_or(0),
            Node::LogicalShiftRight { value, amount, .. } => read(
                values,
                Port {
                    id: value,
                    width: output.width,
                },
            )?
            .bits
            .checked_shr(amount as u32)
            .unwrap_or(0),
            Node::ArithmeticShiftRight { value, amount, .. } => arithmetic_shift_right(
                output.width,
                read(
                    values,
                    Port {
                        id: value,
                        width: output.width,
                    },
                )?
                .bits,
                amount,
            )?,
            Node::UnsignedLessThan {
                width, left, right, ..
            } => u64::from(
                read(values, Port { id: left, width })?.bits
                    < read(values, Port { id: right, width })?.bits,
            ),
            Node::SignedLessThan {
                width, left, right, ..
            } => u64::from(
                as_signed(width, read(values, Port { id: left, width })?.bits)?
                    < as_signed(width, read(values, Port { id: right, width })?.bits)?,
            ),
        };
        values.insert(
            output.id,
            Value {
                width: output.width,
                bits: truncate(output.width, result)?,
            },
        );
    }
    for output in &region.outputs {
        read(values, *output)?;
    }
    Ok(())
}

fn transfer(
    arguments: &[BlockArgument],
    values: &mut BTreeMap<u64, Value>,
) -> Result<(), ExecutionError> {
    // Read the complete predecessor tuple before binding any successor name;
    // this gives edge arguments parallel-copy semantics.
    let transferred = arguments
        .iter()
        .map(|argument| {
            Ok((
                argument.parameter,
                read(
                    values,
                    Port {
                        id: argument.value,
                        width: argument.width,
                    },
                )?,
            ))
        })
        .collect::<Result<Vec<_>, ExecutionError>>()?;
    values.extend(transferred);
    Ok(())
}

fn binary(
    values: &BTreeMap<u64, Value>,
    width: u64,
    left: u64,
    right: u64,
    operation: impl FnOnce(u64, u64) -> u64,
) -> Result<u64, ExecutionError> {
    Ok(operation(
        read(values, Port { id: left, width })?.bits,
        read(values, Port { id: right, width })?.bits,
    ))
}

fn read(values: &BTreeMap<u64, Value>, port: Port) -> Result<Value, ExecutionError> {
    let value = values
        .get(&port.id)
        .copied()
        .ok_or(ExecutionError::MissingValue(port.id))?;
    if value.width != port.width {
        return Err(ExecutionError::InputWidth {
            id: port.id,
            expected: port.width,
            actual: value.width,
        });
    }
    Ok(value)
}

fn truncate(width: u64, bits: u64) -> Result<u64, ExecutionError> {
    match width {
        0 => Ok(0),
        1..=63 => Ok(bits & ((1_u64 << width) - 1)),
        64 => Ok(bits),
        _ => Err(ExecutionError::UnsupportedWidth(width)),
    }
}

fn as_signed(width: u64, bits: u64) -> Result<i128, ExecutionError> {
    let bits = truncate(width, bits)? as i128;
    if width == 0 {
        return Ok(0);
    }
    let sign = 1_i128 << (width - 1);
    Ok(if bits & sign == 0 {
        bits
    } else {
        bits - (1_i128 << width)
    })
}

fn arithmetic_shift_right(width: u64, bits: u64, amount: u64) -> Result<u64, ExecutionError> {
    if amount >= width {
        return Ok(u64::from(width != 0 && as_signed(width, bits)? < 0).wrapping_neg());
    }
    truncate(width, (as_signed(width, bits)? >> amount) as u64)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn port(id: u64, width: u64) -> Port {
        Port { id, width }
    }

    fn max_plus() -> ControlRegion {
        let inputs = vec![port(0, 64), port(1, 64), port(2, 64)];
        let comparison = Region {
            inputs: inputs.clone(),
            nodes: vec![Node::UnsignedLessThan {
                width: 64,
                output: 3,
                left: 0,
                right: 1,
            }],
            outputs: vec![port(3, 1)],
        };
        let branch_inputs = vec![port(0, 64), port(1, 64), port(2, 64)];
        let join = ConditionalJoinRegion {
            inputs: vec![port(0, 64), port(1, 64), port(2, 64), port(3, 1)],
            condition: 3,
            arguments: branch_inputs.clone(),
            when_true: Region {
                inputs: branch_inputs.clone(),
                nodes: vec![],
                outputs: vec![port(1, 64), port(2, 64)],
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
                outputs: vec![port(0, 64), port(2, 64)],
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
                inputs: vec![port(4, 64), port(5, 64)],
                nodes: vec![Node::Add {
                    width: 64,
                    output: 6,
                    left: 4,
                    right: 5,
                }],
                outputs: vec![port(6, 64)],
            },
        };
        ControlRegion {
            prefix: comparison,
            join,
        }
    }

    fn run(a: u64, b: u64, c: u64) -> u64 {
        interpret(
            &max_plus(),
            &[(port(0, 64), a), (port(1, 64), b), (port(2, 64), c)],
        )
        .unwrap()[0]
            .1
    }

    #[test]
    fn conditional_join_passes_the_selected_value_to_one_continuation() {
        assert_eq!(run(3, 7, 11), 18);
        assert_eq!(run(9, 4, 11), 20);
        assert_eq!(run(5, 5, 11), 16);
        assert_eq!(run(u64::MAX, 0, 1), 0);
    }

    #[test]
    fn conditional_join_rejects_stale_edge_interfaces() {
        let mut region = max_plus();
        region.join.true_arguments[0].value = 0;
        assert!(matches!(
            interpret(&region, &[(port(0, 64), 1), (port(1, 64), 2), (port(2, 64), 3)]),
            Err(ExecutionError::InvalidRegion(message))
                if message.contains("true join edge")
        ));
    }
}
