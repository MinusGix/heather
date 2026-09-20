//! Untrusted certificate rendering for concrete FunctionIR regions.
//!
//! The renderer consumes the same finite model a compiler has just built and
//! emits ordinary Heather source proving `RegionValid(region_expr)`.  It is
//! not a trusted validation path: a stale model, renderer bug, or dishonest
//! caller produces a theorem that the ordinary elaborator/kernel rejects.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Port {
    pub id: u64,
    pub width: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Node {
    Const {
        width: u64,
        output: u64,
        value: u64,
    },
    Add {
        width: u64,
        output: u64,
        left: u64,
        right: u64,
    },
    Sub {
        width: u64,
        output: u64,
        left: u64,
        right: u64,
    },
    BitAnd {
        width: u64,
        output: u64,
        left: u64,
        right: u64,
    },
    BitOr {
        width: u64,
        output: u64,
        left: u64,
        right: u64,
    },
    BitXor {
        width: u64,
        output: u64,
        left: u64,
        right: u64,
    },
    ShiftLeft {
        width: u64,
        output: u64,
        value: u64,
        amount: u64,
    },
    LogicalShiftRight {
        width: u64,
        output: u64,
        value: u64,
        amount: u64,
    },
    ArithmeticShiftRight {
        width: u64,
        output: u64,
        value: u64,
        amount: u64,
    },
    UnsignedLessThan {
        width: u64,
        output: u64,
        left: u64,
        right: u64,
    },
    SignedLessThan {
        width: u64,
        output: u64,
        left: u64,
        right: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Region {
    pub inputs: Vec<Port>,
    pub nodes: Vec<Node>,
    pub outputs: Vec<Port>,
}

/// One value carried across a control-flow edge into a fresh block parameter.
///
/// Keeping the width on the edge makes the transfer intrinsically typed while
/// leaving value IDs as compact, compiler-friendly data.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BlockArgument {
    pub width: u64,
    pub value: u64,
    pub parameter: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StructuredRegion {
    Dataflow(Region),
    /// A structured producer feeds explicitly bound values to a continuation.
    Compose { prefix: Box<StructuredRegion>, continuation: Box<StructuredRegion> },
    Sequence {
        prefix: Region,
        continuation: Box<StructuredRegion>,
    },
    Conditional {
        inputs: Vec<Port>,
        condition: u64,
        arguments: Vec<Port>,
        outputs: Vec<Port>,
        when_true: Box<StructuredRegion>,
        when_false: Box<StructuredRegion>,
    },
}

/// The selected arms and their explicit transfers into one shared block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConditionalJoinRegion {
    pub inputs: Vec<Port>,
    pub condition: u64,
    pub arguments: Vec<Port>,
    pub when_true: Region,
    pub true_arguments: Vec<BlockArgument>,
    pub when_false: Region,
    pub false_arguments: Vec<BlockArgument>,
    pub continuation: Region,
}

/// The first real block-argument graph: producer, selected arms, and join.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ControlRegion {
    pub prefix: Region,
    pub join: ConditionalJoinRegion,
}

impl ControlRegion {
    pub fn inputs(&self) -> &[Port] {
        &self.prefix.inputs
    }

    pub fn outputs(&self) -> &[Port] {
        &self.join.continuation.outputs
    }
}

impl StructuredRegion {
    pub fn inputs(&self) -> &[Port] {
        match self {
            Self::Dataflow(region) => &region.inputs,
            Self::Sequence { prefix, .. } => &prefix.inputs,
            Self::Compose { prefix, .. } => prefix.inputs(),
            Self::Conditional { inputs, .. } => inputs,
        }
    }

    pub fn outputs(&self) -> &[Port] {
        match self {
            Self::Dataflow(region) => &region.outputs,
            Self::Sequence { continuation, .. } | Self::Compose { continuation, .. } => continuation.outputs(),
            Self::Conditional { outputs, .. } => outputs,
        }
    }
}

pub fn validate_structured_region(region: &StructuredRegion) -> Result<(), String> {
    match region {
        StructuredRegion::Dataflow(region) => {
            directory_entries(region)?;
            Ok(())
        }
        StructuredRegion::Sequence {
            prefix,
            continuation,
        } => {
            directory_entries(prefix)?;
            for input in continuation.inputs() {
                if !prefix.inputs.contains(input) && !prefix.outputs.contains(input) {
                    return Err(format!(
                        "continuation input {}:{} is not available from the prefix",
                        input.id, input.width,
                    ));
                }
            }
            validate_structured_region(continuation)
        }
        StructuredRegion::Compose { prefix, continuation } => {
            validate_structured_region(prefix)?;
            for input in continuation.inputs() {
                if !prefix.inputs().contains(input) && !prefix.outputs().contains(input) {
                    return Err(format!("continuation input {}:{} is not available from the structured prefix", input.id, input.width));
                }
            }
            validate_structured_region(continuation)
        }
        StructuredRegion::Conditional {
            inputs,
            condition,
            arguments,
            outputs,
            when_true,
            when_false,
        } => {
            ensure_unique_interface("conditional input", inputs)?;
            ensure_unique_interface("conditional argument", arguments)?;
            if !inputs
                .iter()
                .any(|port| port.id == *condition && port.width == 1)
            {
                return Err(format!(
                    "conditional value {condition} is not an available one-bit input"
                ));
            }
            for argument in arguments {
                if !inputs.contains(argument) {
                    return Err(format!(
                        "conditional argument {}:{} is not an input",
                        argument.id, argument.width,
                    ));
                }
            }
            for (side, branch) in [("true", when_true), ("false", when_false)] {
                if branch.inputs() != arguments {
                    return Err(format!("{side} branch captures undeclared inputs"));
                }
                if branch.outputs() != outputs {
                    return Err(format!("{side} branch yields a different interface"));
                }
                validate_structured_region(branch)?;
            }
            Ok(())
        }
    }
}

pub fn validate_control_region(region: &ControlRegion) -> Result<(), String> {
    directory_entries(&region.prefix)?;
    for input in &region.join.inputs {
        if !region.prefix.inputs.contains(input) && !region.prefix.outputs.contains(input) {
            return Err(format!(
                "join input {}:{} is not available from the prefix",
                input.id, input.width,
            ));
        }
    }
    let ConditionalJoinRegion {
        inputs,
        condition,
        arguments,
        when_true,
        true_arguments,
        when_false,
        false_arguments,
        continuation,
    } = &region.join;
    ensure_unique_interface("conditional-join input", inputs)?;
    ensure_unique_interface("conditional-join argument", arguments)?;
    if !inputs
        .iter()
        .any(|port| port.id == *condition && port.width == 1)
    {
        return Err(format!(
            "conditional-join value {condition} is not an available one-bit input"
        ));
    }
    for argument in arguments {
        if !inputs.contains(argument) {
            return Err(format!(
                "conditional-join argument {}:{} is not an input",
                argument.id, argument.width,
            ));
        }
    }
    for (side, branch, edge) in [
        ("true", when_true, true_arguments),
        ("false", when_false, false_arguments),
    ] {
        if branch.inputs != *arguments {
            return Err(format!("{side} join branch captures undeclared inputs"));
        }
        let yielded = edge
            .iter()
            .map(|argument| Port {
                id: argument.value,
                width: argument.width,
            })
            .collect::<Vec<_>>();
        if branch.outputs != yielded {
            return Err(format!(
                "{side} join edge does not pass the branch output interface"
            ));
        }
        directory_entries(branch)?;
    }
    let true_parameters = edge_parameters(true_arguments);
    let false_parameters = edge_parameters(false_arguments);
    if true_parameters != false_parameters {
        return Err("conditional-join edges bind different parameters".to_string());
    }
    ensure_unique_interface("join parameter", &true_parameters)?;
    for parameter in &true_parameters {
        if inputs.iter().any(|input| input.id == parameter.id) {
            return Err(format!(
                "join parameter {} is not fresh from the conditional inputs",
                parameter.id,
            ));
        }
    }
    if continuation.inputs != true_parameters {
        return Err("conditional-join continuation does not bind the edge parameters".to_string());
    }
    directory_entries(continuation).map(|_| ())
}

fn edge_parameters(arguments: &[BlockArgument]) -> Vec<Port> {
    arguments
        .iter()
        .map(|argument| Port {
            id: argument.parameter,
            width: argument.width,
        })
        .collect()
}

fn ensure_unique_interface(kind: &str, ports: &[Port]) -> Result<(), String> {
    let mut ids = std::collections::BTreeSet::new();
    for port in ports {
        if !ids.insert(port.id) {
            return Err(format!("duplicate {kind} ID {}", port.id));
        }
    }
    Ok(())
}

impl Node {
    pub fn output(self) -> Port {
        match self {
            Node::Const { width, output, .. }
            | Node::Add { width, output, .. }
            | Node::Sub { width, output, .. }
            | Node::BitAnd { width, output, .. }
            | Node::BitOr { width, output, .. }
            | Node::BitXor { width, output, .. }
            | Node::ShiftLeft { width, output, .. }
            | Node::LogicalShiftRight { width, output, .. }
            | Node::ArithmeticShiftRight { width, output, .. } => Port { id: output, width },
            Node::UnsignedLessThan { output, .. } | Node::SignedLessThan { output, .. } => Port {
                id: output,
                width: 1,
            },
        }
    }

    fn operands(self) -> Vec<Port> {
        match self {
            Node::Const { .. } => Vec::new(),
            Node::ShiftLeft { width, value, .. }
            | Node::LogicalShiftRight { width, value, .. }
            | Node::ArithmeticShiftRight { width, value, .. } => {
                vec![Port { id: value, width }]
            }
            Node::Add {
                width, left, right, ..
            }
            | Node::Sub {
                width, left, right, ..
            }
            | Node::BitAnd {
                width, left, right, ..
            }
            | Node::BitOr {
                width, left, right, ..
            }
            | Node::BitXor {
                width, left, right, ..
            }
            | Node::UnsignedLessThan {
                width, left, right, ..
            }
            | Node::SignedLessThan {
                width, left, right, ..
            } => {
                vec![Port { id: left, width }, Port { id: right, width }]
            }
        }
    }
}

#[derive(Debug)]
pub struct Emission {
    pub theorem_name: String,
    pub text: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Origin {
    Input(u64),
    Node(u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DirectoryEntry {
    port: Port,
    origin: Origin,
}

#[derive(Debug)]
struct Directory {
    entry: DirectoryEntry,
    left: Option<Box<Directory>>,
    right: Option<Box<Directory>>,
}

/// Render a compact directory/rank certificate for `region_expr`, which
/// should be a closed Heather expression such as `sum4_left_first_raw()`.
/// Its proof size is linearithmic: directory ordering is linear and every
/// declaration/use follows one path through a balanced tree.
pub fn generate(
    theorem_name: &str,
    region_expr: &str,
    region: &Region,
) -> Result<Emission, String> {
    let entries = directory_entries(region)?;
    let directory = build_directory(&entries);
    let directory_name = format!("{theorem_name}_directory");
    let ordered_name = format!("{theorem_name}_directory_ordered");
    let mut declarations = String::new();
    emit_directory_declarations(
        theorem_name,
        directory.as_deref(),
        None,
        None,
        true,
        &mut declarations,
    );
    for entry in &entries {
        let fact_name = port_fact_name(theorem_name, entry.port.id);
        let proof = prove_directory_lookup(
            theorem_name,
            directory.as_deref(),
            entry.port.id,
            entry.port.width,
            entry.origin,
        )?;
        declarations.push_str(&format!(
            "theorem {fact_name}(): HasDirectoryPortAt(\
             {directory_name}(), {}, {}, {}) {{\n\
             \x20   {proof}\n\
             }}\n",
            entry.port.id,
            entry.port.width,
            render_origin(entry.origin),
        ));
    }

    let mut inputs_indexed = format!(
        "input_entries_indexed_nil(directory := {directory_name}(), index := {})",
        region.inputs.len()
    );
    for (index, port) in region.inputs.iter().enumerate().rev() {
        inputs_indexed = format!(
            "input_entries_indexed_cons(index := {index}, port := {}, found := {}(), tail := {inputs_indexed})",
            render_port(*port),
            port_fact_name(theorem_name, port.id),
        );
    }

    let terminal_nodes_name = node_list_name(theorem_name, region.nodes.len());
    let terminal_proof_name = nodes_proof_name(theorem_name, region.nodes.len());
    declarations.push_str(&format!(
        "fn {terminal_nodes_name}() → List<Node> {{ [] }}\n\
         theorem {terminal_proof_name}(): NodesIndexed(\
             {directory_name}(), {terminal_nodes_name}(), {}) {{\n\
         \x20   nodes_indexed_nil(\
             directory := {directory_name}(), index := {})\n\
         }}\n",
        region.nodes.len(),
        region.nodes.len(),
    ));
    for (index, node) in region.nodes.iter().enumerate().rev() {
        let rank = index as u64;
        let head =
            render_node_indexed_proof(theorem_name, &directory_name, &entries, index, rank, *node)?;
        let nodes_name = node_list_name(theorem_name, index);
        let next_nodes_name = node_list_name(theorem_name, index + 1);
        let proof_name = nodes_proof_name(theorem_name, index);
        let next_proof_name = nodes_proof_name(theorem_name, index + 1);
        declarations.push_str(&format!(
            "fn {nodes_name}() → List<Node> {{\n\
             \x20   Cons({}, {next_nodes_name}())\n\
             }}\n\
             theorem {proof_name}(): NodesIndexed(\
                 {directory_name}(), {nodes_name}(), {index}) {{\n\
             \x20   nodes_indexed_cons(\
                 index := {index}, node := {}, head := {head},\
                 tail := {next_proof_name}())\n\
             }}\n",
            render_node(*node),
            render_node(*node),
        ));
    }
    let nodes_indexed = format!("{}()", nodes_proof_name(theorem_name, 0));

    let mut outputs_indexed =
        format!("output_entries_indexed_nil(directory := {directory_name}())");
    for port in region.outputs.iter().rev() {
        find_entry(&entries, port.id, port.width)?;
        let found = format!(
            "directory_port_exists({}())",
            port_fact_name(theorem_name, port.id)
        );
        outputs_indexed = format!(
            "output_entries_indexed_cons(output := {}, found := {found}, tail := {outputs_indexed})",
            render_port(*port),
        );
    }

    let text = format!(
        "{declarations}\
         theorem {theorem_name}(): RegionValid({region_expr}) {{\n\
         \x20   RegionValid {{\n\
         \x20       directory: {directory_name}(),\n\
         \x20       directory_ordered: {ordered_name}(),\n\
         \x20       directory_size: refl,\n\
         \x20       inputs_indexed: {inputs_indexed},\n\
         \x20       nodes_indexed: {nodes_indexed},\n\
         \x20       outputs_indexed: {outputs_indexed},\n\
         \x20   }}\n\
         }}\n"
    );
    Ok(Emission {
        theorem_name: theorem_name.to_string(),
        text,
    })
}

/// Render the concrete raw-region declaration used by scaling tests and by
/// compiler prototypes that do not already have a Heather declaration.
pub fn render_region_function(name: &str, region: &Region) -> String {
    let ports = |ports: &[Port]| {
        ports
            .iter()
            .map(|p| format!("Port(id := {}, width := {})", p.id, p.width))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let nodes = region
        .nodes
        .iter()
        .map(|node| render_node(*node))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "fn {name}() → Region {{\n\
         \x20   Region(inputs := Ports([{}]), nodes := [{}], outputs := Ports([{}]))\n\
         }}\n",
        ports(&region.inputs),
        nodes,
        ports(&region.outputs)
    )
}

/// Render the four-block control graph through the same inspectable Heather
/// source boundary as flat regions.
pub fn render_control_region_function(
    name: &str,
    region: &ControlRegion,
) -> Result<String, String> {
    validate_control_region(region)?;
    let prefix_name = format!("{name}_prefix");
    let true_name = format!("{name}_true");
    let false_name = format!("{name}_false");
    let continuation_name = format!("{name}_continuation");
    let ports = |ports: &[Port]| {
        ports
            .iter()
            .map(|port| render_port(*port))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let edge = |arguments: &[BlockArgument]| {
        arguments.iter().rev().fold("Nil".to_string(), |tail, argument| {
            format!(
                "Cons(BlockArgument(width := {}, value := {}, parameter := {}), {tail})",
                argument.width, argument.value, argument.parameter,
            )
        })
    };
    Ok(format!(
        "{}\n{}\n{}\n{}\n\
         fn {name}() → ControlRegion {{\n\
         \x20   ControlRegion(prefix := {prefix_name}(), join := ConditionalJoinRegion(\n\
         \x20       inputs := Ports([{}]), condition := {}, arguments := Ports([{}]),\n\
         \x20       when_true := {true_name}(), true_arguments := {},\n\
         \x20       when_false := {false_name}(), false_arguments := {},\n\
         \x20       continuation := {continuation_name}()))\n\
         }}\n",
        render_region_function(&prefix_name, &region.prefix),
        render_region_function(&true_name, &region.join.when_true),
        render_region_function(&false_name, &region.join.when_false),
        render_region_function(&continuation_name, &region.join.continuation),
        ports(&region.join.inputs),
        region.join.condition,
        ports(&region.join.arguments),
        edge(&region.join.true_arguments),
        edge(&region.join.false_arguments),
    ))
}

fn directory_entries(region: &Region) -> Result<Vec<DirectoryEntry>, String> {
    let mut entries = Vec::with_capacity(region.inputs.len() + region.nodes.len());
    for (index, port) in region.inputs.iter().copied().enumerate() {
        insert_entry(
            &mut entries,
            DirectoryEntry {
                port,
                origin: Origin::Input(index as u64),
            },
        )?;
    }
    for (index, node) in region.nodes.iter().enumerate() {
        for (operand_index, operand) in node.operands().into_iter().enumerate() {
            find_entry(&entries, operand.id, operand.width).map_err(|why| {
                format!("node {index}'s operand {operand_index} is invalid: {why}")
            })?;
        }
        insert_entry(
            &mut entries,
            DirectoryEntry {
                port: node.output(),
                origin: Origin::Node(index as u64),
            },
        )
        .map_err(|why| format!("node {index}'s output is invalid: {why}"))?;
    }
    for (index, output) in region.outputs.iter().enumerate() {
        find_entry(&entries, output.id, output.width)
            .map_err(|why| format!("output {index} is invalid: {why}"))?;
    }
    entries.sort_by_key(|entry| entry.port.id);
    Ok(entries)
}

fn insert_entry(entries: &mut Vec<DirectoryEntry>, entry: DirectoryEntry) -> Result<(), String> {
    if entries
        .iter()
        .any(|present| present.port.id == entry.port.id)
    {
        return Err(format!("value {} is already defined", entry.port.id));
    }
    entries.push(entry);
    Ok(())
}

fn find_entry(entries: &[DirectoryEntry], id: u64, width: u64) -> Result<DirectoryEntry, String> {
    let Some(entry) = entries.iter().find(|entry| entry.port.id == id).copied() else {
        return Err(format!("value {id} is undefined"));
    };
    if entry.port.width != width {
        return Err(format!(
            "value {id} has width {}, not requested width {width}",
            entry.port.width
        ));
    }
    Ok(entry)
}

fn build_directory(entries: &[DirectoryEntry]) -> Option<Box<Directory>> {
    if entries.is_empty() {
        return None;
    }
    let middle = entries.len() / 2;
    Some(Box::new(Directory {
        entry: entries[middle],
        left: build_directory(&entries[..middle]),
        right: build_directory(&entries[middle + 1..]),
    }))
}

fn emit_directory_declarations(
    theorem_name: &str,
    directory: Option<&Directory>,
    lower: Option<u64>,
    upper: Option<u64>,
    root: bool,
    declarations: &mut String,
) {
    if directory.is_none() && !root {
        return;
    }
    let name = directory_node_name(theorem_name, directory, root);
    let ordered_name = format!("{name}_ordered");
    let Some(directory) = directory else {
        debug_assert!(root, "empty child directories need no declaration");
        declarations.push_str(&format!(
            "fn {name}() → PortDirectory {{ DirectoryEmpty }}\n\
             theorem {ordered_name}(): DirectoryOrdered({name}()) {{\n\
             \x20   directory_within_empty(None, None)\n\
             }}\n"
        ));
        return;
    };

    emit_directory_declarations(
        theorem_name,
        directory.left.as_deref(),
        lower,
        Some(directory.entry.port.id),
        false,
        declarations,
    );
    emit_directory_declarations(
        theorem_name,
        directory.right.as_deref(),
        Some(directory.entry.port.id),
        upper,
        false,
        declarations,
    );

    let left = directory_child_ref(theorem_name, directory.left.as_deref());
    let right = directory_child_ref(theorem_name, directory.right.as_deref());
    let left_ordered = directory_child_ordered(
        theorem_name,
        directory.left.as_deref(),
        lower,
        Some(directory.entry.port.id),
    );
    let right_ordered = directory_child_ordered(
        theorem_name,
        directory.right.as_deref(),
        Some(directory.entry.port.id),
        upper,
    );
    let ordered_type = if root {
        format!("DirectoryOrdered({name}())")
    } else {
        format!(
            "DirectoryWithin({name}(), {}, {})",
            render_bound(lower),
            render_bound(upper)
        )
    };
    declarations.push_str(&format!(
        "fn {name}() → PortDirectory {{\n\
         \x20   DirectoryBranch({left}, {}, {right})\n\
         }}\n\
         theorem {ordered_name}(): {ordered_type} {{\n\
         \x20   directory_within_branch(\
             entry := {}, above := trivial, below := trivial,\
             left_within := {left_ordered}, right_within := {right_ordered})\n\
         }}\n",
        render_directory_entry(directory.entry),
        render_directory_entry(directory.entry),
    ));
}

fn directory_node_name(theorem_name: &str, directory: Option<&Directory>, root: bool) -> String {
    if root {
        format!("{theorem_name}_directory")
    } else {
        format!(
            "{theorem_name}_directory_at_{}",
            directory.expect("only the root may be empty").entry.port.id
        )
    }
}

fn directory_child_ref(theorem_name: &str, directory: Option<&Directory>) -> String {
    match directory {
        None => "DirectoryEmpty".to_string(),
        Some(_) => format!("{}()", directory_node_name(theorem_name, directory, false)),
    }
}

fn directory_child_ordered(
    theorem_name: &str,
    directory: Option<&Directory>,
    lower: Option<u64>,
    upper: Option<u64>,
) -> String {
    match directory {
        None => format!(
            "directory_within_empty({}, {})",
            render_bound(lower),
            render_bound(upper)
        ),
        Some(_) => format!(
            "{}_ordered()",
            directory_node_name(theorem_name, directory, false)
        ),
    }
}

fn render_directory_entry(entry: DirectoryEntry) -> String {
    format!(
        "DirectoryPort(port := Port(id := {}, width := {}), origin := {})",
        entry.port.id,
        entry.port.width,
        render_origin(entry.origin),
    )
}

fn render_port(port: Port) -> String {
    format!("Port(id := {}, width := {})", port.id, port.width)
}

fn render_node(node: Node) -> String {
    match node {
        Node::Const {
            width,
            output,
            value,
        } => {
            format!("Const(width := {width}, output := {output}, value := {value})")
        }
        Node::Add {
            width,
            output,
            left,
            right,
        } => render_binary("Add", width, output, left, right),
        Node::Sub {
            width,
            output,
            left,
            right,
        } => render_binary("Sub", width, output, left, right),
        Node::BitAnd {
            width,
            output,
            left,
            right,
        } => render_binary("BitAnd", width, output, left, right),
        Node::BitOr {
            width,
            output,
            left,
            right,
        } => render_binary("BitOr", width, output, left, right),
        Node::BitXor {
            width,
            output,
            left,
            right,
        } => render_binary("BitXor", width, output, left, right),
        Node::ShiftLeft {
            width,
            output,
            value,
            amount,
        } => render_shift("ShiftLeft", width, output, value, amount),
        Node::LogicalShiftRight {
            width,
            output,
            value,
            amount,
        } => render_shift("LogicalShiftRight", width, output, value, amount),
        Node::ArithmeticShiftRight {
            width,
            output,
            value,
            amount,
        } => render_shift("ArithmeticShiftRight", width, output, value, amount),
        Node::UnsignedLessThan {
            width,
            output,
            left,
            right,
        } => render_binary("UnsignedLessThan", width, output, left, right),
        Node::SignedLessThan {
            width,
            output,
            left,
            right,
        } => render_binary("SignedLessThan", width, output, left, right),
    }
}

fn render_binary(name: &str, width: u64, output: u64, left: u64, right: u64) -> String {
    format!("{name}(width := {width}, output := {output}, left := {left}, right := {right})")
}

fn render_shift(name: &str, width: u64, output: u64, value: u64, amount: u64) -> String {
    format!("{name}(width := {width}, output := {output}, value := {value}, amount := {amount})")
}

fn render_node_indexed_proof(
    theorem_name: &str,
    directory_name: &str,
    entries: &[DirectoryEntry],
    index: usize,
    rank: u64,
    node: Node,
) -> Result<String, String> {
    let output_port = node.output();
    let output = format!("{}()", port_fact_name(theorem_name, output_port.id));
    let common = format!(
        "directory := {directory_name}(), index := {index}, width := {}, output := {}",
        match node {
            Node::UnsignedLessThan { width, .. } | Node::SignedLessThan { width, .. } => width,
            _ => output_port.width,
        },
        output_port.id,
    );
    match node {
        Node::Const { value, .. } => Ok(format!(
            "node_indexed_const({common}, value := {value}, output_found := {output})"
        )),
        Node::ShiftLeft {
            width,
            value,
            amount,
            ..
        }
        | Node::LogicalShiftRight {
            width,
            value,
            amount,
            ..
        }
        | Node::ArithmeticShiftRight {
            width,
            value,
            amount,
            ..
        } => {
            let found = prove_available_from_fact(entries, theorem_name, value, width, rank)?;
            let theorem = match node {
                Node::ShiftLeft { .. } => "node_indexed_shift_left",
                Node::LogicalShiftRight { .. } => "node_indexed_logical_shift_right",
                Node::ArithmeticShiftRight { .. } => "node_indexed_arithmetic_shift_right",
                _ => unreachable!(),
            };
            Ok(format!(
                "{theorem}({common}, value := {value}, amount := {amount}, output_found := {output}, value_found := {found})"
            ))
        }
        Node::Add {
            width, left, right, ..
        }
        | Node::Sub {
            width, left, right, ..
        }
        | Node::BitAnd {
            width, left, right, ..
        }
        | Node::BitOr {
            width, left, right, ..
        }
        | Node::BitXor {
            width, left, right, ..
        } => {
            let left_found = prove_available_from_fact(entries, theorem_name, left, width, rank)?;
            let right_found = prove_available_from_fact(entries, theorem_name, right, width, rank)?;
            let theorem = match node {
                Node::Add { .. } => "node_indexed_add",
                Node::Sub { .. } => "node_indexed_sub",
                Node::BitAnd { .. } => "node_indexed_bitand",
                Node::BitOr { .. } => "node_indexed_bitor",
                Node::BitXor { .. } => "node_indexed_bitxor",
                _ => unreachable!(),
            };
            Ok(format!(
                "{theorem}({common}, left := {left}, right := {right}, output_found := {output}, left_found := {left_found}, right_found := {right_found})"
            ))
        }
        Node::UnsignedLessThan {
            width, left, right, ..
        }
        | Node::SignedLessThan {
            width, left, right, ..
        } => {
            let left_found = prove_available_from_fact(entries, theorem_name, left, width, rank)?;
            let right_found = prove_available_from_fact(entries, theorem_name, right, width, rank)?;
            let theorem = match node {
                Node::UnsignedLessThan { .. } => "node_indexed_unsigned_less_than",
                Node::SignedLessThan { .. } => "node_indexed_signed_less_than",
                _ => unreachable!(),
            };
            Ok(format!(
                "{theorem}({common}, left := {left}, right := {right}, output_found := {output}, left_found := {left_found}, right_found := {right_found})"
            ))
        }
    }
}

fn render_bound(bound: Option<u64>) -> String {
    match bound {
        None => "None".to_string(),
        Some(bound) => format!("Some({bound})"),
    }
}

fn prove_directory_lookup(
    theorem_name: &str,
    directory: Option<&Directory>,
    id: u64,
    width: u64,
    origin: Origin,
) -> Result<String, String> {
    let Some(directory) = directory else {
        return Err(format!("value {id} is absent from the directory"));
    };
    if id == directory.entry.port.id {
        if width != directory.entry.port.width || origin != directory.entry.origin {
            return Err(format!("value {id} has inconsistent directory metadata"));
        }
        return Ok(format!(
            "directory_has_here(left := {}, right := {}, entry := {})",
            directory_child_ref(theorem_name, directory.left.as_deref()),
            directory_child_ref(theorem_name, directory.right.as_deref()),
            render_directory_entry(directory.entry)
        ));
    }
    if id < directory.entry.port.id {
        let found =
            prove_directory_lookup(theorem_name, directory.left.as_deref(), id, width, origin)?;
        Ok(format!(
            "directory_has_left(left := {}, right := {}, entry := {}, found := {found})",
            directory_child_ref(theorem_name, directory.left.as_deref()),
            directory_child_ref(theorem_name, directory.right.as_deref()),
            render_directory_entry(directory.entry)
        ))
    } else {
        let found =
            prove_directory_lookup(theorem_name, directory.right.as_deref(), id, width, origin)?;
        Ok(format!(
            "directory_has_right(left := {}, right := {}, entry := {}, found := {found})",
            directory_child_ref(theorem_name, directory.left.as_deref()),
            directory_child_ref(theorem_name, directory.right.as_deref()),
            render_directory_entry(directory.entry)
        ))
    }
}

fn prove_available_from_fact(
    entries: &[DirectoryEntry],
    theorem_name: &str,
    id: u64,
    width: u64,
    before: u64,
) -> Result<String, String> {
    let entry = find_entry(entries, id, width)?;
    let fact = format!("{}()", port_fact_name(theorem_name, id));
    match entry.origin {
        Origin::Input(index) => Ok(format!("available_input({index}, {before}, {fact})")),
        Origin::Node(index) if index < before => Ok(format!(
            "available_node({index}, {before}, {fact}, trivial)"
        )),
        Origin::Node(_) => Err(format!("value {id} is not available before node {before}")),
    }
}

fn render_origin(origin: Origin) -> String {
    match origin {
        Origin::Input(index) => format!("InputAt({index})"),
        Origin::Node(index) => format!("NodeAt({index})"),
    }
}

fn port_fact_name(theorem_name: &str, id: u64) -> String {
    format!("{theorem_name}_port_{id}")
}

fn node_list_name(theorem_name: &str, index: usize) -> String {
    format!("{theorem_name}_nodes_at_{index}")
}

fn nodes_proof_name(theorem_name: &str, index: usize) -> String {
    format!("{theorem_name}_nodes_indexed_at_{index}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_bad_models_before_emission() {
        let duplicate = Region {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 0, width: 64 }],
            nodes: vec![],
            outputs: vec![],
        };
        assert!(
            generate("bad", "bad()", &duplicate)
                .unwrap_err()
                .contains("already defined")
        );
        let future_reference = Region {
            inputs: vec![Port { id: 0, width: 64 }],
            nodes: vec![Node::Add {
                width: 64,
                output: 1,
                left: 0,
                right: 2,
            }],
            outputs: vec![],
        };
        assert!(
            generate("future", "future()", &future_reference)
                .unwrap_err()
                .contains("undefined")
        );

        let duplicate_output = Region {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
            nodes: vec![
                Node::Add {
                    width: 64,
                    output: 2,
                    left: 0,
                    right: 1,
                },
                Node::Add {
                    width: 64,
                    output: 2,
                    left: 0,
                    right: 1,
                },
            ],
            outputs: vec![],
        };
        assert!(
            generate("duplicate", "duplicate()", &duplicate_output)
                .unwrap_err()
                .contains("already defined")
        );

        let wrong_output_width = Region {
            inputs: vec![Port { id: 0, width: 8 }],
            nodes: vec![],
            outputs: vec![Port { id: 0, width: 64 }],
        };
        assert!(
            generate("width", "width()", &wrong_output_width)
                .unwrap_err()
                .contains("not requested width")
        );
    }

    #[test]
    fn structured_conditionals_reject_captures_and_interface_mismatches() {
        let arguments = vec![Port { id: 0, width: 64 }];
        let output = vec![Port { id: 2, width: 64 }];
        let leaf = |inputs: Vec<Port>, outputs: Vec<Port>| {
            StructuredRegion::Dataflow(Region {
                inputs,
                nodes: vec![],
                outputs,
            })
        };
        let valid = StructuredRegion::Conditional {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 1 }],
            condition: 1,
            arguments: arguments.clone(),
            outputs: output.clone(),
            when_true: Box::new(leaf(arguments.clone(), output.clone())),
            when_false: Box::new(leaf(arguments.clone(), output.clone())),
        };
        // Empty leaves cannot actually yield the requested output, so flat
        // validation remains authoritative inside the structural check.
        assert!(
            validate_structured_region(&valid)
                .unwrap_err()
                .contains("undefined")
        );

        let producing_leaf = |inputs: Vec<Port>| {
            StructuredRegion::Dataflow(Region {
                inputs,
                nodes: vec![Node::Const {
                    width: 64,
                    output: 2,
                    value: 0,
                }],
                outputs: output.clone(),
            })
        };
        let valid = StructuredRegion::Conditional {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 1 }],
            condition: 1,
            arguments: arguments.clone(),
            outputs: output.clone(),
            when_true: Box::new(producing_leaf(arguments.clone())),
            when_false: Box::new(producing_leaf(arguments.clone())),
        };
        assert_eq!(validate_structured_region(&valid), Ok(()));

        let mut unavailable = valid.clone();
        if let StructuredRegion::Conditional { condition, .. } = &mut unavailable {
            *condition = 99;
        }
        assert!(
            validate_structured_region(&unavailable)
                .unwrap_err()
                .contains("not an available one-bit input")
        );

        let mut mismatched_yield = valid.clone();
        if let StructuredRegion::Conditional { when_false, .. } = &mut mismatched_yield {
            *when_false = Box::new(producing_leaf(vec![Port { id: 0, width: 64 }]));
            if let StructuredRegion::Dataflow(region) = &mut **when_false {
                region.outputs[0].width = 32;
            }
        }
        assert!(
            validate_structured_region(&mismatched_yield)
                .unwrap_err()
                .contains("yields a different interface")
        );

        let captured = StructuredRegion::Conditional {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 1 }],
            condition: 1,
            arguments: arguments.clone(),
            outputs: output.clone(),
            when_true: Box::new(producing_leaf(vec![
                Port { id: 0, width: 64 },
                Port { id: 9, width: 64 },
            ])),
            when_false: Box::new(producing_leaf(arguments)),
        };
        assert!(
            validate_structured_region(&captured)
                .unwrap_err()
                .contains("captures undeclared")
        );
    }

    #[test]
    fn structured_sequence_exposes_only_inputs_and_declared_prefix_outputs() {
        let prefix = Region {
            inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
            nodes: vec![Node::UnsignedLessThan {
                width: 64,
                output: 2,
                left: 0,
                right: 1,
            }],
            outputs: vec![Port { id: 2, width: 1 }],
        };
        let continuation = |condition| StructuredRegion::Conditional {
            inputs: vec![
                Port { id: 0, width: 64 },
                Port { id: 1, width: 64 },
                Port {
                    id: condition,
                    width: 1,
                },
            ],
            condition,
            arguments: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
            outputs: vec![Port { id: 3, width: 64 }],
            when_true: Box::new(StructuredRegion::Dataflow(Region {
                inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
                nodes: vec![Node::Add {
                    width: 64,
                    output: 3,
                    left: 0,
                    right: 1,
                }],
                outputs: vec![Port { id: 3, width: 64 }],
            })),
            when_false: Box::new(StructuredRegion::Dataflow(Region {
                inputs: vec![Port { id: 0, width: 64 }, Port { id: 1, width: 64 }],
                nodes: vec![Node::Sub {
                    width: 64,
                    output: 3,
                    left: 0,
                    right: 1,
                }],
                outputs: vec![Port { id: 3, width: 64 }],
            })),
        };
        let valid = StructuredRegion::Sequence {
            prefix: prefix.clone(),
            continuation: Box::new(continuation(2)),
        };
        assert_eq!(validate_structured_region(&valid), Ok(()));

        let unavailable = StructuredRegion::Sequence {
            prefix,
            continuation: Box::new(continuation(9)),
        };
        assert!(
            validate_structured_region(&unavailable)
                .unwrap_err()
                .contains("not available from the prefix")
        );
    }
}
