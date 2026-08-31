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
pub struct AddNode {
    pub width: u64,
    pub output: u64,
    pub left: u64,
    pub right: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Region {
    pub inputs: Vec<Port>,
    pub nodes: Vec<AddNode>,
    pub outputs: Vec<Port>,
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

/// Render a certificate for `region_expr`, which should be a closed Heather
/// expression such as `sum4_left_first_raw()`.
pub fn generate(
    theorem_name: &str,
    region_expr: &str,
    region: &Region,
) -> Result<Emission, String> {
    let inputs_unique = unique(&region.inputs)?;
    let mut definitions = region.inputs.clone();
    let mut node_proofs = Vec::with_capacity(region.nodes.len());
    for (index, node) in region.nodes.iter().enumerate() {
        let left = lookup(&definitions, node.left, node.width)
            .map_err(|why| format!("node {index}'s left operand is invalid: {why}"))?;
        let right = lookup(&definitions, node.right, node.width)
            .map_err(|why| format!("node {index}'s right operand is invalid: {why}"))?;
        let fresh = fresh(&definitions, node.output)
            .map_err(|why| format!("node {index}'s output is invalid: {why}"))?;
        node_proofs.push(pair(left, pair(right, fresh)));
        definitions.insert(
            0,
            Port {
                id: node.output,
                width: node.width,
            },
        );
    }
    let nodes_valid = conjunction(node_proofs);

    let mut output_proofs = Vec::with_capacity(region.outputs.len());
    for (index, output) in region.outputs.iter().enumerate() {
        output_proofs.push(
            lookup(&definitions, output.id, output.width)
                .map_err(|why| format!("output {index} is invalid: {why}"))?,
        );
    }
    let outputs_valid = conjunction(output_proofs);

    let text = format!(
        "theorem {theorem_name}(): RegionValid({region_expr}) {{\n\
         \x20   RegionValid {{\n\
         \x20       inputs_unique: {inputs_unique},\n\
         \x20       nodes_valid: {nodes_valid},\n\
         \x20       outputs_valid: {outputs_valid},\n\
         \x20   }}\n\
         }}\n"
    );
    Ok(Emission {
        theorem_name: theorem_name.to_string(),
        text,
    })
}

/// Render the experimental directory/rank certificate. Unlike `generate`,
/// its proof size is linearithmic: the directory ordering proof is linear and
/// every declaration/use follows one path through a balanced tree.
pub fn generate_v2(
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
        let fact_name = v2_port_fact_name(theorem_name, entry.port.id);
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
            v2_port_fact_name(theorem_name, port.id),
        );
    }

    let terminal_nodes_name = v2_nodes_name(theorem_name, region.nodes.len());
    let terminal_proof_name = v2_nodes_proof_name(theorem_name, region.nodes.len());
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
        let output = format!("{}()", v2_port_fact_name(theorem_name, node.output));
        let left = prove_available_from_fact(&entries, theorem_name, node.left, node.width, rank)?;
        let right =
            prove_available_from_fact(&entries, theorem_name, node.right, node.width, rank)?;
        let head = format!(
            "node_indexed_add(directory := {directory_name}(), index := {index}, width := {}, output := {}, left := {}, right := {}, output_found := {output}, left_found := {left}, right_found := {right})",
            node.width, node.output, node.left, node.right,
        );
        let nodes_name = v2_nodes_name(theorem_name, index);
        let next_nodes_name = v2_nodes_name(theorem_name, index + 1);
        let proof_name = v2_nodes_proof_name(theorem_name, index);
        let next_proof_name = v2_nodes_proof_name(theorem_name, index + 1);
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
    let nodes_indexed = format!("{}()", v2_nodes_proof_name(theorem_name, 0));

    let mut outputs_indexed =
        format!("output_entries_indexed_nil(directory := {directory_name}())");
    for port in region.outputs.iter().rev() {
        find_entry(&entries, port.id, port.width)?;
        let found = format!(
            "directory_port_exists({}())",
            v2_port_fact_name(theorem_name, port.id)
        );
        outputs_indexed = format!(
            "output_entries_indexed_cons(output := {}, found := {found}, tail := {outputs_indexed})",
            render_port(*port),
        );
    }

    let text = format!(
        "{declarations}\
         theorem {theorem_name}(): RegionValidV2({region_expr}) {{\n\
         \x20   RegionValidV2 {{\n\
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
        .map(|n| {
            format!(
                "Add(width := {}, output := {}, left := {}, right := {})",
                n.width, n.output, n.left, n.right
            )
        })
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

fn lookup(definitions: &[Port], id: u64, width: u64) -> Result<String, String> {
    let Some(position) = definitions
        .iter()
        .position(|port| port.id == id && port.width == width)
    else {
        if let Some(port) = definitions.iter().find(|port| port.id == id) {
            return Err(format!(
                "value {id} has width {}, not requested width {width}",
                port.width
            ));
        }
        return Err(format!("value {id} is undefined"));
    };
    let mut proof = "⟨⟨refl, refl⟩ |⟩".to_string();
    for _ in 0..position {
        proof = format!("⟨| {proof}⟩");
    }
    Ok(proof)
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
        find_entry(&entries, node.left, node.width)
            .map_err(|why| format!("node {index}'s left operand is invalid: {why}"))?;
        find_entry(&entries, node.right, node.width)
            .map_err(|why| format!("node {index}'s right operand is invalid: {why}"))?;
        insert_entry(
            &mut entries,
            DirectoryEntry {
                port: Port {
                    id: node.output,
                    width: node.width,
                },
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

fn render_node(node: AddNode) -> String {
    format!(
        "Add(width := {}, output := {}, left := {}, right := {})",
        node.width, node.output, node.left, node.right
    )
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
    let fact = format!("{}()", v2_port_fact_name(theorem_name, id));
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

fn v2_port_fact_name(theorem_name: &str, id: u64) -> String {
    format!("{theorem_name}_port_{id}")
}

fn v2_nodes_name(theorem_name: &str, index: usize) -> String {
    format!("{theorem_name}_nodes_at_{index}")
}

fn v2_nodes_proof_name(theorem_name: &str, index: usize) -> String {
    format!("{theorem_name}_nodes_indexed_at_{index}")
}

fn fresh(definitions: &[Port], id: u64) -> Result<String, String> {
    let mut proofs = Vec::with_capacity(definitions.len());
    for port in definitions {
        if id == port.id {
            return Err(format!("value {id} is already defined"));
        }
        proofs.push(distinct(id, port.id));
    }
    Ok(conjunction(proofs))
}

fn unique(entries: &[Port]) -> Result<String, String> {
    let mut proof = "trivial".to_string();
    for index in (0..entries.len()).rev() {
        proof = pair(fresh(&entries[index + 1..], entries[index].id)?, proof);
    }
    Ok(proof)
}

fn distinct(left: u64, right: u64) -> String {
    if left < right {
        format!("nat::ne_of_lt({left}, {right}, trivial)")
    } else {
        format!("nat::ne_of_gt({left}, {right}, trivial)")
    }
}

fn pair(left: String, right: String) -> String {
    format!("⟨{left}, {right}⟩")
}

fn conjunction(proofs: Vec<String>) -> String {
    proofs
        .into_iter()
        .rev()
        .fold("trivial".to_string(), |rest, proof| pair(proof, rest))
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
        assert!(generate("bad", "bad()", &duplicate)
            .unwrap_err()
            .contains("already defined"));
        assert!(generate_v2("bad_v2", "bad()", &duplicate)
            .unwrap_err()
            .contains("already defined"));

        let future_reference = Region {
            inputs: vec![Port { id: 0, width: 64 }],
            nodes: vec![AddNode {
                width: 64,
                output: 1,
                left: 0,
                right: 2,
            }],
            outputs: vec![],
        };
        assert!(generate_v2("future", "future()", &future_reference)
            .unwrap_err()
            .contains("undefined"));
    }
}
