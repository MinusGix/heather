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
    }
}
