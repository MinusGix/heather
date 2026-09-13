#[path = "function_ir_x86.rs"]
mod common;

#[test]
#[ignore = "20/100-node elaborated source-to-x86 scaling rail; run explicitly"]
fn elaborated_source_x86_scaling() {
    common::elaborated_source_x86_scaling();
}

/// The 20-node FunctionIR/x86 rail, a **gate** in the full lane since
/// `docs/x86-scaling-rail-out-of-fuel-design.md` §4. It is the regression pin
/// for the projection boundary: the moment a record's field type and a
/// statement written against the same computed state stop spelling a field
/// read alike, the artifact theorem's conversion falls to symbolically
/// executing the whole block and the kernel refuses it `OutOfFuel` — under the
/// committed budgets, with nothing to tune. `slow_acceptance_` is `scripts/test`'s
/// own opt-in: the fast lane filters that prefix, the full lane runs it
/// (~5 s warm, ~16 s cold on the semantic image store, well inside the rail).
#[test]
fn slow_acceptance_generated_20_node_mixed_binary_alu_dag_checks() {
    common::generated_20_node_mixed_binary_alu_dag_checks();
}

/// 50 nodes stays an explicit stress rail: the same harness one size up, run
/// by hand when the boundary or the generator moves.
#[test]
#[ignore = "50-node FunctionIR/x86 stress rail; run explicitly"]
fn generated_50_node_mixed_binary_alu_dag_checks() {
    common::generated_50_node_mixed_binary_alu_dag_checks();
}
