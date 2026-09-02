#[path = "function_ir_x86.rs"]
mod common;

#[test]
#[ignore = "20/100-node elaborated source-to-x86 scaling rail; run explicitly"]
fn elaborated_source_x86_scaling() {
    common::elaborated_source_x86_scaling();
}

#[test]
#[ignore = "20-node FunctionIR/x86 scaling rail; run explicitly"]
fn generated_20_node_mixed_binary_alu_dag_checks() {
    common::generated_20_node_mixed_binary_alu_dag_checks();
}
