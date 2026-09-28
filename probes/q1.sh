set -x
echo "== q1 start $(date -u +%T) =="
cd "$(dirname "$0")/.."
cargo test -p heather-elab --test function_ir_x86_scaling --no-run 2>&1 | grep -E "^error" -A 10 | head -30
cargo test -p heather-cli --test native_summary --no-run 2>&1 | tail -2
echo "=== B: SHALLOW rail 20 ==="
( ulimit -v 16777216 -t 1800
  RUST_MIN_STACK=8388608 HEATHER_FUNCTION_IR_X86_NODES=20 \
  cargo test -p heather-elab --test function_ir_x86_scaling generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -E "test result|rejected|panicked|finished in" | cut -c1-200 )
echo "=== C: SHALLOW rail 50 ==="
( ulimit -v 16777216 -t 3000
  RUST_MIN_STACK=8388608 HEATHER_FUNCTION_IR_X86_NODES=50 \
  cargo test -p heather-elab --test function_ir_x86_scaling generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -E "test result|rejected|panicked|finished in" | cut -c1-200 )
echo "=== E: native_summary SHALLOW ==="
rm -rf target/native-test-images
( ulimit -v 16777216 -t 2400
  cargo test -p heather-cli --test native_summary -- --nocapture 2>&1 | grep -E "test result|rejected|panicked|OutOfFuel|finished in" | cut -c1-200 )
echo "=== F: native_calls + native + stack_local SHALLOW ==="
rm -rf target/native-test-images
( ulimit -v 16777216 -t 3000
  cargo test -p heather-cli --test native_calls --test native --test native_stack_local 2>&1 | grep -E "test result|rejected|panicked|OutOfFuel|finished in" | cut -c1-200 )
echo "=== ALL DONE ==="
