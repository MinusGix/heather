set -x
mkdir -p /tmp/w1
echo "== w1 start $(date -u +%T) =="
cd "$(dirname "$0")/.."
cargo test -p heather-elab --test function_ir_x86_scaling --no-run 2>&1 | tail -3
cargo test -p heather-cli --test native_summary --no-run 2>&1 | tail -3
echo "=== A: baseline rail (no widen) ==="
( ulimit -v 16777216 -t 1200
  RUST_MIN_STACK=8388608 HEATHER_FUNCTION_IR_X86_NODES=20 \
  cargo test -p heather-elab --test function_ir_x86_scaling generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -E "test result|rejected|panicked|finished in" | cut -c1-200 )
echo "=== B: WIDEN rail 20 ==="
( ulimit -v 16777216 -t 1800
  RUST_MIN_STACK=8388608 HEATHER_PROJ_WIDEN=1 HEATHER_FUNCTION_IR_X86_NODES=20 \
  cargo test -p heather-elab --test function_ir_x86_scaling generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -E "test result|rejected|panicked|finished in" | cut -c1-200 )
echo "=== C: WIDEN rail 50 ==="
( ulimit -v 16777216 -t 3000
  RUST_MIN_STACK=8388608 HEATHER_PROJ_WIDEN=1 HEATHER_FUNCTION_IR_X86_NODES=50 \
  cargo test -p heather-elab --test function_ir_x86_scaling generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -E "test result|rejected|panicked|finished in" | cut -c1-200 )
echo "=== D: native_summary baseline ==="
( ulimit -v 16777216 -t 2400
  cargo test -p heather-cli --test native_summary -- --nocapture 2>&1 | grep -E "test result|rejected|panicked|OutOfFuel|finished in" | cut -c1-200 )
echo "=== E: native_summary WIDEN ==="
( ulimit -v 16777216 -t 2400
  HEATHER_PROJ_WIDEN=1 cargo test -p heather-cli --test native_summary -- --nocapture 2>&1 | grep -E "test result|rejected|panicked|OutOfFuel|finished in" | cut -c1-200 )
echo "=== ALL DONE ==="
