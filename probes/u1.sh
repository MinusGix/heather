set -x
echo "== u1 start $(date -u +%T) =="
cd "$(dirname "$0")/.."
cargo test -p heather-elab --test function_ir_x86_scaling --no-run 2>&1 | grep -E "^error" -A 10 | head -30
cargo test -p heather-cli --test native_summary --no-run 2>&1 | tail -1
for m in chain neutral; do
echo "=== rail 20 mode=$m ==="
( ulimit -v 16777216 -t 1800
  RUST_MIN_STACK=8388608 HEATHER_PROJ_GATE=$m HEATHER_FUNCTION_IR_X86_NODES=20 \
  cargo test -p heather-elab --test function_ir_x86_scaling generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -E "test result|rejected|panicked" | cut -c1-160 )
done
echo "=== rail 50 mode=chain ==="
( ulimit -v 16777216 -t 3000
  RUST_MIN_STACK=8388608 HEATHER_PROJ_GATE=chain HEATHER_FUNCTION_IR_X86_NODES=50 \
  cargo test -p heather-elab --test function_ir_x86_scaling generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -E "test result|rejected|panicked" | cut -c1-160 )
echo "=== native_summary mode=chain ==="
rm -rf target/native-test-images
( ulimit -v 16777216 -t 2400
  HEATHER_PROJ_GATE=chain cargo test -p heather-cli --test native_summary -- --nocapture 2>&1 | grep -E "test result|rejected|panicked|OutOfFuel" | cut -c1-160 )
echo "=== ALL DONE ==="
