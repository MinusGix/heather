echo "== remote start $(date -u +%T) =="
grep -n "^pub const NATIVE_DEPTH_LIMIT" crates/kernel/src/reduce.rs 2>/dev/null
cargo test -p heather-elab --test function_ir_x86_scaling --no-run 2>&1 | grep -E "^error" -A 8 | head -30
( ulimit -v 16777216 -t 900
  RUST_MIN_STACK=8388608 HEATHER_FUNCTION_IR_X86_NODES=20 \
  cargo test -p heather-elab --test function_ir_x86_scaling generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -E "test result|rejected|panicked|finished in" | cut -c1-300 )
echo "== remote end $(date -u +%T) =="
echo "=== ALL DONE ==="
