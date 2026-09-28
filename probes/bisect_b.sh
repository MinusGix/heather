set -x
echo "== start $(date -u +%FT%TZ) =="
grep -n "^pub const NATIVE_DEPTH_LIMIT" crates/kernel/src/reduce.rs
cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling --no-run 2>&1 | grep -E "^error" -A 8 | head -40
echo "=== BUILT ==="
for n in 20 50; do
  echo "=== SCALING n=$n start $(date -u +%T) ==="
  ( ulimit -v 16777216 -t 3600
    RUST_MIN_STACK=67108864 HEATHER_FUNCTION_IR_X86_NODES=$n HEATHER_TIMINGS=/tmp/k1/bisB_$n.tsv HEATHER_FUNCTION_IR_X86_VALUE_METRICS=1 \
    cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling \
      generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -vE "^\s+(Compiling|Finished|Running)|^warning|^ *=|^ *\||^ *[0-9]* *\|" | grep -E "metrics|result|rejected|panicked|finished" | cut -c1-2000 )
  echo "=== SCALING n=$n end $(date -u +%T) ==="
  python3 probes/agg.py /tmp/k1/bisB_$n.tsv 2>&1 | tail -3
done
echo "=== ALL DONE exit=0 ==="
