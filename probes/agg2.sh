set -x
echo "== agg2 start $(date -u +%T) =="
cd "$(dirname "$0")/.."
for m in neutral chain; do
  echo "=== TOTALS mode=$m ==="
  if [ -f /tmp/k1-$m/t.tsv ]; then python3 probes/agg.py /tmp/k1-$m/t.tsv | tail -8; else echo "MISSING /tmp/k1-$m/t.tsv"; fi
done
echo "=== compile check of the landed boundary ==="
cargo test -p heather-elab --lib --no-run 2>&1 | grep -E "^(error|warning)" -A 12 | head -60
echo "=== new unit probes ==="
( ulimit -v 8388608 -t 900
  cargo test -p heather-elab --lib tycode_fn 2>&1 | tail -20 )
echo "=== promoted rail (default 20 nodes, committed budgets) ==="
rm -rf target/semantic-test-images
( ulimit -v 16777216 -t 1800
  cargo test -p heather-elab --test function_ir_x86_scaling 2>&1 | tail -8 )
echo "=== 50-node stress rail ==="
( ulimit -v 16777216 -t 3000
  cargo test -p heather-elab --test function_ir_x86_scaling generated_50_node -- --ignored --exact generated_50_node_mixed_binary_alu_dag_checks 2>&1 | tail -6 )
echo "=== ALL DONE ==="
