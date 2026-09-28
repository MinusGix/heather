set -x
echo "== full2 start $(date -u +%T) =="
cd "$(dirname "$0")/.."
scripts/test > /tmp/full2.txt 2>&1
echo "exit=$?"
grep -nE "^failures:|^test .* FAILED|panicked at|^error(\[|:)" /tmp/full2.txt | head -40
echo "--- failure blocks ---"
awk '/^failures:/,0' /tmp/full2.txt | head -60
echo "--- suite line ---"
grep -E "^== suite:|runner wall time" /tmp/full2.txt
echo "=== post measurements ==="
cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling --no-run 2>&1 | grep -E "^error" -A 8 | head -20
for n in 5 20; do
  echo "=== artifact item at $n nodes ==="
  ( ulimit -v 16777216 -t 1800
    HEATHER_FUNCTION_IR_X86_NODES=$n HEATHER_TIMINGS=/tmp/p$n.tsv \
    cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling slow_acceptance -- --exact slow_acceptance_generated_20_node_mixed_binary_alu_dag_checks 2>&1 | grep -E "test result" )
  awk -F'\t' 'NR>1 && $3 ~ /mixed_binary_alu_x86_artifact/ {printf "artifact kernel_ns=%s misses=%s steps=%s\n", $8, $43, $46}' /tmp/p$n.tsv
done
echo "=== ALL DONE ==="
