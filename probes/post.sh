set -x
echo "== post start $(date -u +%T) =="
cd "$(dirname "$0")/.."
( ulimit -v 8388608 -t 900
  cargo test -p heather-elab --lib tycode 2>&1 | tail -12 )
cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling --no-run 2>&1 | grep -E "^error" -A 8 | head -20
for n in 5 20; do
  echo "=== artifact item at $n nodes ==="
  ( ulimit -v 16777216 -t 1800
    HEATHER_FUNCTION_IR_X86_NODES=$n HEATHER_TIMINGS=/tmp/p$n.tsv \
    cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling slow_acceptance -- --nocapture --exact slow_acceptance_generated_20_node_mixed_binary_alu_dag_checks 2>&1 | grep -E "test result" )
  awk -F'\t' 'NR==1{for(i=1;i<=NF;i++)h[$i]=i} NR>1 && $3 ~ /mixed_binary_alu_x86_artifact/ {printf "item=%s kernel_ns=%s misses=%s steps=%s\n", $3, $8, $43, $46}' /tmp/p$n.tsv
  awk -F'\t' 'NR>1 && $1=="module" {printf "module kernel_ns=%s steps=%s\n", $8, $46}' /tmp/p$n.tsv | tail -2
done
echo "=== ALL DONE ==="
