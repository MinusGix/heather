# Checkpoint job (2026-09-13): is the perf detour over? Family table on the
# reused_callee recipe (release, value-metrics, W=1) plus the x86 scaling rail
# at 20/50/100 nodes with per-item timings (dev profile, comparable to the
# issue's own 64.5 s / 154.1 s datum).
set -x
echo "== start $(date -u +%FT%TZ) rev=$(git rev-parse --short HEAD) =="
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 8 | head -40
cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling --no-run 2>&1 | grep -E "^error" -A 8 | head -40
echo "=== BUILT ==="
rm -rf /tmp/k1 /tmp/imgA; mkdir -p /tmp/k1
(ulimit -v 8388608 -t 1800; HEATHER_KERNEL_WORKERS=1 target/release/heather build-x86 \
  examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1 \
  -o /tmp/k1/caller --cache-dir /tmp/imgA --kernel-workers 1 --timings /tmp/k1/t.tsv) 2>&1 | tail -3
echo "=== AGG reused_callee ==="
python3 probes/agg.py /tmp/k1/t.tsv
for n in 20 50 100; do
  echo "=== SCALING n=$n start $(date -u +%T) ==="
  ( ulimit -v 16777216 -t 3600
    HEATHER_FUNCTION_IR_X86_NODES=$n HEATHER_TIMINGS=/tmp/k1/scal_$n.tsv HEATHER_FUNCTION_IR_X86_VALUE_METRICS=1 \
    cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling \
      generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -vE "^\s+(Compiling|Finished|Running)" | tail -25 )
  echo "=== SCALING n=$n exit=$? end $(date -u +%T) ==="
  echo "--- agg n=$n ---"; python3 probes/agg.py /tmp/k1/scal_$n.tsv 2>&1 | head -60
done
echo "=== ALL DONE exit=0 $(date -u +%FT%TZ) ==="
