set -x
echo "== start $(date -u +%FT%TZ) =="
md5sum lib/std/bitvec.hthr
for n in 5 20; do
  echo "=== SCALING n=$n start $(date -u +%T) ==="
  ( ulimit -v 16777216 -t 3600
    HEATHER_FUNCTION_IR_X86_NODES=$n HEATHER_TIMINGS=/tmp/k1/bisA_$n.tsv \
    cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling \
      generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact 2>&1 | grep -vE "^\s+(Compiling|Finished|Running)|^warning|^ *=|^ *\||^ *[0-9]* *\|" | tail -12 )
  echo "=== SCALING n=$n end $(date -u +%T) ==="
  python3 probes/agg.py /tmp/k1/bisA_$n.tsv 2>&1 | tail -4
done
echo "=== ALL DONE exit=0 ==="
