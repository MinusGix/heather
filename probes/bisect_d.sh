echo "== artifact row n=20 (cols 3,8,40-52)"
head -1 /tmp/k1/bisC_20.tsv | cut -f3,8,40-52
grep -E "	mixed_binary_alu_x86_artifact	" /tmp/k1/bisC_20.tsv | cut -f3,8,40-52
for n in 5 20; do
  ( ulimit -v 16777216 -t 3600
    RUST_MIN_STACK=268435456 HEATHER_FUNCTION_IR_X86_NODES=$n HEATHER_TIMINGS=/tmp/k1/bisD_$n.tsv HEATHER_FUNCTION_IR_X86_VALUE_METRICS=1 \
    cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling \
      generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact > /tmp/k1/d$n.txt 2>&1 )
  echo "== n=$n artifact row"; grep -E "	mixed_binary_alu_x86_artifact	" /tmp/k1/bisD_$n.tsv | cut -f3,8,40-52
  echo "== n=$n result"; grep -E "test result" /tmp/k1/d$n.txt
  echo "== n=$n metrics/miss table"; grep -n -i -A 40 "value metrics" /tmp/k1/d$n.txt | cut -c1-400 | head -60
done
echo "=== ALL DONE ==="
