mkdir -p /tmp/attr
set -x
echo "== attr start $(date -u +%T) =="
cd "$(dirname "$0")/.."
cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling --no-run 2>&1 | tail -5
( ulimit -v 16777216 -t 1800
  RUST_MIN_STACK=8388608 HEATHER_FUNCTION_IR_X86_NODES=20 \
  HEATHER_FUNCTION_IR_X86_VALUE_METRICS=1 \
  HEATHER_FUNCTION_IR_X86_DUMP=/tmp/attr/mod20.hthr \
  HEATHER_CONV_MISS_TRACE=mixed_binary_alu_x86_artifact \
  HEATHER_PROJ_TRACE=1 \
  cargo test -p heather-elab --features value-metrics --test function_ir_x86_scaling generated_20_node_mixed_binary_alu_dag_checks -- --ignored --nocapture --exact > /tmp/attr/out.txt 2>&1 )
echo "exit=$?"
mkdir -p out
grep -c "^projtrace" /tmp/attr/out.txt
grep "^projtrace" /tmp/attr/out.txt | sort | uniq -c | sort -rn > out/projtrace.txt
head -80 out/projtrace.txt
echo "=== CONV MISS TRACE ==="
grep -A 3 "^conv miss trace" /tmp/attr/out.txt > out/convmiss.txt
wc -l out/convmiss.txt
head -120 out/convmiss.txt
echo "=== TAIL ==="
grep -v "^projtrace" /tmp/attr/out.txt | tail -60
cp /tmp/attr/mod20.hthr out/mod20.hthr 2>/dev/null
echo "=== ALL DONE ==="
