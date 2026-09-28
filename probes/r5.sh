set -x
echo "== r5 start $(date -u +%T) =="
cd "$(dirname "$0")/.."
cargo test -p heather-elab --lib --no-run 2>&1 | grep -E "^(error|warning: unused)" -A 10 | head -40
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 8 | head -40
for m in neutral chain; do
  rm -rf /tmp/k1-$m /tmp/img-$m; mkdir -p /tmp/k1-$m
  echo "=== reused_callee mode=$m ==="
  (ulimit -v 8388608 -t 2400; HEATHER_PROJ_GATE=$m HEATHER_KERNEL_WORKERS=1 target/release/heather build-x86 \
    examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1 \
    -o /tmp/k1-$m/caller --cache-dir /tmp/img-$m --kernel-workers 1 --timings /tmp/k1-$m/t.tsv) 2>&1 | tail -2
  python3 probes/agg.py /tmp/k1-$m/t.tsv 2>&1 | head -25
done
echo "=== ALL DONE ==="
