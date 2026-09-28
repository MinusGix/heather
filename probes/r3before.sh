set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 8 | head -40
echo "=== WORKLOAD ==="
rm -rf /tmp/k1 /tmp/imgA; mkdir -p /tmp/k1
(ulimit -v 8388608 -t 1800; HEATHER_KERNEL_WORKERS=1 target/release/heather build-x86 \
  examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1 \
  -o /tmp/k1/caller --cache-dir /tmp/imgA --kernel-workers 1 --timings /tmp/k1/t.tsv) 2>&1 | tail -3
echo "=== AGG ==="
python3 probes/agg.py /tmp/k1/t.tsv
echo "=== UNITPROBES ==="
rm -rf /tmp/pc1
(ulimit -v 6291456 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache --cache-dir /tmp/pc1 \
   -L lib/std -L lib probes/t_*.hthr 2>&1 | grep -E "^item	t_")
echo "=== DONE ==="
