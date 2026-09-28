set -x
rm -rf /tmp/k4 /tmp/imgK4; mkdir -p /tmp/k4
(ulimit -v 8388608 -t 1800; HEATHER_KERNEL_WORKERS=1 target/release/heather build-x86 \
  examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1 \
  -o /tmp/k4/caller --cache-dir /tmp/imgK4 --kernel-workers 1 --timings /tmp/k4/t.tsv) 2>&1 | tail -3
echo "=== AGG ==="
python3 probes/agg.py /tmp/k4/t.tsv
echo "=== DONE ==="
