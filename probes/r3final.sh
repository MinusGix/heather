set -x
run_one () {
  tag=$1
  cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 8 | head -40
  rm -rf /tmp/k$tag /tmp/img$tag; mkdir -p /tmp/k$tag
  (ulimit -v 8388608 -t 1800; HEATHER_KERNEL_WORKERS=1 target/release/heather build-x86 \
    examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1 \
    -o /tmp/k$tag/caller --cache-dir /tmp/img$tag --kernel-workers 1 --timings /tmp/k$tag/t.tsv) 2>&1 | tail -2
  echo "=== AGG $tag ==="
  python3 probes/agg.py /tmp/k$tag/t.tsv
  echo "=== PROBES $tag ==="
  rm -rf /tmp/pc$tag
  (ulimit -v 6291456 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
     --cache-dir /tmp/pc$tag -L lib/std -L lib probes/t_*.hthr 2>&1 | grep -E "^item	t_")
}
patch -p1 -R --batch < probes/k1.patch
run_one BEFORE
patch -p1 --batch < probes/k1.patch
run_one AFTER
echo "=== DONE ==="
