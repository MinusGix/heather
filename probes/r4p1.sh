set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 8 | head -40
echo "=== BUILT ==="
rm -rf /tmp/pcR4A
(ulimit -v 6291456 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/pcR4A -L lib/std -L lib probes/t_*.hthr 2>&1 | grep -E "^(item|scope)")
echo "=== DONE ==="
