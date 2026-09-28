set -x
rm -rf /tmp/v3c
(ulimit -v 8388608 -t 300; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/v3c -L lib/std -L lib probes/t_v3_oddbit.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== DONE ==="
