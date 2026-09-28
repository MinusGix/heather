set -x
rm -rf /tmp/pcE
echo "=== P3C ==="
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/pcE -L lib/std -L lib probes/t_p3c_ofnat_halves.hthr 2>&1 | grep -E "^(item	t_p3c|error)") || true
echo "=== DONE ==="
