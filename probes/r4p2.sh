set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 8 | head -40
echo "=== BUILT ==="
rm -rf /tmp/pcB /tmp/pcC /tmp/pcD
echo "=== P2P3 ==="
(ulimit -v 6291456 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/pcB -L lib/std -L lib probes/t_p2_lit_split.hthr probes/t_p3_ofnat.hthr 2>&1 | grep -vE "^item	(prelude|t_p2_lit_split	import|t_p3_ofnat	import)") || true
echo "=== P4 ==="
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/pcC -L lib/std -L lib probes/t_p4_mov_imm64.hthr 2>&1 | tail -40) || true
echo "=== DONE ==="
