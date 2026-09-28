set -x
mkdir -p /tmp/archL && cp lib/std/arch/x86_64/model.hthr /tmp/archL/x86_64.hthr
rm -rf /tmp/pcB /tmp/pcC /tmp/pcD
echo "=== P2 ==="
(ulimit -v 6291456 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/pcB -L lib/std -L lib probes/t_p2_lit_split.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== P3B ==="
(ulimit -v 6291456 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/pcC -L lib/std -L lib probes/t_p3b_ofnat_parts.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== P4 ==="
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/pcD -L lib/std -L lib -L /tmp/archL probes/t_p4_mov_imm64.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== DONE ==="
