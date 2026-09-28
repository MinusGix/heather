set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^(error|warning: unused)" -A 8 | head -40
echo "=== BUILT ==="
mkdir -p /tmp/archL && cp lib/std/arch/x86_64/model.hthr /tmp/archL/x86_64.hthr
rm -rf /tmp/vA /tmp/vB /tmp/vC /tmp/vD /tmp/vE /tmp/vF
echo "=== P1 ==="
(ulimit -v 6291456 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/vA -L lib/std -L lib probes/t_a1_lib_xor.hthr probes/t_a3_literal.hthr \
   probes/t_a4_lib_add.hthr probes/t_c1_tonat.hthr probes/t_c2_is_zero.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== P2 ==="
(ulimit -v 6291456 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/vB -L lib/std -L lib probes/t_p2_lit_split.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== P3B ==="
(ulimit -v 6291456 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/vC -L lib/std -L lib probes/t_p3b_ofnat_parts.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== P3C ==="
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/vD -L lib/std -L lib probes/t_p3c_ofnat_halves.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== P4 ==="
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/vE -L lib/std -L lib -L /tmp/archL probes/t_p4_mov_imm64.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== V4 ==="
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/vF -L lib/std -L lib probes/t_v4_mag.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== DONE ==="
