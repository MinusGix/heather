set -x
mkdir -p /tmp/archL && cp lib/std/arch/x86_64/model.hthr /tmp/archL/x86_64.hthr
rm -rf /tmp/pcF /tmp/pcG
echo "=== P5 ==="
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/pcF -L lib/std -L lib probes/t_p5_born.hthr 2>&1 | grep -E "^(item	t_p5|error)") || true
echo "=== P4B ==="
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/pcG -L lib/std -L lib -L /tmp/archL probes/t_p4b_mov_half.hthr 2>&1 | grep -E "^(item	t_p4b|error)") || true
echo "=== DONE ==="
