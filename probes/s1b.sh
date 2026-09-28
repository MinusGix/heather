set -x
mkdir -p /tmp/archL && cp lib/std/arch/x86_64/model.hthr /tmp/archL/x86_64.hthr
echo "=== BEFORE: build ==="
cp probes/bitvec_before.hthr lib/std/bitvec.hthr
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 8 | head -20
echo "=== BEFORE: workload (cold) ==="
rm -rf /tmp/s1b /tmp/imgB; mkdir -p /tmp/s1b
(ulimit -v 8388608 -t 1800; HEATHER_KERNEL_WORKERS=1 target/release/heather build-x86 \
  examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1 \
  -o /tmp/s1b/caller --cache-dir /tmp/imgB --kernel-workers 1 --timings /tmp/s1b/t.tsv) 2>&1 | tail -3
python3 probes/agg.py /tmp/s1b/t.tsv
echo "=== AFTER: build ==="
cp probes/bitvec_after.hthr lib/std/bitvec.hthr
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 8 | head -20
echo "=== AFTER: workload (cold) ==="
rm -rf /tmp/s1a /tmp/imgA; mkdir -p /tmp/s1a
(ulimit -v 8388608 -t 1800; HEATHER_KERNEL_WORKERS=1 target/release/heather build-x86 \
  examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1 \
  -o /tmp/s1a/caller --cache-dir /tmp/imgA --kernel-workers 1 --timings /tmp/s1a/t.tsv) 2>&1 | tail -3
python3 probes/agg.py /tmp/s1a/t.tsv
echo "=== PROBES AFTER ==="
rm -rf /tmp/s1p /tmp/s1q
(ulimit -v 6291456 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/s1p -L lib/std -L lib probes/t_a1_lib_xor.hthr probes/t_a3_literal.hthr \
   probes/t_a4_lib_add.hthr probes/t_c1_tonat.hthr probes/t_c2_is_zero.hthr 2>&1 | grep -E "^(item|error)") || true
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/s1q -L lib/std -L lib -L /tmp/archL probes/t_p4_mov_imm64.hthr 2>&1 | grep -E "^(item|error)") || true
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/s1r -L lib/std -L lib probes/t_v4_mag.hthr 2>&1 | grep -E "^(item	v4_ship|error)") || true
echo "=== DONE ==="
