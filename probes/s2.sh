set -x
mkdir -p /tmp/archL && cp lib/std/arch/x86_64/model.hthr /tmp/archL/x86_64.hthr
echo "=== BEFORE (step 1 only): revert kernel, build ==="
patch -p1 -R --batch < probes/step2.patch
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 8 | head -20
echo "=== BEFORE: workload (cold) ==="
rm -rf /tmp/s2b /tmp/imgB2; mkdir -p /tmp/s2b
(ulimit -v 8388608 -t 1800; HEATHER_KERNEL_WORKERS=1 target/release/heather build-x86 \
  examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1 \
  -o /tmp/s2b/caller --cache-dir /tmp/imgB2 --kernel-workers 1 --timings /tmp/s2b/t.tsv) 2>&1 | tail -3
python3 probes/agg.py /tmp/s2b/t.tsv
echo "=== AFTER: apply kernel, build ==="
patch -p1 --batch < probes/step2.patch
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 8 | head -20
echo "=== AFTER: workload (cold) ==="
rm -rf /tmp/s2a /tmp/imgA2; mkdir -p /tmp/s2a
(ulimit -v 8388608 -t 1800; HEATHER_KERNEL_WORKERS=1 target/release/heather build-x86 \
  examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1 \
  -o /tmp/s2a/caller --cache-dir /tmp/imgA2 --kernel-workers 1 --timings /tmp/s2a/t.tsv) 2>&1 | tail -3
python3 probes/agg.py /tmp/s2a/t.tsv
echo "=== PROBES AFTER ==="
rm -rf /tmp/s2p /tmp/s2q
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/s2p -L lib/std -L lib -L /tmp/archL probes/t_p4_mov_imm64.hthr 2>&1 | grep -E "^(item|error)") || true
(ulimit -v 8388608 -t 900; HEATHER_TIMINGS=- target/release/heather check --cache \
   --cache-dir /tmp/s2q -L lib/std -L lib probes/t_v4_mag.hthr probes/t_p5_born.hthr 2>&1 | grep -E "^(item|error)") || true
echo "=== DONE ==="
