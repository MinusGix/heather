set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^error' -A 10 | head -30
echo "=== BUILT ==="
( ulimit -v 6291456 -t 300; HEATHER_PROJ_MATCH=1 HEATHER_PROJ_DUMP=Cur target/release/heather check \
   --kernel-workers 1 probes/t_pc1.hthr 2>&1 | grep -A 2 '^#dump' | head -12 )
echo "=== DIAG6 DONE ==="
