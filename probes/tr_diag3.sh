set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -20
echo "=== BUILT ==="
( ulimit -v 6291456 -t 300; HEATHER_PROJ_MATCH=1 HEATHER_PROJ_DECLINE=1 target/release/heather check \
   --kernel-workers 1 probes/t_pc1.hthr 2>&1 | grep -E '^#' | head -80 )
echo "=== DIAG3 DONE ==="
