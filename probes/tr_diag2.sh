set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E "^error" -A 10 | head -60
echo "=== BUILT ==="
( ulimit -v 6291456 -t 300; HEATHER_PROJ_MATCH=1 HEATHER_PROJ_DECLINE=1 target/release/heather check \
   --kernel-workers 1 probes/t_pc1.hthr 2>&1 | grep -E '^#(tycodefn|projdecline|projenter)' | sort | uniq -c | sort -rn | head -60 )
echo "--- match reasons"
( ulimit -v 6291456 -t 300; HEATHER_PROJ_MATCH=1 target/release/heather check \
   --kernel-workers 1 probes/t_pc1.hthr 2>&1 | grep -E '^#match' | sort | uniq -c | sort -rn | head -30 )
echo "=== DIAG2 DONE ==="
