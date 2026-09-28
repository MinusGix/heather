set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^error' -A 12 | head -40
echo "=== BUILT ==="
( ulimit -v 6291456 -t 300; HEATHER_PROJ_DECLINE=1 target/release/heather check \
   --kernel-workers 1 probes/t_pc2.hthr 2>&1 | grep -E '^#projwalk' > /tmp/d7.txt )
awk '{print $2, $4, $5, $6, $7}' /tmp/d7.txt | sort | uniq -c | sort -rn | head -25
echo "=== DIAG7 DONE ==="
