set -x
echo "=== BUILT ==="
( ulimit -v 6291456 -t 300; HEATHER_PROJ_MATCH=1 target/release/heather check \
   --kernel-workers 1 probes/t_pc2.hthr 2>&1 | grep -E '^#match' | sort | uniq -c | sort -rn | head -20 )
echo "--- dump Cert"
( ulimit -v 6291456 -t 300; HEATHER_PROJ_MATCH=1 HEATHER_PROJ_DUMP=Cert target/release/heather check \
   --kernel-workers 1 probes/t_pc2.hthr 2>&1 | grep -A 2 '^#dump' | head -3 )
echo "=== DIAG8 DONE ==="
