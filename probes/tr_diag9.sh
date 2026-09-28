set -x
echo "=== START ==="
( ulimit -v 6291456 -t 600; HEATHER_VALUE_METRICS=1 target/release/heather check \
   --kernel-workers 1 probes/t_pc3.hthr 2>&1 | tail -45 )
echo "--- trace chain3"
( ulimit -v 6291456 -t 600; HEATHER_CONV_MISS_TRACE=chain3 target/release/heather check \
   --kernel-workers 1 probes/t_pc3.hthr 2>&1 | tail -30 )
echo "=== DIAG9 DONE ==="
