set -x
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^error' -A 10 | head -30
echo "=== BUILT ==="
( ulimit -v 6291456 -t 300; HEATHER_PROJ_MATCH=1 HEATHER_PROJ_DECLINE=1 target/release/heather check \
   --kernel-workers 1 probes/t_pc1.hthr 2>&1 | grep -E '^#' > /tmp/d5.txt )
echo "--- tycodefn + projdecline + projenter + match (all, aggregated)"
grep -E '^#(tycodefn|projdecline|projenter|match)' /tmp/d5.txt | sort | uniq -c | sort -rn
echo "--- projwalk by declaration/reason"
grep -E '^#projwalk' /tmp/d5.txt | awk '{print $2, $NF, $(NF-1), $(NF-2)}' | sort | uniq -c | sort -rn | head -20
echo "=== DIAG5 DONE ==="
