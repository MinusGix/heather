set -u
cd "$(dirname "$0")/.."
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr
( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time W=1 %es wall %MKB maxrss" \
  target/release/heather check $L --kernel-workers 1 --timings /tmp/top_after.tsv $F 2>&1 | tail -2 )
echo "== top 25 items by total: name total_ms gate_ms misses queries steps"
awk -F'\t' '$1=="item"{printf "%-40s %9.1f %9.1f %8d %10d %10d\n",$2"::"$3,$4/1e6,$8/1e6,$43,$41,$46}' /tmp/top_after.tsv | sort -k2 -rn | head -25
echo "== totals"
awk -F'\t' '$1=="item"{n++;t+=$4;k+=$8;m+=$43;q+=$41;s+=$46} END{printf "items=%d total=%.2fs gate=%.2fs misses=%d queries=%d steps=%d\n",n,t/1e9,k/1e9,m,q,s}' /tmp/top_after.tsv
echo "== per-module totals"
awk -F'\t' '$1=="item"{t[$2]+=$4;q[$2]+=$41} END{for(m in t) printf "%-28s %8.2fs %10d\n",m,t[m]/1e9,q[m]}' /tmp/top_after.tsv | sort -k2 -rn | head -12
echo "== MARKER done"
