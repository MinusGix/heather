# Round "complete_post attribution", job 1: check the brief's premise with
# `--timings` before reading any trace. The showcase, serial, untraced, no
# cache — a traced run inflates total_ns about 2x, and `--cache` replays the
# library images and reports zeros.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cp1
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== showcase W=1 untraced start $(date +%T)"
( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time W=1 %es wall %Us user %MKB maxrss" \
  target/release/heather check $L --kernel-workers 1 --timings "$OUT/sc.tsv" $F 2>&1 | tail -4 )
echo "== rc=$? $(date +%T)"

echo "== HEADER with 1-based indices"
head -1 "$OUT/sc.tsv" | tr '\t' '\n' | nl | awk '{printf "  %s=%s\n", $1, $2}' | paste -d' ' - - - -

echo "== complete_post WHOLE ROW, name=value, nonzero only"
awk -F'\t' 'NR==1{for(i=1;i<=NF;i++) n[i]=$i; next}
  $1=="item" && $3=="complete_post"{for(i=1;i<=NF;i++) if ($i != "" && $i != "0") printf "  [%d] %s = %s\n", i, n[i], $i}' "$OUT/sc.tsv"

echo "== every item row of the parser modules (module, item, total ms, gate ms, elab ms, emit ms, misses, shortcut, steps, delta)"
awk -F'\t' '$1=="item" && ($2 ~ /parser/ || $2 ~ /calc/) {
    printf "  %-22s %-30s tot %8.1f gate %8.1f elab %8.1f emit %7.1f  miss %7d  short %9d  steps %10d  delta %9d\n",
      $2,$3,$4/1e6,$8/1e6,($4-$8-$6)/1e6,$11/1e6,$43,$41,$46,$47 }' "$OUT/sc.tsv" \
  | sort -t' ' -k1,1

echo "== top 15 items of the whole run by total"
awk -F'\t' '$1=="item"{printf "  %-22s %-30s tot %8.1f gate %8.1f miss %7d steps %10d\n",$2,$3,$4/1e6,$8/1e6,$43,$46}' "$OUT/sc.tsv" \
  | sort -k4 -rn | head -15

echo "== module rows"
awk -F'\t' '$1=="module"{printf "  %-24s tot %9.1f ms  gate %9.1f ms  miss %8d  steps %11d\n",$2,$4/1e6,$8/1e6,$43,$46}' "$OUT/sc.tsv"
echo "== run row"
awk -F'\t' '$1=="run"{printf "  tot %9.1f ms  gate %9.1f ms  parse %7.1f  miss %8d  short %10d  memo %9d  steps %11d  delta %10d  drives %10d\n",$4/1e6,$8/1e6,$6/1e6,$43,$41,$42,$46,$47,$48}' "$OUT/sc.tsv"
echo "== TOTALS over item rows"
awk -F'\t' '$1=="item"{t+=$4;k+=$8;m+=$43;s+=$46;n++} END{printf "  items=%d total=%.2f s gate=%.2f s misses=%d steps=%d\n",n,t/1e9,k/1e9,m,s}' "$OUT/sc.tsv"
echo "== MARKER done $(date +%T)"
