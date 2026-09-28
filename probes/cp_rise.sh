# Round "quote the respelled type" (2026-09-16), job 4: the four head-pair
# rows that ROSE (brief step 1: no head-pair count may rise). Both binaries,
# value-metrics on the showcase, and for each rising pair the summed count and
# the per-item lines the report prints under it — so the rise is attributed to
# an item rather than left as a number.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cpr
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

for who in parent q; do
  echo "== value metrics $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 \
    target/heather_$who check $L --kernel-workers 1 $F > "$OUT/${who}.out" 2> "$OUT/${who}.err" )
  echo "== rc=$? $(date +%T)"
  cat "$OUT/${who}.out" "$OUT/${who}.err" > "$OUT/${who}.all" 2>/dev/null
  for pair in 'expected=El^δ inferred=Sum' 'expected=El^δ inferred=Sigma' 'expected=El(?) inferred=Sum' 'expected=Sum inferred=El(?)'; do
    echo "-- $who | $pair"
    awk -v want="$pair" '
      /^conv miss expected=/ { blk = index($0, want) > 0; if (blk) { split($0, f, "count="); split(f[2], g, " "); tot += g[1]; } next }
      blk && /^    item / { split($0, h, "count="); split(h[2], i2, " "); c[$2] += i2[1] }
      END { printf "   summed count=%d\n", tot; for (k in c) printf "   item %-34s count=%d\n", k, c[k] }' "$OUT/${who}.all" \
      | sort -k4 -rn | head -10
  done
done
echo "== MARKER done $(date +%T)"
