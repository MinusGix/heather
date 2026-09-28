# Round "complete_post attribution", job 2: the trace read.
# `HEATHER_CONV_MISS_TRACE=complete_post` on the showcase, then
#   (a) trace_agg's head-pair and group tables,
#   (b) whole records bucketed by the `expected len=… inferred len=… first
#       difference at …` signature (trace_agg truncates at 260 chars and hides
#       the excerpt) — the s4_excerpt.sh read,
#   (c) the site lines, so a bucket is tied to a conversion site,
#   (d) the SUM of the traced misses' milliseconds against the item's gate:
#       what the misses do NOT account for is the steps side.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cp2
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== trace complete_post start $(date +%T)"
( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=complete_post \
  target/release/heather check $L --kernel-workers 1 --timings "$OUT/tr.tsv" $F \
  > "$OUT/tr.out" 2> "$OUT/tr.err" )
echo "== rc=$? $(date +%T)  err bytes=$(wc -c < "$OUT/tr.err")  records=$(grep -c '^conv miss trace complete_post' "$OUT/tr.err")"

echo "== the TRACED run's complete_post row (inflated; for the ratio only)"
awk -F'\t' '$1=="item" && $3=="complete_post"{printf "  total %9.1f ms  gate %9.1f ms  emit %8.1f ms  misses %8d  steps %10d  delta %8d\n",$4/1e6,$8/1e6,$11/1e6,$43,$46,$47}' "$OUT/tr.tsv"

echo "== traced-miss milliseconds, summed (sampler clock, one Instant per miss)"
grep -o 'conv miss trace complete_post [^ ]* [0-9.]*ms' "$OUT/tr.err" \
  | awk '{gsub("ms","",$NF); t+=$NF; n++} END{printf "  records=%d  summed=%.1f ms\n", n, t}'

echo "== (a) trace_agg"
python3 probes/trace_agg.py "$OUT/tr.err" 2>&1 | sed -n '1,40p' | cut -c1-320

echo "== (b) buckets by (expected len, inferred len, first difference at)"
grep '^expected len=' "$OUT/tr.err" | sort | uniq -c | sort -rn | head -25

echo "== (b2) head pair x bucket: count and ms"
awk '/^conv miss trace complete_post /{split($0,f," "); hp=f[5]; ms=f[6]; sub("ms","",ms); next}
     /^expected len=/{k=hp" | "$0; c[k]++; s[k]+=ms}
     END{for (k in c) printf "  %7d  %10.1f ms  %s\n", c[k], s[k], k}' "$OUT/tr.err" \
  | sort -k2 -rn | head -25

echo "== (c) site lines, grouped (top 20)"
grep '^site: ' "$OUT/tr.err" | sort | uniq -c | sort -rn | head -20 | cut -c1-320

echo "== (c2) site x head pair"
awk '/^conv miss trace complete_post /{split($0,f," "); hp=f[5]; next}
     /^site: /{c[hp" | "$0]++} END{for (k in c) printf "  %7d  %s\n", c[k], k}' "$OUT/tr.err" \
  | sort -rn | head -20 | cut -c1-320

for n in 1 2 3 4; do
  echo "== FULL RECORD $n"
  awk -v want=$n '/^conv miss trace complete_post /{m++} m==want{print} m==want+1{exit}' "$OUT/tr.err" | cut -c1-1600
done

echo "== the most common expected/inferred excerpt lines"
grep -E '^(expected|inferred): ' "$OUT/tr.err" | sort | uniq -c | sort -rn | head -12 | cut -c1-700

echo "== whole summed head-pair table of the RUN (value-metrics, all modules)"
grep -h '^conv miss expected=' "$OUT/tr.out" "$OUT/tr.err" 2>/dev/null \
  | sed 's/^conv miss expected=//; s/ inferred=/\t/; s/ count=/\t/; s/ total=/\t/; s/s$//' \
  | awk -F'\t' '{k=$1"/"$2; c[k]+=$3; s[k]+=$4} END{for (k in c) printf "  %10d  %9.3fs  %s\n", c[k], s[k], k}' \
  | sort -k2 -rn | head -20
echo "== MARKER done $(date +%T)"
