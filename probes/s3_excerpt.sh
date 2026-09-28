# Job 2: the first-difference excerpts for the top Pi/Pi groups, and the
# item names t_pcr3 actually uses (job 1's qchain3 trace was empty).
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_s3x
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' -A 6 | tail -20

echo "== t_pcr3 item names $(date +%T)"
rm -rf /tmp/s3x
( ulimit -v 8388608 -t 900; target/release/heather check --cache --cache-dir /tmp/s3x $L \
  --kernel-workers 1 --timings "$OUT/r3.tsv" probes/t_pcr3.hthr > "$OUT/r3.out" 2>&1 )
echo "== rc=$?"
awk -F'\t' '$1=="item"{printf "  item=%-28s total %9.1f ms kernel %9.1f ms misses %7d steps %9d\n",$3,$4/1e6,$8/1e6,$43,$46}' "$OUT/r3.tsv"

echo "== showcase close_body trace $(date +%T)"
( ulimit -v 16777216 -t 1800; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=close_body \
  target/release/heather check $L --kernel-workers 1 $F > "$OUT/sc.out" 2> "$OUT/sc.err" )
echo "== rc=$? $(date +%T)"
echo "== how many Pi/Pi records: $(grep -c '^conv miss trace close_body Pi/Pi' "$OUT/sc.err")"
echo "== first-difference summary lines, bucketed by (len,len,pos)"
grep '^expected len=' "$OUT/sc.err" | sort | uniq -c | sort -rn | head -20
echo "== FULL RECORD 1 (first Pi/Pi, whole block)"
awk '/^conv miss trace close_body Pi\/Pi/{n++} n==1{print} n==2{exit}' "$OUT/sc.err" | cut -c1-1400
echo "== FULL RECORD 2"
awk '/^conv miss trace close_body Pi\/Pi/{n++} n==2{print} n==3{exit}' "$OUT/sc.err" | cut -c1-1400
echo "== FULL RECORD: the widest-count group (App<...<App<Snd<Snd<Fst<Fst<App<App<Fst)"
grep -A 24 '^conv miss trace close_body Pi/Pi' "$OUT/sc.err" \
  | grep -E '^(expected|inferred): ' | sort | uniq -c | sort -rn | head -12 | cut -c1-1000
echo "== MARKER done $(date +%T)"
