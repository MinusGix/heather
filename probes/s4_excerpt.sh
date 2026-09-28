# Round 2026-09-15 part A, job 3: the first-difference excerpts of the
# `Pi`/`Pi` records that **remain** on part A's `close_body` trace (design §7
# item 3: re-read the excerpt before changing anything). `probes/s3_excerpt.sh`
# is the same read on the parent tree.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_s4x
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== showcase close_body trace on part A $(date +%T)"
( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=close_body \
  target/heather_a check $L --kernel-workers 1 $F > "$OUT/sc.out" 2> "$OUT/sc.err" )
echo "== rc=$? $(date +%T)"
echo "== Pi/Pi records: $(grep -c '^conv miss trace close_body Pi/Pi' "$OUT/sc.err")"
echo "== first-difference summary lines, bucketed by (len,len,pos)"
grep '^expected len=' "$OUT/sc.err" | sort | uniq -c | sort -rn | head -20
echo "== FULL RECORD 1 (first Pi/Pi, whole block)"
awk '/^conv miss trace close_body Pi\/Pi/{n++} n==1{print} n==2{exit}' "$OUT/sc.err" | cut -c1-1400
echo "== FULL RECORD 2"
awk '/^conv miss trace close_body Pi\/Pi/{n++} n==2{print} n==3{exit}' "$OUT/sc.err" | cut -c1-1400
echo "== FULL RECORD 3"
awk '/^conv miss trace close_body Pi\/Pi/{n++} n==3{print} n==4{exit}' "$OUT/sc.err" | cut -c1-1400
echo "== the most common expected/inferred lines"
grep -A 24 '^conv miss trace close_body Pi/Pi' "$OUT/sc.err" \
  | grep -E '^(expected|inferred): ' | sort | uniq -c | sort -rn | head -10 | cut -c1-900
echo "== MARKER done $(date +%T)"
