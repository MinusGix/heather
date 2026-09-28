# Round "quote the respelled type" (2026-09-16), job 5: the gates, in one
# detached job (brief step 2).
#
#   (a) the per-item diff of the showcase, parent against the change: the
#       brief's "no head-pair count may rise" read where it matters — no
#       ITEM's misses, queries or steps may rise;
#   (b) the full `scripts/test` (not --fast: this changes what the frontend
#       emits, and the fast lane replays images an earlier build wrote);
#   (c) the `scripts/bench --save` / apply / `--check` dance from
#       probes/README.md, since the committed baseline is desktop-recorded.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cpg
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== (a) per-item diff $(date +%T)"
for who in parent q; do
  ( ulimit -v 16777216 -t 3600; target/heather_$who check $L --kernel-workers 1 \
    --timings "$OUT/${who}.tsv" $F > "$OUT/${who}.out" 2>&1 )
  echo "== rc=$? $who $(date +%T)"
done
join -t'	' -j 1 \
  <(awk -F'\t' '$1=="item"{printf "%s\t%d\t%d\t%d\n",$2"::"$3,$43,$41,$46}' "$OUT/parent.tsv" | sort -u -t'	' -k1,1) \
  <(awk -F'\t' '$1=="item"{printf "%s\t%d\t%d\t%d\n",$2"::"$3,$43,$41,$46}' "$OUT/q.tsv" | sort -u -t'	' -k1,1) \
  > "$OUT/joined.tsv"
echo "== items whose misses ROSE"
awk -F'\t' '$5>$2 {printf "  %-46s misses %8d -> %8d\n",$1,$2,$5}' "$OUT/joined.tsv" | head -20
echo "== items whose conversion QUERIES rose"
awk -F'\t' '$6>$3 {printf "  %-46s shortcut %9d -> %9d\n",$1,$3,$6}' "$OUT/joined.tsv" | head -20
echo "== items whose eval STEPS rose"
awk -F'\t' '$7>$4 {printf "  %-46s steps %10d -> %10d\n",$1,$4,$7}' "$OUT/joined.tsv" | head -20
echo "== the ten items that fell most (misses)"
awk -F'\t' '{printf "  %-46s misses %8d -> %8d  queries %9d -> %9d\n",$1,$2,$5,$3,$6}' "$OUT/joined.tsv" \
  | sort -k4 -rn | head -10
echo "== rows joined: $(wc -l < "$OUT/joined.tsv")"

echo "== (b) full scripts/test $(date +%T)"
scripts/test > "$OUT/suite.log" 2>&1; echo "== suite rc=$? $(date +%T)"
grep -a -E '^== suite:|INCOMPLETE' "$OUT/suite.log" | tail -3
echo "== failures, if any"
grep -a -E '^(test .* FAILED|failures:|---- )' "$OUT/suite.log" | head -30
grep -a -E 'panicked at' "$OUT/suite.log" | head -20
echo "== slowest targets"
sed -n '/slowest test targets/,/^$/p' "$OUT/suite.log" | head -12

echo "== (c) the bench dance $(date +%T)"
patch -p1 -R --batch < probes/cp.patch > "$OUT/patch1.log" 2>&1; echo "== reverse-apply rc=$?"
scripts/bench --save 2>&1 | tail -4
patch -p1 --batch < probes/cp.patch > "$OUT/patch2.log" 2>&1; echo "== re-apply rc=$?"
scripts/bench --check 2>&1 | tail -20
echo "== MARKER done $(date +%T)"
