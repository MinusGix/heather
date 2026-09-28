# Round "quote the respelled type" (2026-09-16), job 6: the final verification
# on the tree that is left for review — the spike's `eprintln!` removed — plus
# the showcase serial row re-read on it, to say the removal changed nothing.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cpf
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr
echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
cp target/release/heather target/heather_q
echo "== showcase W=1 on the final tree $(date +%T)"
( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time final W=1 %es wall %MKB maxrss" \
  target/heather_q check $L --kernel-workers 1 --timings "$OUT/sc.tsv" $F 2>&1 | tail -3 )
awk -F'\t' '$1=="item" && $3 ~ /^(complete_post|close_body|checked_expr|number_grammar)$/ {
  printf "  %-16s total %9.1f ms gate %9.1f ms misses %8d shortcut %10d steps %10d\n",$3,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/sc.tsv"
awk -F'\t' '$1=="item"{t+=$4;k+=$8;m+=$43;h+=$41;s+=$46;n+=1}
  END{printf "  TOTALS final-W1 items=%d total=%.2f s kernel=%.2f s misses=%d shortcut=%d steps=%d\n",n,t/1e9,k/1e9,m,h,s}' "$OUT/sc.tsv"
echo "== full scripts/test $(date +%T)"
scripts/test > "$OUT/suite.log" 2>&1; echo "== suite rc=$? $(date +%T)"
grep -a -E '^== suite:|INCOMPLETE' "$OUT/suite.log" | tail -3
grep -a -E 'panicked at|^failures:' "$OUT/suite.log" | head -20
echo "== MARKER done $(date +%T)"
