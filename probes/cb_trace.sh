# Round "the close_body family: what the six million queries are" (2026-09-16),
# job 1: the premise (the showcase serial, --timings) and the site histogram of
# QUERIES for each unattributed item of the family.
#
# `HEATHER_CONV_QUERY_TRACE=<item>[:N]` needs `--timings` twice over: once for
# the item scopes the filter reads, once for the table. One process per traced
# item, because the filter is a single item.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cb1
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
N=128
SHOW=docs/showcase/calc_parser.hthr

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
ls -l target/release/heather

table () { # $1 = tsv
  # `--timings` writes the item's BARE name in column 3 (the module is column
  # 2), and `HEATHER_CONV_QUERY_TRACE` filters on that same bare name --- not
  # on the `module::item` form the docs' tables print.
  awk -F'\t' '$1=="item" && ($3=="complete_post" || $3=="close_body" || $3=="expr_body" || $3=="factor_body" || $3=="number_grammar" || $3=="Grammar" || $3=="checked_expr" || $3=="open_body" || $3=="atom_body" || $3=="Certified" || $3=="certify_at" || $3=="sum_finish" || $3=="product_finish" || $3=="symbol_span" || $3=="GrammarSpec"){
    printf "  %-20s %-18s total %9.1f ms gate %9.1f ms misses %8d QUERIES %10d steps %10d\n",$2,$3,$4/1e6,$8/1e6,$43,$41,$46}' "$1"
  awk -F'\t' '$1=="item"{t+=$4; g+=$8; m+=$43; q+=$41; s+=$46; n++} END {
    printf "  == %d items: total %.2f s gate %.2f s misses %d queries %d steps %d\n", n, t/1e9, g/1e9, m, q, s}' "$1"
}

head -1 "$OUT/base.tsv" 2>/dev/null | tr '\t' '\n' | head -3
echo "== premise: showcase serial, untraced $(date +%T)"
( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 \
  target/release/heather check $L --kernel-workers 1 --timings "$OUT/base.tsv" $SHOW \
  > "$OUT/base.out" 2> "$OUT/base.err" ); echo "== rc=$? $(date +%T)"
head -1 "$OUT/base.tsv" | awk -F'\t' '{print "  header cols 1-3: "$1" "$2" "$3}'
table "$OUT/base.tsv"

run () { # $1 = tag, $2 = item
  echo "== traced $2 $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CONV_QUERY_TRACE="$2:$N" \
    target/release/heather check $L --kernel-workers 1 --timings "$OUT/$1.tsv" $SHOW \
    > "$OUT/$1.out" 2> "$OUT/$1.err" ); echo "== rc=$? $(date +%T)"
  awk -F'\t' -v it="$2" '$1=="item" && $3==it {printf "  %-20s %-18s total %9.1f ms gate %9.1f ms misses %8d QUERIES %10d steps %10d\n",$2,$3,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/$1.tsv"
  python3 probes/qt_agg.py "$OUT/$1.err" $N "$1/$2"
}

run cb close_body
run eb expr_body
run gr Grammar
run ce Certified
run ng number_grammar

echo "== MARKER done $(date +%T)"
