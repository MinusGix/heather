# Round "where the millions of conversion queries come from" (2026-09-16),
# job 2: the multiplier, measured two ways.
#
#   (1) the instrument deepened — 40 site frames instead of 12 (the first
#       run's stacks were 100 % at the cap, so the spine length was unread)
#       and the ADDRESS of the type compared, which separates "the elaborator
#       wrote this once and shared it" from "it wrote one per occurrence";
#   (2) t_qt1/2/3: t_cp9's component (`And<relation(…),True>`, +1.72 M
#       queries over t_cp2) with the ENCLOSING proof shortened to one
#       combinator, to none, and lengthened by one. Component fixed, proof
#       varied. t_cp9 and t_cp2 are the controls, re-run here.
#   (3) `close_body`, the item the quote slice did not move (its component is
#       built from primitives), traced from the showcase for the transfer read.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_qt2
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr
N=128

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
cp target/release/heather target/heather_qt

run () { # $1 = probe stem, $2 = item name
  f=$1; item=$2
  echo "== $f/$item traced $(date +%T)"
  ( ulimit -v 8388608 -t 1800; HEATHER_VALUE_METRICS=1 HEATHER_CONV_QUERY_TRACE="$item:$N" \
    target/heather_qt check $L --kernel-workers 1 --timings "$OUT/$f.tsv" probes/$f.hthr \
    > "$OUT/$f.out" 2> "$OUT/$f.err" )
  rc=$?
  echo "== rc=$rc $(date +%T)"
  if [ $rc -ne 0 ]; then echo "== FAILED, last 25 lines of stdout:"; tail -25 "$OUT/$f.out"; return; fi
  awk -F'\t' -v it="$item" '$1=="item" && ($3==it || $3=="complete_post"){
    printf "  %-16s total %9.1f ms gate %9.1f ms misses %8d QUERIES %10d steps %10d\n",$3,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/$f.tsv"
  python3 probes/qt_agg.py "$OUT/$f.err" $N "$f/$item"
}

run t_qt1 qt_pure
run t_qt2 qt_floor
run t_qt3 qt_deep
run t_cp9 cp_andt
run t_cp2 cp_plain
run t_cp1 cp_full

echo "== close_body from the showcase $(date +%T)"
( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CONV_QUERY_TRACE="close_body:$N" \
  target/heather_qt check $L --kernel-workers 1 --timings "$OUT/sc.tsv" $F \
  > "$OUT/sc.out" 2> "$OUT/sc.err" )
echo "== rc=$? $(date +%T)"
awk -F'\t' '$1=="item" && $3 ~ /^(close_body|expr_body|factor_body|complete_post|number_grammar)$/{
  printf "  %-16s total %9.1f ms gate %9.1f ms misses %8d QUERIES %10d steps %10d\n",$3,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/sc.tsv"
python3 probes/qt_agg.py "$OUT/sc.err" $N "showcase/close_body"

echo "== MARKER done $(date +%T)"
