# Round "where the millions of conversion queries come from" (2026-09-16),
# job 1: build the instrument and take the site histogram of QUERIES.
#
#   (0) the sanity check the brief demands: sampled lines x stride must
#       reproduce `conv_shortcut_hits` for the item within a few percent, or
#       the instrument is wrong and nothing below may be attributed;
#   (1) t_cp1 (cp_full, 3.68 M queries) traced and aggregated by site;
#   (2) the subtraction table's members traced the same way: t_cp2 (the
#       0.68 M base), t_cp17 (+Le), t_cp12 (+the equation), t_cp9 (+the
#       relation applied). The difference between two site histograms is the
#       block's owner.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_qt1
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
N=128

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
cp target/release/heather target/heather_qt
ls -l target/heather_qt

run () { # $1 = probe stem, $2 = item name
  f=$1; item=$2
  echo "== $f/$item traced $(date +%T)"
  ( ulimit -v 8388608 -t 1800; HEATHER_VALUE_METRICS=1 HEATHER_CONV_QUERY_TRACE="$item:$N" \
    target/heather_qt check $L --kernel-workers 1 --timings "$OUT/$f.tsv" probes/$f.hthr \
    > "$OUT/$f.out" 2> "$OUT/$f.err" )
  echo "== rc=$? $(date +%T)"
  awk -F'\t' -v it="$item" '$1=="item" && ($3==it || $3=="complete_post"){
    printf "  %-16s total %9.1f ms gate %9.1f ms misses %8d QUERIES %10d steps %10d\n",$3,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/$f.tsv"
  python3 probes/qt_agg.py "$OUT/$f.err" $N "$f/$item"
}

run t_cp1 cp_full
run t_cp2 cp_plain
run t_cp17 cp_le
run t_cp12 cp_teq
run t_cp9 cp_andt

echo "== MARKER done $(date +%T)"
