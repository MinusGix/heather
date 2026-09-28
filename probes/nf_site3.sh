# Round "emit the application, not its normal form" (2026-09-16), job 3:
# the spike applied to the CURVE — which site's clock follows the 3.5× per
# combinator layer (design §3.1). `--timings` is what opens the declaration
# scopes the spike reads for `item=`; without it every record is attributed to
# `-` (job 2b's whole table).
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_nf3
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
cp target/release/heather target/heather_spike

spike () { # $1 stem, $2 item, $3 budget µs, $4 rail KB
  f=$1; item=$2; b=$3
  echo "== $f/$item spike budget=${b}us $(date +%T)"
  ( ulimit -v $4 -t 3600; HEATHER_NF_SPIKE=$b \
    target/heather_spike check $L --kernel-workers 1 --timings "$OUT/$f.tsv" probes/$f.hthr \
    > "$OUT/$f.out" 2> "$OUT/$f.err" )
  echo "== rc=$? $(date +%T)"
  echo "== ALL items"
  python3 probes/nf_agg.py "$OUT/$f.err" "$b"
  echo "== ONLY $item"
  python3 probes/nf_agg.py "$OUT/$f.err" "$b" "$item"
  echo "== ONLY complete_post"
  python3 probes/nf_agg.py "$OUT/$f.err" "$b" "complete_post"
}

spike t_qt2 qt_floor 20  8388608
spike t_cp9 cp_andt  20  8388608
spike t_qt3 qt_deep  20 16777216

echo "== MARKER done $(date +%T)"
