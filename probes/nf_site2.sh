# Round "emit the application, not its normal form" (2026-09-16), job 2b:
# the same spike, read through `probes/nf_agg.py` (job 2's inline awk keyed on
# the wrong field). Budget 500 µs, so the emission chokepoint's own walk shows
# up beside the head-shape probes.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_nf2b
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
cp target/release/heather target/heather_spike

spike () { # $1 stem, $2 budget µs, $3 floor µs for the tables
  f=$1; b=$2
  echo "== $f spike budget=${b}us $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_NF_SPIKE=$b \
    target/heather_spike check $L --kernel-workers 1 probes/$f.hthr \
    > "$OUT/$f.out" 2> "$OUT/$f.err" )
  echo "== rc=$? $(date +%T)"
  python3 probes/nf_agg.py "$OUT/$f.err" "$3"
}

spike t_qt2 500 2000
spike t_cp9 500 2000

echo "== MARKER done $(date +%T)"
