# Round "emit the application, not its normal form" (2026-09-16), job 4:
# design §8 item 2's second half — is the pre-whnf term still in hand, and is
# it small? The spike now prints `in_len` beside `out_len` and the input's
# whole bounded spelling, so the one call that carries the exponent
# (`build_ctor`'s `whnf`, jobs 3's table) can be read as folded-or-not.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_nf4
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
cp target/release/heather target/heather_spike

spike () { # $1 stem, $2 item, $3 budget, $4 rail
  f=$1; item=$2
  echo "== $f/$item spike budget=$3us $(date +%T)"
  ( ulimit -v $4 -t 3600; HEATHER_NF_SPIKE=$3 \
    target/heather_spike check $L --kernel-workers 1 --timings "$OUT/$f.tsv" probes/$f.hthr \
    > "$OUT/$f.out" 2> "$OUT/$f.err" )
  echo "== rc=$? $(date +%T)"
  echo "== ONLY $item"; python3 probes/nf_agg.py "$OUT/$f.err" 2000 "$item"
  echo "== ONLY complete_post"; python3 probes/nf_agg.py "$OUT/$f.err" 2000 "complete_post"
}

spike t_cp9 cp_andt 2000 8388608
spike t_qt2 qt_floor 200 8388608

echo "== MARKER done $(date +%T)"
