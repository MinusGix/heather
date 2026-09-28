# Round "the close_body family" (2026-09-16), job 2: the reproducers, and the
# node/read counter that says what the two factors are.
#
#   (1) the probe table, untraced and uninstrumented: t_cb1..t_cb6 and the
#       existing t_pc3/t_pcr3 (the same chain without and with the
#       function-typed `relation` parameter);
#   (2) `HEATHER_CB=1` on the showcase: one `cb decl` line per declaration
#       (the tree size of the pair the kernel is handed) and one `cb read`
#       line per field read (route, spine size). The counter is exhaustive
#       and unbudgeted, which the bounded `Debug` of the query trace is not.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cb2
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
SHOW=docs/showcase/calc_parser.hthr

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2

probe () { # $1 = stem
  ( ulimit -v 8388608 -t 900; HEATHER_VALUE_METRICS=1 \
    target/release/heather check $L --kernel-workers 1 --timings "$OUT/$1.tsv" probes/$1.hthr \
    > "$OUT/$1.out" 2> "$OUT/$1.err" ); rc=$?
  awk -F'\t' -v f="$1" -v rc=$rc '$1=="item" && $2 ~ /^t_/ {
    printf "  %-10s %-12s rc=%s total %8.1f ms gate %8.1f ms misses %7d QUERIES %9d steps %8d\n",f,$3,rc,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/$1.tsv"
}

echo "== probes $(date +%T)"
for f in t_cb1 t_cb2 t_cb3 t_cb4 t_cb5 t_cb6 t_pc3 t_pcr3; do probe $f; done

echo "== showcase under HEATHER_CB $(date +%T)"
( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CB=1 \
  target/release/heather check $L --kernel-workers 1 --timings "$OUT/cb.tsv" $SHOW \
  > "$OUT/cb.out" 2> "$OUT/cb.err" ); echo "== rc=$? $(date +%T)"
python3 probes/cb_agg.py "$OUT/cb.err" "$OUT/cb.tsv"

echo "== probes under HEATHER_CB $(date +%T)"
for f in t_cb1 t_cb4 t_cb6 t_pcr3; do
  ( ulimit -v 8388608 -t 900; HEATHER_VALUE_METRICS=1 HEATHER_CB=1 \
    target/release/heather check $L --kernel-workers 1 --timings "$OUT/$f.cb.tsv" probes/$f.hthr \
    > "$OUT/$f.cb.out" 2> "$OUT/$f.cb.err" )
  python3 probes/cb_agg.py "$OUT/$f.cb.err" "$OUT/$f.cb.tsv" t_
done

echo "== MARKER done $(date +%T)"
