# The conv-miss trace of one item, for attributing the top head-pair row
# (`HEATHER_CONV_MISS_TRACE=<item>`), on both binaries.
set -u
cd "$(dirname "$0")/.."
ITEM="${ITEM:-chain3}"
FILE="${FILE:-probes/t_pc3.hthr}"
OUT=probes/out_trace
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
for who in parent changed; do
  BIN=target/heather_parent; [ $who = changed ] && BIN=target/release/heather
  echo "== trace $who $ITEM $(date +%T)"
  rm -rf /tmp/tr_$who
  ( ulimit -v 16777216 -t 1800; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE="$ITEM" \
    $BIN check --cache --cache-dir /tmp/tr_$who $L --kernel-workers 1 "$FILE" \
    > "$OUT/$who.out" 2> "$OUT/$who.err" )
  echo "== rc=$? $who $(date +%T)"
  echo "== head pairs $who"
  grep -h '^conv miss expected=' "$OUT/$who.out" "$OUT/$who.err" | head -10
  echo "== first excerpts $who"
  grep -h -A 12 '^conv miss expected=' "$OUT/$who.out" "$OUT/$who.err" | head -60
done
echo "== MARKER done $(date +%T)"
