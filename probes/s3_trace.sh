# Design pass 2, job 1: the trace read (slice 2's first hour) plus the
# baseline decline listing (slice 1). One furnace round trip.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_s3
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== build start $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' -A 6 | tail -40
test -x target/release/heather || { echo "== NO BINARY"; echo "== MARKER done"; exit 1; }
echo "== build done $(date +%T)"

echo "== trace close_body (showcase) start $(date +%T)"
( ulimit -v 16777216 -t 1800; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=close_body \
  target/release/heather check $L --kernel-workers 1 $F > "$OUT/sc_cb.out" 2> "$OUT/sc_cb.err" )
echo "== rc=$? $(date +%T) err lines=$(wc -l < "$OUT/sc_cb.err")"
echo "== AGG close_body begin"
python3 probes/trace_agg.py "$OUT/sc_cb.err"
echo "== AGG close_body end"
echo "== RAW first 3 Pi/Pi trace records"
grep -A 4 '^conv miss trace close_body Pi/Pi' "$OUT/sc_cb.err" | head -60

echo "== trace qchain3 (t_pcr3) start $(date +%T)"
rm -rf /tmp/s3r3
( ulimit -v 8388608 -t 900; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=qchain3 \
  target/release/heather check --cache --cache-dir /tmp/s3r3 $L --kernel-workers 1 \
  probes/t_pcr3.hthr > "$OUT/r3.out" 2> "$OUT/r3.err" )
echo "== rc=$? $(date +%T) err lines=$(wc -l < "$OUT/r3.err")"
echo "== AGG qchain3 begin"
python3 probes/trace_agg.py "$OUT/r3.err"
echo "== AGG qchain3 end"
echo "== RAW first 3 Pi/Pi trace records (t_pcr3)"
grep -A 4 '^conv miss trace qchain3 Pi/Pi' "$OUT/r3.err" | head -60

echo "== listing on showcase $(date +%T)"
( ulimit -v 16777216 -t 2400; HEATHER_GENDEF_DECLINES=1 \
  target/release/heather check $L --kernel-workers 1 $F > "$OUT/sc_l.out" 2> "$OUT/sc_l.err" )
echo "== rc=$? $(date +%T)"
echo "== decline lines: $(grep -c '^gendef-decline' "$OUT/sc_l.err")"
grep '^gendef-decline' "$OUT/sc_l.err" | cut -f2,3,4 | sort | uniq -c | sort -rn | head -40
echo "== MARKER done $(date +%T)"
