set -u
cd "$(dirname "$0")/.."
TAG="${TAG:-after}"
OUT=probes/out_$TAG
rm -rf "$OUT"; mkdir -p "$OUT"
echo "== build start $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|warning: unused|    Finished)' | tail -20
echo "== build rc=$? $(date +%T)"
test -x target/release/heather || { echo "== NO BINARY"; echo "== MARKER done"; exit 1; }

L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== declines start $(date +%T)"
( ulimit -v 16777216 -t 1800; HEATHER_GENDEF_DECLINES=1 \
  target/release/heather check $L --kernel-workers 1 $F > "$OUT/decl.out" 2> "$OUT/decl.err" )
echo "== declines rc=$? $(date +%T)"
grep -c '^gendef-decline' "$OUT/decl.err" | sed 's/^/== decline lines: /'
echo "== decline listing by (site, declaration, reason)"
grep '^gendef-decline' "$OUT/decl.err" | cut -f2,3,4 | sort | uniq -c | sort -rn

echo "== timings start $(date +%T)"
( ulimit -v 16777216 -t 1800; /usr/bin/time -f "== wall %es user %Us maxrss %MKB" \
  target/release/heather check $L --kernel-workers 1 --timings "$OUT/t.tsv" $F 2>&1 | tail -4 )
echo "== timings rc=$? $(date +%T)"

echo "== metrics start $(date +%T)"
( ulimit -v 16777216 -t 1800; HEATHER_VALUE_METRICS=1 \
  target/release/heather check $L --kernel-workers 1 $F > "$OUT/vm.out" 2> "$OUT/vm.err" )
echo "== metrics rc=$? $(date +%T)"

echo "== TSV begin"; cat "$OUT/t.tsv"; echo "== TSV end"
echo "== VM begin"; cat "$OUT/vm.out" "$OUT/vm.err"; echo "== VM end"

echo "== unit tests start $(date +%T)"
scripts/test --fast -p heather-elab --lib stale_template 2>&1 | tail -30
echo "== unit tests rc=$? $(date +%T)"
echo "== MARKER done $(date +%T)"
