set -u
cd "$(dirname "$0")/.."
echo "== build start $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
echo "== build done $(date +%T)"
L="-L lib/std -L lib/std/parser"
for w in 1 8; do
  echo "== check workers=$w start $(date +%T)"
  ( ulimit -v 16777216 -t 900; /usr/bin/time -f "== time workers=$w %es wall %Us user %MKB maxrss" \
    target/release/heather check $L --kernel-workers $w --timings probes/timings_w$w.tsv docs/showcase/calc_parser.hthr 2>&1 | tail -5 )
  echo "== check workers=$w done $(date +%T)"
done
echo "== TSV w1 begin"; cat probes/timings_w1.tsv; echo "== TSV w1 end"
echo "== TSV w8 begin"; cat probes/timings_w8.tsv; echo "== TSV w8 end"
