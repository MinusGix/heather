set -u
cd "$(dirname "$0")/.."
L="-L lib/std -L lib/std/parser"
for item in close_body complete_post; do
  echo "== trace $item start $(date +%T)"
  ( ulimit -v 16777216 -t 900; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=$item \
    target/release/heather check $L --kernel-workers 1 docs/showcase/calc_parser.hthr > probes/trace_$item.txt 2>&1 )
  echo "== trace $item done $(date +%T) lines=$(wc -l < probes/trace_$item.txt)"
  echo "== AGG $item begin"; python3 probes/trace_agg.py probes/trace_$item.txt; echo "== AGG $item end"
done
echo "== SNAPSHOT begin"; grep -n 'ValueMetrics' probes/trace_close_body.txt | head -40; echo "== SNAPSHOT end"
echo "== NONTRACE tail"; grep -v '^conv miss trace' probes/trace_close_body.txt | grep -v '^  ' | tail -40
