set -u
cd "$(dirname "$0")/.."
TAG=${TAG:-x}
for f in "$@"; do
  b=$(basename $f .hthr)
  echo "== probe $f start $(date +%T)"
  ( ulimit -v 6291456 -t 600; /usr/bin/time -f "== time $f %es wall %MKB maxrss" \
    target/release/heather check --kernel-workers 1 -L lib/std -L lib/std/parser \
      --timings probes/tm_${TAG}_${b}.tsv $f 2>&1 | tail -4 )
  echo "== TSV $f"
  awk -F'\t' '$1=="item"{printf "%-14s total %9.1f ms  kernel %9.1f ms  emit %8.1f ms  body %8.1f ms  misses %7d steps %9d\n",$3,$4/1e6,$8/1e6,$11/1e6,$10/1e6,$43,$46}' \
    probes/tm_${TAG}_${b}.tsv | grep -E 'qchain|qev|^Q|close_body|complete_post|parenthes|missing_close|nested'
done
echo "== LIB DONE"
