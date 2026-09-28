set -u
cd "$(dirname "$0")/.."
for f in "$@"; do
  echo "== probe $f start $(date +%T)"
  ( ulimit -v 4194304 -t 300; /usr/bin/time -f "== time $f %es wall %MKB maxrss" \
    target/release/heather check --kernel-workers 1 --timings probes/tm_$(basename $f .hthr).tsv $f 2>&1 | grep -v '^\s*$' | tail -8 )
  echo "== TSV $f"; awk -F'\t' '$1=="item"{printf "%-10s total %8.1f ms  kernel %8.1f ms  emit %8.1f ms  body %7.1f ms  misses %6d steps %8d\n",$3,$4/1e6,$8/1e6,$11/1e6,$10/1e6,$43,$46}' probes/tm_$(basename $f .hthr).tsv
done
