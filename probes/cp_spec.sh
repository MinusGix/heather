# Round "complete_post attribution", job 4: decomposing the spec (same recipe
# as probes/cp_repro.sh, second batch of files).
# One process per file, **no cache at all** — the declaration cache is keyed on
# the obligation term, and rather than reason about whether six variants of one
# statement collide, every file pays the library prefix afresh. The prefix is
# subtracted by reading the item rows out of `--timings`, never the wall.
#
# Every file also re-elaborates `parser_primitives::complete_post` itself, so
# each run carries the library item as its own control on the same box.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cp4
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

row () { awk -F'\t' '$1=="item" && ($3 ~ /^cp_/ || $3 ~ /^CP/ || $3=="complete_post" || $3=="CTok" || $3=="CPR"){
   printf "  %-12s %-12s total %9.1f ms  gate %9.1f ms  elab %9.1f ms  emit %8.1f ms  misses %8d  short %10d  steps %10d  delta %8d\n",
   $2,$3,$4/1e6,$8/1e6,($4-$8-$6)/1e6,$11/1e6,$43,$41,$46,$47 }' "$1"; }

for f in t_cp7 t_cp8 t_cp9 t_cp10; do
  echo "== $f start $(date +%T)"
  ( ulimit -v 8388608 -t 900; /usr/bin/time -f "== time $f %es wall %MKB maxrss" \
    target/release/heather check $L --kernel-workers 1 --timings "$OUT/$f.tsv" \
    probes/$f.hthr > "$OUT/$f.out" 2>&1 )
  echo "== rc=$? $f $(date +%T)"
  tail -3 "$OUT/$f.out"
  [ -f "$OUT/$f.tsv" ] && row "$OUT/$f.tsv"
done
echo "== MARKER done $(date +%T)"
