# Round "one name per value — the implementation, second pass" (2026-09-16),
# job 0: the brief's step 0 items 1, 2 and 4, before any commit-path edit.
#
#   - build release with `value-metrics` and park the parent binary
#     (`target/heather_parent`), which is HEAD's;
#   - re-read §8.1/§8.2's per-item columns in the **split** keying — `bad`,
#     `closed`, `T64`, `TM64`, `TC64` — which is step 0 item 1;
#   - read the new `tycode_no=` / `tycode_lost=` columns, which are step 0
#     item 2: of the threshold-clearing **type** nodes, how many `code_of`
#     cannot quote at all (its own former, or any type node in its subtree),
#     and what fraction of the type half's saving they carry.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_nm0
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== stray heather processes: $(pgrep -c -f 'heather ' || true)"
echo "== build $(date +%T)"
if ! cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3; then
  echo "BUILD FAILED"; exit 1
fi
cargo build --release -p heather-cli --features value-metrics >/dev/null 2>&1 || { echo "BUILD FAILED"; exit 1; }
cp target/release/heather target/heather_parent
cp target/release/heather target/heather_fv
echo "== binary: $(ls -l target/heather_fv | awk '{print $5, $6, $7, $8}') (built here, this run)"

for f in t_qt1:qt_pure t_cp9:cp_andt t_qt3:qt_deep; do
  file=${f%%:*}; item=${f##*:}
  t0=$SECONDS
  ( ulimit -v 8388608 -t 1800; env HEATHER_RB=fv HEATHER_RB_FVDEPTH=1 HEATHER_RB_FVSPLIT=1 \
    target/heather_fv check $L --kernel-workers 1 \
    --timings /tmp/nm0_$file.tsv probes/$file.hthr > "$OUT/$file.out" 2>&1 )
  echo "-- rc=$? $file/$item $((SECONDS - t0))s $(date +%T)  binary=target/heather_fv"
  for it in "$item" complete_post; do
    grep -a "^rb fv item=.*::$it " "$OUT/$file.out" \
      | awk '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} if(n>m){m=n;l=$0}} END{print "   " l}'
  done
done

echo "-- showcase $(date +%T)"
t0=$SECONDS
( ulimit -v 16777216 -t 3600; env HEATHER_RB=fv HEATHER_RB_FVDEPTH=1 HEATHER_RB_FVSPLIT=1 \
  target/heather_fv check $L --kernel-workers 1 \
  --timings /tmp/nm0_show.tsv docs/showcase/calc_parser.hthr > "$OUT/show.out" 2>&1 )
echo "-- rc=$? showcase $((SECONDS - t0))s"
grep -a "^rb fv item=" "$OUT/show.out" | python3 probes/nm0_agg.py
echo "== MARKER done $(date +%T)"
