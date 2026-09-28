# Round "one name per value — the implementation", job 0b: the four rows of
# §2's decisive table read **per item** in the split keying (job 0's `row`
# reported the largest `naive` of a run, which is `complete_post` on every
# one of them), plus the two columns the implementation needs and the design
# pass did not print:
#
#   - `tynode=` — of the threshold-clearing shared values, how many are of the
#     value language's **type** sort. A Ψ binding names a term, so those are
#     nameable only through a minted code, which `docs/name-per-value-design`
#     §5 keeps as a separate device;
#   - `TM64=` — the same emitted count with exactly those excluded, i.e. the
#     ceiling the term-only mint of §4 can actually reach.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_np0b
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
cp target/release/heather target/heather_fv

for f in t_qt1:qt_pure t_cp9:cp_andt t_qt3:qt_deep; do
  file=${f%%:*}; item=${f##*:}
  t0=$SECONDS
  ( ulimit -v 8388608 -t 1800; env HEATHER_RB=fv HEATHER_RB_FVDEPTH=1 HEATHER_RB_FVSPLIT=1 \
    target/heather_fv check $L --kernel-workers 1 \
    --timings /tmp/np0b_$file.tsv probes/$file.hthr > "$OUT/$file.out" 2>&1 )
  echo "-- rc=$? $file/$item $((SECONDS - t0))s $(date +%T)"
  for it in "$item" complete_post; do
    grep -a "^rb fv item=.*::$it " "$OUT/$file.out" \
      | awk '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} if(n>m){m=n;l=$0}} END{print "   " l}'
  done
done
echo "== MARKER done $(date +%T)"
