# Round "one name per value — the implementation", job 0d: the measure of
# sharing, re-asked.
#
# Job 0c's `TM` column loses most of §2's names because a shared value of the
# **type** sort cannot be a Ψ binding. But the in-degree the threshold
# columns measure sharing by is the wrong measure once some nodes cannot be
# named: an `El` that is written twenty times has one edge to the *term*
# under it, so that term reads as "shared once" and is never named, even
# though its expansion is written twenty times.
#
# `TE<t>=` is the same term-only rule with the saving taken over the node's
# multiplicity **in the tree** instead — `El l (c^δ)` over a named code,
# which is a Ψ `Tm` binding and needs no new device. If that column lands
# near §2's `T64`, the sort split is a measurement artefact and §4's mint
# reaches its own bar; if it does not, the type-code device of §5 is on the
# round's critical path after all.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_np0d
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
E="HEATHER_RB=fv HEATHER_RB_FVDEPTH=1 HEATHER_RB_FVSPLIT=1"

echo "== build $(date +%T)"
echo "   stray jobs: $(pgrep -c -f heather || true)"
# A stale binary from a previous job lives on the cache volume, so a failed
# build must stop the run rather than re-measure the last one.
if ! cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -25; then
  echo "== MARKER done (build failed) $(date +%T)"; exit 1
fi
cp target/release/heather target/heather_te

for f in t_qt1:qt_pure t_cp9:cp_andt t_qt3:qt_deep; do
  file=${f%%:*}; item=${f##*:}
  t0=$SECONDS
  ( ulimit -v 8388608 -t 1800; env $E target/heather_te check $L \
    --kernel-workers 1 --timings /tmp/np0d_$file.tsv probes/$file.hthr \
    > "$OUT/$file.out" 2>&1 )
  echo "-- rc=$? $file/$item $((SECONDS - t0))s $(date +%T)"
  for it in "$item" complete_post; do
    grep -a "^rb fv item=.*::$it " "$OUT/$file.out" \
      | awk '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} if(n>m){m=n;l=$0}} END{print "   " l}'
  done
done
echo "== MARKER done $(date +%T)"
