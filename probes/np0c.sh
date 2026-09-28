# Round "one name per value — the implementation", job 0c: the sort split.
#
# §2's `Δ = fv` column names every shared value that clears the threshold,
# whatever its sort. A Ψ binding names a **term** (§12.1 item 1), so the mint
# of §4 can take only the term-sort ones; a shared *type* is nameable through
# its **code** — mint `c : Ty l`, spell the occurrence `El (c^δ)` — which §5
# keeps as a separate device and prices at "about 2 %" on §12.3's graph.
#
# Three columns per reduct, priced on one walk:
#   `T64=`  §2's, every sort, a reference charged `1 + |fv|`;
#   `TM64=` the **term-only** mint of §4 — the ceiling this round's device can
#           reach, and `TM0=` is that ceiling with the threshold waived;
#   `TC64=` both devices together, with a type occurrence charged the `El` as
#           well (`2 + |fv|`).
# `tynode=` says how many of the threshold-clearing values are types.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_np0c
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
E="HEATHER_RB=fv HEATHER_RB_FVDEPTH=1 HEATHER_RB_FVSPLIT=1"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
cp target/release/heather target/heather_fv

for f in t_qt1:qt_pure t_cp9:cp_andt t_qt3:qt_deep; do
  file=${f%%:*}; item=${f##*:}
  t0=$SECONDS
  ( ulimit -v 8388608 -t 1800; env $E target/heather_fv check $L \
    --kernel-workers 1 --timings /tmp/np0c_$file.tsv probes/$file.hthr \
    > "$OUT/$file.out" 2>&1 )
  echo "-- rc=$? $file/$item $((SECONDS - t0))s $(date +%T)"
  for it in "$item" complete_post; do
    grep -a "^rb fv item=.*::$it " "$OUT/$file.out" \
      | awk '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} if(n>m){m=n;l=$0}} END{print "   " l}'
  done
done

echo "== the whole showcase, split keying $(date +%T)"
t0=$SECONDS
( ulimit -v 16777216 -t 3600; env $E target/heather_fv check $L \
  --kernel-workers 1 --timings /tmp/np0c_sc.tsv docs/showcase/calc_parser.hthr \
  > "$OUT/sc.out" 2>&1 )
echo "-- rc=$? showcase $((SECONDS - t0))s $(date +%T)"
awk '/^rb fv /{r+=1; for(i=1;i<=NF;i++){split($i,a,"=");
      if(a[1]=="thr") t+=a[2]; if(a[1]=="bad") b+=a[2];
      if(a[1]=="tynode") y+=a[2]; if(a[1]=="closed") c+=a[2];
      if(a[1]=="shared") s+=a[2]}}
    END{printf "   reducts=%d shared=%d thr=%d tynode=%d bad=%d closed=%d\n", r, s, t, y, b, c}' \
  "$OUT/sc.out"
awk '/^rb fv /{for(i=1;i<=NF;i++){
      if($i ~ /^T64=/){split($i,a,"="); split(a[2],p,"|"); split(p[1],q,"/"); n+=q[1]; e+=q[2]}
      if($i ~ /^TM64=/){split($i,a,"="); split(a[2],q,"/"); tn+=q[1]; te+=q[2]}
      if($i ~ /^TM0=/){split($i,a,"="); split(a[2],q,"/"); zn+=q[1]; ze+=q[2]}
      if($i ~ /^TC64=/){split($i,a,"="); split(a[2],q,"/"); cn+=q[1]; ce+=q[2]}}}
    END{printf "   T64   names=%d emitted=%d\n   TM64  names=%d emitted=%d\n   TM0   names=%d emitted=%d\n   TC64  names=%d emitted=%d\n", n,e,tn,te,zn,ze,cn,ce}' \
  "$OUT/sc.out"
echo "   items that mint a **term** at all (TM64):"
awk '/^rb fv /{it=""; v=0; for(i=1;i<=NF;i++){split($i,a,"=");
      if(a[1]=="item") it=a[2];
      if($i ~ /^TM64=/){split(a[2],q,"/"); v=q[1]}}
      if(v>0) c[it]+=v} END{for(k in c) printf "     %-44s %d\n", k, c[k]}' \
  "$OUT/sc.out" | sort -k2 -rn | head -20
echo "== MARKER done $(date +%T)"
