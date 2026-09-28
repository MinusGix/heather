# Round "one name per value" (2026-09-16), job 2: the whole showcase under
# the free-variable instrument, so the per-value table is over all 8 092
# `build_ctor` reducts and not four of them. Depth numbering (§11.1's graph
# to the unit) and the counter numbering, one process each.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_fv
mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr
for mode in split depth; do
  e="HEATHER_RB_FVDEPTH=1"
  [ "$mode" = split ] && e="HEATHER_RB_FVDEPTH=1 HEATHER_RB_FVSPLIT=1"
  t0=$SECONDS
  ( ulimit -v 16777216 -t 3600; env HEATHER_RB=fv $e \
    target/heather_fv check $L --kernel-workers 1 \
    --timings /tmp/nv_sc.tsv $F > "$OUT/sc_$mode.out" 2>&1 )
  echo "-- rc=$? showcase/$mode $((SECONDS - t0))s $(date +%T)"
  awk '/^rb fv /{r+=1; for(i=1;i<=NF;i++){split($i,a,"=");
        if(a[1]=="thr") t+=a[2]; if(a[1]=="bad") b+=a[2];
        if(a[1]=="unb") u+=a[2]; if(a[1]=="closed") c+=a[2];
        if(a[1]=="shared") s+=a[2]}}
      END{printf "   reducts=%d shared=%d thr=%d bad=%d unb=%d closed=%d\n", r, s, t, b, u, c}' \
    "$OUT/sc_$mode.out"
  awk '/^rb fv /{for(i=1;i<=NF;i++){if($i ~ /^T64=/){split($i,a,"=");
        split(a[2],p,"|"); split(p[1],q,"/"); n+=q[1]; e+=q[2];
        split(p[2],r2,"="); split(r2[2],z,"/"); ni+=z[1]; ei+=z[2]}}}
      END{printf "   T64 names=%d emitted=%d  |  ideal names=%d emitted=%d\n", n, e, ni, ei}' \
    "$OUT/sc_$mode.out"
  echo "   items that name at all:"
  awk '/^rb fv /{it=""; v=0; for(i=1;i<=NF;i++){split($i,a,"=");
        if(a[1]=="item") it=a[2];
        if($i ~ /^T64=/){split(a[2],p,"|"); split(p[1],q,"/"); v=q[1]}}
        if(v>0) c[it]+=v} END{for(k in c) printf "     %-44s %d\n", k, c[k]}' \
    "$OUT/sc_$mode.out" | sort -k2 -rn | head -16
done
echo "== MARKER done $(date +%T)"
