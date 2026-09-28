# Round "one name per value — the implementation", job 0f: what the type half
# has to cover.
#
# §8.2 says §5's type-code device is on the critical path after all, so the
# question the next pass opens with is which formers `code.rs`'s `code_of`
# has to encode: `tyshapes=` tallies the **former** of every
# threshold-clearing shared value of the type sort, per reduct and summed
# over the showcase.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_np0f
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
E="HEATHER_RB=fv HEATHER_RB_FVDEPTH=1 HEATHER_RB_FVSPLIT=1"

echo "== build $(date +%T)"
# A failed build must stop the run: the cache volume keeps the previous
# binary, and a stale one re-measures the last job in silence.
cargo build --release -p heather-cli --features value-metrics > /tmp/np0f_build.log 2>&1
rc=$?
tail -25 /tmp/np0f_build.log
if [ $rc -ne 0 ]; then echo "== MARKER done (build failed) $(date +%T)"; exit 1; fi
cp target/release/heather target/heather_ts

for f in t_qt1:qt_pure t_cp9:cp_andt t_qt3:qt_deep; do
  file=${f%%:*}; item=${f##*:}
  ( ulimit -v 8388608 -t 1800; env $E target/heather_ts check $L \
    --kernel-workers 1 --timings /tmp/np0f_$file.tsv probes/$file.hthr \
    > "$OUT/$file.out" 2>&1 )
  echo "-- rc=$? $file/$item $(date +%T)"
  for it in "$item" complete_post; do
    grep -a "^rb fv item=.*::$it " "$OUT/$file.out" \
      | awk '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} if(n>m){m=n;l=$0}}
             END{sub(/ closed=.*/, "", l); print "   " l}'
  done
done

echo "== the showcase $(date +%T)"
( ulimit -v 16777216 -t 3600; env $E target/heather_ts check $L \
  --kernel-workers 1 --timings /tmp/np0f_sc.tsv docs/showcase/calc_parser.hthr \
  > "$OUT/sc.out" 2>&1 )
echo "-- rc=$? $(date +%T)"
grep -a -o 'tyshapes={[^}]*}' "$OUT/sc.out" \
  | sed 's/tyshapes={//; s/}//' | tr ',' '\n' | tr -d '" ' \
  | awk -F: '$1!=""{c[$1]+=$2} END{for(k in c) printf "   %-18s %d\n", k, c[k]}' | sort -k2 -rn
echo "== MARKER done $(date +%T)"
