# Round "the naming half of the readback" (2026-09-16), job 1 — the brief's
# step 0: the mints in a scratch world, counted, before any commit-path edit.
#
# Three questions, in order:
#   1. do §11.1's counts still hold on this tree (`HEATHER_RB=count`)?
#   2. with the naming on (`HEATHER_RB=name`), is the emitted node count the
#      graph's — `qt_deep` a small multiple of `qt_pure`, `complete_post`
#      ≈ 80 k — and how many mints per reduct?
#   3. can every mint be *typed*? `HEATHER_RB_TYPE=1` infers each mint's
#      statement in the scratch world and prints the ones that fail.
#
# The naming is measured with the readback's answer **discarded**: the item
# still checks against the rewriter's reduct, so nothing on the commit path
# moves.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_rnspike
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== park $(date +%T)"
ls -l target/release/heather
cp target/release/heather target/heather_parent

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
cp target/release/heather target/heather_rn

# The largest line of a run, by one of its `key=value` columns.
best () { grep -a "^rb $1 " "$2" | awk -v key="$3" '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]==key) n=a[2]+0} if(n>m){m=n; l=$0}} END{print "  " l}'; }
sum () { grep -a "^rb $1 " "$2" | awk -v key="$3" '{for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]==key) s+=a[2]+0} n+=1} END{printf "  rows=%d sum(%s)=%d\n", n, key, s}'; }

echo "== 1. §11.1 re-confirmed (HEATHER_RB=count) $(date +%T)"
for f in t_qt1 t_cp9 t_qt3; do
  ( ulimit -v 16777216 -t 1800; HEATHER_RB=count target/heather_rn check $L \
    --kernel-workers 1 probes/$f.hthr > "$OUT/count_$f.out" 2>&1 )
  echo "-- rc=$? $f $(date +%T)"
  best count "$OUT/count_$f.out" naive
done

echo "== 2/3. the naming, counted and typed (HEATHER_RB=name) $(date +%T)"
for f in t_qt2 t_qt1 t_cp9 t_qt3; do
  ( ulimit -v 16777216 -t 1800; HEATHER_RB=name HEATHER_RB_TYPE=1 \
    /usr/bin/time -f "  == time $f %es wall %MKB maxrss" \
    target/heather_rn check $L --kernel-workers 1 probes/$f.hthr \
    > "$OUT/name_$f.out" 2>&1 )
  echo "-- rc=$? $f $(date +%T)"
  grep -a '== time' "$OUT/name_$f.out"
  grep -a -iE '^error|panick' "$OUT/name_$f.out" | head -3
  best name "$OUT/name_$f.out" naive
  sum name "$OUT/name_$f.out" mints
  echo "  UNTYPED=$(grep -ac 'UNTYPED' "$OUT/name_$f.out") DECLINED=$(grep -ac 'rb name .* DECLINED' "$OUT/name_$f.out")"
  grep -a 'UNTYPED' "$OUT/name_$f.out" | head -3
done

echo "== the showcase, counted (no per-mint typing) $(date +%T)"
( ulimit -v 33554432 -t 3600; HEATHER_RB=name \
  /usr/bin/time -f "  == time showcase %es wall %MKB maxrss" \
  target/heather_rn check $L --kernel-workers 1 $F > "$OUT/name_sc.out" 2>&1 )
echo "-- rc=$? $(date +%T)"
grep -a '== time' "$OUT/name_sc.out"
grep -a -iE '^error|panick' "$OUT/name_sc.out" | head -3
sum name "$OUT/name_sc.out" mints
sum name "$OUT/name_sc.out" emitted
echo "  DECLINED=$(grep -ac 'rb name .* DECLINED' "$OUT/name_sc.out")"
echo "-- complete_post's own reducts (the largest three)"
grep -a '^rb name item=.*::complete_post ' "$OUT/name_sc.out" \
  | awk '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} print n"\t"$0}' \
  | sort -rn | head -3 | cut -f2- | sed 's/^/  /'
echo "-- the items that mint at all (§11.2 predicts 152 names over 8 092 reducts)"
grep -a '^rb name ' "$OUT/name_sc.out" \
  | awk '{m=0; it=""; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="mints") m=a[2]+0; if(a[1]=="item") it=a[2]} if(m>0){c[it]+=m}} END{for(k in c) printf "  %-40s %d\n", k, c[k]}' \
  | sort -k2 -rn | head -20
echo "-- declines that cleared the threshold, summed"
for k in dty dforeign damb dcap dlost; do sum name "$OUT/name_sc.out" $k; done

echo "== MARKER done $(date +%T)"
