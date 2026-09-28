# Round "the naming half of the readback" (2026-09-16), job 2 — the two
# questions job 1 raised, before any commit-path edit:
#
#   a. **how much of the collapse is in type nodes?** A Ψ binding names a
#      *term* (`GlobalBinding::Ty` has no body), so job 1's naming declined
#      every shared **type**. `HEATHER_RB_TYCODE=1` re-runs the *arithmetic*
#      with type nodes counted as nameable — what a device that minted a
#      type's **code** and spelled the occurrence `El (u^δ)` (the registry's
#      own shape) would emit. Counting only; the rebuild still leaves them
#      inline.
#   b. **why does `infer_term` refuse some mints?** `HEATHER_RB_TYPE=1` now
#      prints the context length, the node count and a bounded `Debug` of
#      every mint it cannot type.
#
# `--timings` is passed so `stats::current_item()` names the item on every
# line (job 1's lines all read `item=-::-`).
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_rntypes
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
cp target/release/heather target/heather_rn

top () { grep -a "^rb name item" "$1" | awk '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} print n"\t"$0}' \
  | sort -rn | head -"$2" | cut -f2- | sed 's/^/  /'; }
sum () { grep -a "^rb name item" "$1" | awk -v key="$2" '{for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]==key) s+=a[2]+0} n+=1} END{printf "  rows=%d sum(%s)=%d\n", n, key, s}'; }

echo "== a. terms only, then with type nodes counted as nameable $(date +%T)"
for f in t_qt1 t_cp9 t_qt3; do
  for mode in terms tycode; do
    e=""; [ "$mode" = tycode ] && e="HEATHER_RB_TYCODE=1"
    ( ulimit -v 16777216 -t 1800; env HEATHER_RB=name ${e:+$e} target/heather_rn check $L \
      --kernel-workers 1 --timings "$OUT/${mode}_$f.tsv" probes/$f.hthr \
      > "$OUT/${mode}_$f.out" 2>&1 )
    echo "-- rc=$? $f $mode $(date +%T)"
    grep -a -iE '^error|panick' "$OUT/${mode}_$f.out" | head -3
    top "$OUT/${mode}_$f.out" 4
    sum "$OUT/${mode}_$f.out" mints
    sum "$OUT/${mode}_$f.out" emitted
  done
done

echo "== the showcase, both ways $(date +%T)"
for mode in terms tycode; do
  e=""; [ "$mode" = tycode ] && e="HEATHER_RB_TYCODE=1"
  ( ulimit -v 33554432 -t 3600; env HEATHER_RB=name ${e:+$e} target/heather_rn check $L \
    --kernel-workers 1 --timings "$OUT/sc_$mode.tsv" $F > "$OUT/sc_$mode.out" 2>&1 )
  echo "-- rc=$? showcase $mode $(date +%T)"
  sum "$OUT/sc_$mode.out" mints
  sum "$OUT/sc_$mode.out" emitted
  for k in dty damb dforeign dcap dlost; do sum "$OUT/sc_$mode.out" $k; done
  echo "-- the items that name at all"
  grep -a '^rb name item' "$OUT/sc_$mode.out" \
    | awk '{m=0; it=""; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="mints") m=a[2]+0; if(a[1]=="item") it=a[2]} if(m>0) c[it]+=m} END{for(k in c) printf "  %-44s %d\n", k, c[k]}' \
    | sort -k2 -rn | head -12
  echo "-- complete_post's own reducts, largest three"
  grep -a '^rb name item=[^ ]*::complete_post ' "$OUT/sc_$mode.out" \
    | awk '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} print n"\t"$0}' \
    | sort -rn | head -3 | cut -f2- | sed 's/^/  /'
done

echo "== b. the mints infer_term refuses $(date +%T)"
for f in t_qt1 t_cp9; do
  ( ulimit -v 16777216 -t 1800; HEATHER_RB=name HEATHER_RB_TYPE=1 target/heather_rn check $L \
    --kernel-workers 1 --timings "$OUT/typed_$f.tsv" probes/$f.hthr > "$OUT/typed_$f.out" 2>&1 )
  echo "-- rc=$? $f $(date +%T)"
  for k in typed untyped refused mints stmt; do sum "$OUT/typed_$f.out" $k; done
  grep -a 'UNTYPED' "$OUT/typed_$f.out" | sed 's/body=.*//' | head -8
  top "$OUT/typed_$f.out" 2
done

echo "== MARKER done $(date +%T)"
