# Round "the projected tuple tower" (2026-09-16), job 2: candidate D measured
# end to end — the curve and the showcase, parent against the change.
#
# One binary, two behaviours: `target/heather_tt` with `HEATHER_TT` unset is
# the parent's code path (the simplifier is not called), with `HEATHER_TT=fire`
# it is D. The parked `target/heather_parent` (HEAD, before the edit synced) is
# the control that says the unset path really is the parent.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_ttsl
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
cp target/release/heather target/heather_tt
test -x target/heather_parent || echo "== MISSING target/heather_parent"

# Columns (1-based): 4 total_ns, 8 kernel_gate_ns, 11 decl_emit_ns,
# 14 elab_whnf_ns, 41 conv_shortcut_hits, 43 conv_misses, 46 eval_steps,
# 47 eval_delta_steps (probes/README.md, and stats::header()'s order).
row () { awk -F'\t' -v w="$2" '$1=="item"{printf "  %-6s %-14s total %9.1f gate %9.1f elab_whnf %8.1f emit %8.1f misses %8d queries %10d steps %10d dsteps %9d\n",w,$3,$4/1e6,$8/1e6,$14/1e6,$11/1e6,$43,$41,$46,$47}' "$1"; }

echo "== the curve $(date +%T)"
for f in t_qt2 t_qt1 t_cp9 t_qt3 t_qt4 t_cp1 t_cp18 t_qt5; do
  for who in off fire; do
    env_tt=""
    if [ "$who" = fire ]; then env_tt="fire"; fi
    ( ulimit -v 33554432 -t 3600; /usr/bin/time -f "== time $who $f %es wall %MKB maxrss" \
      env ${env_tt:+HEATHER_TT=$env_tt} target/heather_tt check $L --kernel-workers 1 \
      --timings "$OUT/${who}_$f.tsv" probes/$f.hthr > "$OUT/${who}_$f.out" 2>&1 )
    echo "== rc=$? $who $f $(date +%T)"
    grep -a '^== time' "$OUT/${who}_$f.out"; grep -a -iE 'error|panick' "$OUT/${who}_$f.out" | head -3
    row "$OUT/${who}_$f.tsv" "$who"
  done
done

echo "== the fifth count point: t_qt5 under the instrument $(date +%T)"
( ulimit -v 33554432 -t 3600; HEATHER_TT=count \
  target/heather_tt check $L --kernel-workers 1 --timings "$OUT/c_t_qt5.tsv" probes/t_qt5.hthr \
  > "$OUT/c_t_qt5.out" 2> "$OUT/c_t_qt5.err" )
echo "== rc=$? $(date +%T)"
grep -a '^tt count' "$OUT/c_t_qt5.err" \
  | sed 's/nodes=//; s/proj=//; s/beta=//; s/case=//; s/us=//; s/ -> / /g' \
  | awk '{printf "   %-22s pre %9d post %9d | proj %8d %8d | beta %7d %7d | case %6d %6d | %8d us\n",$3,$4,$5,$6,$7,$8,$9,$10,$11,$12}' \
  | sort -k3 -rn | head -4

echo "== parent control on t_cp9 (is the unset path the parent's?) $(date +%T)"
( ulimit -v 16777216 -t 1800; target/heather_parent check $L --kernel-workers 1 \
  --timings "$OUT/parent_t_cp9.tsv" probes/t_cp9.hthr > "$OUT/parent_t_cp9.out" 2>&1 )
echo "== rc=$?"; row "$OUT/parent_t_cp9.tsv" parent

echo "== the showcase $(date +%T)"
named () { awk -F'\t' -v w="$2" '$1=="item" && $3 ~ /^(complete_post|close_body|expr_body|factor_body|number_grammar|checked_expr|Grammar|Certified)$/ {
    printf "  %-9s %-16s total %9.1f ms gate %9.1f ms misses %8d queries %10d steps %10d\n",w,$3,$4/1e6,$8/1e6,$43,$41,$46}' "$1"; }
totals () { awk -F'\t' -v w="$2" '$1=="item"{t+=$4;k+=$8;m+=$43;h+=$41;s+=$46;n+=1}
  END{printf "  TOTALS %-12s items=%d total=%.2f s kernel=%.2f s misses=%d queries=%d steps=%d\n",w,n,t/1e9,k/1e9,m,h,s}' "$1"; }
for who in off fire; do
  env_tt=""; if [ "$who" = fire ]; then env_tt="fire"; fi
  echo "== showcase W=1 $who $(date +%T)"
  ( ulimit -v 33554432 -t 3600; /usr/bin/time -f "== time $who W=1 %es wall %MKB maxrss" \
    env ${env_tt:+HEATHER_TT=$env_tt} target/heather_tt check $L --kernel-workers 1 \
    --timings "$OUT/${who}_sc.tsv" $F 2>&1 | tail -3 )
  named "$OUT/${who}_sc.tsv" "$who-W1"; totals "$OUT/${who}_sc.tsv" "$who-W1"
done
for who in off fire; do
  env_tt=""; if [ "$who" = fire ]; then env_tt="fire"; fi
  echo "== showcase default width $who $(date +%T)"
  ( ulimit -v 33554432 -t 3600; /usr/bin/time -f "== time $who Wdef %es wall %MKB maxrss" \
    env ${env_tt:+HEATHER_TT=$env_tt} target/heather_tt check $L \
    --timings "$OUT/${who}_scd.tsv" $F 2>&1 | tail -3 )
  named "$OUT/${who}_scd.tsv" "$who-Wdef"; totals "$OUT/${who}_scd.tsv" "$who-Wdef"
done

echo "== the per-item join (no item's misses, queries or steps may rise)"
join -t'	' -j 1 \
  <(awk -F'\t' '$1=="item"{printf "%s\t%d\t%d\t%d\n",$2"::"$3,$43,$41,$46}' "$OUT/off_sc.tsv" | sort -u -t'	' -k1,1) \
  <(awk -F'\t' '$1=="item"{printf "%s\t%d\t%d\t%d\n",$2"::"$3,$43,$41,$46}' "$OUT/fire_sc.tsv" | sort -u -t'	' -k1,1) \
  > "$OUT/joined.tsv"
echo "  rows joined: $(wc -l < "$OUT/joined.tsv")"
echo "-- misses ROSE"; awk -F'\t' '$5>$2{printf "  %-46s %8d -> %8d\n",$1,$2,$5}' "$OUT/joined.tsv" | head -20
echo "-- queries ROSE"; awk -F'\t' '$6>$3{printf "  %-46s %9d -> %9d\n",$1,$3,$6}' "$OUT/joined.tsv" | head -20
echo "-- steps ROSE"; awk -F'\t' '$7>$4{printf "  %-46s %10d -> %10d\n",$1,$4,$7}' "$OUT/joined.tsv" | head -20
echo "-- the ten that fell most (queries)"
awk -F'\t' '{printf "  %-46s misses %8d -> %8d queries %9d -> %9d\n",$1,$2,$5,$3,$6}' "$OUT/joined.tsv" \
  | sort -k7 -rn | head -10

echo "== the whole summed head-pair table, both sides $(date +%T)"
head_pairs () { grep -h '^conv miss expected=' "$1" 2>/dev/null \
  | sed 's/^conv miss expected=//; s/ inferred=/\t/; s/ count=/\t/; s/ total=/\t/; s/s$//' \
  | awk -F'\t' '{k=$1"/"$2; c[k]+=$3; s[k]+=$4} END{for (k in c) printf "  %10d  %9.3fs  %s\n", c[k], s[k], k}' | sort -k2 -rn; }
for who in off fire; do
  env_tt=""; if [ "$who" = fire ]; then env_tt="fire"; fi
  ( ulimit -v 33554432 -t 3600; HEATHER_VALUE_METRICS=1 \
    env ${env_tt:+HEATHER_TT=$env_tt} target/heather_tt check $L --kernel-workers 1 $F \
    > "$OUT/${who}_vm.out" 2> "$OUT/${who}_vm.err" )
  cat "$OUT/${who}_vm.out" "$OUT/${who}_vm.err" > "$OUT/${who}_vm.all"
  head_pairs "$OUT/${who}_vm.all" > "$OUT/${who}_hp.txt"
  echo "-- $who"; head -14 "$OUT/${who}_hp.txt"
  awk '{c+=$1; s+=$2} END{printf "  ALL PAIRS misses=%d seconds=%.3f rows=%d\n", c, s, NR}' "$OUT/${who}_hp.txt"
done
echo "== rows that ROSE off -> fire"
join -j 3 -o 0,1.1,1.2,2.1,2.2 <(sort -k3 "$OUT/off_hp.txt") <(sort -k3 "$OUT/fire_hp.txt") 2>/dev/null \
  | awk '{if ($4+0 > $2+0) printf "  ROSE %-28s %d -> %d\n", $1, $2, $4}'

echo "== MARKER done $(date +%T)"
