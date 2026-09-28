# Round "the projected tuple tower" (2026-09-16), job 1: park the parent
# binary, build the spike, and run the NODE-COUNT INSTRUMENT over the curve.
#
# `HEATHER_TT=count` prints, per `build_ctor` reduct: the reduct's node count
# before and after the δ-free deep simplifier, the `Fst`/`Snd`-of-`Pair`,
# `App`-of-`Lam` and `case`-of-constructor counts on both sides, and the
# simplifier's own microseconds. The binary behaves exactly as the parent in
# this mode (the fired reduct is measured and thrown away), so the item rows
# in the same run are the parent's.
#
# `HEATHER_TT=fire` is candidate D. Here it is only smoke-tested: does the
# kernel still accept what the elaborator writes?
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_ttc
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== park $(date +%T)"
ls -l target/release/heather
cp target/release/heather target/heather_parent

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
cp target/release/heather target/heather_tt
ls -l target/heather_parent target/heather_tt

for f in t_qt2 t_qt1 t_cp9 t_qt3; do
  echo "== count $f $(date +%T)"
  ( ulimit -v 16777216 -t 1800; HEATHER_TT=count \
    target/heather_tt check $L --kernel-workers 1 --timings "$OUT/c_$f.tsv" probes/$f.hthr \
    > "$OUT/c_$f.out" 2> "$OUT/c_$f.err" )
  echo "== rc=$? records=$(grep -ca '^tt count' "$OUT/c_$f.err")"
  tail -2 "$OUT/c_$f.out"
  awk -F'\t' '$1=="item"{printf "  item %-12s total %9.1f ms gate %9.1f ms misses %8d queries %10d steps %10d\n",$3,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/c_$f.tsv"
  echo "-- the ten largest reducts (pre-firing nodes), by item"
  grep -a '^tt count' "$OUT/c_$f.err" \
    | sed 's/nodes=//; s/proj=//; s/beta=//; s/case=//; s/us=//; s/ -> / /g' \
    | awk '{printf "   %-22s pre %9d post %9d | proj %8d %8d | beta %7d %7d | case %6d %6d | %8d us\n",$3,$4,$5,$6,$7,$8,$9,$10,$11,$12}' \
    | sort -k3 -rn | head -10
  echo "-- summed over every reduct of this file"
  grep -a '^tt count' "$OUT/c_$f.err" \
    | sed 's/nodes=//; s/proj=//; s/beta=//; s/case=//; s/us=//; s/ -> / /g' \
    | awk '{pre+=$4; post+=$5; p0+=$6; p1+=$7; b0+=$8; b1+=$9; c0+=$10; c1+=$11; us+=$12; n++}
           END{printf "   reducts=%d pre=%d post=%d ratio=%.3f | proj %d -> %d | beta %d -> %d | case %d -> %d | %.1f ms\n", n,pre,post,(pre?post/pre:0),p0,p1,b0,b1,c0,c1,us/1000}'
done

echo "== fire smoke $(date +%T) (does the kernel accept what D writes?)"
for f in t_qt2 t_cp9; do
  ( ulimit -v 16777216 -t 1800; HEATHER_TT=fire \
    target/heather_tt check $L --kernel-workers 1 --timings "$OUT/f_$f.tsv" probes/$f.hthr \
    > "$OUT/f_$f.out" 2>&1 )
  echo "== rc=$? fire $f"; tail -3 "$OUT/f_$f.out"
  awk -F'\t' '$1=="item"{printf "  item %-12s total %9.1f ms gate %9.1f ms misses %8d queries %10d steps %10d\n",$3,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/f_$f.tsv"
done
echo "== parent control on the same two"
for f in t_qt2 t_cp9; do
  ( ulimit -v 16777216 -t 1800; target/heather_parent check $L --kernel-workers 1 \
    --timings "$OUT/p_$f.tsv" probes/$f.hthr > "$OUT/p_$f.out" 2>&1 )
  echo "== rc=$? parent $f"
  awk -F'\t' '$1=="item"{printf "  item %-12s total %9.1f ms gate %9.1f ms misses %8d queries %10d steps %10d\n",$3,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/p_$f.tsv"
done
echo "== MARKER done $(date +%T)"
