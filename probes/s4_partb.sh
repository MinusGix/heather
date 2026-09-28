# Round 2026-09-15 part B, its own before/after: part A (`target/heather_a`,
# parked by `probes/s4_build.sh`) against part A + the level-tree
# normalization. Design §5.3 / `issues/fn-statement-level-trees.md`.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_s4b
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

head_pairs () {
  grep -h '^conv miss expected=' "$1" "$2" 2>/dev/null \
    | sed 's/^conv miss expected=//; s/ inferred=/\t/; s/ count=/\t/; s/ total=/\t/; s/s$//' \
    | awk -F'\t' '{k=$1"/"$2; c[k]+=$3; s[k]+=$4}
                  END{for (k in c) printf "  %10d  %9.3fs  %s\n", c[k], s[k], k}' | sort -k2 -rn
}
totals () { awk -F'\t' '$1=="item"{t+=$4;k+=$8;e+=$11;m+=$43;s+=$46;n+=1}
  END{printf "  TOTALS %s items=%d total=%.2f s kernel=%.2f s emit=%.2f s misses=%d steps=%d\n","'"$2"'",n,t/1e9,k/1e9,e/1e6/1000,m,s}' "$1"; }
named () { awk -F'\t' '$1=="item"{printf "  %-34s total %9.1f ms kernel %9.1f ms emit %8.1f ms misses %8d steps %10d\n",$3,$4/1e6,$8/1e6,$11/1e6,$43,$46}' "$1"; }

echo "== A+B build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error(\[|:)|    Finished)' -A 8 | tail -40
test -x target/release/heather || { echo "== BUILD FAILED"; echo "== MARKER done"; exit 1; }
cmp -s target/heather_a target/release/heather && { echo "== A+B IDENTICAL TO A — the edit did not land"; echo "== MARKER done"; exit 1; }
cp target/release/heather target/heather_ab
echo "== A+B parked $(date +%T)"

for who in a ab; do
  BIN=target/heather_a; [ $who = ab ] && BIN=target/heather_ab
  rm -rf /tmp/s4b_$who; mkdir -p /tmp/s4b_$who
  echo "== t_pc1..4 $who $(date +%T)"
  for n in 1 2 3 4; do
    ( ulimit -v 8388608 -t 900; $BIN check --cache --cache-dir /tmp/s4b_$who/$n $L \
      --kernel-workers 1 --timings "$OUT/${who}_pc$n.tsv" probes/t_pc$n.hthr > "$OUT/${who}_pc$n.out" 2>&1 )
    echo "== t_pc$n $who rc=$?"; tail -1 "$OUT/${who}_pc$n.out"
    [ -f "$OUT/${who}_pc$n.tsv" ] && named "$OUT/${who}_pc$n.tsv"
  done
done

for who in a ab; do
  BIN=target/heather_a; [ $who = ab ] && BIN=target/heather_ab
  echo "== showcase W=1 $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time $who W=1 %es wall %MKB maxrss" \
    $BIN check $L --kernel-workers 1 --timings "$OUT/${who}_sc.tsv" $F 2>&1 | tail -3 )
  named "$OUT/${who}_sc.tsv" | grep -E 'close_body|complete_post'
  totals "$OUT/${who}_sc.tsv" "$who-W1"
  echo "== head pairs (whole table) $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 \
    $BIN check $L --kernel-workers 1 $F > "$OUT/${who}_vm.out" 2> "$OUT/${who}_vm.err" )
  head_pairs "$OUT/${who}_vm.out" "$OUT/${who}_vm.err" | head -12
done
echo "== MARKER done $(date +%T)"
