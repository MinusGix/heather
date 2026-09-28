# Round "quote the respelled type" (2026-09-16), job 3: the bar
# (`docs/complete-post-attribution-design.md` §8 items 2, 5, 6 and the brief's
# step 1). Parent (`target/heather_parent`, HEAD fb069d5) against the change
# (`target/heather_q`), one box, one job, counts first.
#
#   (1) the probe rows t_cp1/2/9/12/17/18, both binaries, no cache;
#   (2) the showcase serial and at the default gate width, both binaries,
#       with complete_post, close_body, number_grammar, checked_expr,
#       expr_body, factor_body named;
#   (3) the WHOLE summed head-pair table both sides, and the rows that ROSE;
#   (4) the decline listing on t_cp1, both sides.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cpsl
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -2
cp target/release/heather target/heather_q
for b in parent q; do test -x target/heather_$b || { echo "== MISSING target/heather_$b"; echo "== MARKER done"; exit 1; }; done

# Only the rows this round names; the full item list drowns the log.
named () { awk -F'\t' -v w="$2" '$1=="item" && $3 ~ /^(cp_full|cp_plain|cp_andt|cp_teq|cp_le|cp_twice|complete_post|close_body|number_grammar|checked_expr|expr_body|factor_body)$/ {
    printf "  %-10s %-16s total %9.1f ms gate %9.1f ms misses %8d shortcut %10d steps %10d\n",w,$3,$4/1e6,$8/1e6,$43,$41,$46}' "$1"; }
totals () { awk -F'\t' -v w="$2" '$1=="item"{t+=$4;k+=$8;m+=$43;h+=$41;s+=$46;n+=1}
  END{printf "  TOTALS %-14s items=%d total=%.2f s kernel=%.2f s misses=%d shortcut=%d steps=%d\n",w,n,t/1e9,k/1e9,m,h,s}' "$1"; }
head_pairs () { grep -h '^conv miss expected=' "$1" "$2" 2>/dev/null \
  | sed 's/^conv miss expected=//; s/ inferred=/\t/; s/ count=/\t/; s/ total=/\t/; s/s$//' \
  | awk -F'\t' '{k=$1"/"$2; c[k]+=$3; s[k]+=$4} END{for (k in c) printf "  %10d  %9.3fs  %s\n", c[k], s[k], k}' | sort -k2 -rn; }

# ---------- (1) the probes ---------------------------------------------------
for f in t_cp1 t_cp2 t_cp9 t_cp12 t_cp17 t_cp18; do
  for who in parent q; do
    ( ulimit -v 8388608 -t 1800; /usr/bin/time -f "== time $who $f %es wall %MKB maxrss" \
      target/heather_$who check $L --kernel-workers 1 --timings "$OUT/${who}_$f.tsv" probes/$f.hthr \
      > "$OUT/${who}_$f.out" 2>&1 )
    echo "== rc=$? $who $f $(date +%T)"; grep -a '^== time' "$OUT/${who}_$f.out"; tail -1 "$OUT/${who}_$f.out"
    named "$OUT/${who}_$f.tsv" "$who"
  done
done

# ---------- (2) the showcase -------------------------------------------------
for who in parent q; do
  echo "== showcase W=1 $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time $who W=1 %es wall %MKB maxrss" \
    target/heather_$who check $L --kernel-workers 1 --timings "$OUT/${who}_sc.tsv" $F 2>&1 | tail -3 )
  named "$OUT/${who}_sc.tsv" "$who-W1"; totals "$OUT/${who}_sc.tsv" "$who-W1"
done
for who in parent q; do
  echo "== showcase default width $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time $who Wdef %es wall %MKB maxrss" \
    target/heather_$who check $L --timings "$OUT/${who}_scd.tsv" $F 2>&1 | tail -3 )
  named "$OUT/${who}_scd.tsv" "$who-Wdef"; totals "$OUT/${who}_scd.tsv" "$who-Wdef"
done

# ---------- (3) the head-pair table ------------------------------------------
for who in parent q; do
  echo "== head pairs (whole table) $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 \
    target/heather_$who check $L --kernel-workers 1 $F > "$OUT/${who}_vm.out" 2> "$OUT/${who}_vm.err" )
  head_pairs "$OUT/${who}_vm.out" "$OUT/${who}_vm.err" > "$OUT/${who}_hp.txt"
  cat "$OUT/${who}_hp.txt"
  awk '{c+=$1; s+=$2} END{printf "  ALL PAIRS misses=%d seconds=%.3f rows=%d\n", c, s, NR}' "$OUT/${who}_hp.txt"
done
echo "== rows that ROSE parent -> q (no head-pair count may rise)"
join -j 3 -o 0,1.1,1.2,2.1,2.2 <(sort -k3 "$OUT/parent_hp.txt") <(sort -k3 "$OUT/q_hp.txt") 2>/dev/null \
  | awk '{if ($4+0 > $2+0) printf "  ROSE %-28s %d -> %d\n", $1, $2, $4}'
echo "== pairs only in q"
comm -13 <(awk '{print $3}' "$OUT/parent_hp.txt" | sort) <(awk '{print $3}' "$OUT/q_hp.txt" | sort)
echo "== pairs only in parent"
comm -23 <(awk '{print $3}' "$OUT/parent_hp.txt" | sort) <(awk '{print $3}' "$OUT/q_hp.txt" | sort)

# ---------- (4) the decline listing ------------------------------------------
for who in parent q; do
  echo "== declines $who $(date +%T)"
  ( ulimit -v 8388608 -t 1800; HEATHER_GENDEF_DECLINES=1 \
    target/heather_$who check $L --kernel-workers 1 probes/t_cp1.hthr > "$OUT/${who}_l.out" 2> "$OUT/${who}_l.err" )
  echo "== rc=$? total decline lines: $(grep -ac '^gendef-decline' "$OUT/${who}_l.err")"
  grep -a '^gendef-decline' "$OUT/${who}_l.err" | cut -f2,3,4 | sort | uniq -c | sort -rn | head -12
done
echo "== MARKER done $(date +%T)"
