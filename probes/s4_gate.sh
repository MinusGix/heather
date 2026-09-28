# Round 2026-09-15 part A, job 2: the gate (design §7 items 2-4 and the
# telescoped design's §9 item 6). Parent (`target/heather_parent`) and part A
# (`target/heather_a`), one box, one job. Built by `probes/s4_build.sh`.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_s4g
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

# The WHOLE summed head-pair table, not its head: the table is printed once
# per module and summing the blocks is the run's table (probes/README.md).
head_pairs () { # $1 out $2 err
  grep -h '^conv miss expected=' "$1" "$2" 2>/dev/null \
    | sed 's/^conv miss expected=//; s/ inferred=/\t/; s/ count=/\t/; s/ total=/\t/; s/s$//' \
    | awk -F'\t' '{k=$1"/"$2; c[k]+=$3; s[k]+=$4}
                  END{for (k in c) printf "  %10d  %9.3fs  %s\n", c[k], s[k], k}' \
    | sort -k2 -rn
}
totals () { awk -F'\t' '$1=="item"{t+=$4;k+=$8;e+=$11;m+=$43;s+=$46;n+=1}
  END{printf "  TOTALS %s items=%d total=%.2f s kernel=%.2f s emit=%.2f s misses=%d steps=%d\n","'"$2"'",n,t/1e9,k/1e9,e/1e6/1000,m,s}' "$1"; }
named () { awk -F'\t' '$1=="item"{printf "  %-34s total %9.1f ms kernel %9.1f ms emit %8.1f ms misses %8d steps %10d\n",$3,$4/1e6,$8/1e6,$11/1e6,$43,$46}' "$1"; }

for who in parent a; do
  BIN=target/heather_parent; [ $who = a ] && BIN=target/heather_a
  test -x $BIN || { echo "== MISSING $BIN"; echo "== MARKER done"; exit 1; }
done

# ---------- decline listing, both ------------------------------------------
for who in parent a; do
  BIN=target/heather_parent; [ $who = a ] && BIN=target/heather_a
  echo "== listing $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_GENDEF_DECLINES=1 \
    $BIN check $L --kernel-workers 1 $F > "$OUT/${who}_l.out" 2> "$OUT/${who}_l.err" )
  echo "== rc=$? $who listing $(date +%T); tail:"; tail -2 "$OUT/${who}_l.out"
  echo "== total decline lines: $(grep -c '^gendef-decline' "$OUT/${who}_l.err")"
  grep '^gendef-decline' "$OUT/${who}_l.err" | cut -f2,3,4 \
    | grep -E 'instance_match|project_field' | sort | uniq -c | sort -rn | head -30
  echo "== identity-match rows $who"
  grep '^gendef-decline' "$OUT/${who}_l.err" | cut -f2,3,4 \
    | grep 'identity-match' | sort | uniq -c | sort -rn | head -10
done

# ---------- the trace, re-read on part A ------------------------------------
for who in parent a; do
  BIN=target/heather_parent; [ $who = a ] && BIN=target/heather_a
  echo "== trace close_body $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=close_body \
    $BIN check $L --kernel-workers 1 $F > "$OUT/${who}_cb.out" 2> "$OUT/${who}_cb.err" )
  echo "== rc=$? $who $(date +%T)"
  python3 probes/trace_agg.py "$OUT/${who}_cb.err" 2>&1 | sed -n '1,16p'
done

# ---------- t_pcr3, both ----------------------------------------------------
for who in parent a; do
  BIN=target/heather_parent; [ $who = a ] && BIN=target/heather_a
  rm -rf /tmp/s4_$who
  echo "== t_pcr3 $who $(date +%T)"
  ( ulimit -v 8388608 -t 900; /usr/bin/time -f "== time $who t_pcr3 %es wall %MKB maxrss" \
    $BIN check --cache --cache-dir /tmp/s4_$who $L --kernel-workers 1 \
    --timings "$OUT/${who}_r3.tsv" probes/t_pcr3.hthr > "$OUT/${who}_r3.out" 2>&1 )
  echo "== rc=$? $who t_pcr3"; tail -2 "$OUT/${who}_r3.out"
  [ -f "$OUT/${who}_r3.tsv" ] && named "$OUT/${who}_r3.tsv"
done

# ---------- showcase, serial, both -----------------------------------------
for who in parent a; do
  BIN=target/heather_parent; [ $who = a ] && BIN=target/heather_a
  echo "== showcase W=1 $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time $who W=1 %es wall %MKB maxrss" \
    $BIN check $L --kernel-workers 1 --timings "$OUT/${who}_sc.tsv" $F 2>&1 | tail -3 )
  named "$OUT/${who}_sc.tsv" | grep -E 'close_body|complete_post'
  totals "$OUT/${who}_sc.tsv" "$who-W1"
done

# ---------- showcase, default width, both ----------------------------------
for who in parent a; do
  BIN=target/heather_parent; [ $who = a ] && BIN=target/heather_a
  echo "== showcase default width $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time $who Wdef %es wall %MKB maxrss" \
    $BIN check $L --timings "$OUT/${who}_scd.tsv" $F 2>&1 | tail -3 )
  named "$OUT/${who}_scd.tsv" | grep -E 'close_body|complete_post'
  totals "$OUT/${who}_scd.tsv" "$who-Wdef"
done

# ---------- the WHOLE head-pair table, both --------------------------------
for who in parent a; do
  BIN=target/heather_parent; [ $who = a ] && BIN=target/heather_a
  echo "== head pairs (whole table) $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 \
    $BIN check $L --kernel-workers 1 $F > "$OUT/${who}_vm.out" 2> "$OUT/${who}_vm.err" )
  head_pairs "$OUT/${who}_vm.out" "$OUT/${who}_vm.err" > "$OUT/${who}_hp.txt"
  cat "$OUT/${who}_hp.txt"
  awk '{c+=$1; s+=$2} END{printf "  ALL PAIRS misses=%d seconds=%.3f rows=%d\n", c, s, NR}' "$OUT/${who}_hp.txt"
done
echo "== rows that ROSE from parent to A (design telescoped §9 item 6)"
join -j 3 -o 0,1.1,1.2,2.1,2.2 <(sort -k3 "$OUT/parent_hp.txt") <(sort -k3 "$OUT/a_hp.txt") 2>/dev/null \
  | awk '{gsub("s","",$3); gsub("s","",$5); if ($4+0 > $2+0) printf "  ROSE %-28s %d -> %d\n", $1, $2, $4}'
echo "== pairs only in A"
comm -13 <(awk '{print $3}' "$OUT/parent_hp.txt" | sort) <(awk '{print $3}' "$OUT/a_hp.txt" | sort)
echo "== MARKER done $(date +%T)"
