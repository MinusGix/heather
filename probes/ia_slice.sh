# Round "the matcher sees through a quote" (2026-09-16), job 2: the bar
# (`docs/instance-match-quote-arm-design.md` §5). Parent
# (`target/heather_parent`, HEAD 1a91fc1 with value-metrics, parked by
# `probes/ia_spell.sh`) against the change (`target/heather_ia`), one box,
# one job, counts first.
#
#   (0) the flipped unit test and its neighbours;
#   (1) the curve t_cb3/t_cb2/t_cb1 and t_pcr3's qchain1..3, both binaries;
#   (2) the showcase serial and at the default gate width, both binaries,
#       with the family named;
#   (3) the WHOLE summed head-pair table both sides, and the rows that ROSE;
#   (4) the decline listing on the showcase and on t_ia1/t_ia3, both sides.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_ia3
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' -A 8 | tail -20
cp target/release/heather target/heather_ia
for b in parent ia; do test -x target/heather_$b || { echo "== MISSING target/heather_$b"; echo "== MARKER done"; exit 1; }; done

named () { awk -F'\t' -v w="$2" '$1=="item" && $3 ~ /^(cb_one|cb_two|cb_full|qchain1|qchain2|qchain3|qev3|ia_one|ia_res|close_body|expr_body|factor_body|open_body|atom_body|number_grammar|complete_post|Grammar|Certified|checked_expr)$/ {
    printf "  %-10s %-16s total %9.1f ms gate %9.1f ms misses %8d QUERIES %10d steps %10d\n",w,$3,$4/1e6,$8/1e6,$43,$41,$46}' "$1"; }
totals () { awk -F'\t' -v w="$2" '$1=="item"{t+=$4;k+=$8;m+=$43;h+=$41;s+=$46;n+=1}
  END{printf "  TOTALS %-14s items=%d total=%.2f s kernel=%.2f s misses=%d queries=%d steps=%d\n",w,n,t/1e9,k/1e9,m,h,s}' "$1"; }
head_pairs () { grep -h '^conv miss expected=' "$1" "$2" 2>/dev/null \
  | sed 's/^conv miss expected=//; s/ inferred=/\t/; s/ count=/\t/; s/ total=/\t/; s/s$//' \
  | awk -F'\t' '{k=$1"/"$2; c[k]+=$3; s[k]+=$4} END{for (k in c) printf "  %10d  %9.3fs  %s\n", c[k], s[k], k}' | sort -k2 -rn; }

# ---------- (0) the unit tests ------------------------------------------------
echo "== (0) the matcher's own tests $(date +%T)"
scripts/test --fast -p heather-elab wf::tests > "$OUT/unit.log" 2>&1; echo "== unit rc=$? $(date +%T)"
grep -a -E '^== suite:|INCOMPLETE|^test result:' "$OUT/unit.log" | tail -5
grep -a -E '^(failures:|---- |panicked at)' "$OUT/unit.log" | head -30

# ---------- (1) the curve ----------------------------------------------------
for f in t_cb3 t_cb2 t_cb1 t_pcr3 t_ia1 t_ia3; do
  for who in parent ia; do
    ( ulimit -v 8388608 -t 1800; /usr/bin/time -f "== time $who $f %es wall %MKB maxrss" \
      target/heather_$who check $L --kernel-workers 1 --timings "$OUT/${who}_$f.tsv" probes/$f.hthr \
      > "$OUT/${who}_$f.out" 2>&1 )
    echo "== rc=$? $who $f $(date +%T)"; grep -a '^== time' "$OUT/${who}_$f.out"; tail -1 "$OUT/${who}_$f.out"
    named "$OUT/${who}_$f.tsv" "$who"
  done
done

# ---------- (2) the showcase -------------------------------------------------
for who in parent ia; do
  echo "== showcase W=1 $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time $who W=1 %es wall %MKB maxrss" \
    target/heather_$who check $L --kernel-workers 1 --timings "$OUT/${who}_sc.tsv" $F 2>&1 | tail -3 )
  named "$OUT/${who}_sc.tsv" "$who-W1"; totals "$OUT/${who}_sc.tsv" "$who-W1"
done
for who in parent ia; do
  echo "== showcase default width $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time $who Wdef %es wall %MKB maxrss" \
    target/heather_$who check $L --timings "$OUT/${who}_scd.tsv" $F 2>&1 | tail -3 )
  named "$OUT/${who}_scd.tsv" "$who-Wdef"; totals "$OUT/${who}_scd.tsv" "$who-Wdef"
done

echo "== (2b) the per-item join, all rows"
join -t'	' -j 1 \
  <(awk -F'\t' '$1=="item"{printf "%s\t%d\t%d\t%d\n",$2"::"$3,$43,$41,$46}' "$OUT/parent_sc.tsv" | sort -u -t'	' -k1,1) \
  <(awk -F'\t' '$1=="item"{printf "%s\t%d\t%d\t%d\n",$2"::"$3,$43,$41,$46}' "$OUT/ia_sc.tsv" | sort -u -t'	' -k1,1) \
  > "$OUT/joined.tsv"
echo "-- rows joined: $(wc -l < "$OUT/joined.tsv")"
echo "-- items whose misses ROSE";   awk -F'\t' '$5>$2 {printf "  %-46s misses %8d -> %8d\n",$1,$2,$5}' "$OUT/joined.tsv" | head -20
echo "-- items whose QUERIES rose";  awk -F'\t' '$6>$3 {printf "  %-46s queries %9d -> %9d\n",$1,$3,$6}' "$OUT/joined.tsv" | head -20
echo "-- items whose STEPS rose";    awk -F'\t' '$7>$4 {printf "  %-46s steps %10d -> %10d\n",$1,$4,$7}' "$OUT/joined.tsv" | head -20
echo "-- the ten items that fell most (queries)"
awk -F'\t' '{printf "  %-46s misses %8d -> %8d  queries %9d -> %9d\n",$1,$2,$5,$3,$6}' "$OUT/joined.tsv" | sort -k7 -rn | head -10

# ---------- (3) the head-pair table ------------------------------------------
for who in parent ia; do
  echo "== head pairs (whole table) $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 \
    target/heather_$who check $L --kernel-workers 1 $F > "$OUT/${who}_vm.out" 2> "$OUT/${who}_vm.err" )
  head_pairs "$OUT/${who}_vm.out" "$OUT/${who}_vm.err" > "$OUT/${who}_hp.txt"
  head -14 "$OUT/${who}_hp.txt"
  awk '{c+=$1; s+=$2} END{printf "  ALL PAIRS misses=%d seconds=%.3f rows=%d\n", c, s, NR}' "$OUT/${who}_hp.txt"
done
echo "== rows that ROSE parent -> ia"
join -j 3 -o 0,1.1,1.2,2.1,2.2 <(sort -k3 "$OUT/parent_hp.txt") <(sort -k3 "$OUT/ia_hp.txt") 2>/dev/null \
  | awk '{if ($4+0 > $2+0) printf "  ROSE %-28s %d -> %d   %ss -> %ss\n", $1, $2, $4, $3, $5}'
echo "== pairs only in ia";     comm -13 <(awk '{print $3}' "$OUT/parent_hp.txt" | sort) <(awk '{print $3}' "$OUT/ia_hp.txt" | sort)
echo "== pairs only in parent"; comm -23 <(awk '{print $3}' "$OUT/parent_hp.txt" | sort) <(awk '{print $3}' "$OUT/ia_hp.txt" | sort)

# ---------- (4) the decline listing ------------------------------------------
for who in parent ia; do
  echo "== declines, showcase, $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_GENDEF_DECLINES=1 \
    target/heather_$who check $L --kernel-workers 1 --timings "$OUT/${who}_d.tsv" $F > "$OUT/${who}_d.out" 2> "$OUT/${who}_d.err" )
  echo "== rc=$? total decline lines: $(grep -ac '^gendef-decline' "$OUT/${who}_d.err")"
  echo "-- project_field, by declaration and reason (whole file)"
  awk -F'\t' '$1=="gendef-decline" && $2=="project_field" {r=$4; sub(/-[0-9]+$/,"",r); print $3"\t"r}' "$OUT/${who}_d.err" |
    sort | uniq -c | sort -rn | head -12
  echo "-- project_field, the family's items"
  awk -F'\t' '$1=="gendef-decline" && $2=="project_field" &&
    ($5 ~ /::(close_body|expr_body|factor_body|number_grammar|open_body|atom_body|checked_expr)$/) {r=$4; sub(/-[0-9]+$/,"",r); print $5"\t"$3"\t"r}' "$OUT/${who}_d.err" |
    sort | uniq -c | sort -rn | head -14
  echo "-- instance_match Certified / Exists / Result, the family's items"
  awk -F'\t' '$1=="gendef-decline" && $2=="instance_match" && ($3=="Certified"||$3=="Exists"||$3=="Result"||$3=="Grammar") &&
    ($5 ~ /::(close_body|expr_body|factor_body|number_grammar)$/) {print $5"\t"$3"\t"$4}' "$OUT/${who}_d.err" |
    sort | uniq -c | sort -rn | head -14
done
echo "== MARKER done $(date +%T)"
