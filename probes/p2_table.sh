# The round's bar (design §9 items 3-5), both binaries in one job on one box.
# target/heather_parent is the HEAD build (probes/p2_parent.sh); target/release/
# heather is the changed one.
set -u
cd "$(dirname "$0")/.."
TAG="${TAG:-t1}"
OUT=probes/out_$TAG
rm -rf "$OUT"; mkdir -p "$OUT"
echo "== build start $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' -A 6 | tail -40
test -x target/release/heather || { echo "== NO BINARY"; echo "== MARKER done"; exit 1; }
test -x target/heather_parent || { echo "== NO PARENT BINARY"; echo "== MARKER done"; exit 1; }
echo "== build done $(date +%T)"

echo "== unit tests start $(date +%T)"
scripts/test --fast -p heather-elab --lib tycode 2>&1 | tail -30
echo "== unit tests done $(date +%T)"

L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

row () { # $1 tsv
  awk -F'\t' '$1=="item"{printf "  %-34s total %9.1f ms  kernel %9.1f ms  emit %8.1f ms  misses %8d  steps %10d\n",$3,$4/1e6,$8/1e6,$11/1e6,$43,$46}' "$1"
}

# ---- reproducers -----------------------------------------------------------
for who in parent changed; do
  BIN=target/heather_parent; [ $who = changed ] && BIN=target/release/heather
  echo "== reproducers $who start $(date +%T)"
  # A **fresh** cache directory per file (probes/README.md): the declaration
  # cache is keyed on the proof obligation term, so `Cur`/`Cert` declared
  # identically in two probe files would be answered from the first file's
  # images and the declaration items — which §9 item 3 asks about by name —
  # would read as zeros.
  for f in t_pc1 t_pc2 t_pc3 t_pc4 t_pcev3 t_pcr3; do
    rm -rf /tmp/pc_${who}_$f
    ( ulimit -v 8388608 -t 600; /usr/bin/time -f "== time $who $f %es wall %MKB maxrss (rc in next line)" \
      $BIN check --cache --cache-dir /tmp/pc_${who}_$f $L --kernel-workers 1 \
      --timings "$OUT/${who}_$f.tsv" probes/$f.hthr > "$OUT/${who}_$f.out" 2>&1 )
    echo "== rc=$? $who $f"
    tail -2 "$OUT/${who}_$f.out"
    [ -f "$OUT/${who}_$f.tsv" ] && row "$OUT/${who}_$f.tsv"
  done
  echo "== reproducers $who done $(date +%T)"
done

# ---- showcase, serial ------------------------------------------------------
for who in parent changed; do
  BIN=target/heather_parent; [ $who = changed ] && BIN=target/release/heather
  echo "== showcase W=1 $who start $(date +%T)"
  ( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time $who W=1 %es wall %Us user %MKB maxrss" \
    $BIN check $L --kernel-workers 1 --timings "$OUT/${who}_sc.tsv" $F 2>&1 | tail -4 )
  echo "== rc=$? $who W=1 $(date +%T)"
  echo "== showcase rows $who"
  awk -F'\t' '$1=="item"{printf "  %-44s total %9.1f ms  kernel %9.1f ms  emit %8.1f ms  misses %8d  steps %10d\n",$3,$4/1e6,$8/1e6,$11/1e6,$43,$46}' "$OUT/${who}_sc.tsv" \
    | grep -E 'close_body|complete_post|number_grammar|checked_expr|parentheses|nested_parentheses|missing_close'
  awk -F'\t' '$1=="run"{print "  RUN "$0}' "$OUT/${who}_sc.tsv"
  awk -F'\t' '$1=="item"{t+=$4; k+=$8; m+=$43; s+=$46; n+=1} END{printf "  TOTALS items=%d total=%.1f s kernel=%.1f s misses=%d steps=%d\n",n,t/1e9,k/1e9,m,s}' "$OUT/${who}_sc.tsv"
done

# ---- head pairs ------------------------------------------------------------
for who in parent changed; do
  BIN=target/heather_parent; [ $who = changed ] && BIN=target/release/heather
  echo "== head pairs $who start $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 \
    $BIN check $L --kernel-workers 1 $F > "$OUT/${who}_vm.out" 2> "$OUT/${who}_vm.err" )
  echo "== rc=$? $who $(date +%T)"
  # The table is printed once per module, so the run's head pairs are the sum
  # over every block — `head` on the raw lines samples one module and misranks.
  echo "== top head pairs $who (count, seconds, expected/inferred)"
  grep -h '^conv miss expected=' "$OUT/${who}_vm.out" "$OUT/${who}_vm.err" 2>/dev/null \
    | sed 's/^conv miss expected=//; s/ inferred=/\t/; s/ count=/\t/; s/ total=/\t/; s/s$//' \
    | awk -F'\t' '{k=$1"/"$2; c[k]+=$3; s[k]+=$4} END{for (k in c) printf "  %10d  %9.3fs  %s\n", c[k], s[k], k}' \
    | sort -rn | head -10
  grep -h '^conv miss expected=' "$OUT/${who}_vm.out" "$OUT/${who}_vm.err" 2>/dev/null \
    | sed 's/.*count=\([0-9]*\) .*/\1/' | awk '{t+=$1} END{print "  head-pair miss total = "t}'
done

# ---- default gate width ----------------------------------------------------
for who in parent changed; do
  BIN=target/heather_parent; [ $who = changed ] && BIN=target/release/heather
  echo "== showcase default width $who start $(date +%T)"
  ( ulimit -v 25165824 -t 3600; /usr/bin/time -f "== time $who Wdefault %es wall %Us user %MKB maxrss" \
    $BIN check $L $F 2>&1 | tail -3 )
  echo "== rc=$? $who default $(date +%T)"
done
echo "== MARKER done $(date +%T)"
