# Job 3: the slice-1 spike, before and after, in one job.
# `probes/s3_base/gendefs.rs` is HEAD's copy; the synced tree carries the spike.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_s3s
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr
SPIKE=$(mktemp); cp crates/elab/src/gendefs.rs "$SPIKE"

head_pairs () { # $1 out $2 err
  grep -h '^conv miss expected=' "$1" "$2" 2>/dev/null \
    | sed 's/^conv miss expected=//; s/ inferred=/\t/; s/ count=/\t/; s/ total=/\t/; s/s$//' \
    | awk -F'\t' '{k=$1"/"$2; c[k]+=$3; s[k]+=$4} END{for (k in c) printf "  %10d  %9.3fs  %s\n", c[k], s[k], k}' \
    | sort -rn | head -8
}
row () { awk -F'\t' '$1=="item"{printf "  %-22s total %9.1f ms kernel %9.1f ms emit %8.1f ms misses %7d steps %9d\n",$3,$4/1e6,$8/1e6,$11/1e6,$43,$46}' "$1"; }

# ---------- base ------------------------------------------------------------
cp probes/s3_base/gendefs.rs crates/elab/src/gendefs.rs
echo "== base build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|warning: unused|    Finished)' -A 6 | tail -30
test -x target/release/heather || { echo "== BASE BUILD FAILED"; cp "$SPIKE" crates/elab/src/gendefs.rs; echo "== MARKER done"; exit 1; }
cp target/release/heather target/heather_base
echo "== base build done $(date +%T)"

# ---------- spike -----------------------------------------------------------
cp "$SPIKE" crates/elab/src/gendefs.rs
echo "== spike build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|warning: unused|    Finished)' -A 8 | tail -60
echo "== spike build rc above; $(date +%T)"
cmp -s target/heather_base target/release/heather && { echo "== SPIKE BINARY IDENTICAL TO BASE — build failed"; echo "== MARKER done"; exit 1; }

echo "== unit tests: wf tycode + dependent_telescope $(date +%T)"
scripts/test --fast -p heather-elab --lib 'wf::tests' 2>&1 | tail -40
echo "== unit tests done $(date +%T)"

# ---------- decline listing, both ------------------------------------------
for who in base spike; do
  BIN=target/heather_base; [ $who = spike ] && BIN=target/release/heather
  echo "== listing $who $(date +%T)"
  ( ulimit -v 16777216 -t 2400; HEATHER_GENDEF_DECLINES=1 \
    $BIN check $L --kernel-workers 1 $F > "$OUT/${who}_l.out" 2> "$OUT/${who}_l.err" )
  echo "== rc=$? $who listing $(date +%T); tail:"; tail -2 "$OUT/${who}_l.out"
  grep '^gendef-decline' "$OUT/${who}_l.err" | cut -f2,3,4 \
    | grep -E 'instance_match|project_field' | sort | uniq -c | sort -rn | head -22
done

# ---------- t_pcr3, both ----------------------------------------------------
for who in base spike; do
  BIN=target/heather_base; [ $who = spike ] && BIN=target/release/heather
  rm -rf /tmp/s3_$who
  echo "== t_pcr3 $who $(date +%T)"
  ( ulimit -v 8388608 -t 900; /usr/bin/time -f "== time $who t_pcr3 %es wall %MKB maxrss" \
    $BIN check --cache --cache-dir /tmp/s3_$who $L --kernel-workers 1 \
    --timings "$OUT/${who}_r3.tsv" probes/t_pcr3.hthr > "$OUT/${who}_r3.out" 2>&1 )
  echo "== rc=$? $who t_pcr3"; tail -2 "$OUT/${who}_r3.out"
  [ -f "$OUT/${who}_r3.tsv" ] && row "$OUT/${who}_r3.tsv" | grep -E 'qchain|qev|QR'
done

# ---------- showcase, both --------------------------------------------------
for who in base spike; do
  BIN=target/heather_base; [ $who = spike ] && BIN=target/release/heather
  echo "== showcase W=1 $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; /usr/bin/time -f "== time $who W=1 %es wall %MKB maxrss" \
    $BIN check $L --kernel-workers 1 --timings "$OUT/${who}_sc.tsv" $F 2>&1 | tail -3 )
  echo "== rc=$? $who showcase"
  awk -F'\t' '$1=="item"{printf "  %-30s total %9.1f ms kernel %9.1f ms misses %8d steps %10d\n",$3,$4/1e6,$8/1e6,$43,$46}' "$OUT/${who}_sc.tsv" \
    | grep -E 'close_body|complete_post'
  awk -F'\t' '$1=="item"{t+=$4;k+=$8;m+=$43;s+=$46;n+=1} END{printf "  TOTALS %s items=%d total=%.1f s kernel=%.1f s misses=%d steps=%d\n","'$who'",n,t/1e9,k/1e9,m,s}' "$OUT/${who}_sc.tsv"
  echo "== head pairs $who $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 \
    $BIN check $L --kernel-workers 1 $F > "$OUT/${who}_vm.out" 2> "$OUT/${who}_vm.err" )
  head_pairs "$OUT/${who}_vm.out" "$OUT/${who}_vm.err"
done
echo "== MARKER done $(date +%T)"
