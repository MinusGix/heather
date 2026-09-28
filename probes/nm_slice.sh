# Round "one name per value — the implementation", job 1: parent against the
# landed device, on the curve and on the showcase, for **both stages** — the
# term mint alone (`HEATHER_RB_TERMS_ONLY=1`) and the two spellings together.
#
# The parent binary is `target/heather_parent`, parked by `probes/nm0.sh` from
# HEAD; this script never overwrites it and prints which binary each run used.
# It aborts if the build fails, because a silently re-measured previous binary
# is the trap that cost this round's predecessor a whole job.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_nm_slice
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

# A stray from a killed job holds `target/heather_mint` open, `cp` fails with
# "Text file busy", and the run silently re-measures the previous binary —
# the trap `probes/README.md` records. Kill first, and abort if the copy fails.
pkill -f heather_mint || true
pkill -f heather_parent || true
sleep 2
echo "== stray heather processes: $(pgrep -af 'heather ' | wc -l)"
if [ ! -f target/heather_parent ]; then echo "NO PARKED PARENT"; exit 1; fi
echo "== parent: $(stat -c '%s %y' target/heather_parent)"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
if ! cargo build --release -p heather-cli --features value-metrics >/dev/null 2>&1; then
  echo "BUILD FAILED"; exit 1
fi
rm -f target/heather_mint
if ! cp target/release/heather target/heather_mint; then
  echo "COPY FAILED — refusing to measure a stale binary"; exit 1
fi
echo "== changed: $(stat -c '%s %y' target/heather_mint)"

run () { # run <tag> <binary> <file> <extra-env>
  tag=$1; bin=$2; f=$3; env_extra=${4:-}
  t0=$SECONDS
  ( ulimit -v 16777216 -t 1800; env $env_extra "$bin" check $L --kernel-workers 1 \
      --timings "$OUT/$tag.$f.tsv" "probes/$f.hthr" > "$OUT/$tag.$f.out" 2>&1 )
  echo "-- rc=$? $tag/$f $((SECONDS - t0))s bin=$bin $(date +%T)"
}

# The smoke test first: the whole library under the device, before anything
# long is spent measuring a binary that does not check it.
run both target/heather_mint t_qt2
if ! grep -qa 'probes/t_qt2.hthr: ok' "$OUT/both.t_qt2.out"; then
  echo "SMOKE FAILED — the library does not check under the device"
  grep -a '^error' -A6 "$OUT/both.t_qt2.out" | head -40
  exit 1
fi

for f in t_qt2 t_qt1 t_cp9 t_qt3 t_qt4 t_qt5 t_cp1 t_cp2 t_cp18; do
  for m in parent terms both; do
    bin=target/heather_mint; e=""
    [ "$m" = parent ] && bin=target/heather_parent
    [ "$m" = terms ] && e="HEATHER_RB_TERMS_ONLY=1"
    [ -f "$OUT/$m.$f.tsv" ] && continue
    run "$m" "$bin" "$f" "$e"
  done
  for m in parent terms both; do
    echo "  == $f/$m"
    python3 probes/nm_agg.py "$OUT/$m.$f.tsv" 2>/dev/null | tail -20
  done
done

echo "-- showcase $(date +%T)"
for m in parent terms both; do
  bin=target/heather_mint; e=""
  [ "$m" = parent ] && bin=target/heather_parent
  [ "$m" = terms ] && e="HEATHER_RB_TERMS_ONLY=1"
  for w in 1 8; do
    t0=$SECONDS
    ( ulimit -v 16777216 -t 3600; env $e /usr/bin/time -v "$bin" check $L \
        --kernel-workers $w --timings "$OUT/show.$m.$w.tsv" \
        docs/showcase/calc_parser.hthr > "$OUT/show.$m.$w.out" 2> "$OUT/show.$m.$w.err" )
    echo "-- rc=$? showcase/$m/w$w $((SECONDS - t0))s bin=$bin"
    grep -a 'Maximum resident\|Elapsed (wall' "$OUT/show.$m.$w.err" || true
  done
done

echo "== the per-item join, serial"
for m in terms both; do
  echo "  -- parent -> $m"
  ( cd probes && python3 nm_join.py "../$OUT/show.parent.1.tsv" "../$OUT/show.$m.1.tsv" )
done
echo "== the named items, serial"
for m in parent terms both; do
  echo "  -- $m"
  python3 probes/nm_agg.py "$OUT/show.$m.1.tsv" complete_post close_body expr_body \
    factor_body number_grammar checked_expr Grammar Certified
done
echo "== Psi growth (mints pushed), serial"
for m in terms both; do
  awk -F'\t' 'NR==1{for(i=1;i<=NF;i++)h[$i]=i} NR>1{s+=$h["mints_pushed"]; d+=$h["mints_declined"]} END{printf "   %s mints=%d declined=%d\n", M, s, d}' M=$m "$OUT/show.$m.1.tsv"
done

echo "== MARKER done $(date +%T)"
