# Round "the naming half of the readback" (2026-09-16), job 5: one loose end,
# then the plain full `scripts/test` on the tree offered for review.
#
# The loose end: the instrument's reserved block defaults to 256 slots, and
# the `T0` column of the threshold sweep — "name every shared node", §11.2's
# first reading — **hits that cap** on the library's reduct, so its number is
# a truncation rather than an answer. `HEATHER_RB_CAP=4096` asks it properly.
#
# The suite: the naming is inert with `HEATHER_RB` unset, so this is the check
# that "inert" is literal — the elaborator emits exactly what it emitted,
# `WALK_RESIDUE` and the `psi().bindings.len()` fixtures included.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_rnsuite
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
cp target/release/heather target/heather_rn

echo "== the uncapped T0 column $(date +%T)"
top () { grep -a "^rb name item" "$1" | awk '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} print n"\t"$0}' \
  | sort -rn | head -"$2" | cut -f2- | sed 's/^/  /'; }
for f in t_qt1 t_cp9; do
  ( ulimit -v 16777216 -t 1800; HEATHER_RB=name HEATHER_RB_CAP=4096 target/heather_rn check $L \
    --kernel-workers 1 --timings "$OUT/cap_$f.tsv" probes/$f.hthr > "$OUT/cap_$f.out" 2>&1 )
  echo "-- rc=$? $f $(date +%T)"
  top "$OUT/cap_$f.out" 2
done

echo "== does the readback's own answer type? (the control for the refused mints) $(date +%T)"
for f in t_qt1 t_cp9; do
  ( ulimit -v 16777216 -t 1800; HEATHER_RB=name HEATHER_RB_CHECK=1 target/heather_rn check $L \
    --kernel-workers 1 --timings "$OUT/root_$f.tsv" probes/$f.hthr > "$OUT/root_$f.out" 2>&1 )
  echo "-- rc=$? $f $(date +%T)"
  echo "  ROOT ok=$(grep -ac 'ROOT=ok' "$OUT/root_$f.out") FAIL=$(grep -ac 'ROOT=FAIL' "$OUT/root_$f.out")"
  grep -a 'ROOT=FAIL' "$OUT/root_$f.out" | cut -c1-200 | head -4
done

echo "== suite $(date +%T)"
scripts/test 2>&1 | tail -40
echo "== MARKER done $(date +%T)"
