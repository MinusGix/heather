# Round "one name per value" (2026-09-16) — the free-variable instrument.
#
# `HEATHER_RB=fv` re-runs `rbcount.rs`'s value-graph walk with, per shared
# sub-value, its exact **free-variable set** (the ambient Γ levels and fresh
# neutrals reachable through the value) and, per occurrence, whether the
# binder chain it is reached under contains all of them. The emitted count is
# then taken under the rule the pass exists to price: **one mint per value,
# Δ = fv, a reference costing 1 + |fv|**.
#
# Two numberings, because the question cannot be asked in one of them alone:
#   - default: every opening takes its own binder identities from a counter,
#     so a scope test is exact (depth-keyed levels alias across branches);
#   - `HEATHER_RB_FVDEPTH=1`: the walk's own depth numbering, i.e. §11.1's
#     graph to the unit, where the test degenerates to "is the chain long
#     enough" — §12.5's own criterion.
#
# Columns: `thr` shared values clearing T=64, `bad` of those whose scope is
# missing a free variable, `unb` the sub-case no path binds at all (the
# instrument's own contamination bound), `closed` those with |fv| = 0,
# `T64=<names>/<emitted>` the rule, `ideal=` the same with the scope test
# waived — §11.2's predicted column, re-derived.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_fv
mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

row () { grep -a "^rb fv " "$1" | awk -v it="$2" '$0 ~ it {n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} if(n>m){m=n;l=$0}} END{print "  " l}'; }

for f in t_qt1 t_cp9 t_qt3; do
  for mode in split uniq depth; do
    e="HEATHER_RB_FVDEPTH=1"
    [ "$mode" = split ] && e="HEATHER_RB_FVDEPTH=1 HEATHER_RB_FVSPLIT=1"
    [ "$mode" = uniq ] && e=""
    t0=$SECONDS
    ( ulimit -v 8388608 -t 1800; env HEATHER_RB=fv $e \
      target/heather_fv check $L --kernel-workers 1 \
      --timings /tmp/nv_$f.tsv probes/$f.hthr > "$OUT/${f}_$mode.out" 2>&1 )
    echo "-- rc=$? $f/$mode $((SECONDS - t0))s $(date +%T)"
    row "$OUT/${f}_$mode.out" "."
  done
done
echo "== MARKER done $(date +%T)"
