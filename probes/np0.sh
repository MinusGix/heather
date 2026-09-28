# Round "one name per value — the implementation" (2026-09-16), job 0: the
# brief's step 0 items 1 and 4 on this tree, before any commit-path edit.
#
#   - build release with `value-metrics`, park the parent binary
#     (`target/heather_parent`) and the instrument's copy
#     (`target/heather_fv`);
#   - re-run `probes/nv_table.sh`'s four rows and read `naive`, `bad`, `badc`
#     and `closed` off them. `naive` in split keying must be §12.3's column
#     (293 908 / 1 056 154 / 4 006 444 / 1 584 491), `bad` and `badc` must be
#     0, and `closed` must be 7 on `complete_post`. Anything else and the
#     walk and the emitter have drifted apart and §2's table is not about the
#     object the emitter writes.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_np0
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
cp target/release/heather target/heather_parent
cp target/release/heather target/heather_fv
ls -l target/heather_parent

# The row of one item, or the largest `naive` row when no item is named.
row () { grep -a "^rb fv " "$1" | awk -v it="$2" '$0 ~ it {n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} if(n>m){m=n;l=$0}} END{print "  " l}'; }

for f in t_qt1 t_cp9 t_qt3; do
  for mode in split uniq depth; do
    e="HEATHER_RB_FVDEPTH=1"
    [ "$mode" = split ] && e="HEATHER_RB_FVDEPTH=1 HEATHER_RB_FVSPLIT=1"
    [ "$mode" = uniq ] && e=""
    t0=$SECONDS
    ( ulimit -v 8388608 -t 1800; env HEATHER_RB=fv $e \
      target/heather_fv check $L --kernel-workers 1 \
      --timings /tmp/np0_$f.tsv probes/$f.hthr > "$OUT/${f}_$mode.out" 2>&1 )
    echo "-- rc=$? $f/$mode $((SECONDS - t0))s $(date +%T)"
    echo "   probe:        $(row "$OUT/${f}_$mode.out" '.')"
    echo "   complete_post:$(row "$OUT/${f}_$mode.out" 'complete_post')"
  done
done
echo "== MARKER done $(date +%T)"
