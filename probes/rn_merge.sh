# Round "the naming half of the readback" (2026-09-16), job 4 — the one
# experiment that decides whether §11.2's price was ever the emitter's.
#
# `rbcount.rs` memoizes a **0-binder closure on its identity alone**, merging
# its occurrences at every depth; `rbemit.rs` keys on `(CloId, d)`, because the
# readback of a closure one binder down is different syntax (its free variables
# are indices `d − lvl − 1` and its references' substitution tails carry
# `δ̂ = d`). §11.2's 80 477 was priced on the first memo and §12.3 measures the
# second. `HEATHER_RB_MERGE=1` keys the emitter the counter's way — **unsound
# syntax**, counted and discarded, and only under `HEATHER_RB=name` — so the
# two numbers can be read side by side and the gap attributed.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_rnmerge
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
cp target/release/heather target/heather_rn

top () { grep -a "^rb name item" "$1" | awk '{n=0; for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]=="naive") n=a[2]+0} print n"\t"$0}' \
  | sort -rn | head -"$2" | cut -f2- | sed 's/^/  /'; }

for f in t_qt1 t_cp9 t_qt3; do
  for mode in keyed merged; do
    e=""; [ "$mode" = merged ] && e="HEATHER_RB_MERGE=1"
    ( ulimit -v 16777216 -t 1800; env HEATHER_RB=name HEATHER_RB_TYCODE=1 ${e:+$e} \
      target/heather_rn check $L --kernel-workers 1 --timings "$OUT/${mode}_$f.tsv" \
      probes/$f.hthr > "$OUT/${mode}_$f.out" 2>&1 )
    echo "-- rc=$? $f $mode $(date +%T)"
    grep -a -iE '^error|panick' "$OUT/${mode}_$f.out" | head -3
    top "$OUT/${mode}_$f.out" 2
  done
done

echo "== the mints infer_term refuses, with a sixteenfold-fuel retry $(date +%T)"
sum () { grep -a "^rb name item" "$1" | awk -v key="$2" '{for(i=1;i<=NF;i++){split($i,a,"="); if(a[1]==key) s+=a[2]+0} n+=1} END{printf "  rows=%d sum(%s)=%d\n", n, key, s}'; }
for f in t_qt1 t_cp9; do
  ( ulimit -v 16777216 -t 1800; HEATHER_RB=name HEATHER_RB_TYPE=1 target/heather_rn check $L \
    --kernel-workers 1 --timings "$OUT/typed_$f.tsv" probes/$f.hthr > "$OUT/typed_$f.out" 2>&1 )
  echo "-- rc=$? $f $(date +%T)"
  for k in typed untyped stmt; do sum "$OUT/typed_$f.out" $k; done
  echo "  retry=ok: $(grep -ac 'retry=ok' "$OUT/typed_$f.out")  retry=fail: $(grep -ac 'retry=fail' "$OUT/typed_$f.out")"
  grep -a 'UNTYPED' "$OUT/typed_$f.out" | sed 's/body=.*//' | head -8
done

echo "== MARKER done $(date +%T)"
