# Round "the close_body family" (2026-09-16), job 3: WHY the named projection
# declines at the family's field reads. `HEATHER_GENDEF_DECLINES=1` prints
#
#   gendef-decline<TAB>site<TAB>decl<TAB>reason<TAB>module::item
#
# and `project_field`'s reason is one of `receiver-gate` / `instance-args` /
# `no-projection-def` per field index. The counter (job 2) says 18 of
# `close_body`'s 29 `Certified` reads take the fallback walk and that those
# 18 carry 78 % of its read nodes; this says which decline that is, and so
# whose slice the fix is.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cb3
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
SHOW=docs/showcase/calc_parser.hthr

echo "== showcase, decline listing $(date +%T)"
( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_GENDEF_DECLINES=1 \
  target/release/heather check $L --kernel-workers 1 --timings "$OUT/d.tsv" $SHOW \
  > "$OUT/d.out" 2> "$OUT/d.err" ); echo "== rc=$? $(date +%T)"

echo "-- project_field declines, by item and reason (family items only)"
awk -F'\t' '$1=="gendef-decline" && $2=="project_field" &&
  ($5 ~ /::(close_body|expr_body|factor_body|number_grammar|open_body|atom_body|sum_finish|product_finish|checked_expr|symbol_span)$/) {
    split($4,r,"-"); print $5"\t"$3"\t"$4}' "$OUT/d.err" | sort | uniq -c | sort -rn | head -40

echo "-- every project_field decline reason, summed over the file"
awk -F'\t' '$1=="gendef-decline" && $2=="project_field" {n=split($4,r,"-"); reason=$4; sub(/-[0-9]+$/,"",reason); print $3"\t"reason}' "$OUT/d.err" |
  sort | uniq -c | sort -rn | head -20

echo "-- other sites declining inside the family's items"
awk -F'\t' '$1=="gendef-decline" && $2!="project_field" &&
  ($5 ~ /::(close_body|expr_body|factor_body|number_grammar)$/) {print $5"\t"$2"\t"$3"\t"$4}' "$OUT/d.err" |
  sort | uniq -c | sort -rn | head -15

echo "-- the same for the probes $(date +%T)"
for f in t_cb1 t_cb6 t_pcr3; do
  ( ulimit -v 8388608 -t 900; HEATHER_VALUE_METRICS=1 HEATHER_GENDEF_DECLINES=1 \
    target/release/heather check $L --kernel-workers 1 --timings "$OUT/$f.tsv" probes/$f.hthr \
    > "$OUT/$f.out" 2> "$OUT/$f.err" )
  echo "  -- $f"
  awk -F'\t' '$1=="gendef-decline" && $2=="project_field" {reason=$4; sub(/-[0-9]+$/,"",reason); print "     "$3"\t"reason"\t"$5}' "$OUT/$f.err" |
    sort | uniq -c | sort -rn | head -8
done

echo "== the probes' own node counts (job 2's aggregator took no rows: the probe\n   items are named after their fns, not prefixed) $(date +%T)"
for f in t_cb1 t_cb3 t_cb4 t_cb6 t_pcr3 t_pc3; do
  ( ulimit -v 8388608 -t 900; HEATHER_VALUE_METRICS=1 HEATHER_CB=1 \
    target/release/heather check $L --kernel-workers 1 --timings "$OUT/$f.cb.tsv" probes/$f.hthr \
    > "$OUT/$f.cb.out" 2> "$OUT/$f.cb.err" )
  python3 probes/cb_agg.py "$OUT/$f.cb.err" "$OUT/$f.cb.tsv" all
done

echo "== MARKER done $(date +%T)"
