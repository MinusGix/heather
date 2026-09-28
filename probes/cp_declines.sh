# Round "complete_post attribution", job 6: the decline listing on the two
# probes that bracket the finding — `t_cp1` (the base, `And<relation,eq>`) and
# `t_cp2` (the same theorem with the spec replaced by the plain relation).
# Grouped by (site, declaration, reason) and by the declaration scope the
# listing's fifth field names, so the rows belonging to the probe's own
# theorem can be read apart from the library's.
#
# No `--cache`: a replayed image skips elaboration and the listing prints
# nothing (probes/README.md, p2_listing.sh).
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cp6
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

for f in t_cp1 t_cp2; do
  echo "== listing $f start $(date +%T)"
  ( ulimit -v 8388608 -t 900; HEATHER_GENDEF_DECLINES=1 \
    target/release/heather check $L --kernel-workers 1 probes/$f.hthr \
    > "$OUT/$f.out" 2> "$OUT/$f.err" )
  echo "== rc=$? $f $(date +%T); total decline lines: $(grep -c '^gendef-decline' "$OUT/$f.err")"
  echo "== $f: declines charged to the probe's OWN item"
  grep '^gendef-decline' "$OUT/$f.err" | awk -F'\t' '$5 ~ /^t_cp/ {print $2"\t"$3"\t"$4}' \
    | sort | uniq -c | sort -rn | head -25
  echo "== $f: declines charged to parser_primitives::complete_post"
  grep '^gendef-decline' "$OUT/$f.err" | awk -F'\t' '$5=="parser_primitives::complete_post"{print $2"\t"$3"\t"$4}' \
    | sort | uniq -c | sort -rn | head -25
  echo "== $f: whole-run top declines by (site, decl, reason)"
  grep '^gendef-decline' "$OUT/$f.err" | cut -f2,3,4 | sort | uniq -c | sort -rn | head -15
done
echo "== MARKER done $(date +%T)"

# ---- job 7, folded into the same round trip: the head pairs of the two
# single-component variants, so the additive split (cp9 = the relation in an
# argument slot, cp12 = the equation in one) can be read as head pairs rather
# than only as counts.
for pair in t_cp9:cp_andt t_cp12:cp_teq; do
  f=${pair%%:*}; item=${pair##*:}
  echo "== trace $item on $f start $(date +%T)"
  ( ulimit -v 8388608 -t 900; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=$item \
    target/release/heather check $L --kernel-workers 1 probes/$f.hthr \
    > "$OUT/${f}_tr.out" 2> "$OUT/${f}_tr.err" )
  echo "== rc=$? $item $(date +%T) records=$(grep -c "^conv miss trace $item" "$OUT/${f}_tr.err")"
  python3 probes/trace_agg.py "$OUT/${f}_tr.err" 2>&1 | sed -n '1,14p' | cut -c1-200
  echo "== $item buckets by (expected len, inferred len, first difference at)"
  grep '^expected len=' "$OUT/${f}_tr.err" | sort | uniq -c | sort -rn | head -10
  echo "== $item site x head pair"
  awk -v it="$item" '$0 ~ "^conv miss trace "it" "{split($0,g," "); hp=g[5]; next}
       /^site: /{c[hp" | "$0]++} END{for (k in c) printf "  %7d  %s\n", c[k], k}' "$OUT/${f}_tr.err" \
    | sort -rn | head -8 | cut -c1-240
done
echo "== MARKER two done $(date +%T)"
