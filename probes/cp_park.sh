# Round "quote the respelled type" (2026-09-16), job 1: park the parent binary
# and read t_cp1's trace excerpt.
#
# (a) `target/release/heather` on the box is HEAD (fb069d5, value-metrics);
#     copy it to `target/heather_parent` BEFORE any crates/ edit is synced, so
#     every before/after table below runs both binaries on one box (the remote
#     checkout is an rsync and not a git repository — see probes/README.md).
# (b) The design's §8 item 1 spike, part one: is the repeated 732-character
#     `El «Wf «(«Σ…` literal an **App annotation** inside the quoted component?
#     t_cp1 reproduces the library item to the unit (design §2), so trace it
#     rather than the 74 s showcase.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cpk
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== park $(date +%T)"
ls -l target/release/heather
cp target/release/heather target/heather_parent
ls -l target/heather_parent
( ulimit -v 8388608 -t 120; target/heather_parent --version ) || echo "== parent --version rc=$?"

echo "== trace cp_full $(date +%T)"
( ulimit -v 8388608 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=cp_full \
  target/heather_parent check $L --kernel-workers 1 --timings "$OUT/tr.tsv" probes/t_cp1.hthr \
  > "$OUT/tr.out" 2> "$OUT/tr.err" )
echo "== rc=$? $(date +%T) records=$(grep -c '^conv miss trace cp_full' "$OUT/tr.err")"

echo "== the item rows"
awk -F'\t' '$1=="item"{printf "  %-28s total %9.1f ms gate %9.1f ms misses %8d shortcut %9d steps %10d\n",$3,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/tr.tsv"

echo "== (b) buckets by (expected len, inferred len, first difference at)"
grep '^expected len=' "$OUT/tr.err" | sort | uniq -c | sort -rn | head -12

echo "== (c) site x head pair"
awk '/^conv miss trace cp_full /{split($0,f," "); hp=f[5]; next}
     /^site: /{c[hp" | "$0]++} END{for (k in c) printf "  %7d  %s\n", c[k], k}' "$OUT/tr.err" \
  | sort -rn | head -14 | cut -c1-400

echo "== (d) the elaborator frames, grouped — which emission site wrote the annotation"
grep -A 14 '^elaborator frames:' "$OUT/tr.err" | grep -oE 'heather_elab::[A-Za-z_:<>{} .0-9]+' \
  | sed 's/::h[0-9a-f]*$//' | sort | uniq -c | sort -rn | head -25

echo "== (e) FULL records 1..6 — term: line included, uncut to 4000 chars"
for n in 1 2 3 4 5 6; do
  echo "== FULL RECORD $n"
  awk -v want=$n '/^conv miss trace cp_full /{m++} m==want{print} m==want+1{exit}' "$OUT/tr.err" | cut -c1-4000
done

echo "== (f) one record per distinct site, term line only (is the 732-char side an App annotation?)"
awk '/^conv miss trace cp_full /{hp=$5; next}
     /^site: /{s=$0; next}
     /^term: /{k=hp" | "s; if (!(k in seen)) {seen[k]=1; print "---- "k; print substr($0,1,1200)}}' "$OUT/tr.err" | head -120

echo "== MARKER done $(date +%T)"
