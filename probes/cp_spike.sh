# Round "quote the respelled type" (2026-09-16), job 2: the §8-item-1 spike.
#
# (a) The trace tables job 1 printed but the log truncated: buckets, site x
#     head pair, and the elaborator frames of t_cp1's 110 851 misses, read off
#     the PARKED parent binary.
# (b) Does `emit_ty` change the quoted components at all? `HEATHER_QUOTE_SPIKE`
#     prints one line per `quote_type_at` call with `changed=` and the two
#     spellings' bounded-Debug lengths; the change itself is applied, so the
#     same binary gives the first count read in (c).
# (c) t_cp1 and t_cp2, parent against changed, counts only (design §8 item 2).
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_cpsp
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

test -x target/heather_parent || { echo "== MISSING target/heather_parent"; echo "== MARKER done"; exit 1; }

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
cp target/release/heather target/heather_q
echo "== built $(date +%T)"

echo "== (a) trace cp_full on the PARENT $(date +%T)"
( ulimit -v 8388608 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CONV_MISS_TRACE=cp_full \
  target/heather_parent check $L --kernel-workers 1 probes/t_cp1.hthr \
  > "$OUT/tr.out" 2> "$OUT/tr.err" )
echo "== rc=$? records=$(grep -c '^conv miss trace cp_full' "$OUT/tr.err") $(date +%T)"
echo "== buckets by (expected len, inferred len, first difference at)"
grep '^expected len=' "$OUT/tr.err" | sort | uniq -c | sort -rn | head -12
echo "== head pair x bucket"
awk '/^conv miss trace cp_full /{hp=$5; next}
     /^expected len=/{c[hp" | "$0]++} END{for (k in c) printf "  %7d  %s\n", c[k], k}' "$OUT/tr.err" \
  | sort -rn | head -14
echo "== site x head pair"
awk '/^conv miss trace cp_full /{hp=$5; next}
     /^site: /{c[hp" | "$0]++} END{for (k in c) printf "  %7d  %s\n", c[k], k}' "$OUT/tr.err" \
  | sort -rn | head -14 | cut -c1-260
echo "== the 732-char family: full expected/inferred excerpt lines, most common"
grep -E '^(expected|inferred): ' "$OUT/tr.err" | sort | uniq -c | sort -rn | head -8 | cut -c1-900

echo "== (b) the spike listing on t_cp1 $(date +%T)"
( ulimit -v 8388608 -t 1800; HEATHER_QUOTE_SPIKE=1 \
  target/heather_q check $L --kernel-workers 1 probes/t_cp1.hthr \
  > "$OUT/sp.out" 2> "$OUT/sp.err" )
echo "== rc=$? $(date +%T)"
echo "== quote_type_at calls: $(grep -c '^quote-spike' "$OUT/sp.err")"
grep '^quote-spike' "$OUT/sp.err" | awk '{print $3}' | sort | uniq -c
echo "== changed=true calls by (before_len, after_len)"
grep '^quote-spike' "$OUT/sp.err" | grep 'changed=true' | awk '{print $4, $5}' | sort | uniq -c | sort -rn | head -20
echo "== changed=false calls by before_len"
grep '^quote-spike' "$OUT/sp.err" | grep 'changed=false' | awk '{print $4}' | sort | uniq -c | sort -rn | head -10
echo "== the five largest before/after pairs, with both spellings"
grep -A 2 '^quote-spike.*changed=true' "$OUT/sp.err" | head -60 | cut -c1-700

echo "== (c) counts, both binaries $(date +%T)"
for who in parent q; do
  BIN=target/heather_$who
  for f in t_cp1 t_cp2; do
    ( ulimit -v 8388608 -t 1800; /usr/bin/time -f "== time $who $f %es wall %MKB maxrss" \
      $BIN check $L --kernel-workers 1 --timings "$OUT/${who}_$f.tsv" probes/$f.hthr \
      > "$OUT/${who}_$f.out" 2>&1 )
    echo "== rc=$? $who $f $(date +%T)"; tail -2 "$OUT/${who}_$f.out"
    awk -F'\t' -v w="$who" -v f="$f" '$1=="item"{printf "  %-8s %-10s %-24s total %9.1f ms gate %9.1f ms misses %8d shortcut %10d steps %10d\n",w,f,$3,$4/1e6,$8/1e6,$43,$41,$46}' "$OUT/${who}_$f.tsv"
  done
done
echo "== MARKER done $(date +%T)"
