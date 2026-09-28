# Round "the matcher sees through a quote" (2026-09-16), job 3: the gates
# (`docs/instance-match-quote-arm-design.md` §5 items 3 and 7), detached.
#
#   (a) the route split: `probes/cb_count.patch` re-applied as an instrument,
#       `HEATHER_CB=1` on the showcase and on t_cb1/t_cb3, aggregated by
#       `probes/cb_agg.py`, then reverted. `Certified walk` must be zero.
#   (b) the x86 rails inside the DEFAULT fuel, at two sizes;
#   (c) the full `scripts/test` (not --fast: this is a generator change and
#       the fast lane replays images an earlier build wrote);
#   (d) the `scripts/bench --save` / apply / `--check` dance, since the
#       committed baseline is desktop-recorded.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_iag
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"
F=docs/showcase/calc_parser.hthr

echo "== (a) the route split $(date +%T)"
patch -p1 --batch < probes/cb_count.patch > "$OUT/cbp.log" 2>&1; echo "== cb_count apply rc=$?"
cargo build --release -p heather-cli --features value-metrics 2>&1 | grep -E '^(error|    Finished)' -A 8 | tail -20
( ulimit -v 16777216 -t 3600; HEATHER_VALUE_METRICS=1 HEATHER_CB=1 \
  target/release/heather check $L --kernel-workers 1 --timings "$OUT/cb.tsv" $F \
  > "$OUT/cb.out" 2> "$OUT/cb.err" ); echo "== rc=$? $(date +%T)"
python3 probes/cb_agg.py "$OUT/cb.err" "$OUT/cb.tsv"
for f in t_cb1 t_cb3; do
  ( ulimit -v 8388608 -t 900; HEATHER_VALUE_METRICS=1 HEATHER_CB=1 \
    target/release/heather check $L --kernel-workers 1 --timings "$OUT/$f.tsv" probes/$f.hthr \
    > "$OUT/$f.out" 2> "$OUT/$f.err" )
  echo "-- $f"; python3 probes/cb_agg.py "$OUT/$f.err" "$OUT/$f.tsv" all
done
patch -p1 -R --batch < probes/cb_count.patch > "$OUT/cbr.log" 2>&1; echo "== cb_count revert rc=$?"
git status --short crates/ | head

echo "== (b) the x86 rails, default fuel $(date +%T)"
scripts/test function_ir_x86_scaling > "$OUT/x86.log" 2>&1; echo "== x86 rc=$? $(date +%T)"
grep -a -E '^== suite:|INCOMPLETE|test result:|scaling|fuel|depth' "$OUT/x86.log" | tail -25
scripts/test caller_native_memory_same > "$OUT/native.log" 2>&1; echo "== native rc=$? $(date +%T)"
grep -a -E '^== suite:|INCOMPLETE|test result:|fuel|depth' "$OUT/native.log" | tail -20
echo "-- WALK_RESIDUE / record_projection_size / psi bindings fixtures"
scripts/test --fast record_projection_size > "$OUT/rps.log" 2>&1; echo "== rps rc=$?"
grep -a -E '^== suite:|test result:|assertion|left|right' "$OUT/rps.log" | tail -20

echo "== (c) full scripts/test $(date +%T)"
scripts/test > "$OUT/suite.log" 2>&1; echo "== suite rc=$? $(date +%T)"
grep -a -E '^== suite:|INCOMPLETE' "$OUT/suite.log" | tail -3
grep -a -E '^(test .* FAILED|failures:|---- )' "$OUT/suite.log" | head -40
grep -a -E 'panicked at' "$OUT/suite.log" | head -20

echo "== (d) the bench dance $(date +%T)"
patch -p1 -R --batch < probes/ia.patch > "$OUT/p1.log" 2>&1; echo "== reverse-apply rc=$?"
scripts/bench --save 2>&1 | tail -4
patch -p1 --batch < probes/ia.patch > "$OUT/p2.log" 2>&1; echo "== re-apply rc=$?"
scripts/bench --check 2>&1 | tail -20
echo "== MARKER done $(date +%T)"
