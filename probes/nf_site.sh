# Round "emit the application, not its normal form" (2026-09-16), job 2:
# design §8 item 2 — NAME the normalization site and the emitter.
#
# `HEATHER_NF_SPIKE=<µs>` (this round's temporary instrument, value-metrics
# only) prints every head-shape probe (`Elaborator::whnf`, `whnf_tm`) and every
# emission-chokepoint call (`emit_ty`) that cost more than the budget, with the
# input's bounded spelling and the elaborator frames that asked for it. The
# exponential normal forms are milliseconds each; ordinary probes are ~1 µs.
set -u
cd "$(dirname "$0")/.."
OUT=probes/out_nf2
rm -rf "$OUT"; mkdir -p "$OUT"
L="-L lib/std -L lib/std/parser"

echo "== build $(date +%T)"
cargo build --release -p heather-cli --features value-metrics 2>&1 | tail -3
cp target/release/heather target/heather_spike

spike () { # $1 stem, $2 budget µs
  f=$1; b=$2
  echo "== $f spike budget=${b}us $(date +%T)"
  ( ulimit -v 16777216 -t 3600; HEATHER_NF_SPIKE=$b \
    target/heather_spike check $L --kernel-workers 1 probes/$f.hthr \
    > "$OUT/$f.out" 2> "$OUT/$f.err" )
  echo "== rc=$? $(date +%T) records=$(grep -ac '^nf spike' "$OUT/$f.err")"
  echo "== by (what, site), count and total ms"
  awk '/^nf spike /{us=$3; sub("us","",us);
        i=index($0," site: "); s=substr($0,i+7);
        k=$3=="" ? "?" : $2" | "s; c[k]++; t[k]+=us+0}
       END{for (x in c) printf "  %6d  %10.1f ms  %s\n", c[x], t[x]/1000, x}' "$OUT/$f.err" \
    | sort -k2 -rn | head -14 | cut -c1-520
  echo "== the five costliest single records, input spelling cut to 700"
  grep -a '^nf spike ' "$OUT/$f.err" | sort -t' ' -k3 -rn | head -5 | cut -c1-700
}

spike t_qt2 2000
spike t_cp9 2000

echo "== MARKER done $(date +%T)"
