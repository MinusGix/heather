# Build write-elf's size probes (the `cat_x` sources of lib/_tests/native/native_compile_tests.hthr,
# issues/native-compile-capacity.md) one at a
# time at kernel width one, each over a fresh copy of a warmed cache so the
# verdict store does not hide the certificate's gate. Usage:
#   perf/fixtures/native_sizes/run.sh [out-dir] [symbols...]
# Leaves <sym>.tsv (read with scripts/timings) and <sym>.log in out-dir.
set -u
root="$(cd "$(dirname "$0")/../../.." && pwd)"
out="${1:-$root/target/native-sizes}"; shift || true
syms="${*:-cat_x2 cat_x4 cat_x8}"
src="$root/lib/_tests/native/native_compile_tests.hthr"
mkdir -p "$out"
cd "$root"
cargo build --release -q -p heather-cli || exit 1
# Warm the library's images once; each probe then starts from a copy.
( ulimit -v 8388608 -t 3000 -c 0; target/release/heather check "$src" --cache --cache-dir "$out/warm" ) > "$out/warm.log" 2>&1
for sym in $syms; do
  rm -rf "$out/c-$sym"; cp -r "$out/warm" "$out/c-$sym"
  start=$(date +%s)
  ( ulimit -v "${VMEM:-8388608}" -t 7000 -c 0; HEATHER_KERNEL_WORKERS=1 target/release/heather write-elf "$src" "$sym" \
      -o "$out/$sym" --cache-dir "$out/c-$sym" --timings "$out/$sym.tsv" ) > "$out/$sym.log" 2>&1
  echo "$sym: $(( $(date +%s) - start ))s $(grep -E 'bytes,|rror' "$out/$sym.log" | head -1)"
  rm -rf "$out/c-$sym"
done
