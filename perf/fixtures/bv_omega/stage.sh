# Stage bv_omega's perf fixture (issues/bv-omega-check-cost.md) beside the two
# modules it imports under their harness names, which a plain `heather check`
# cannot resolve from lib/std. Prints the staged fixture's path.
root="$(cd "$(dirname "$0")/../../.." && pwd)"
dir="$root/target/bv-fixture"
mkdir -p "$dir"
cp "$root/lib/std/bitvec/nat.hthr" "$dir/bitvec_nat.hthr"
cp "$root/lib/std/bitvec/omega.hthr" "$dir/bitvec_omega.hthr"
cp "$root/perf/fixtures/bv_omega/bv_decimal_line.hthr" "$dir/bv_decimal_line.hthr"
echo "$dir/bv_decimal_line.hthr"
