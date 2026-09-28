import sys
# A place chain of depth d over one word, as decimal_line spells it.
d = int(sys.argv[1])
expr = "n.add(BitVec::ofNat(1))"
for i in range(d):
    expr = f"place({expr}, BitVec::ofNat({1000 + i}), BitVec::ofNat({i + 1}))"
print("""import bitvec;
import bool;
fn place(state, threshold, weight: BitVec(64)) → BitVec(64) {
    match state.unsigned_lt_bit(threshold) {
        True => state,
        False => state.sub(threshold).add(weight),
    }
}
fn chain(n, unused: BitVec(64)) → BitVec(64) {
    %s
}""" % expr)
