import sys
K=int(sys.argv[1]); variant=sys.argv[2] if len(sys.argv)>2 else "graph"
out=["import function_ir;","import bitvec;","import bool;","import nat;","import list;","import logic;",
"fn v0(values: Valuation(), width: Nat) → BitVec(width) { values(width, 0) }"]
for k in range(1,K+1):
    p=f"v{k-1}(values, width)"
    out+= [f"fn b{k}(values: Valuation(), width: Nat) → BitVec(width) {{ @bitvec::BitVec::band(width, {p}, @bitvec::BitVec::ofNat(width, 65535)) }}",
     f"fn c{k}(values: Valuation(), width: Nat) → BitVec(width) {{ match width as λ n => BitVec(n) {{ Zero => @bitvec::BitVec::zero(0), Succ(k) => @bitvec::BitVec::cons_bit(k, @bitvec::BitVec::unsigned_lt_bit(64, b{k}(values, 64), @bitvec::BitVec::ofNat(64, {k*7})), @bitvec::BitVec::zero(k)) }} }}",
     f"fn s{k}(values: Valuation(), width: Nat) → BitVec(width) {{ @bitvec::BitVec::sub(width, {p}, @bitvec::BitVec::ofNat(width, {k*7})) }}",
     f"fn f{k}(values: Valuation(), width: Nat) → BitVec(width) {{ @bitvec::BitVec::add(width, s{k}(values, width), @bitvec::BitVec::ofNat(width, {k*100})) }}",
     f"fn t{k}(values: Valuation(), width: Nat) → BitVec(width) {{ {p} }}",
     f"fn v{k}(values: Valuation(), width: Nat) → BitVec(width) {{ match @bitvec::BitVec::head_bit(0, c{k}(values, 1)) {{ False => f{k}(values, width), True => t{k}(values, width) }} }}"]
k=K
if variant=="graph":
    out.append(f"theorem g(values: Valuation()): b{k}(values, 64) = @bitvec::BitVec::band(64, v{k-1}(values, 64), @bitvec::BitVec::ofNat(64, 65535)) {{ refl }}")
elif variant=="self":
    out.append(f"theorem g(values: Valuation()): v{k}(values, 64) = v{k}(values, 64) {{ refl }}")
print("\n".join(out))
