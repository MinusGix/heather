import sys
K=int(sys.argv[1]); mode=sys.argv[2]
W="Valuation()"
out=["import function_ir;","import bitvec;","import bool;","import nat;","import list;","import logic;",
f"fn V0(values: {W}, width: Nat) → BitVec(width) {{ values(width, 0) }}"]
def fn(name, body): out.append(f"fn {name}(values: {W}, width: Nat) → BitVec(width) {{ {body} }}")
for k in range(1,K+1):
    p=f"V{k-1}(values, width)"
    C=k*7+1
    fn(f"a{k}", "@bitvec::BitVec::ofNat(width, 65535)")
    fn(f"b{k}", f"@bitvec::BitVec::band(width, {p}, a{k}(values, width))")
    fn(f"c{k}", f"@bitvec::BitVec::ofNat(width, {C})")
    fn(f"d{k}", f"match width as λ n => BitVec(n) {{ Zero => @bitvec::BitVec::zero(0), Succ(k) => @bitvec::BitVec::cons_bit(k, @bitvec::BitVec::unsigned_lt_bit(64, b{k}(values, 64), c{k}(values, 64)), @bitvec::BitVec::zero(k)) }}")
    fn(f"t{k}", f"@bitvec::BitVec::bor(width, @bitvec::BitVec::ofNat(width, 0), {p})")
    fn(f"s{k}", f"@bitvec::BitVec::sub(width, {p}, @bitvec::BitVec::ofNat(width, {C}))")
    fn(f"f{k}", f"@bitvec::BitVec::add(width, s{k}(values, width), @bitvec::BitVec::ofNat(width, {k*1000}))")
    fn(f"V{k}", f"match @bitvec::BitVec::head_bit(0, d{k}(values, 1)) {{ False => f{k}(values, width), True => t{k}(values, width) }}")
k=K+1
p=f"V{K}(values, width)"
fn(f"a{k}", "@bitvec::BitVec::ofNat(width, 65535)")
fn(f"b{k}", f"@bitvec::BitVec::band(width, {p}, a{k}(values, width))")
fn(f"c{k}", f"@bitvec::BitVec::ofNat(width, 400)")
fn(f"d{k}", f"match width as λ n => BitVec(n) {{ Zero => @bitvec::BitVec::zero(0), Succ(k) => @bitvec::BitVec::cons_bit(k, @bitvec::BitVec::unsigned_lt_bit(64, b{k}(values, 64), c{k}(values, 64)), @bitvec::BitVec::zero(k)) }}")
vals={0:"values(width, 0)",5:p,6:f"a{k}(values, width)",7:f"b{k}(values, width)",8:f"c{k}(values, width)",9:f"d{k}(values, width)"}
cases="@bitvec::BitVec::zero(width)"
for i in range(9,-1,-1):
    nm="id" if i==0 else f"id_{i}"
    v=vals.get(i,"@bitvec::BitVec::zero(width)")
    cases=f"match {nm} {{ Zero => {v}, Succ(id_{i+1}) => {cases} }}"
out.append(f"fn valuation(values: {W}) → {W} {{ λ width id => {cases} }}")
out.append("fn raw() → Region { Region(inputs := Ports([Port(id := 0, width := 64), Port(id := 5, width := 64)]), nodes := [Const(width := 64, output := 6, value := 65535), BitAnd(width := 64, output := 7, left := 5, right := 6), Const(width := 64, output := 8, value := 400), UnsignedLessThan(width := 64, output := 9, left := 7, right := 8)], outputs := Ports([Port(id := 9, width := 1)])) }")
if mode=="graph": out.append("theorem graph(values: Valuation()): RegionHolds(raw(), valuation(values)) { ⟨refl, ⟨refl, ⟨refl, ⟨refl, trivial⟩⟩⟩⟩ }")
if mode=="and": out.append(f"theorem n2(values: Valuation()): valuation(values)(64, 7) = @bitvec::BitVec::band(64, valuation(values)(64, 5), valuation(values)(64, 6)) {{ refl }}")
if mode=="lt": out.append(f"theorem n4(values: Valuation()): valuation(values)(1, 9) = bitvec::BitVec::ofBool(@bitvec::BitVec::unsigned_lt_bit(64, valuation(values)(64, 7), valuation(values)(64, 8))) {{ refl }}")
print("\n".join(out))
