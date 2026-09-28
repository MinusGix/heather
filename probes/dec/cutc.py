import re,sys
L=int(sys.argv[1])
src=open('target/probe-dec/cert.hthr').read().split('\n')
Q=('probe_native_'+'prefix_'*L).rstrip('_')
P=Q+'_prefix'
link=[k for k,l in enumerate(src) if l.startswith('theorem '+Q+'_link(')][0]
end=link
while src[end]!='}': end+=1
# carried port id of P's carry: find `_source(values)` inside the carry body -> preceding leb key
carry=[k for k,l in enumerate(src) if l.startswith('fn '+P+'_carry(')][0]
body=src[carry+2]
i=body.index(P+'_source(values)')
key=re.findall(r'Nat::leb\((\d+), id\)', body[:i])[-1]
tests=f'''
theorem t_carry(values: Valuation()): {P}_carry(values)(64, {key}) = {P}_source(values) {{ refl }}
theorem t_cv(values: Valuation()): {P}_result(values) = {P}_continuation_value({P}_carry(values), 64) {{ refl }}
theorem t_abs(values: Valuation()): {P}_continuation_value(values, 64) = format::place(values(64, {key}), @bitvec::BitVec::ofNat(64, 1), @bitvec::BitVec::ofNat(64, 1)) {{ refl }}
'''
open(sys.argv[2],'w').write('\n'.join(src[:end+1])+tests)
print(key)
