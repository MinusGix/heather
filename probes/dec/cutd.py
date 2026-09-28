import re,sys
L=int(sys.argv[1]); out=sys.argv[2]
src=open('target/probe-dec/lcert.hthr').read().split('\n')
Q=('probe_native_'+'prefix_'*L).rstrip('_')
P=Q+'_prefix'
link=[k for k,l in enumerate(src) if l.startswith('theorem '+Q+'_link(')][0]
end=link
while src[end]!='}': end+=1
carry=[k for k,l in enumerate(src) if l.startswith('fn '+P+'_carry(')][0]
body=src[carry+2]
i=body.index('_source(values)')
key=re.findall(r'Nat::leb\((\d+), id\)', body[:i])[-1]
child=re.findall(r'(probe_native_[a-z_]*_source)\(values\)', body)[0]
tests=f'''
theorem t_delta(values: Valuation()): {Q}_prefix_result(values) = {P}_continuation_value({P}_carry(values), 64) {{ refl }}
theorem t_abs(values: Valuation()): {P}_continuation_value(values, 64) = line::times256(values(64, {key})) {{ refl }}
theorem t_carry(values: Valuation()): {P}_carry(values)(64, {key}) = {child}(values) {{ refl }}
'''
open(out,'w').write('\n'.join(src[:end+1])+tests)
print(key, child[-60:])
