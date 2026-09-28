import re,sys
L=int(sys.argv[1])
src=open('target/probe-dec/cert.hthr').read().split('\n')
Q=('probe_native_'+'prefix_'*L).rstrip('_')
Q13=Q+'_prefix'
link=[k for k,l in enumerate(src) if l.startswith('theorem '+Q+'_link(')][0]
end=link
while src[end]!='}': end+=1
carry=[k for k,l in enumerate(src) if l.startswith('fn '+Q13+'_carry(')][0]
m=re.findall(r'match (id(?:_\d+)?) \{ Zero => (match width as|values\(width, \d+\)|@bitvec::BitVec::zero\(width\))', src[carry+2])
cid=[i for i,(a,b) in enumerate(m) if b.startswith('match width')][0]
tests=f'''
theorem t_carry(values: Valuation()): {Q13}_carry(values)(64, {cid}) = {Q13}_source(values) {{ refl }}
theorem t_src(values: Valuation()): {Q13}_source(values) = {Q13}_source(values) {{ refl }}
'''
open(sys.argv[2],'w').write('\n'.join(src[:end+1])+tests)
