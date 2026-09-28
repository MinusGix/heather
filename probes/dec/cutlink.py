import re,sys
L=int(sys.argv[1]); out=sys.argv[2]
src=open('target/probe-dec/cert.hthr').read().split('\n')
Q=('probe_native_'+'prefix_'*L).rstrip('_')
link=[k for k,l in enumerate(src) if l.startswith('theorem '+Q+'_link(')][0]
end=link
while src[end]!='}': end+=1
rhs=src[link+1].split(' = ',1)[1]
inner=rhs[len('format::place('):]
depth=0
for j,ch in enumerate(inner):
    if ch=='(': depth+=1
    elif ch==')': depth-=1
    elif ch==',' and depth==0: break
sv2=inner[:j]
carry=[k for k,l in enumerate(src) if l.startswith('fn '+Q+'_prefix_carry(')][0]
m=re.findall(r'match (id(?:_\d+)?) \{ Zero => (match width as|values\(width, \d+\)|@bitvec::BitVec::zero\(width\))', src[carry+2])
cid=[i for i,(a,b) in enumerate(m) if b.startswith('match width')][0]
lines=src[:end+1]
tests=f'''
theorem t_carry(values: Valuation()): {Q}_prefix_carry(values)(64, {cid}) = {sv2} {{ refl }}
theorem t_link2(values: Valuation()): {Q}_prefix_continuation_value({Q}_prefix_carry(values), 64) = {rhs} {{ refl }}
theorem t_syn(values: Valuation()): {rhs} = {rhs} {{ refl }}
'''
open(out,'w').write('\n'.join(lines)+tests)
