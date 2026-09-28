import sys,re
src=open('target/probe-dec/cert.hthr').read().split('\n')
name=sys.argv[1]; out=sys.argv[2]
start=[i for i,l in enumerate(src) if re.match(r'^theorem '+re.escape(name)+r'\(',l)][0]
end=start
while src[end]!='}': end+=1
lines=src[:end+1]
# drop failing source_expands-style theorems that aren't needed? keep all.
open(out,'w').write('\n'.join(lines)+'\n')
print(start,end)
