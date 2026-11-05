import os,re,sys
mods={}
for root,_,fs in os.walk('lib'):
    if '_tests' in root: continue
    for f in fs:
        if f.endswith('.hthr'):
            p=os.path.join(root,f); src=open(p).read()
            mods[f[:-5]]=(p,re.findall(r'\bimport\s+([A-Za-z_0-9]+)\s*;',src))
memo={}
def clo(m):
    if m in memo: return memo[m]
    memo[m]=set()
    s=set()
    for d in mods.get(m,(None,[]))[1]:
        s.add(d); s|=clo(d)
    memo[m]=s; return s
for m in sys.argv[1:]:
    c=clo(m)
    print(m, 'tactic' in c, 'derive' in c, 'egraph' in c, 'grind' in c, len(c))
