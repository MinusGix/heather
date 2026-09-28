import re, subprocess, sys, collections
files = subprocess.check_output(['git','diff','--name-only','f9fe5ad^','HEAD','--','lib','crates/elab/src/prelude.hthr'],text=True).split()
decl = re.compile(r'^\s*(?:pub\s+)?(fn|theorem|axiom|inductive|record|class|def|opaque)\s+([A-Za-z_][\w:]*)', re.M)
def names(src): return [m.group(2) for m in decl.finditer(src)]
for f in files:
    old = subprocess.check_output(['git','show','f9fe5ad^:'+f],text=True)
    new = subprocess.check_output(['git','show','HEAD:'+f],text=True)
    o, n = names(old), names(new)
    so, sn = set(o), set(n)
    gone = [x for x in o if x not in sn]
    added = [x for x in n if x not in so]
    mod = f.split('/')[-1].replace('.hthr','')
    for g in gone:
        cands = [a for a in added if a.split('::')[-1] == g.split('::')[-1]]
        print(f"{mod}\t{g}\t{','.join(cands) if cands else '??'}")
    for a in added:
        if not any(a.split('::')[-1]==g.split('::')[-1] for g in gone):
            print(f"{mod}\t+\t{a}")
