import re, sys, glob, collections, os
SP = os.path.dirname(os.path.abspath(__file__))
MAP = collections.defaultdict(dict)
for fn in ('map.tsv', 'extra.tsv'):
    for line in open(f'{SP}/{fn}'):
        mod, old, new = line.rstrip('\n').split('\t')
        if old == '+' or new == '??' or ',' in new: continue
        MAP[mod][old] = new
write = '--write' in sys.argv
pat = re.compile(r'\b(' + '|'.join(MAP) + r')::([A-Za-z_]\w*)\b(?!::)')
hits = collections.Counter()
for f in sorted(glob.glob('crates/**/*.rs', recursive=True)):
    src = open(f).read()
    def sub(m):
        new = MAP[m.group(1)].get(m.group(2))
        if not new: return m.group(0)
        hits[(f, m.group(0), f'{m.group(1)}::{new}')] += 1
        return f'{m.group(1)}::{new}'
    out = pat.sub(sub, src)
    if write and out != src: open(f, 'w').write(out)
for (f, a, b), n in sorted(hits.items()): print(f'{n}\t{f}\t{a} -> {b}')
