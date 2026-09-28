# Pair pass: a method site (2) whose receiver site is @ (0) -> outer qualified (1),
# receiver bare (1). `try` sets every candidate pair and records them;
# `revert OUTPUTS..` restores pairs an error lands in (by span).
import sys, json, os
SP = os.path.dirname(os.path.abspath(__file__))
L = os.path.join(SP, 'levels.json'); P = os.path.join(SP, 'pairs.json')
levels = json.load(open(L)); recv = json.load(open(os.path.join(SP, 'recvs.json')))
if sys.argv[1] == 'try':
    pairs = [(o, r) for o, r in recv.items() if levels.get(o) == 2 and levels.get(r) == 0]
    for o, r in pairs: levels[o] = 1; levels[r] = 1
    json.dump(pairs, open(P, 'w')); json.dump(levels, open(L, 'w'), indent=0, sort_keys=True)
    print(len(pairs), 'pairs tried')
else:
    import re
    spans = json.load(open(os.path.join(SP, 'spans.json'))); pairs = json.load(open(P))
    ROOT = '/home/minus/Kairos/Code/heather'
    pm = dict(l.split() for l in open(os.path.join(SP, 'dx/pathmap')))
    hits = []
    for o in sys.argv[2:]:
        for m in re.finditer(r'^error[^\n]*\n(?:(?!^error).*\n)*?\s*--> ([^:\n]+):(\d+):(\d+)', open(o).read(), re.M):
            p = m.group(1).replace(ROOT + '/', ''); p = pm.get(p, p); hits.append((p, int(m.group(2))))
    keep = []; n = 0
    for o, r in pairs:
        l1, _, l2, _ = spans[o]; p = o.split('#')[0]
        # generous: any error on the pair's lines, or in the decl below (one error per decl)
        if any(hp == p and l1 - 1 <= hl <= l2 + 1 for hp, hl in hits):
            levels[o] = 2; levels[r] = 0; n += 1
        else: keep.append((o, r))
    json.dump(keep, open(P, 'w')); json.dump(levels, open(L, 'w'), indent=0, sort_keys=True)
    print(n, 'pairs reverted;', len(keep), 'kept')
