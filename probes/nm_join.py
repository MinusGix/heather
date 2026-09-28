# The per-item join: every declaration of a run, parent against changed, on the
# three columns a spelling change may not move the wrong way.
import sys
from nm_agg import rows, num

a, b = rows(sys.argv[1]), rows(sys.argv[2])
cols = ["conv_misses", "queries", "eval_steps"]
worse, better, moved = [], 0, 0
for item, ra in a.items():
    rb = b.get(item)
    if rb is None:
        print("   MISSING in changed: %s" % item)
        continue
    d = [(c, num(ra, c), num(rb, c)) for c in cols]
    if any(y > x for _, x, y in d):
        worse.append((item, d))
    if any(y < x for _, x, y in d):
        better += 1
    if any(y != x for _, x, y in d):
        moved += 1
print("   rows=%d moved=%d improved=%d regressed=%d" % (len(a), moved, better, len(worse)))
for item, d in sorted(worse, key=lambda r: -max(y - x for _, x, y in r[1]))[:25]:
    print("     %-40s " % item + "  ".join("%s %d->%d" % (c, x, y) for c, x, y in d))
for c in cols:
    print("   total %-12s %d -> %d" % (c, sum(num(r, c) for r in a.values()),
                                       sum(num(r, c) for r in b.values())))
