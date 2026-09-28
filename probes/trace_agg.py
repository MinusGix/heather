import sys, collections, re
path = sys.argv[1]
groups = collections.defaultdict(lambda: [0, 0.0])
heads = collections.defaultdict(lambda: [0, 0.0])
cur = None; body = []
def flush():
    if cur is None: return
    key = (cur[0], " ".join(body)[:260])
    g = groups[key]; g[0] += 1; g[1] += cur[1]
    h = heads[cur[0]]; h[0] += 1; h[1] += cur[1]
for line in open(path, errors="replace"):
    m = re.match(r"conv miss trace (\S+) (\S+) ([0-9.]+)ms", line)
    if m:
        flush(); cur = (m.group(2), float(m.group(3))); body = []
    elif cur is not None and not line.startswith(("ValueMetrics", "==", "error")):
        body.append(line.rstrip())
flush()
print("### by head pair: count ms")
for k, v in sorted(heads.items(), key=lambda kv: -kv[1][1])[:12]:
    print("%6d %9.1f  %s" % (v[0], v[1], k))
print("### top groups: count ms | head | site+excerpt")
for (h, b), v in sorted(groups.items(), key=lambda kv: -kv[1][1])[:45]:
    print("%6d %9.1f | %s | %s" % (v[0], v[1], h, b))
