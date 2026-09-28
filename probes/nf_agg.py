# Aggregate `HEATHER_NF_SPIKE` records (round "emit the application, not its
# normal form", 2026-09-16). One record per line:
#   nf spike <what> <us>us in=<bounded spelling> out_len=<n> site: <frames>
import sys, re, collections

path, floor_us = sys.argv[1], int(sys.argv[2])
only = sys.argv[3] if len(sys.argv) > 3 else ""
rec = re.compile(r"^nf spike (\S+) (\d+)us item=(\S*) in_len=(\d+) out_len=(\d+) in=(.*) site: (.*)$")
rows = []
for line in open(path, errors="replace"):
    m = rec.match(line.rstrip("\n"))
    if m:
        rows.append((m.group(1), int(m.group(2)), m.group(3), m.group(6), (int(m.group(4)), int(m.group(5))), m.group(7)))

def short(site):
    s = site.replace("<heather_elab::Elaborator>::", "").replace("heather_elab::", "")
    s = re.sub(r"::<[^>]*>", "", s)
    s = re.sub(r"\d+: ", "", s)
    return s

print("  records=%d  over %dus=%d" % (len(rows), floor_us,
                                      sum(1 for r in rows if r[1] >= floor_us)))
by = collections.defaultdict(lambda: [0, 0, 0])
for what, us, item, _inp, olen, site in rows:
    if us < floor_us or (only and only not in item):
        continue
    k = (what, item, short(site))
    by[k][0] += 1
    by[k][1] += us
    by[k][2] = max(by[k][2], us)
print("  == by (what, site): count, total ms, worst ms")
for (what, item, site), (c, t, w) in sorted(by.items(), key=lambda kv: -kv[1][1])[:14]:
    print("   %6d  %9.1f ms  %8.1f ms  %-8s %-28s %s" % (c, t / 1000, w / 1000, what, item[-28:], site[:300]))
print("  == the ten costliest records: what, ms, out_len, site, input head")
for what, us, item, inp, olen, site in sorted([r for r in rows if not only or only in r[2]], key=lambda r: -r[1])[:6]:
    print("   %-8s %8.1f ms in_len=%-7d out_len=%-7d %s | %s" % (what, us / 1000, olen[0], olen[1], item, short(site)[:240]))
    print("        in= " + inp[:1800])
