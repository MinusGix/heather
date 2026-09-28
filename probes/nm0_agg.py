# Sum the free-variable instrument's `rb fv` lines over a whole run: the
# per-value table, the three threshold columns the implementation is ranked
# against (`T64` both devices, `TM64` terms only, `TC64` both spellings), and
# step 0 item 2's `code_of` coverage of the type half.
import sys, collections

tot = collections.Counter()
cols = collections.defaultdict(lambda: [0, 0])
lost = [0, 0]
reducts = 0
for line in sys.stdin:
    f = dict(p.split("=", 1) for p in line.split() if "=" in p)
    reducts += 1
    for k in ("shared", "thr", "bad", "badc", "unb", "closed", "tynode", "opaque",
              "basevar", "decl", "tycode_no"):
        tot[k] += int(f.get(k, 0))
    for k in ("T64", "TM64", "TC64", "TM0"):
        v = f.get(k)
        if v:
            n, e = v.split("|")[0].split("/")
            cols[k][0] += int(n); cols[k][1] += int(e)
    if "tycode_lost" in f:
        a, b = f["tycode_lost"].split("/")
        lost[0] += int(a); lost[1] += int(b)

print("   reducts=%d " % reducts + " ".join("%s=%d" % (k, tot[k]) for k in
      ("shared", "thr", "bad", "badc", "unb", "closed", "tynode", "opaque",
       "basevar", "decl", "tycode_no")))
for k in ("T64", "TM64", "TC64"):
    print("   %-5s names=%d emitted=%d" % (k, cols[k][0], cols[k][1]))
print("   tycode_lost=%d/%d of the type half's saving" % (lost[0], lost[1]))
