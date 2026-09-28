# Aggregate `HEATHER_CONV_QUERY_TRACE` lines (the query-traversal round,
# 2026-09-16, docs/conversion-query-traversal-design.md).
#
#   conv query trace <item> <head>/<head> size=<n> site: <f0> < <f1> < ...
#
# `f0` is innermost. Every count printed is multiplied back by the stride, so
# the tables are in units of conversion QUERIES, which is what the round's
# subtraction table is in.
#
#   python3 probes/qt_agg.py <file> <stride> [label]
import sys, collections, re

path = sys.argv[1]
stride = int(sys.argv[2])
label = sys.argv[3] if len(sys.argv) > 3 else path

LINE = re.compile(r"^conv query trace (\S+) (\S+) size=(\d+) at=(\S+) site: (.*)$")

# The rule frame a query sits in: the innermost stack entry that names one of
# the kernel's own rule families. A code's formation walk (`Tm…`), an
# application's annotation checks, an eliminator's motive/branches, a binder.
CODE = {"TmSigma", "TmId", "TmWf", "TmSEq", "TmSum", "TmW", "TmPi", "TmVec",
        "TmFin", "TmSquash", "TmNat", "TmTy", "TmUnit", "TmEmpty", "TmSEmpty"}
ELIM = {"ElimNat", "ElimW", "ElimWf", "ElimSum", "ElimEmpty", "ElimSEmpty",
        "ElimSquash", "ElimId", "ElimSEq", "ElimVec", "ElimFin", "ElimCodeTy",
        "ElimCodeTm", "Case"}


def frame_class(frames):
    for f in frames:
        if f in CODE:
            return "code formation (%s)" % f
        if f in ELIM:
            return "eliminator (%s)" % f
        if f == "App":
            return "App annotation"
        if f in ("Lam", "ULam", "CtxLam", "TyLam"):
            return "binder (%s)" % f
        if f in ("BoxTy", "BoxTm"):
            return "quote (%s)" % f
    return "other (%s)" % (frames[0] if frames else "-")


rows = []
for line in open(path, errors="replace"):
    m = LINE.match(line)
    if m:
        rows.append((m.group(2), int(m.group(3)), m.group(5).split(" < "), m.group(4)))

if not rows:
    print("%s: NO QUERY TRACE LINES" % label)
    sys.exit(0)

total = len(rows) * stride
print("== %s: %d samples x %d = %d queries (compare conv_shortcut_hits)"
      % (label, len(rows), stride, total))


def table(title, key, top=14, of=None):
    c = collections.Counter()
    for r in rows:
        c[key(r)] += stride
    print("-- %s" % title)
    denom = of or total
    for k, v in c.most_common(top):
        print("  %10d  %5.1f%%  %s" % (v, 100.0 * v / denom, str(k)[:220]))
    if len(c) > top:
        print("  ... %d more keys, %d queries" % (len(c) - top, sum(c.values()) - sum(v for _, v in c.most_common(top))))


table("by head pair", lambda r: r[0])
table("by rule frame", lambda r: frame_class(r[2]))
for k in (1, 2, 3, 4):
    table("by innermost %d frame(s)" % k, lambda r, k=k: " < ".join(r[2][:k]))
table("by full site (up to 40 frames)", lambda r: " < ".join(r[2]), top=20)


# The same sites with runs collapsed (`App < App < App` ⇒ `App×3`). This is
# the shape table: an application spine inside a Σ-tuple inside a projection
# chain reads as `App×22 < Pair×12 < Snd×2 < Fst×2 < App×5`, which the
# uncollapsed table cannot show at any width.
def collapse(frames):
    out = []
    for f in frames:
        if out and out[-1][0] == f:
            out[-1][1] += 1
        else:
            out.append([f, 1])
    return " < ".join(f if n == 1 else "%s×%d" % (f, n) for f, n in out)


table("by site SHAPE (runs collapsed)", lambda r: collapse(r[2]), top=18)


def bucket(n):
    for hi in (8, 16, 32, 64, 128, 256, 512, 1024, 2048):
        if n < hi:
            return "<%d" % hi
    return ">=2048 (Debug budget saturates near here)"


table("by bounded size of the type compared", lambda r: bucket(r[1]))
sizes = sorted(r[1] for r in rows)
print("-- size: min %d  p50 %d  p90 %d  max %d  mean %.1f"
      % (sizes[0], sizes[len(sizes) // 2], sizes[int(len(sizes) * 0.9)], sizes[-1],
         sum(sizes) / len(sizes)))

# The stack DEPTH histogram: if a component's code is re-walked once per node
# of something, the depth is where that shows.
table("by stack depth (frames on the checker's stack, capped at 40)",
      lambda r: "%02d" % len(r[2]))

# The longest run of `App` frames enclosing the query — the application
# spine the kernel is inside. The `App` rule's `cod` annotation carries the
# whole remaining telescope, so a spine of length n writes its tail n times.
def app_run(frames):
    n = 0
    for f in frames:
        if f == "App":
            n += 1
        elif n:
            break
    return n


table("by enclosing App-spine length (innermost run)",
      lambda r: "%02d" % app_run(r[2]))

# Identity of the compared type. Many queries at ONE address = a shared
# annotation the kernel re-walks; one query per address = a term the
# elaborator wrote out per occurrence.
addrs = collections.Counter(r[3] for r in rows)
stack_like = [a for a in addrs if a.startswith("0x7f") and len(a) >= 14]
print("-- addresses: %d distinct over %d samples (%.2f samples per address)"
      % (len(addrs), len(rows), len(rows) / len(addrs)))
print("   heap-like %d distinct / %d samples; stack-like %d distinct / %d samples"
      % (len(addrs) - len(stack_like), len(rows) - sum(addrs[a] for a in stack_like),
         len(stack_like), sum(addrs[a] for a in stack_like)))
print("-- top addresses (samples x stride = queries charged to ONE type object)")
for a, c in addrs.most_common(10):
    ex = next(r for r in rows if r[3] == a)
    print("  %10d  %s  %s size=%d  %s" % (c * stride, a, ex[0], ex[1],
                                          " < ".join(ex[2][:6])))
