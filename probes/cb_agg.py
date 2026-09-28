# Aggregate the `HEATHER_CB` listing (the close_body-family attribution round,
# 2026-09-16).
#
#   cb decl item=<name> stmt_nodes=<n> term_nodes=<n> total_nodes=<n>
#   cb read item=<name> decl=<D> idx=<j> route=ref|walk args=<n> tm_nodes=<n> ty_nodes=<n>
#
# One table per item of interest: the emitted pair's node count beside the
# item's conversion queries (the gate is a flat cost per node on this family,
# so the two are read against each other), and the field reads that built it,
# grouped by declaration and route, with count x mean size = the block.
#
#   python3 probes/cb_agg.py <stderr> <timings.tsv> [item-prefix]
import sys, collections, re

err, tsv = sys.argv[1], sys.argv[2]
prefix = sys.argv[3] if len(sys.argv) > 3 else ""

DECL = re.compile(r"^cb decl item=(\S+) stmt_nodes=(\d+) term_nodes=(\d+) total_nodes=(\d+)$")
READ = re.compile(r"^cb read item=(\S+) decl=(\S+) idx=(\d+) route=(\S+) args=(\d+) "
                  r"tm_nodes=(\d+) ty_nodes=(\d+)$")

WANT = ("close_body", "expr_body", "factor_body", "number_grammar", "Grammar",
        "Certified", "complete_post", "checked_expr", "open_body", "atom_body",
        "sum_finish", "product_finish", "certify_at", "symbol_span")

decls, reads = {}, collections.defaultdict(list)
for line in open(err, errors="replace"):
    m = DECL.match(line.rstrip("\n"))
    if m:
        decls[m.group(1)] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
        continue
    m = READ.match(line.rstrip("\n"))
    if m:
        reads[m.group(1)].append((m.group(2), int(m.group(3)), m.group(4),
                                  int(m.group(5)), int(m.group(6)), int(m.group(7))))

# The item table from the timings, so nodes and queries sit in one row.
q = {}
for line in open(tsv, errors="replace"):
    f = line.rstrip("\n").split("\t")
    if len(f) > 46 and f[0] == "item":
        q[f[2]] = (float(f[3]) / 1e6, int(f[42]), int(f[40]), int(f[45]))

# `all` takes every declaration of the file (the probes, whose item names are
# their own); a prefix takes what starts with it; no argument takes the
# showcase's family rows.
items = [i for i in decls
         if prefix == "all" or (i.startswith(prefix) if prefix else i in WANT)]
items.sort(key=lambda i: -decls[i][2])
print("== nodes emitted vs queries (%s)" % err)
print("  %-18s %10s %10s %11s %11s %8s %9s" %
      ("item", "stmt", "term", "TOTAL nodes", "queries", "q/node", "reads"))
for i in items:
    s, t, tot = decls[i]
    ms, misses, queries, steps = q.get(i, (0, 0, 0, 0))
    print("  %-18s %10d %10d %11d %11d %8.2f %9d" %
          (i, s, t, tot, queries, (queries / tot) if tot else 0, len(reads.get(i, []))))

print("== field reads, by item and declaration (count x mean spine nodes)")
for i in items:
    rs = reads.get(i, [])
    if not rs:
        continue
    by = collections.defaultdict(list)
    for decl, idx, route, args, tm, ty in rs:
        by[(decl, route)].append(tm + ty)
    rows = sorted(by.items(), key=lambda kv: -sum(kv[1]))
    print("  -- %s: %d reads, %d nodes in them" %
          (i, len(rs), sum(sum(v) for v in by.values())))
    for (decl, route), v in rows[:8]:
        print("     %-22s %-5s %6d reads x %9.1f mean = %10d  (max %d)" %
              (decl, route, len(v), sum(v) / len(v), sum(v), max(v)))
