#!/usr/bin/env python3
"""Aggregate a heather --timings TSV into family rows.

Usage: python3 probes/agg.py <timings.tsv>
Prints the run row, the module rows, and item rows grouped by family
(the item name up to the first digit-run), with seconds, kernel seconds,
conversion misses and evaluator steps.
"""
import sys, re, collections

path = sys.argv[1]
rows = [l.rstrip("\n").split("\t") for l in open(path)]
head = rows[0]
ix = {n: i for i, n in enumerate(head)}


def num(r, n):
    try:
        return int(r[ix[n]] or 0)
    except (IndexError, ValueError):
        return 0


def family(name):
    n = re.sub(r"[_0-9]+$", "", name)
    n = re.sub(r"_\d+(_\d+)*", "", n)
    return n


fams = collections.defaultdict(lambda: [0, 0, 0, 0, 0, 0])
run = None
for r in rows[1:]:
    if not r or r[0] == "scope":
        continue
    if r[0] == "run":
        run = r
        continue
    if r[0] != "item":
        continue
    f = family(r[ix["item"]])
    a = fams[f]
    a[0] += 1
    a[1] += num(r, "total_ns")
    a[2] += num(r, "kernel_gate_ns")
    a[3] += num(r, "conv_misses")
    a[4] += num(r, "eval_steps")
    a[5] += num(r, "conv_shortcut_hits")

print("family\titems\ttotal_s\tkernel_s\tmisses\tsteps\tshortcut")
for f, a in sorted(fams.items(), key=lambda kv: -kv[1][2])[:40]:
    print("%s\t%d\t%.3f\t%.3f\t%d\t%d\t%d" % (f, a[0], a[1] / 1e9, a[2] / 1e9, a[3], a[4], a[5]))

if run:
    print("\nrun\ttotal_s\tkernel_s\tmisses\tsteps\tshortcut\tdelta")
    print("run\t%.3f\t%.3f\t%d\t%d\t%d\t%d" % (
        num(run, "total_ns") / 1e9, num(run, "kernel_gate_ns") / 1e9,
        num(run, "conv_misses"), num(run, "eval_steps"),
        num(run, "conv_shortcut_hits"), num(run, "eval_delta_steps")))

tot = [0, 0, 0, 0]
for r in rows[1:]:
    if r and r[0] == "item":
        tot[0] += 1
        tot[1] += num(r, "total_ns")
        tot[2] += num(r, "kernel_gate_ns")
        tot[3] += num(r, "eval_steps")
print("\nitems\t%d\ttotal_s\t%.3f\tkernel_s\t%.3f\tsteps\t%d" % (
    tot[0], tot[1] / 1e9, tot[2] / 1e9, tot[3]))
