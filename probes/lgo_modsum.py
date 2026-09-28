import csv, sys, collections
f=sys.argv[1]
cols=["total_ns","kernel_gate_ns","shift_global_nodes","delta_body_rescopes","global_ref_rescopes","eval_steps","conv_misses"]
agg=collections.defaultdict(lambda: collections.Counter())
with open(f) as fh:
    for r in csv.DictReader(fh, delimiter='\t'):
        if r.get("scope")!="item": continue
        m=r["module"]
        for c in cols:
            if c in r and r[c]: agg[m][c]+=int(r[c])
for m,c in sorted(agg.items(), key=lambda kv:-kv[1]["shift_global_nodes"]):
    print(f'{m:24s} total {c["total_ns"]/1e9:8.2f}s gate {c["kernel_gate_ns"]/1e9:8.2f}s rescope {c["shift_global_nodes"]:>12,} unfolds {c["delta_body_rescopes"]:>8,} refs {c["global_ref_rescopes"]:>10,} steps {c["eval_steps"]:>10,} misses {c["conv_misses"]:>9,}')
