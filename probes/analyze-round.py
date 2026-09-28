import csv,glob,os,statistics,sys
OUT=sys.argv[1]
ITEMS=["complete_post","close_body","number_grammar","Grammar","Certified",
       "factor_body","expr_body","checked_expr","whole_grammar"]
def load(p):
    rows=list(csv.DictReader(open(p),delimiter='\t'))
    return rows
def n(r,k): return int(r[k] or 0)
def agg(w):
    per={}; runs=[]
    seen=set()
    for p in sorted(glob.glob(f"{OUT}/{w}-*.tsv")):
        rows=load(p)
        for r in rows: seen.add(r['scope'])
        items=[r for r in rows if r['scope']=='item']
        runs.append(dict(
            total=sum(n(r,'total_ns') for r in items)/1e9,
            gate=sum(n(r,'kernel_gate_ns') for r in items)/1e9,
            resc=sum(n(r,'shift_global_nodes') for r in items),
            refs=sum(n(r,'global_ref_rescopes') for r in items),
            sigs=sum(n(r,'global_sig_rescopes') for r in items) if 'global_sig_rescopes' in rows[0] else 0,
            unf=sum(n(r,'delta_body_rescopes') for r in items),
            miss=sum(n(r,'conv_misses') for r in items),
            q=sum(n(r,'conv_shortcut_hits')+n(r,'conv_memo_hits')+n(r,'conv_misses') for r in items),
            steps=sum(n(r,'eval_steps') for r in items),
            dsteps=sum(n(r,'eval_delta_steps') for r in items),
            ct=sum(n(r,'check_terms') for r in items)))
        for r in items:
            if r['item'] in ITEMS:
                per.setdefault(r['item'],[]).append((n(r,'kernel_gate_ns')/1e6,
                    n(r,'shift_global_nodes'), n(r,'global_ref_rescopes'),
                    n(r,'global_sig_rescopes') if 'global_sig_rescopes' in r else 0))
    print(f"[{w}] scope values seen: {sorted(seen)}; item rows in first file: "
          f"{sum(1 for r in load(sorted(glob.glob(f'{OUT}/{w}-*.tsv'))[0]) if r['scope']=='item')}")
    return per,runs
pb,rb=agg("before"); pa,ra=agg("after")
def med(rs,k): return statistics.median([r[k] for r in rs])
print("\n=== whole run (3 samples each, median) ===")
print(f"{'metric':10}{'before':>16}{'after':>16}{'delta':>10}")
for k,f in [('total','%.2f s'),('gate','%.2f s'),('resc','%d'),('refs','%d'),('sigs','%d'),
            ('unf','%d'),('miss','%d'),('q','%d'),('steps','%d'),('dsteps','%d'),('ct','%d')]:
    b,a=med(rb,k),med(ra,k)
    d=f"{(a-b)/b*100:+.1f}%" if b else "—"
    print(f"{k:10}{f%b:>16}{f%a:>16}{d:>10}")
print("\nper-sample gate s: before",[round(r['gate'],2) for r in rb],"after",[round(r['gate'],2) for r in ra])
print("per-sample total s: before",[round(r['total'],2) for r in rb],"after",[round(r['total'],2) for r in ra])
print("\n=== per item: gate ms (all 3 samples), rescope, refs, sigs ===")
for it in ITEMS:
    if it not in pb: continue
    gb=[round(x[0]) for x in pb[it]]; ga=[round(x[0]) for x in pa.get(it,[])]
    mb=statistics.median(gb); ma=statistics.median(ga) if ga else 0
    print(f"{it:18} gate {mb:7.0f} -> {ma:7.0f} ({(ma-mb)/mb*100:+5.1f}%)  b{gb} a{ga}"
          f"  rescope {pb[it][0][1]:>9,} -> {pa[it][0][1]:>9,}  refs {pb[it][0][2]:>8,}  sigs {pa[it][0][3]:>5,}")
