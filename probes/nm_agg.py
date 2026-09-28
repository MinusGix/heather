# One row per item from a `--timings` TSV: the columns the round is ranked on.
import sys, csv

COLS = ["total_ns", "kernel_gate_ns", "conv_misses", "queries", "eval_steps",
        "eval_delta_steps", "elab_whnf_ns", "decl_emit_ns", "mints_pushed",
        "mints_declined", "gendefs_pushed"]

def rows(path):
    out = {}
    with open(path, newline="") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            if r.get("item") in (None, "-", ""):
                continue
            out[r["item"]] = r
    return out

def num(r, c):
    # A conversion *query* is every call the kernel's conversion answered,
    # however it answered it — the column `docs/…` §11.3 reads.
    if c == "queries":
        return sum(num(r, k) for k in
                   ("conv_shortcut_hits", "conv_memo_hits", "conv_misses"))
    v = r.get(c)
    if v in (None, ""):
        return 0
    try:
        return int(v)
    except ValueError:
        return 0

if __name__ == "__main__":
    want = sys.argv[2:] or None
    rs = rows(sys.argv[1])
    for item, r in rs.items():
        if want and item not in want:
            continue
        print("   %-24s " % item + " ".join("%s=%d" % (c, num(r, c)) for c in COLS))
