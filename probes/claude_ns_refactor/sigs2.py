# Parse parameter lists: {qualified-or-bare name: [(pname, implicit, is_self), ...] or None}
# for the working tree (new) and HEAD (old) versions of the library.
import re, glob, json, subprocess, os
SP = os.path.dirname(os.path.abspath(__file__))
decl = re.compile(r'^\s*(fn|theorem|axiom|inductive|record|class)\s+([A-Za-z_][\w:]*)\s*(<[^>(]*>)?\s*(\(?)', re.M)
def split_top(params):
    parts, d, cur = [], 0, ''
    for k, c in enumerate(params):
        prev = params[k-1] if k else ' '; nxt = params[k+1] if k+1 < len(params) else ' '
        if c in '([{' or (c == '<' and (prev.isalnum() or prev == '_') and nxt != '='): d += 1
        if c in ')]}' or (c == '>' and d > 0 and prev not in '-='): d -= 1
        if c == ',' and d == 0: parts.append(cur); cur = ''
        else: cur += c
    parts.append(cur); return parts
def split_arrows(t):
    parts, d, cur, k = [], 0, '', 0
    while k < len(t):
        c = t[k]
        if c in '([{': d += 1
        if c in ')]}': d -= 1
        if d == 0 and t.startswith('→', k): parts.append(cur); cur = ''; k += 1; continue
        if d == 0 and t.startswith('->', k): parts.append(cur); cur = ''; k += 2; continue
        cur += c; k += 1
    parts.append(cur); return parts
def params_of(text):
    ps = []
    for p in split_top(text):
        p = p.strip()
        if not p: continue
        if p.startswith('{') and p.endswith('}'):
            for q in split_top(p[1:-1]):
                if q.strip(): ps.append((q.split(':')[0].strip(), True, False))
            continue
        name = p.split(':')[0].strip()
        is_self = name.startswith('self ')
        if is_self: name = name[5:].strip()
        ps.append((name, False, is_self))
    return ps
def parse(src):
    out = {}
    for m in decl.finditer(src):
        ps = []
        j = m.end()
        if m.group(4) == '(':
            i = m.end(); depth = 1
            while depth:
                c = src[j]; depth += c in '([{'; depth -= c in ')]}'; j += 1
            ps = params_of(src[i:j-1])
        elif m.group(1) not in ('fn', 'theorem', 'axiom'):
            out[m.group(2)] = None; continue
        # curried tail: after ')' comes ':' or '→', then a type up to the top-level body '{'
        rest = src[j:]; rm = re.match(r'\s*(:|→|->)', rest)
        if rm:
            k = rm.end(); d = 0; t = ''
            while k < len(rest):
                c = rest[k]
                if c == '{' and d == 0: break
                if c in '([{': d += 1
                if c in ')]}': d -= 1
                t += c; k += 1
            for a in split_arrows(t)[:-1]:
                a = a.strip()
                if a.startswith('(') and a.endswith(')') and ':' in a:
                    ps += params_of(a[1:-1])
                elif a.startswith('{') and a.endswith('}'):
                    ps += [(q.split(':')[0].strip(), True, False) for q in split_top(a[1:-1]) if q.strip()]
                else:
                    ps.append(('_', False, False))
        out[m.group(2)] = ps
    return out
files = [f for f in glob.glob('lib/**/*.hthr', recursive=True)] + ['crates/elab/src/prelude.hthr']
new, old = {}, {}
for f in files:
    mod = os.path.basename(f)[:-5]
    new.update({k: v for k, v in parse(open(f).read()).items()})
    try: src = subprocess.check_output(['git', 'show', 'HEAD:' + f], text=True, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError: continue
    for k, v in parse(src).items(): old[f'{mod}\t{k}'] = v
for f in files:
    mod = os.path.basename(f)[:-5]
    try: src = subprocess.check_output(['git', 'show', 'f9fe5ad^:' + f], text=True, stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError: continue
    for k, v in parse(src).items(): old.setdefault(f'{mod}\t{k}', v)
json.dump({'new': new, 'old': old}, open(f'{SP}/sigs2.json', 'w'))
print(new['BitVec::concat'], old['bitvec\tconcat'], new['Nat::add_assoc'], sep='\n')
