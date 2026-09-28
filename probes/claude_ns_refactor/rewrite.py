"""Rewrite call sites of library names that moved into namespaces.
usage: rewrite.py [--novalue a,b] [--qualify a,b] file...
Arguments are remapped by parameter name between the HEAD and working-tree
signatures (params that became implicit are dropped); a call whose new
signature takes `self` becomes recv.f(rest), otherwise Ns::f(...).
Anything that cannot be reconciled is left alone and logged as FLAG."""
import re, sys, json, os, collections
SP = os.path.dirname(os.path.abspath(__file__))
S = json.load(open(f'{SP}/sigs2.json')); NEW, OLD = S['new'], S['old']
MAP = collections.defaultdict(dict)
for fn in ('map.tsv', 'extra.tsv'):
    for line in open(f'{SP}/{fn}'):
        mod, old, new = line.rstrip('\n').split('\t')
        if old == '+' or new == '??' or ',' in new: continue
        MAP[mod][old] = new
args = sys.argv[1:]
def opt(flag):
    global args
    if flag in args:
        i = args.index(flag); v = set(args[i+1].split(',')); args = args[:i] + args[i+2:]; return v
    return set()
qualify, novalue = opt('--qualify'), opt('--novalue')
EXPLICIT = set()
QSITES = set()
for f in opt('--qualify-sites'):
    for line in open(f):
        pth, ln, fn = line.split()
        QSITES.add((pth, int(ln), fn))
for f in opt('--explicit'):
    for line in open(f):
        pth, ln, fn = line.split()
        EXPLICIT.add((pth, int(ln), fn))

def full_order(oldps, newps, nargs):
    """old-arg indices for every new param (implicit included), for @f(...)"""
    O = [p[0] for p in oldps if not p[1]]
    plan = remap(oldps, newps, nargs)
    if plan is None: return None
    order, _ = plan
    exp = iter(order[:len([p for p in newps if not p[1]])])
    out = []
    for name, implicit, _s in newps:
        if implicit:
            if name not in O or O.index(name) >= nargs: return None
            out.append(O.index(name))
        else:
            k = next(exp, None)
            if k is None: break
            out.append(k)
    return out + list(range(len(O), nargs))
IDENT = re.compile(r'[A-Za-z_]\w*(?:::[A-Za-z_]\w*)*')
LIT = re.compile(r'\s*(0x[0-9A-Fa-f_]+|0b[01_]+|\d[\d_]*)\s*')
decl = re.compile(r'(?:^|(?<=[\s;}]))(?:fn|theorem|axiom|inductive|record|class)\s+([A-Za-z_][\w:]*)', re.M)

def match_close(s, i):
    d = 0; j = i
    while j < len(s):
        if s.startswith('//', j):
            e = s.find('\n', j); j = len(s) if e < 0 else e; continue
        c = s[j]
        if c in '([{': d += 1
        elif c in ')]}':
            d -= 1
            if d == 0: return j + 1
        j += 1
    raise ValueError('unbalanced')

def angle_open(s, j):
    """is the `>` at j closing a type-argument `<` (an identifier-adjacent one)?"""
    d = 0
    for k in range(j - 1, -1, -1):
        c = s[k]
        if c == '>' and s[k-1:k] not in ('-', '='): d += 1
        elif c == '<' and s[k+1:k+2] != '=' and k and (s[k-1].isalnum() or s[k-1] == '_'):
            if d == 0: return True
            d -= 1
        elif c in '([{;': return False
    return False

def split_args(s):
    parts, d, cur, j = [], 0, '', 0
    while j < len(s):
        if s.startswith('//', j):
            e = s.find('\n', j); e = len(s) if e < 0 else e
            cur += s[j:e]; j = e; continue
        c = s[j]
        prev = s[j-1] if j else ' '
        if c in '([{' or (c == '<' and (prev.isalnum() or prev == '_') and s[j+1:j+2] != '='): d += 1
        if c in ')]}' or (c == '>' and d > 0 and prev not in '-=' and angle_open(s, j)): d -= 1
        if c == ',' and d == 0: parts.append(cur); cur = ''
        else: cur += c
        j += 1
    parts.append(cur)
    return [] if len(parts) == 1 and not parts[0].strip() else parts

def atomic(e):
    e = e.strip(); m = IDENT.match(e)
    if m: i = m.end()
    elif e.startswith('('): i = match_close(e, 0)
    else: return False
    while i < len(e):
        if e[i] == '(': i = match_close(e, i)
        elif e[i] == '.' and IDENT.match(e, i+1): i = IDENT.match(e, i+1).end()
        elif e[i] == '<' and not e.startswith('<=', i) and '>' in e[i:]: i = e.index('>', i) + 1
        else: return False
    return True

def remap(oldps, newps, nargs):
    """-> (list of old-arg indices in new explicit order, self index in that list or None)"""
    if newps is None or oldps is None: return None
    O = [p[0] for p in oldps if not p[1]]
    N = [(p[0], p[2]) for p in newps if not p[1]]
    imp = {p[0] for p in newps if p[1]}
    nnames = [n for n, _ in N]
    matched, un_old = {}, []
    for i, name in enumerate(O):
        if name != '_' and name in nnames and nnames.index(name) not in matched: matched[nnames.index(name)] = i
        elif name != '_' and name in imp: pass
        else: un_old.append(i)
    un_new = [p for p in range(len(N)) if p not in matched]
    if len(un_old) != len(un_new): return None
    for p, i in zip(un_new, un_old): matched[p] = i
    order = [matched[p] for p in range(len(N))]
    selfi = next((p for p, (_, s) in enumerate(N) if s), None)
    if nargs < len(O):  # partial application: the supplied args must be a prefix in new order
        have = [i < nargs for i in order]
        if any(have[k] and not have[k-1] for k in range(1, len(have))): return None
        order = [i for i in order if i < nargs]
        if selfi is not None and selfi >= len(order): selfi = None
    order += list(range(len(O), nargs))
    return order, selfi

import glob
MODFILES = {os.path.basename(f)[:-5]: f for f in glob.glob('lib/std/**/*.hthr', recursive=True) if '/arch/' not in f and '/bitvec/' not in f}
MODFILES['prelude'] = 'crates/elab/src/prelude.hthr'
_bare = {}
def bare_decls(mod):
    if mod not in _bare:
        f = MODFILES.get(mod)
        _bare[mod] = {n for n in decl.findall(open(f).read()) if '::' not in n} if f else set()
    return _bare[mod]

def _top_split(t):
    parts, d, cur = [], 0, ''
    for c in t:
        if c in '([{': d += 1
        if c in ')]}': d -= 1
        if c == ',' and d == 0: parts.append(cur); cur = ''
        else: cur += c
    return parts + [cur]

def _names_before_colon(t):
    return re.findall(r'[A-Za-z_]\w*', t.split(':')[0].replace('self ', ' '))

def binders(src):
    """Names the file binds locally: decl params, let, lambda, match-arm patterns."""
    src = re.sub(r'//[^\n]*', '', src)
    b = set(re.findall(r'\blet\s+([A-Za-z_]\w*)', src))
    for m in re.finditer(r'λ', src):   # lambda header up to `=>`, depth-aware
        i = m.end(); d = 0
        while i < len(src) and not (d == 0 and src.startswith('=>', i)):
            c = src[i]
            if c == '(' and d == 0:
                try: e = match_close(src, i)
                except ValueError: break
                b |= set(_names_before_colon(src[i+1:e-1])); i = e; continue
            if c in '([{': d += 1
            if c in ')]}': d -= 1
            if d == 0 and re.match(r'[A-Za-z_]', c) and (i == 0 or not (src[i-1].isalnum() or src[i-1] in '_:')):
                w = re.match(r'[A-Za-z_]\w*', src[i:]).group(0); b.add(w); i += len(w); continue
            i += 1
    for h in re.findall(r'\b[A-Z]\w*\(([^()]*)\)\s*=>', src):
        b |= set(re.findall(r'[A-Za-z_]\w*', h))
    for m in re.finditer(r'^\s*(?:fn|theorem|axiom)\s+[\w:]+\s*(?:<[^>(]*>)?\s*\(', src, re.M):
        try: e = match_close(src, m.end() - 1)
        except ValueError: continue
        for part in _top_split(src[m.end():e-1]):
            nm = re.match(r'\s*\{?\s*(?:self\s+)?([A-Za-z_]\w*)', part)
            if nm: b.add(nm.group(1))
            if part.strip().startswith('{'):
                for q in _top_split(part.strip()[1:].rstrip('}')): b |= set(_names_before_colon(q)[:1])
    return b

RS_MODE = False
log = []
def process(path, src=None, scope=None, local_src=None):
    text = src
    if src is None: src = open(path).read()
    scope = src if scope is None else scope
    imports = re.findall(r'(?:^|;)\s*import\s+([\w:]+?)(?:::\{([^}]*)\})?\s*;', scope, re.M)
    full = {m for m, sel in imports if not sel}
    selective = {m: {x.strip() for x in sel.split(',')} for m, sel in imports if sel}
    mod = os.path.basename(path)[:-5]
    for m in list(full):  # follow re-exports of fully imported modules
        if m in MODFILES:
            for em, esel in re.findall(r'^export\s+(\w+)(?:::\{([^}]*)\})?\s*;', open(MODFILES[m]).read(), re.M):
                if esel: selective.setdefault(em, set()).update(x.strip() for x in esel.split(',') if x.strip())
                else: full.add(em)
    local = set(decl.findall(re.sub(r'//[^\n]*', '', scope if local_src is None else local_src)))
    bound = binders(scope if local_src is None else local_src)
    in_scope = {n for n in local if '::' not in n} | bare_decls('prelude')
    for m in full: in_scope |= bare_decls(m)
    for m, sel in selective.items(): in_scope |= sel
    def resolve(tok):
        if '::' in tok:
            q, n = tok.rsplit('::', 1)
            return [(q, n, MAP[q][n])] if n in MAP.get(q, {}) else []
        if tok in local: return []
        return sorted({(m, tok, MAP[m][tok]) for m in MAP if tok in MAP[m]
                       and (m in full or tok in selective.get(m, ()) or MAP[m][tok].split('::')[0] in selective.get(m, ()) or m == mod or m == 'prelude')})
    def lineno(s, i): return s.count('\n', 0, i) + 1
    def rw(s, base):
        out = []; i = 0
        while i < len(s):
            if s.startswith('//', i):
                e = s.find('\n', i); e = len(s) if e < 0 else e
                out.append(s[i:e]); i = e; continue
            if s[i] == '"':
                e = s.find('"', i+1) + 1
                if e == 0: out.append(s[i]); i += 1; continue
                out.append(s[i:e]); i = e; continue
            m = IDENT.match(s, i)
            if not m or (i and (s[i-1].isalnum() or s[i-1] in '_.:')):
                out.append(s[i]); i += 1; continue
            tok = m.group(0); j = m.end()
            if s[max(0, s.rfind('\n', 0, i)):i].lstrip().startswith(('import', 'export')):
                out.append(tok); i = j; continue
            if re.search(r'\b(fn|theorem|axiom|inductive|record|class|let|designation)\s+$', s[max(0, i-20):i]):
                out.append(tok); i = j; continue
            cands = resolve(tok)
            if not cands or re.match(r'\s*:=', s[j:j+4]) or re.match(r'\s*:[^:=]', s[j:j+3]):
                out.append(tok); i = j; continue
            where = f'{path}:{base + lineno(s, i)}'
            short = tok.rsplit('::', 1)[-1]
            tyargs = ''; j2 = j
            if s.startswith('<', j) and not s.startswith('<=', j):
                d, k = 0, j
                while k < len(s):
                    if s[k] == '<': d += 1
                    elif s[k] == '>' and s[k-1] not in '-=':
                        d -= 1
                        if d == 0: break
                    elif s[k] in ';{}=' or s.startswith('→', k): k = len(s); break
                    k += 1
                if k < len(s): j2 = k + 1; tyargs = s[j:j2]
            if j2 < len(s) and s[j2] == '(':
                if short in bound: log.append(f'{where}: BOUNDCALL {tok}')
                try: e = match_close(s, j2)
                except ValueError: out.append(tok); i = j; continue
                inner = s[j2+1:e-1]
                a = []; off = j2 + 1
                for x in split_args(inner):
                    a.append(rw(x, base + lineno(s, off) - 1)); off += len(x) + 1
                # absorb curried groups `f(a)(b)` when the old signature takes more
                _o = OLD.get(f'{cands[0][0]}\t{cands[0][1]}') or NEW.get(cands[0][2]) or []
                _need = len([p for p in _o if not p[1]])
                while len(a) < _need and e < len(s) and s[e] == '(':
                    try: e2 = match_close(s, e)
                    except ValueError: break
                    off = e + 1
                    for x in split_args(s[e+1:e2-1]):
                        a.append((' ' if a else '') + rw(x, base + lineno(s, off) - 1).lstrip(' ')); off += len(x) + 1
                    e = e2
                if len(cands) > 1:  # disambiguate by the old explicit arity
                    def _arity(c): return len([p for p in (OLD.get(f'{c[0]}\t{c[1]}') or NEW.get(c[2]) or []) if not p[1]])
                    exact = [c for c in cands if _arity(c) == len(a)]
                    if len(exact) == 1: cands = exact
                plans = [(new, remap(OLD.get(f'{mm}\t{n}') or NEW.get(new), NEW.get(new), len(a))) for mm, n, new in cands]
                if any(pl is None for _, pl in plans) or len({(tuple(pl[0]), pl[1]) for _, pl in plans}) > 1 or any(re.match(r'\s*\w+\s*:=', x) for x in a):
                    log.append(f'{where}: FLAG {tok}({len(a)} args) -> {[c[2] for c in cands]}')
                    out.append(f'{tok}{tyargs}({",".join(a)})'); i = e; continue
                new = plans[0][0]; order, selfi = plans[0][1]
                oldps0 = OLD.get(f'{cands[0][0]}\t{cands[0][1]}') or NEW.get(new) or []
                O0 = [p[0] for p in oldps0 if not p[1]]
                imp0 = {p[0] for p in (NEW.get(new) or []) if p[1]}
                partial_dropped = len(a) < len(O0) and any(nm in imp0 for nm in O0[:len(a)])
                if RS_MODE and any(nm in imp0 for nm in O0[:len(a)]): partial_dropped = True
                if partial_dropped or (path, base + lineno(s, i), new) in EXPLICIT:
                    fo = full_order(OLD.get(f'{cands[0][0]}	{cands[0][1]}'), NEW.get(new), len(a))
                    if fo is None:
                        log.append(f'{where}: FLAG explicit {tok} impossible')
                    else:
                        xs = [a[k] for k in fo]; xs = [xs[0].lstrip(' ')] + [x if x[:1].isspace() else ' ' + x for x in xs[1:]] if xs else xs
                        out.append(f'@{new}({",".join(xs)})'); i = e
                        log.append(f'{where}: explicit {tok} -> @{new}'); continue
                nshort = new.rsplit('::', 1)[-1]
                if len(cands) > 1 and len({p[0].rsplit('::', 1)[-1] for p in plans}) > 1:
                    log.append(f'{where}: FLAG {tok} ambiguous -> {[p[0] for p in plans]}'); out.append(f'{tok}{tyargs}({",".join(a)})'); i = e; continue
                na = [a[k] for k in order]
                strip0 = lambda xs: [xs[0].lstrip(' ')] + [x if x[:1].isspace() else ' ' + x for x in xs[1:]] if xs else xs
                call_lines = range(base + lineno(s, i), base + lineno(s, e) + 1)
                use_method = (selfi is not None and not tyargs and short not in qualify and nshort not in in_scope
                              and not any((path, ln, nshort) in QSITES for ln in call_lines)
                              and not LIT.fullmatch(na[selfi]) and not re.fullmatch(r'\s*[A-Z]\w*\s*', na[selfi]))
                if use_method:
                    lead = na[selfi][:len(na[selfi]) - len(na[selfi].lstrip())].lstrip(' ')
                    recv = na[selfi].strip(); recv = lead + (recv if atomic(recv) else f'({recv})')
                    rest = strip0(na[:selfi] + na[selfi+1:])
                    out.append(f'{recv}.{nshort}({",".join(rest)})')
                    log.append(f'{where}: method {tok} -> .{nshort}')
                else:
                    if len(cands) > 1:
                        log.append(f'{where}: FLAG {tok} ambiguous, cannot qualify -> {[p[0] for p in plans]}'); out.append(f'{tok}{tyargs}({",".join(a)})'); i = e; continue
                    out.append(f'{new}{tyargs}({",".join(strip0(na))})')
                    log.append(f'{where}: qualify {tok} -> {new}' + (' (args remapped)' if order != list(range(len(a))) else ''))
                i = e; continue
            if len(cands) > 1 or short in novalue or short in bound:
                log.append(f'{where}: FLAG value {tok} -> {[c[2] for c in cands]}'); out.append(tok); i = j; continue
            new = cands[0][2]
            o, nw = OLD.get(f'{cands[0][0]}\t{cands[0][1]}'), NEW.get(new)
            if o and nw and [p[0] for p in o if not p[1]] != [p[0] for p in nw if not p[1]]:
                log.append(f'{where}: value {tok} -> {new} (SIGNATURE CHANGED, check)')
            else: log.append(f'{where}: value {tok} -> {new}')
            out.append(new + tyargs); i = j2
        return ''.join(out)
    body = rw(src, 0)
    if text is not None: return body
    if body != src: open(path, 'w').write(body)

RS_STR = re.compile(r'r(#*)"(.*?)"\1|"((?:[^"\\]|\\.)*)"', re.S)
RS_MODE = False
def process_rs(path):
    global RS_MODE; RS_MODE = True
    src = open(path).read()
    lits = [(m, m.group(2) if m.group(2) is not None else m.group(3)) for m in RS_STR.finditer(src)]
    scope = '\n'.join(t for _, t in lits if t).replace('\\n', '\n')
    if not re.search(r'\b(import|theorem|fn)\b', scope): return
    out, last = [], 0
    for m, t in lits:
        if not t or not re.search(r'[A-Za-z_]\w*\s*[(<]|::', t): continue
        if '`' in re.sub(r'//[^\n]*', '', t): continue  # a diagnostic, not source
        if re.search(r'(contains|starts_with|ends_with)\(\s*&?\s*$', src[max(0, m.start()-40):m.start()]): continue  # printer output
        g = 2 if m.group(2) is not None else 3
        new = process(path, t, scope, t)
        out.append(src[last:m.start(g)]); out.append(new); last = m.end(g)
    out.append(src[last:])
    body = ''.join(out)
    if body != src: open(path, 'w').write(body)

for p in args: process_rs(p) if p.endswith('.rs') else process(p)
print('\n'.join(log))
