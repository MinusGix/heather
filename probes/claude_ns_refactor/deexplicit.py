# Drop needless `@` explicit forms. Each `@Callee(args)` site in the HEAD
# version of a file gets a level:
#   2  method form      recv.f(rest)         (callee has `self`, receiver fits)
#   1  qualified form   Ns::f(rest)          (leading implicits dropped)
#   0  original         @Ns::f(implicits, rest)
# Levels live in levels.json keyed "path#ordinal"; a missing key starts at the
# highest applicable level. Usage:
#   deexplicit.py render FILES...        rewrite FILES from HEAD, write spans.json
#   deexplicit.py demote CHECK_OUTPUTS.. map errors to sites and lower them
import sys, re, json, os, subprocess, glob
SP = os.path.dirname(os.path.abspath(__file__))
ROOT = '/home/minus/Kairos/Code/heather'
sys.path.insert(0, SP)
LEVELS = os.path.join(SP, 'levels.json')
SPANS = os.path.join(SP, 'spans.json')
CALLEES = os.path.join(SP, 'callees.json')
CALLEE = json.load(open(CALLEES)) if os.path.exists(CALLEES) else {}
RECVS = os.path.join(SP, 'recvs.json')
RECV = json.load(open(RECVS)) if os.path.exists(RECVS) else {}

def split_top(params):
    parts, d, cur = [], 0, ''
    for k, c in enumerate(params):
        if c in '([{': d += 1
        if c in ')]}': d -= 1
        if c == ',' and d == 0: parts.append(cur); cur = ''
        else: cur += c
    parts.append(cur); return parts

def load_sigs():
    import importlib.util
    src = open(os.path.join(SP, 'sigs2.py')).read().split('\nfiles = ')[0]
    ns = {'__file__': os.path.join(SP, 'sigs2.py')}; exec(src, ns)
    sigs = {}
    for f in glob.glob(ROOT + '/lib/**/*.hthr', recursive=True) + [ROOT + '/crates/elab/src/prelude.hthr']:
        for k, v in ns['parse'](open(f).read()).items():
            if v is not None: sigs.setdefault(k, v)
    return sigs
SIGS = load_sigs()

def lookup(callee):
    parts = callee.split('::')
    if len(parts) >= 2 and parts[-2][:1].isupper():
        key = '::'.join(parts[-2:])
    else:
        key = parts[-1]
    return key, SIGS.get(key)

CALL = re.compile(r'@([A-Za-z_][A-Za-z_0-9]*(?:::[A-Za-z_][A-Za-z_0-9]*)*)\(')

def match_close(s, i):  # s[i] == '('
    d = 0
    for j in range(i, len(s)):
        c = s[j]
        if c in '([{': d += 1
        elif c in ')]}':
            d -= 1
            if d == 0: return j
    raise ValueError('unbalanced')

def simple_receiver(r):
    # Only word chars, `::`, `.` and bracketed groups at top level.
    d = 0
    for c in r:
        if c in '([{': d += 1; continue
        if c in ')]}': d -= 1; continue
        if d == 0 and not (c.isalnum() or c in '_:.'): return False
    return True

def method_ok(r):
    r = r.strip()
    if not r or r == '·' or r[0].isdigit(): return False
    if re.fullmatch(r'[A-Z]\w*(\(.*\))?', r, re.S): return False  # constructor
    return True

class Site:
    def __init__(self, sid, callee, args, key, sig):
        self.sid, self.callee, self.args, self.key, self.sig = sid, callee, args, key, sig
    def plan(self):
        """(k, self_index_in_rest) or None when only level 0 applies."""
        sig = self.sig
        if not sig: return None
        k = 0
        while k < len(sig) and sig[k][1]: k += 1
        if k == 0 or any(p[1] for p in sig[k:]): return None
        if len(self.args) != len(sig): return None
        si = next((i - k for i, p in enumerate(sig) if p[2]), None)
        return k, si
    def max_level(self, rendered_args):
        p = self.plan()
        if p is None: return 0
        k, si = p
        if si is None or not method_ok(rendered_args[k + si]): return 1
        return 2

def render(text, path, levels, spans, counter):
    out = []; i = 0
    while True:
        m = CALL.search(text, i)
        if not m:
            out.append(text[i:]); break
        out.append(text[i:m.start()])
        open_ = m.end() - 1; close = match_close(text, open_)
        raw_args = split_top(text[open_ + 1:close])
        sid = f'{path}#{counter[0]}'; counter[0] += 1
        args = [render(a, path, levels, spans, counter) for a in raw_args]
        key, sig = lookup(m.group(1))
        site = Site(sid, m.group(1), args, key, sig)
        top = site.max_level(args)
        lvl = min(levels.get(sid, top), top)
        levels[sid] = lvl
        name = m.group(1)
        if lvl == 0:
            body = f'@{name}(' + ','.join(args) + ')'
        else:
            k, si = site.plan()
            rest = [a.strip() for a in args[k:]]
            if lvl == 1:
                body = f'{name}(' + ', '.join(rest) + ')'
            else:
                recv = rest.pop(si)
                rm = re.match(r'\x01([^\x02]*)\x02', recv)
                if rm and recv.endswith('\x03') and recv.count('\x01') >= 1:
                    RECV[sid] = rm.group(1)
                if not simple_receiver(recv.lstrip('@')): recv = f'({recv})'
                body = f'{recv}.{name.split("::")[-1]}(' + ', '.join(rest) + ')'
        # preserve leading whitespace of the whole expression: the callers
        # strip nothing, so emit with markers for span recovery
        CALLEE[sid] = name
        out.append(f'\x01{sid}\x02{body}\x03')
        i = close + 1
    return ''.join(out)

def spans_of(marked):
    """Strip markers; return clean text and {sid: (l1, c1, l2, c2)} 1-based."""
    clean = []; stack = []; res = {}
    line, col = 1, 1; i = 0
    while i < len(marked):
        c = marked[i]
        if c == '\x01':
            j = marked.index('\x02', i); stack.append((marked[i+1:j], line, col)); i = j + 1; continue
        if c == '\x03':
            sid, l, cc = stack.pop(); res[sid] = (l, cc, line, col); i += 1; continue
        clean.append(c)
        if c == '\n': line += 1; col = 1
        else: col += 1
        i += 1
    return ''.join(clean), res

def cmd_render(files):
    RECV.clear()
    levels = json.load(open(LEVELS)) if os.path.exists(LEVELS) else {}
    spans = json.load(open(SPANS)) if os.path.exists(SPANS) else {}
    for f in files:
        src = subprocess.check_output(['git', '-C', ROOT, 'show', 'HEAD:' + f], text=True)
        marked = render(src, f, levels, spans, [0])
        clean, sp = spans_of(marked)
        # a rewrite that shortened a line must not leave a dangling `,` layout
        open(os.path.join(ROOT, f), 'w').write(clean)
        for k in [k for k in spans if k.startswith(f + '#')]: del spans[k]
        spans.update({k: v for k, v in sp.items()})
    json.dump(levels, open(LEVELS, 'w'), indent=0, sort_keys=True)
    json.dump(spans, open(SPANS, 'w'))
    json.dump(CALLEE, open(CALLEES, 'w'))
    json.dump(RECV, open(RECVS, 'w'))

ERR = re.compile(r'^error[^\n]*\n(?:(?!^error).*\n)*?\s*--> ([^:\n]+):(\d+):(\d+)', re.M)

def cmd_demote(outputs, pathmap):
    levels = json.load(open(LEVELS)); spans = json.load(open(SPANS))
    pm = {}
    if pathmap and os.path.exists(pathmap):
        for ln in open(pathmap):
            a, b = ln.split(); pm[a] = b
    changed = []; unmapped = []; skipped = 0; touched = set()
    errs = []
    for o in outputs:
        t = open(o).read()
        for m in ERR.finditer(t):
            p = m.group(1).replace(ROOT + '/', ''); p = pm.get(p, p)
            errs.append((p, int(m.group(2)), int(m.group(3)), m))
    # declarations that failed: their names are unbound downstream (cascades)
    failing = set(); texts = {}
    DECL = re.compile(r'^\s*(?:pub\s+)?(?:fn|theorem|axiom|def)\s+([\w:]+)')
    for p, l, c, m in errs:
        if p not in texts:
            try: texts[p] = open(os.path.join(ROOT, p)).read().split('\n')
            except OSError: texts[p] = []
        for k in range(l - 1, -1, -1):
            if k < len(texts[p]) and (dm := DECL.match(texts[p][k])):
                failing.add(dm.group(1).split('::')[-1]); break
    for p, l, c, m in errs:
            first = m.group(0).splitlines()[0]
            cm = re.match(r"error: (?:unbound name `([\w:]+)`|`([\w:]+)` is qualified by)", first)
            if cm and (cm.group(1) or cm.group(2)).split('::')[-1] in failing:
                skipped += 1; continue
            if 'does not occur in the head' in first:
                hit = [sid for sid, (l1, c1, l2, c2) in spans.items()
                       if sid.startswith(p + '#') and l1 <= l <= l2 + 2 and levels.get(sid, 0) > 0]
                for sid in hit: levels[sid] = 0; changed.append(f'{sid} -> 0  (instance head)')
                if hit: continue
            best = None
            fm = re.search(r'of `([\w:]+)`', first) or re.match(r'error: unbound name `([\w:]+)`', first)
            want = fm.group(1).split('::')[-1] if fm else None
            cands = []
            for sid, (l1, c1, l2, c2) in spans.items():
                if not sid.startswith(p + '#') or levels.get(sid, 0) == 0: continue
                if (l1, c1) <= (l, c) < (l2, c2) or (l1, c1) == (l, c):
                    cands.append(((l2 - l1, c2 - c1), sid))
            named = [x for x in cands if want and CALLEE.get(x[1], '').split('::')[-1] == want]
            if named or cands: best = min(named or cands)
            if best is None or levels.get(best[1], 0) == 0:
                unmapped.append(f'{p}:{l}:{c} {m.group(0).splitlines()[0][:150]}'); continue
            sid = best[1]
            # a method call that fails for want of its receiver's width: the
            # receiver (itself a rewritten site) is what needs the `@`
            r = RECV.get(sid)
            if levels.get(sid) == 2 and r and levels.get(r, 0) > 0:
                sid = r
            if sid in touched: continue
            touched.add(sid)
            msg = m.group(0)
            if re.search(r'implicit argument|could not infer|argument of', first):
                levels[sid] = 0
            else:
                levels[sid] -= 1
            changed.append(f'{sid} -> {levels[sid]}  {msg.splitlines()[0][:120]}')
    json.dump(levels, open(LEVELS, 'w'), indent=0, sort_keys=True)
    print('\n'.join(changed)); print(f'-- {len(changed)} demoted, {skipped} cascades skipped')
    if unmapped: print('UNMAPPED:\n' + '\n'.join(unmapped))

if __name__ == '__main__':
    if sys.argv[1] == 'render': cmd_render(sys.argv[2:])
    elif sys.argv[1] == 'demote': cmd_demote(sys.argv[3:], sys.argv[2])
