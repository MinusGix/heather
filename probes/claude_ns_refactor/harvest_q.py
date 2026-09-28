# unbound-name errors on a method call `.f(` -> (path line f): force the qualified form there
import sys, re
t = sys.stdin.read()
for m in re.finditer(r'error: unbound name `(\w+)`\n\s*--> ([^:]+):(\d+):\d+\n\s*\|\n\s*\d+ \| (.*)\n', t):
    f, p, l, src = m.groups()
    if '.' + f + '(' in src: print(p, l, f)
