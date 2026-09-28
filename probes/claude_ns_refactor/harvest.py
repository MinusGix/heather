import sys, re
t = open(sys.argv[1]).read() if len(sys.argv) > 1 else sys.stdin.read()
for m in re.finditer(r'(?:implicit argument `\w+` of|argument of) `([\w:]+)`.*?\n\s*--> ([^:]+):(\d+):', t, re.S):
    print(m.group(2), m.group(3), m.group(1))
