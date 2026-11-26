#!/usr/bin/env python3
"""The two codes of one row of scripts/bytes-level-compare, disassembled and
compared routine by routine.

    scripts/bytes-level-compare-diff.py <both.txt> <out-dir> [<published.s>]

<both.txt> is `heather eval`'s last line for `both_codes(...)`
(bytes_level_compare): [old bytes, new bytes, old routine starts, new
routine starts]. Writes <out-dir>/old.s, new.s (objdump of each routine,
addresses relative to the routine) and diff.txt (a unified diff of the two
listings with the displacements of calls and jumps removed, since a routine
that moved changes every displacement to it), and prints one line per
routine: same, or its two lengths.
"""
import ast
import difflib
import os
import re
import subprocess
import sys
import tempfile

both = ast.literal_eval(open(sys.argv[1]).read().strip().splitlines()[-1])
out = sys.argv[2]
os.makedirs(out, exist_ok=True)
if not both:
    print('not lowered')
    sys.exit(0)
old, new, old_starts, new_starts = both
# The old bytes as evaluated are the ones published: a check on the
# comparison itself (the program and placement read off the certificate).
if len(sys.argv) > 3:
    published = []
    for line in open(sys.argv[3]):
        line = line.strip()
        if line.startswith('.byte'):
            published += [int(x, 16) for x in line[5:].split(',')]
    if published != old:
        print('the evaluated old code is not the published %s' % sys.argv[3])
        sys.exit(1)


def pieces(code, starts):
    ends = starts[1:] + [len(code)]
    return [bytes(code[a:b]) for a, b in zip(starts, ends)]


def listing(piece):
    with tempfile.NamedTemporaryFile(suffix='.bin', delete=False) as f:
        f.write(piece)
        name = f.name
    try:
        text = subprocess.run(['objdump', '-D', '-b', 'binary', '-mi386:x86-64', '-M', 'intel', name],
                              capture_output=True, text=True, check=True).stdout
    finally:
        os.unlink(name)
    lines = []
    for line in text.splitlines():
        m = re.match(r'\s*([0-9a-f]+):\t([0-9a-f ]+)\t(.*)', line)
        if m:
            lines.append((int(m.group(1), 16), m.group(3).strip()))
    return lines


def shape(instr):
    # A relative target is the routine's layout, not its code.
    return re.sub(r'\b(call|j[a-z]+)\s+0x[0-9a-f]+', r'\1 <target>', instr)


olds, news = pieces(old, old_starts), pieces(new, new_starts)
diff_lines = []
with open(os.path.join(out, 'old.s'), 'w') as fo, open(os.path.join(out, 'new.s'), 'w') as fn:
    for k, (a, b) in enumerate(zip(olds, news)):
        la, lb = listing(a), listing(b)
        fo.write('# routine %d\n' % k + ''.join('%4x  %s\n' % x for x in la))
        fn.write('# routine %d\n' % k + ''.join('%4x  %s\n' % x for x in lb))
        if a == b:
            print('routine %d: same (%d bytes)' % (k, len(a)))
            continue
        sa, sb = [shape(i) for _, i in la], [shape(i) for _, i in lb]
        if sa == sb:
            print('routine %d: same instructions, displacements differ (%d bytes)' % (k, len(a)))
            continue
        print('routine %d: %d bytes old, %d new' % (k, len(a), len(b)))
        diff_lines += ['# routine %d\n' % k] + list(difflib.unified_diff([x + '\n' for x in sa], [x + '\n' for x in sb], 'old', 'new', n=2))
with open(os.path.join(out, 'diff.txt'), 'w') as f:
    f.writelines(diff_lines)
