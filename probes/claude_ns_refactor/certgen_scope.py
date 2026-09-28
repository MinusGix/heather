# certgen_* have no imports: they elaborate after ir_v1's prefix, so rewrite them in its scope.
import sys, os
os.chdir('/home/minus/Kairos/Code/heather')
P='/home/minus/Kairos/Code/heather/probes/claude_ns_refactor/rewrite.py'
sys.argv=['rewrite.py']
src=open(P).read().replace("for p in args: process_rs(p) if p.endswith('.rs') else process(p)\nprint('\\n'.join(log))","")
g={'__file__':P,'__name__':'x'}; exec(src, g)
pre=''.join(l for l in open('lib/ir_v1.hthr') if l.startswith('import'))
for f in ['lib/certgen_code.hthr','lib/certgen_cert.hthr']:
    s=open(f).read(); new=g['process'](f, s, pre + s)
    if new!=s: open(f,'w').write(new)
