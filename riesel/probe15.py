"""First a6 tapes of the real run, and the block structure."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=2000, trace='a6', maxtrace=200)
prev = None
for t in r[5]:
    if t == prev: continue
    prev = t
    s = t.strip('0')
    print(repr(s))
    print('  len', len(s))
    if len(s) > 40: break
