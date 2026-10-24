import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

for c0 in (0, 1):
    build.build(c0=c0)
    Cstr = build.counter_cells(c0 + 1)
    r = tm.run(build.ORDER, build.ST, maxsteps=10**6, trace='a6', maxtrace=20000)
    prev, n = None, 0
    print('c0', c0, 'Cstr', Cstr, 'lstrip', Cstr.lstrip('0'))
    for t in r[5]:
        if t == prev: continue
        prev = t
        print('  a6 tape:', t.strip('0'))
        n += 1
        if n >= 3: break
