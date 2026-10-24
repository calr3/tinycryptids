"""Precise block parse of the a6 tapes."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

for c0 in (0, 1):
    build.build(c0=c0)
    Cstr = build.counter_cells(c0 + 1)
    skip = len(Cstr.lstrip('0'))
    r = tm.run(build.ORDER, build.ST, maxsteps=10**6, trace='a6', maxtrace=20000)
    prev, n = None, 0
    for t in r[5]:
        if t == prev: continue
        prev = t
        s = t.strip('0')
        rest = s[skip:]
        # rest = '0' + K ones + '0' + '1110' + '00' + '0'(R hole) + R ones
        assert rest[0] == '0', rest[:10]
        rest = rest[1:]
        klen = len(rest) - len(rest.lstrip('1'))
        rest = rest[klen:]
        assert rest[0] == '0', rest[:10]
        rest = rest[1:]
        print('c0', c0, 'K =', klen, 'next:', rest[:12], 'Q =', 3 + len(rest) - 8)
        n += 1
        if n >= 4: break
