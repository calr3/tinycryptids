"""Parse the a6 tape of the pseudo-round and of k=3."""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

build.build()
FRESH = re.compile(r'(.*)0(1+)0(1110)000(1*)0*')
for c0 in (0, 1):
    build.build(c0=c0)
    r = tm.run(build.ORDER, build.ST, maxsteps=10**6, trace='a6', maxtrace=20000)
    prev = None
    n = 0
    for t in r[5]:
        if t == prev: continue
        prev = t
        m = FRESH.fullmatch(t.strip('0') + '0' * 8)
        if not m:
            print('no match:', t.strip('0')[:80]); continue
        C, K, _, R = m.groups()
        print('c0', c0, '|C|', len(C), '|K|', len(K), '|R ones|', len(R), '  K=', len(K), 'Q=', 3 + len(R))
        n += 1
        if n >= 4: break
