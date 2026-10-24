"""List the a6 candidates (c, |K|, Q) of the small variants."""
import os, sys, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

FRESH = re.compile(r'(.*)0(1+)0(1110)000(1*)0*')

def decode_c(s):
    s = s.rjust(25, '0')
    return sum(int(s[5 * g:5 * g + 4], 2) << (4 * (4 - g)) for g in range(5))

def cands(maxsteps):
    r = tm.run(build.ORDER, build.ST, maxsteps=maxsteps, trace='a6', maxtrace=10**7)
    out, prev = [], None
    for t in r[5]:
        if t == prev: continue
        prev = t
        m = FRESH.fullmatch(t.strip('0') + '0' * 8)
        if not m: continue
        C, K, _, R = m.groups()
        out.append((decode_c(C), len(K), 3 + len(R)))
    return r, out

for c0 in (0, 1, 2):
    build.build(c0=c0)
    r, c = cands(10**7)
    print('c0', c0, r[0], r[1], c)
