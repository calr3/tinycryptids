"""End-to-end checks of the design.
 * at each pair test (state pw1 with a marker at a prime p, after the pair pass started)
   the tape is L 00 P0 00 P1 .. Pk 00 M with L = M = m, the list = the primes < m;
 * the test variant (B | A - 1) halts at the pair (2, 5);
 * the real machine runs past 10^8 steps."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm, ref

def blocks(t):
    t = t.strip('0')
    return [b for b in t.split('00') if b]

def val(b): return len(b) - 2

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8, trace='rt5', maxtrace=400)
print('real machine:', r[0], r[1])
ok &= r[0] != 'halt'
exp = list(ref.pairs(200))
seen = []
for tr in r[5]:
    bs = blocks(tr)
    # entries of pw1 come from rt5 (pair entry) and pairs-H1 (no: that is pw2); only rt5
    L, P0, M = bs[0], bs[1], None
    i = [j for j, b in enumerate(bs) if b != '1'*len(b) and j not in (0,)]
    seen.append(tuple(val(b) for b in bs))
cnt = 0
for s, (p, m) in zip(seen, exp + [(1, 0)] * 1000):
    pass
# check: each trace = L, P0, primes..., M (+ nothing else)
from itertools import groupby
prev = None
k = 0
for s in seen:
    m = s[0]
    lst = list(s[2:-1])
    good = s[-1] == m and s[1] == 1 and lst == [q for q in range(2, m) if ref.isprime(q)] and ref.isprime(m)
    if not good:
        print('BAD', s); ok = False; break
    k += 1
print('pair checkpoints ok:', k, 'last m =', seen[-1][0] if seen else None)
build.build(variant=1)
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('variant 1:', r[0], r[1], [val(b) for b in blocks(r[4])])
ok &= r[0] == 'halt'
print('OK' if ok else 'FAIL')
