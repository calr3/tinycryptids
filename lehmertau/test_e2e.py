"""End-to-end checks of the design, from a blank tape.
 * the seed writes the start tape for n = 2 (checked at the first k1);
 * with the true exponents and constants, at every compare (state CMb) the
   tape holds M and P as in the reference, for variants with small constants
   (exponents (a, b) in place of (11, 5));
 * variants whose reference first has P = M at some n halt exactly there;
 * the real machine runs 10^8 steps."""
import os, sys, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def sig(k, n): return sum(d**k for d in range(1, n+1) if n % d == 0)
def ref(K, n, a, b):
    k65, k252, k691 = K
    P = k691*k252*sum(sig(b, i)*sig(b, n-i) for i in range(1, n))
    M = k691*sig(b, n) + k65*sig(a, n)
    return P, M

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**9, trace='k1', maxtrace=1)
good = r[5] and r[5][0].strip('0') == build.start_tape()[0]
print('seed writes the start tape:', 'OK' if good else 'FAIL'); ok &= bool(good)

for K, exp in [((1,1,1),(1,1)), ((1,1,1),(2,1)), ((2,3,5),(2,1)), ((1,2,1),(3,2))]:
    build.build(exp=exp, K=K)
    r = tm.run(build.ORDER, build.ST, maxsteps=10**9, trace='CMb', maxtrace=8)
    got = []
    for tr in r[5]:
        bl = [len(b) for b in tr.strip('0').split('00')]
        got.append((bl[1]-1, bl[0]-1))
    want = [ref(K, n, *exp) for n in range(2, 2+len(got))]
    g = got == want and len(got) == 8
    print('values', K, exp, len(got), 'compares', 'OK' if g else 'FAIL'); ok &= g

cands = {}
for exp in [(1,1),(2,1),(2,2),(3,1),(3,2)]:
    for K in itertools.product(range(1, 8), repeat=3):
        hn = next((n for n in range(2, 9) if ref(K, n, *exp)[0] == ref(K, n, *exp)[1]), None)
        if hn and (hn, exp) not in cands: cands[(hn, exp)] = K
for (hn, exp), K in sorted(cands.items()):
    build.build(exp=exp, K=K)
    r = tm.run(build.ORDER, build.ST, maxsteps=3*10**9, trace='CMb', maxtrace=50)
    g = r[0] == 'halt' and len(r[5]) == hn - 1
    print('halts', exp, K, 'at n =', hn, r[0], r[1], 'OK' if g else 'FAIL'); ok &= g

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('real machine after 10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'SOME FAILED')
