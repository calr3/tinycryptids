"""End-to-end checks of the design.
 * at each check (state x1, on the T hole, once per round; the first round is the
   pseudo-round n = -1 of the seed) the tape is T 00 D' with |T| = n + 3, the T hole
   at cell min(s, n+1) + 1 where s is the sum of the proper divisors of n, and
   D' = 10 1^(n+4) (D's cell 1 marked, R's new cells written);
 * the test variant (halt iff s > n) halts at n = 945, the first odd abundant
   number (about 6*10^10 steps; skipped unless --slow);
 * the real machine must run past 10^8 steps."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm

def pds(n): return sum(d for d in range(1, n) if n % d == 0)

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**9, trace='x1', maxtrace=10**6)
n = -3
for tr in r[5]:
    n += 2
    Tb, rest = tr.strip('0').rsplit('00', 1)
    want = ['1'] * (n + 3); want[min(pds(n) if n > 0 else 0, n + 1) + 1] = '0'
    if Tb != ''.join(want) or rest != '10' + '1' * (n + 4):
        print('round', n, 'FAIL', tr); ok = False
print('rounds n = -1 ..', n, 'checked', 'OK' if ok else 'FAIL')
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
if '--slow' in sys.argv:
    build.build(abundant=True)
    h = tm.run(build.ORDER, build.ST, maxsteps=10**12)
    Tb = h[4].strip('0').rsplit('00', 1)[0]
    good = h[0] == 'halt' and len(Tb) == 945 + 3
    print('abundant variant halts at n = 945:', h[0], h[1], 'OK' if good else 'FAIL'); ok &= good
print('ALL OK' if ok else 'FAILURES')
