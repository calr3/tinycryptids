"""End-to-end checks of the design.
 * at each growth of N (state v4, once per round) the tape is W 00 N 00 F with
   |N| = n + 2, |F| = n! + 4 and |W| = 7 - (n - 1) (W gone from n = 8 on);
 * test variants that start the square test earlier halt at the known
   solutions: from n = 4 at 4! + 1 = 5^2, from n = 5 at 11^2, from n = 6 and
   n = 7 at 7! + 1 = 71^2 (S then holds 2m+1 after its last wrap);
 * the real machine runs past 10^9 steps."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm
from math import factorial

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**10, trace='v4', maxtrace=8)
for i, tr in enumerate(r[5]):
    n = i + 2                                   # after round i+1, n = i+2
    blocks = tr.strip('0').split('00')
    if n <= 7:
        Wb, Nb, Fb = blocks
        good = len(Wb) == 7 - (n - 1) and len(Nb) == n + 2 and len(Fb) == factorial(n) + 4
    else:
        Nb, Fb = blocks
        good = len(Nb) == n + 2 and len(Fb) == factorial(n) + 4
    print('n =', n, 'OK' if good else 'FAIL ' + tr[:60]); ok &= good
for warm, n, m in [(3, 4, 5), (4, 5, 11), (5, 7, 71), (6, 7, 71)]:
    build.build(warm=warm)
    h = tm.run(build.ORDER, build.ST, maxsteps=10**10)
    blocks = [len(b) for b in h[4].strip('0').split('00')]
    Nb, Fb, Sb = blocks[-3:]
    good = h[0] == 'halt' and Nb == n + 2 and Fb == factorial(n) + 4 and Sb == 2 * m + 1 + 2
    print(f'test from n = {warm + 1}: halts at n = {n}, m = {m}:', h[0], h[1], 'OK' if good else 'FAIL'); ok &= good
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**9)
print('10^9 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
