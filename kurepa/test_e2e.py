"""End-to-end checks of the design.
 * at the end of each test (state k1, once per round n >= 3) the tape is N 00 L 0 F with
   |N| = n + 1 (its hole at a cell < n, or at n iff n | !n), |L| = !n + n + 1, |F| = n!;
 * test variants halt: from n = 1 at n = 2 (2 | !2); with L one cell longer (testing
   n | !n + 1) at n = 5 (!5 + 1 = 35);
 * the real machine runs past 10^9 steps."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm
from math import factorial

def lf(n): return sum(factorial(k) for k in range(n))

def shape(t):
    """(|N|, N hole cell, |L|, |F|) of a tape N 00 L 0 F (head anywhere)."""
    t = t.strip('0')
    i = t.index('000') + 1 if '000' in t else t.index('00')   # '000': hole at N's last cell
    N, B = t[:i], t[i:].lstrip('0')
    L, F = B.split('0')
    return len(N), N.find('0'), len(L), len(F)

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**10, trace='k1', maxtrace=7)
for i, tr in enumerate(r[5]):
    n = i + 3
    Nn, h, Ln, Fn = shape(tr)
    good = Nn == n + 1 and Ln == lf(n) + n + 1 and Fn == factorial(n) and 1 <= h < n
    print('n =', n, (Nn, h, Ln, Fn), 'OK' if good else 'FAIL'); ok &= good
for kw, n in [(dict(n0=1), 2), (dict(loff=1), 5)]:
    build.build(**kw)
    h = tm.run(build.ORDER, build.ST, maxsteps=10**10, trace='k1', maxtrace=100)
    Nn, hh, Ln, Fn = shape(h[5][-1])
    good = h[0] == 'halt' and Nn == n + 1 and hh == n and Fn == factorial(n)
    print(kw, 'halts at n =', n, h[0], h[1], (Nn, hh, Ln, Fn), 'OK' if good else 'FAIL'); ok &= good
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**9)
print('10^9 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
