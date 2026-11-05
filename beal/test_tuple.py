"""Tuples placed on the tape, run from the coprimality test (state gA0 on x's anchor).
Exponents may be below 3 here (block length E + 1; x >= 2, so that the anchor
is not next to a separator). Expect 'halt' iff
a^x + b^y = c^z and gcd(a, b) = 1; otherwise the machine reaches en2 with the tuple
restored. Usage: python3 test_tuple.py"""
import os, sys
from math import gcd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def tape_for(x, y, z, a, b, c, A='11'):
    bl = ['1' * (e + 1) for e in (x, y, z)] + ['1' * (v + 3) for v in (a, b, c)]
    t = '000' + '00'.join(bl) + '001' + '00' + A + '000'
    return t[:4] + '0' + t[5:]

def check(tup, variant=None, maxsteps=10 ** 9):
    build.build(variant=variant)
    t = tape_for(*tup)
    r = tm.run(build.ORDER, build.ST, start='gA0', tape=t, head=4, maxsteps=maxsteps, trace='en2', maxtrace=1)
    return r[0], r[1], (r[5][0] if r[5] else None), t

CASES = [(3, 3, 4, 2, 2, 2), (2, 2, 2, 3, 4, 5), (2, 2, 2, 6, 8, 10), (3, 2, 2, 2, 1, 3),
         (3, 3, 5, 3, 6, 3), (3, 4, 3, 7, 7, 14), (3, 3, 3, 1, 1, 1), (1, 1, 1, 1, 1, 2),
         (2, 1, 1, 2, 4, 8), (1, 1, 1, 3, 5, 8), (2, 1, 1, 3, 6, 15), (2, 3, 2, 1, 2, 3),
         (3, 3, 3, 6, 8, 9), (5, 2, 2, 1, 1, 1), (1, 2, 1, 5, 2, 9), (2, 1, 1, 6, 12, 48),
         (2, 2, 2, 5, 12, 13), (2, 2, 2, 7, 3, 5)]

def main():
    ok = True
    for tup in CASES:
        x, y, z, a, b, c = tup
        sol = a ** x + b ** y == c ** z
        for var in (None, 'nogcd'):
            want = 'halt' if sol and (gcd(a, b) == 1 or var == 'nogcd') else 'traced'
            st, steps, tr, t = check(tup, var)
            good = st == want
            if st == 'traced':
                good &= t.strip('0').startswith(tr)   # the trace shows the visited cells
            ok &= good
            print(tup, var, st, steps, 'OK' if good else 'FAIL')
    print('tuples:', 'ALL OK' if ok else 'FAILURES'); assert ok

if __name__ == '__main__':
    main()
