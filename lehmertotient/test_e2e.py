"""End-to-end tests of the Lehmer totient machine (build.py's design, or a given file for the
last test).
* Every round end (traced at sh4, the pair's test about to start), from a blank tape: K/R is
  (1, n), the pair holds d = phi(n), p = n - 1 - phi(n), for n = 3, 4, ..., 130.
* Variants: 'prime' halts at n = 3 (the first prime), 'nodiv' at n = 4 (the first composite
  n with phi(n) not dividing n - 1), 'plus1' (one more cell in P, the test phi(n) | n) at
  n = 4 by the mod walk.
* The real machine runs past 10^8 steps (C simulator).
Usage: python3 test_e2e.py [file]"""
import os, re, sys
from math import gcd
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

def phi(n): return sum(1 for k in range(1, n) if gcd(k, n) == 1)

def decode(t):
    """the tape at sh4: (k, r, d, p)"""
    m = re.fullmatch(r'10(1*)001(0)(1*)00101(1*)00(1+)', t.strip('0'))
    assert m, t
    K, _, R, D, P = m.groups()
    return len(K) + 1, len(R) + 1, len(D) + 1, len(P) - 2

def check(nmax=130):
    build.build()
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 11, trace='sh4', maxtrace=nmax - 2)
    assert len(r[5]) == nmax - 2, len(r[5])
    for n, t in zip(range(3, nmax + 1), r[5]):
        assert decode(t) == (1, n, phi(n), n - 1 - phi(n)), (n, decode(t))
    print(f'round ends n = 3..{nmax} as expected ({r[1]} steps)')

def variant(v, n, state):
    build.build(variant=v)
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 9, trace='sh4', maxtrace=100)
    assert r[0] == 'halt' and len(r[5]) == n - 2 and r[2] == state, (v, r[:4], len(r[5]))
    print(f'variant {v}: halts at n = {n} ({r[1]} steps)')

if __name__ == '__main__':
    check()
    variant('prime', 3, 'sh6')
    variant('nodiv', 4, 'k1')
    variant('plus1', 4, 'k1')
    text = open(sys.argv[1]).read() if len(sys.argv) > 1 else build.build()
    order, states, _ = tm.parse(text)
    res = tm.run(order, states, maxsteps=10 ** 8)
    print('C simulator, 10^8 steps:', res[0]); assert res[0] != 'halt'
    print('ALL OK')
