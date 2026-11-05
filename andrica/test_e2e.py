"""End-to-end tests of the Andrica machine (build.py's design, or a given file for the last
test).
* Every rebuild (traced at c5: D's hole at cell 1, D and R one block of m + 5 cells), from a
  blank tape: H has t(m) - 1 cells inside with its hole at 2j - 1, |U| + |T| = t(m) with |T| the
  countdown, for m = 3, 4, ..., 400.
* Variants: 'short' halts at m = 10, 'slow' at m = 126 (see build.py).
* The real machine runs past 10^8 steps (C simulator).
Usage: python3 test_e2e.py [file]"""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

def isprime(n): return n >= 2 and all(n % d for d in range(2, n))

def t_of(m):
    t = 0
    while t * t < 4 * m: t += 1
    return t

def model(variant=None):
    """yields (m, tH, x, |U|, |T|) at each rebuild (m the next number); returns at the halt"""
    t0, tgrow, hgrow = build.VARIANTS[variant]
    tH, x, tT, c, m = 3, 1, t0, None, 2
    while True:
        if isprime(m): c = tT
        elif c == 1: return
        else: c -= 1
        if x + 2 <= tH - 1: x += 2
        else: tH += hgrow; x = 1; tT += tgrow
        m += 1
        if variant is None: assert tH == tT == t_of(m)
        yield (m, tH, x, tT - c, c)

def decode(t):
    mt = re.fullmatch(r'(1*)0(1*)00(1*)00(1+)0010(1+)', t.strip('0'))
    assert mt, t
    a, b, u, c, f = map(len, mt.groups())
    return (f - 4, a + b, a, u, c)

def check(mmax=400):
    build.build()
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 11, trace='c5', maxtrace=mmax - 2)
    assert len(r[5]) == mmax - 2, len(r[5])
    for want, t in zip(model(), r[5]):
        assert decode(t) == want, (want, decode(t))
    print(f'rebuilds m = 3..{mmax} as expected ({r[1]} steps)')

def variant(v, m):
    build.build(variant=v)
    n = len(list(model(v)))
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 10, trace='c5', maxtrace=10 ** 4)
    assert r[0] == 'halt' and r[2] == 'z3' and len(r[5]) == n == m - 2, (v, r[:4], len(r[5]), n)
    print(f'variant {v}: halts at m = {m} ({r[1]} steps)')

if __name__ == '__main__':
    check()
    variant('short', 10)
    variant('slow', 126)
    text = open(sys.argv[1]).read() if len(sys.argv) > 1 else build.build()
    order, states, _ = tm.parse(text)
    res = tm.run(order, states, maxsteps=10 ** 8)
    print('C simulator, 10^8 steps:', res[0]); assert res[0] != 'halt'
    print('ALL OK')
