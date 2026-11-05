"""End-to-end tests of the Agoh-Giuga machine (build.py's design, or a given file for the last
test).
* Every check (traced at k1: R = 101 again, B updated), from a blank tape: N holds n, I holds i
  with its hole at cell 1, |J| = n - i + flag, |K| = 2 - flag, S's hole at cell B + 1 with
  B = sum (j^(n-1) - 1) mod n over j = n - 1 .. i, the flag set iff an earlier B was nonzero;
  for n = 4 .. 6.
* Variants: 'smod' halts at n = 4, 'shift' at n = 5 (see build.py).
* The real machine runs past 10^8 steps (C simulator).
Usage: python3 test_e2e.py [file]"""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

def model(variant=None, nmax=None):
    """yields (n, i, B, flag) at each check; returns at the halt"""
    eoff, soff = build.VARIANTS[variant]
    n = 4
    while nmax is None or n <= nmax:
        B, flag = 0, False
        for i in range(n - 1, 1, -1):
            yield (n, i, (B + i ** (n - 1 + eoff) - 1) % (n + soff), flag)
            B = (B + i ** (n - 1 + eoff) - 1) % (n + soff)
            if B: flag = True
        if flag and B == 0: return
        n += 1

PAT = re.compile(r'10(1+)0010(1+)00(1+)00(1+)00(1+)0(1+)00101')

def decode(t, variant=None):
    eoff, soff = build.VARIANTS[variant]
    m = PAT.fullmatch(t.strip('0'))
    assert m, t
    nN, i, j, k, a, b = map(len, m.groups())
    n = nN - eoff
    flag = k == 1
    assert j == n - i + flag and k == 2 - flag and a + b - 1 == n + soff, (t, n, i, j, k)
    return (n, i, a - 1, flag)

def check(nmax=6):
    build.build()
    want = list(model(nmax=nmax))
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 12, trace='k1', maxtrace=len(want))
    assert len(r[5]) == len(want), len(r[5])
    for w, t in zip(want, r[5]):
        assert decode(t) == w, (w, decode(t))
    print(f'checks for n = 4..{nmax} as expected ({r[1]} steps)')

def variant(v, n):
    build.build(variant=v)
    want = list(model(v))
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 10, trace='k1', maxtrace=10 ** 4)
    assert r[0] == 'halt' and r[2] == 'z6' and want[-1][0] == n, (v, r[:4], want[-1])
    assert len(r[5]) == len(want), (len(r[5]), len(want))
    for w, t in zip(want, r[5]):
        assert decode(t, v) == w, (w, decode(t, v))
    print(f'variant {v}: halts at n = {n} ({r[1]} steps)')

if __name__ == '__main__':
    check()
    variant('smod', 4)
    variant('shift', 5)
    text = open(sys.argv[1]).read() if len(sys.argv) > 1 else build.build()
    order, states, _ = tm.parse(text)
    r = tm.run(order, states, maxsteps=10 ** 8)
    assert r[0] == 'limit', r[:4]
    print('real machine: no halt in 10^8 steps')
