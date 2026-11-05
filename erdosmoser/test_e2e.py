"""End-to-end tests of the Erdos-Moser machine (build.py's design, or a given file for the last
test).
* Every compare, from a blank tape: the pair (k, m) read off K and M follows the diagonal order
  from (2, 2), A holds 1 + 1^k + ... + (m-1)^k and R holds m^k + 2 cells (its hole filled).
* Variants: kmin = 1 halts on 1 + 2 = 3; a_init = 1 + d cells halts on the first pair (in the
  search order) with 1^k + ... + (m-1)^k + d = m^k, for d in 1, 2, 3, 4, 7, 18, 28.
* The real machine runs past 10^8 steps (C simulator).
Usage: python3 test_e2e.py [file]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

def blocks(t):
    """the blocks of a tape string (split at runs of >= 2 zeros)"""
    out, cur, z = [], '', 0
    for ch in t.strip('0'):
        if ch == '0':
            z += 1
        else:
            if z >= 2:
                out.append(cur); cur = ''
            elif z == 1:
                cur += '0'
            cur += '1'; z = 0
    out.append(cur)
    return out

def km(t):
    """(k, m) from a tape at a compare or the halt (K's cursor on its cell 1)"""
    b = blocks(t)
    return len(b[0]) - 2, len(b[1]) - 3

def pairs(kmin=2, start=(2, 2)):
    k, m = start
    while True:
        yield k, m
        k, m = (k + 1, m - 1) if m > 1 else (kmin, k)

def psum(m, k): return sum(i ** k for i in range(1, m))

def first_halt(d, kmin=2, limit=200):
    for n, (k, m) in enumerate(pairs(kmin, (kmin, 2) if kmin == 2 else (1, 2))):
        if psum(m, k) + d == m ** k: return k, m
        if n > limit: return None

if __name__ == '__main__':
    n = 40
    build.build()
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 10, trace='C1', maxtrace=n)
    assert len(r[5]) == n, len(r[5])
    for (k, m), t in zip(pairs(), r[5]):
        K, M, A, R = blocks(t)
        assert km(t) == (k, m), (t, k, m)
        assert K == '10' + '1' * k                           # the anchor on cell 1
        assert M == '10' + '1' * (m + 1)                     # the marker on cell 1
        assert A == '1' * (1 + psum(m, k)), (k, m)
        assert R == '101' + '1' * (m ** k - 1), (k, m)
    print('first', n, 'compares: pairs in order, A and R as expected')
    build.build(kmin=1)
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 9)
    print('variant kmin=1:', r[0], r[1], 'steps, (k, m) =', km(r[4]))
    assert r[0] == 'halt' and km(r[4]) == (1, 3)
    for d in (1, 2, 3, 4, 7, 18, 28):
        want = first_halt(d)
        build.build(a_init='1' * (1 + d))
        r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 10)
        got = km(r[4])
        print(f'variant d={d}:', r[0], r[1], 'steps, (k, m) =', got, 'expected', want)
        assert r[0] == 'halt' and got == want
    text = open(sys.argv[1]).read() if len(sys.argv) > 1 else build.build()
    order, states, _ = tm.parse(text)
    res = tm.run(order, states, maxsteps=10 ** 8)
    print('C simulator, 10^8 steps:', res[0]); assert res[0] != 'halt'
    print('ALL OK')
