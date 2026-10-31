"""End-to-end tests of the Goldbach machine.
* At every entry of the P test (`e1` on P's first cell, a blank left of it) the tape must be
  P s Q (all 1s, Q possibly with one stale b on its 4th cell or later) for the (p, q)
  sequence of the reference: per even n, p = n - 2, n - 3, ... until p and n - p are prime.
* Started at an odd "stage" (all pairs for an odd sum), the machine must halt at (1, m - 1)
  for the first odd m >= start with m - 2 not prime (m = 11: 9 = 3 * 3; from 13: m = 17).
* The real machine runs 10^9 steps without halting (C simulator).
Usage: python3 test_e2e.py [machine.txt]   (default: the design, build.py's output)"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

def isprime(x): return x >= 2 and all(x % d for d in range(2, x))

def reference(nmin, nmax, step=2):
    """(p, q) pairs in order; ('halt', p, q) at the end if a sum has no prime pair."""
    out = []
    for n in range(nmin, nmax + 1, step):
        for p in range(n - 2, 0, -1):
            if p == 1: return out + [('halt', 1, n - 1)]
            out.append((p, n - p))
            if isprime(p) and isprime(n - p): break
    return out

def pairs(text, tape, maxsteps):
    """the (p, q) at each P-test entry, and ('halt', p, q) if the machine halts"""
    order, ST, _ = tm.parse(text)
    t = {i: c for i, c in enumerate(tape)}
    h, q, out = 0, order[0], []
    if tape: q = 'e1'
    for _ in range(maxsteps):
        if q == 'e1' and t.get(h - 1, 0) == 0:
            cells = []; i = h
            while t.get(i, 0) != 0: cells.append(t[i]); i += 1
            assert all(t.get(j, 0) == 0 for j in list(t) if j < h - 1 or j > i), 'stray cells'
            s = cells.index(5); P, Q = cells[:s], cells[s + 1:]
            assert set(P) == {1}, cells
            assert all(c == 1 for j, c in enumerate(Q) if j < 3) and set(Q) <= {1, 4} \
                and Q.count(4) <= 1, cells
            out.append((len(P), len(Q)))
        tr = ST[q][t.get(h, 0)]
        if tr is None:
            p, qq = out[-1]
            return out[:-1] + [('halt', p, qq)]
        w, d, q = tr; t[h] = w; h += 1 if d == 'R' else -1
    return out

def stage(n):
    return [1] * (n - 2) + [5, 1, 1]

def check(text):
    got = pairs(text, [], 3 * 10**7)
    ref = reference(4, 400)
    assert got[0] == (2, 2) and got == ref[:len(got)], 'pair sequence differs'
    print(f'blank tape: {len(got)} pairs agree, up to n = {sum(got[-1])}')
    for start, m in ((11, 11), (13, 17)):
        got = pairs(text, stage(start), 10**7)
        ref = reference(start, 40)
        assert got == ref and got[-1] == ('halt', 1, m - 1), (got[-3:], ref[-3:])
        print(f'odd stage {start}: halts at (1, {m - 1}) as expected ({len(got)} pairs)')
    order, ST, _ = tm.parse(text)
    st, steps, *_ = tm.run(order, ST, maxsteps=10**9)
    assert st != 'halt', st
    print(f'real machine: {st} after {steps} steps')

if __name__ == '__main__':
    check(open(sys.argv[1]).read() if len(sys.argv) > 1 else build.build())
