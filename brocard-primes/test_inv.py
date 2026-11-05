"""Run the machine from a blank tape and check the tape invariant at every
checkpoint (each entry into hg5, i.e. the left end before M grows).

Expected at checkpoint m (m >= 2):  M 00 P_k ... P_j 00100 P_(j-1) ... P_1 000 S 0 K
with M = 1^(m+2); P blocks for all primes p <= m, largest first, each
1 [region of p cells, hole at index p-1-(m mod p)] 1; the marker 00100 right of the
block of q, the smallest prime with q^2 > m (for m < 4: q = 3, or M if 3 > m);
S = 1 [region 2n+1 cells, hole at index 2n-(m-n^2)] 1, n = isqrt(m);
K = 1^(c+1), c = number of primes in (p^2, m] for the largest prime p >= 3 with p^2 <= m,
or the number of primes <= m when m < 9."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import math, build, tm

def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, math.isqrt(p) + 1))

def primes_upto(m):
    return [p for p in range(2, m + 1) if is_prime(p)]

def count(m, c0=1):
    if m < 9:
        return c0 - 1 + len(primes_upto(m))
    p = max(p for p in primes_upto(math.isqrt(m)))
    return sum(1 for x in range(p * p + 1, m + 1) if is_prime(x))

def expected(m, c0=1, c=None):
    n = math.isqrt(m)
    q = 3 if m < 9 else min(p for p in range(2, m + 2) if is_prime(p) and p * p > m)
    t = '1' * (m + 2) + ('001' if q > m else '')
    for p in sorted(primes_upto(m), reverse=True):
        reg = ['1'] * p; reg[p - 1 - m % p] = '0'
        t += '00' + '1' + ''.join(reg) + '1'
        if p == q:
            t += '001'
    c = count(m, c0) if c is None else c
    reg = ['1'] * (2 * n + 1); reg[2 * n - (m - n * n)] = '0'
    t += '000' + '1' + ''.join(reg) + '1' + '0' + '1' * (c + 1)
    return t

def main(N):
    build.build()
    res = tm.run(build.ORDER, build.ST, maxsteps=10**11, trace='hg5', maxtrace=N)
    status, steps, traces = res[0], res[1], res[5]
    assert len(traces) == N, (status, len(traces))
    for i, t in enumerate(traces):
        m = i + 2
        assert t == expected(m), (m, t, expected(m))
    print(f'invariant holds at checkpoints m = 2..{N + 1} ({steps} steps)')

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 300)
