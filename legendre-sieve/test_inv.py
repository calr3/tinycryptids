"""Run the machine from a blank tape and check the tape invariant at every
checkpoint (each entry into hg5, i.e. the left end before M grows).

Expected at checkpoint m:  M 00 P_k 00 ... 00 P_1 000 S 0 F  with
M = 1^(m+2); P blocks for all primes p <= m, largest first, each
1 [region of p cells, hole at index p-1-(m mod p)] 1;
S = 1 [region 2n+1 cells, hole at index 2n-(m-n^2)] 1, n = isqrt(m);
F = 1 iff some prime lies in (n^2, m]."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import sys, math, build, tm

def primes_upto(m):
    return [p for p in range(2, m + 1) if all(p % d for d in range(2, math.isqrt(p) + 1))]

def expected(m):
    n = math.isqrt(m)
    t = '1' * (m + 2)
    for p in sorted(primes_upto(m), reverse=True):
        reg = ['1'] * p; reg[p - 1 - m % p] = '0'
        t += '00' + '1' + ''.join(reg) + '1'
    reg = ['1'] * (2 * n + 1); reg[2 * n - (m - n * n)] = '0'
    t += '000' + '1' + ''.join(reg) + '1'
    if any(n * n < p <= m for p in primes_upto(m)):
        t += '01'
    return t

def main(N):
    build.build()
    res = tm.run(build.ORDER, build.ST, maxsteps=10**10, trace='hg5', maxtrace=N)
    status, steps, traces = res[0], res[1], res[5]
    assert len(traces) == N, (status, len(traces))
    for i, t in enumerate(traces):
        m = i + 1
        assert t == expected(m), (m, t, expected(m))
    print(f'invariant holds at checkpoints m = 1..{N} ({steps} steps)')

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 300)
