"""Halting tests.
1. Variants: with t = 5 the machine must halt at the boundary 9 (4 primes counted);
   with t = 6 and a seed count c0 = 3 it must pass 9 and halt at 25 (5 primes in (9, 25)).
2. Checkpoint tapes placed by hand (test_inv.expected) with the count c in K replaced by
   c = 0 .. 6: run to the next prime square q^2; the machine must halt exactly when
   c + (primes in (m, q^2)) < 4, and otherwise reach the checkpoint q^2."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import math, build, tm, test_inv

def halt_m(**kw):
    """Run a variant from a blank tape; return the checkpoint count at the halt."""
    build.build(**kw)
    r = tm.run(build.ORDER, build.ST, maxsteps=10**8, trace='hg5', maxtrace=10**6)
    return r[0], len(r[5]) + 2      # the number being processed when it halted

print('t=5:', halt_m(t=5)); assert halt_m(t=5) == ('halt', 9)
print('t=6, c0=3:', halt_m(t=6, c0=3)); assert halt_m(t=6, c0=3) == ('halt', 25)
print('t=7, c0=4:', halt_m(t=7, c0=4)); assert halt_m(t=7, c0=4) == ('halt', 25)

build.build()
isp = test_inv.is_prime
bad = 0
N = int(sys.argv[1]) if len(sys.argv) > 1 else 400
for m in range(9, N):
    q = min(p for p in range(2, m + 2) if isp(p) and p * p > m)
    k = q * q - m
    between = sum(1 for x in range(m + 1, q * q) if isp(x))
    for c in range(0, 7):
        tape = '0000' + test_inv.expected(m, c=c) + '0000'
        r = tm.run(build.ORDER, build.ST, start='hg5', tape=tape, head=1,
                   maxsteps=10**9, trace='hg5', maxtrace=k)
        should = c + between < 4
        if (r[0] == 'halt') != should:
            bad += 1; print('FAIL', m, c, r[0])
        elif r[0] == 'halt':
            assert len(r[5]) == k - 1, (m, c, len(r[5]))     # halted while processing q^2
        else:
            assert r[5][k - 1] == test_inv.expected(q * q, c=0), (m, c)
print('checkpoint tests done,', bad, 'failures')
assert bad == 0
