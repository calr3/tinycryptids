"""Halting tests.
1. A variant that never sets F must halt at the first square, m = 4.
2. Checkpoint tapes placed by hand (test_inv.expected), with F flipped:
   with F forced to 0 the machine must halt exactly when the next square
   comes before the next prime; with the true F it must reach the next
   square's checkpoint."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import math, build, tm, test_inv

build.build(set_f=False)
r = tm.run(build.ORDER, build.ST, maxsteps=10**6)
print('no-F variant:', r[0], r[1], 'steps')
assert r[0] == 'halt'

build.build()
P = test_inv.primes_upto

def from_checkpoint(m, F):
    t = test_inv.expected(m)
    if t.endswith('01'): t = t[:-2]
    if F: t += '01'
    tape = '0000' + t + '0000'
    n1 = math.isqrt(m) + 1
    # run until the checkpoint after the next square (or halt)
    k = n1 * n1 - m
    return tm.run(build.ORDER, build.ST, start='hg5', tape=tape, head=1,
                  maxsteps=10**9, trace='hg5', maxtrace=k + 1)

bad = 0
for m in range(2, 400):
    n = math.isqrt(m); sq = (n + 1) ** 2
    prime_before_sq = any(m < p < sq for p in P(sq))
    for F in (0, 1):
        r = from_checkpoint(m, F)
        should_halt = (F == 0 and not prime_before_sq)
        ok = (r[0] == 'halt') == should_halt
        if not ok:
            bad += 1; print('FAIL', m, F, r[0])
        if r[0] == 'halt':      # it halted on the step out of the square's S check
            assert len(r[5]) == sq - m - 1, (m, F, len(r[5]))
print('checkpoint tests done,', bad, 'failures')
assert bad == 0
