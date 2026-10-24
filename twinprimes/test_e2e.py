"""End-to-end checks of the design.
 * Every check (each entry into X1, once per trial divisor, after the pseudo-round's
   one) is compared with a Python model of the algorithm: the candidate m, the divisor
   d = m - r (r read off the tape), the D hole's cell c = (m - 1) mod d, and that D, the
   separator and R are as described in build.py, for every candidate up to m = 120.
   After a beep the model has the check d = m, r = 0 (FAIL).
 * The beep transition (G2 reading 0) is taken exactly at the lesser twin primes
   3, 5, 11, ..., in order (the first 30, with the C simulator), and the tape at a beep is
   D = 1^(m-1) 0, the separator, nothing else.
 * Variant 'halt' (the beep replaced by a halt) halts at the first beep, m = 3.
 * The machine runs 10^8 steps without halting."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm

def is_prime(m): return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))

def model(mmax):
    """(m, d, c) at each check, and the beeps (m), for the candidates 3 .. mmax."""
    checks, beeps = [], []
    for m in range(3, mmax + 1):
        for d in range(2, m):
            c = (m - 1) % d
            checks.append((m, d, c))
            if c == d - 1 or c == d - 3: break
        else:
            beeps.append(m)
            checks.append((m, m, m - 1))   # after the beep: d = m, r = 0, FAIL
    return checks, beeps

ok = True
checks, beeps = model(120)
# at each entry into X1 the head is on D's cell d - 1; r and the hole are read off the tape
build.build()
S = build.ST
tape, head, q, k, seed = {}, 0, build.ORDER[0], 0, 1   # the pseudo-round checks once
while k < len(checks):
    b = tape.get(head, 0)
    w, mv, q2 = S[q][b]
    tape[head] = w; head += 1 if mv == 'R' else -1; q = q2
    if q == 'X1' and seed: seed -= 1
    elif q == 'X1':
        m, d, c = checks[k]
        r = 0
        while tape.get(head + 2 + r, 0) == 1: r += 1
        Dcells = [tape.get(head - (d - 1) + i, 0) for i in range(d)]
        good = (d + r == m and tape.get(head + 1, 0) == 0
                and Dcells == [0 if i == c else 1 for i in range(d)]
                and all(tape.get(head - d - i, 0) == 0 for i in range(1, 5))
                and all(tape.get(head + 2 + r + i, 0) == 0 for i in range(5)))
        if not good:
            print('FAIL at check', k, (m, d, c), 'r =', r, Dcells); ok = False; break
        k += 1
print('checks for m = 3 ..', checks[-1][0], f'({len(checks)} divisors):', 'OK' if ok else 'FAIL')

r = tm.run(build.ORDER, build.ST, maxsteps=10**10, maxtrace=30, beep=build.BEEP)
twins = [p for p in range(3, 10**4) if is_prime(p) and is_prime(p + 2)][:30]
ms = [len(t) - len(t.lstrip('1')) + 1 for s, t in r[5]]
good = ms == twins and all(t == '1' * (m - 1) for (s, t), m in zip(r[5], ms))
print('beeps at', ms[:12], '...', ms[-1], '(%d, last at step %d):' % (len(ms), r[5][-1][0]),
      'OK' if good else 'FAIL'); ok &= good

build.build(variant='halt')
h = tm.run(build.ORDER, build.ST, maxsteps=10**6)
good = h[0] == 'halt' and h[4].strip('0') == '11'
print("variant 'halt' halts at m = 3:", h[0], h[1], 'OK' if good else 'FAIL'); ok &= good

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
