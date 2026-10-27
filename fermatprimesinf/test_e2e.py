"""End-to-end checks of the design.
 * Every walk start (each entry into B2 from G0 reading 1) is compared with a Python model of
   the algorithm: the candidate m and the divisor d, with the tape D 0 R as described in
   build.py (D's d - 1 ones with the hole on the blank cell left of them, the separator,
   R = m - 1 - d ones, B2 on R's cell 0), for every candidate up to m = 201.
 * At each check (each entry into X1 from V) the D hole is on cell (m - 1) mod d.
 * The beep transition (G0 reading 0) is taken exactly at the Fermat primes 3, 5, 17, 257, in
   order (with the C simulator), and the tape at a beep is one block of m - 1 ones; there is
   no other beep in the first 10^10 steps (the next Fermat prime, 65537, is out of reach).
 * Variant 'halt' (the beep replaced by a halt) halts at the first beep, m = 3.
 * The machine runs 10^8 steps without halting."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm

def is_prime(m): return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))
def fermat(m): return is_prime(m) and (m - 1) & (m - 2) == 0

def model(mmax):
    """(m, d) at each walk start and (m, d, c) at each check, for the candidates 5 .. mmax."""
    starts, checks = [], []
    for m in range(5, mmax + 1, 2):
        for d in range(3, m - 1, 2):
            starts.append((m, d))
            c = (m - 1) % d
            checks.append((m, d, c))
            if c == d - 1 or c == 0: break
    return starts, checks

ok = True
starts, checks = model(201)
build.build()
S = build.ST
tape, head, q, prev = {}, 0, build.ORDER[0], None
ks = kc = 0
while ks < len(starts) or kc < len(checks):
    b = tape.get(head, 0)
    w, mv, q2 = S[q][b]
    tape[head] = w; head += 1 if mv == 'R' else -1; prev, q = q, q2
    if q == 'B2' and prev == 'G0' and tape.get(head, 0) == 1 and ks < len(starts):
        m, d = starts[ks]; r = m - 1 - d
        # head on R's cell 0; the separator left of it; D's d - 1 ones; the hole (blank) left
        want = [0] * 3 + [0] + [1] * (d - 1) + [0] + [1] * r + [0] * 3
        got = [tape.get(head - 1 - d - 3 + i, 0) for i in range(len(want))]
        if got != want:
            print('FAIL at walk start', ks, (m, d), got); ok = False; break
        ks += 1
    if q == 'X1' and prev == 'V' and kc < len(checks):
        m, d, c = checks[kc]
        # head on D's cell d - 1
        Dcells = [tape.get(head - (d - 1) + i, 0) for i in range(d)]
        if Dcells != [0 if i == c else 1 for i in range(d)]:
            print('FAIL at check', kc, (m, d, c), Dcells); ok = False; break
        kc += 1
print('walk starts and checks for m = 5 ..', starts[-1][0], f'({len(starts)} divisors):',
      'OK' if ok else 'FAIL')

r = tm.run(build.ORDER, build.ST, maxsteps=10**10, maxtrace=5, beep=build.BEEP)
ms = [t.count('1') + 1 for s, t in r[5]]
want = [m for m in range(3, 300, 2) if fermat(m)]
good = r[0] == 'limit' and ms == want and all(t == '1' * (m - 1) for (s, t), m in zip(r[5], ms))
print('beeps at', ms, '(last at step %d), none more in 10^10 steps (by then m is about %d):'
      % (r[5][-1][0], r[4].count('1') + 2), 'OK' if good else 'FAIL'); ok &= good

build.build(variant='halt')
h = tm.run(build.ORDER, build.ST, maxsteps=10**6)
good = h[0] == 'halt' and h[4].strip('0') == '11'
print("variant 'halt' halts at m = 3:", h[0], h[1], 'OK' if good else 'FAIL'); ok &= good

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
