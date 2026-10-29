"""End-to-end checks of the 4-symbol machine (twinprimes4.txt, = machines/twinprimes4_10.txt).
 * Every check (each step into `chk2` or a FAIL/OK decision of `cur`, i.e. each time `cur`
   reads D's last cell) is compared with a Python model of the algorithm: the candidate m,
   the divisor d, the marker's cell c = (m - 1) mod d, and the tape D R (D = 3s with the
   marker 2 on cell c, R = m - d 1s, blank elsewhere), for every candidate up to m = 150.
 * The beep transition (`beep` reading 0) is taken at step 2 and then exactly at the lesser
   twin primes other than 5 (3, 11, 17, 29, ...: the first 30, with the C simulator), and the
   tape at a beep is m - 1 3s, 1 3 1 (the marker of D = m made a 1, then the 3 and the 1
   written right of it).
 * Variant 'halt' (the beep replaced by a halt) halts at step 3.
 * The machine runs 10^8 steps without halting.
 * twinprimes4.txt is build.py's output, and machines/twinprimes4_10.txt a copy of it."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'tools'))  # tm.py
sys.path.insert(0, HERE)
import build, tm

def is_prime(m): return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))
def twin(m): return is_prime(m) and is_prime(m + 2)

def model(mmax):
    """(m, d, c) at each check, and the beeps (m), for the candidates from 3 up to mmax."""
    checks, beeps, m = [], [], 3
    while m <= mmax:
        for d in range(2, m):
            c = (m - 1) % d
            checks.append((m, d, c))
            if c == d - 1 or c == d - 3: m += 1; break
        else:
            beeps.append(m)
            checks.append((m, m, m - 1))   # d = m, r = 0: the walk ends at once, FAIL
            m += 3
    return checks, beeps

ok = True
text = build.build()
good = text == open(os.path.join(HERE, 'twinprimes4.txt')).read() == \
    open(os.path.join(HERE, 'machines', 'twinprimes4_10.txt')).read()
print('twinprimes4.txt = build.py output = machines/twinprimes4_10.txt:', 'OK' if good else 'FAIL')
ok &= good

checks, beeps = model(150)
S = build.ST
tape, head, q, k = {}, 0, build.ORDER[0], 0
while k < len(checks):
    b = tape.get(head, 0)
    if q == 'cur' and b in (2, 3):     # `cur` on D's last cell: the check
        m, d, c = checks[k]
        cells = [tape.get(head - (d - 1) + i, 0) for i in range(d)]
        r = 0
        while tape.get(head + 1 + r, 0) == 1: r += 1
        good = (d + r == m and cells == [2 if i == c else 3 for i in range(d)]
                and all(tape.get(head - d - i, 0) == 0 for i in range(1, 5))
                and all(tape.get(head + 1 + r + i, 0) == 0 for i in range(5)))
        if not good:
            print('FAIL at check', k, (m, d, c), 'r =', r, cells); ok = False; break
        k += 1
    t = S[q][b]
    if t is None:
        print('undefined transition', q, b); ok = False; break
    w, mv, q2 = t
    tape[head] = w; head += 1 if mv == 'R' else -1; q = q2
print('checks for m = 3 ..', checks[-1][0], f'({len(checks)} divisors):', 'OK' if ok else 'FAIL')

r = tm.run(build.ORDER, build.ST, maxsteps=10**10, maxtrace=31, beep=build.BEEP)
twins = [p for p in range(3, 10**4) if twin(p) and p != 5][:30]
good = r[5][0][0] == 2 and r[5][0][1].strip('0') == '31'
ms = [len(t) - 2 for s, t in r[5][1:]]
good &= ms == twins and all(t == '3' * (m - 1) + '131' for (s, t), m in zip(r[5][1:], ms))
print('beeps at step 2, then m =', ms[:10], '...', ms[-1],
      '(%d, last at step %d):' % (len(ms), r[5][-1][0]), 'OK' if good else 'FAIL'); ok &= good

build.build(variant='halt')
h = tm.run(build.ORDER, build.ST, maxsteps=10**6)
good = h[0] == 'halt' and h[1] == 3
print("variant 'halt' halts at step 3:", h[0], h[1], 'OK' if good else 'FAIL'); ok &= good

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
