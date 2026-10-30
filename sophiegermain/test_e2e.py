"""End-to-end checks of the design (or of a machine file given as argument for the beep checks).
 * Every walk start (each entry into B2 from G0 reading 1) is compared with a Python model of the
   algorithm: the candidate n and the divisor d, with the tape D 0 R as described in
   build.py (D's d - 1 ones with the hole on the blank cell left of them, the separator,
   R = n - 1 - d ones, B2 on R's cell 0), for every candidate up to n = 301.
 * At each check (each entry into K1 from X, except in the rebuild) the hole just filled was
   on cell (2n - 2) mod d.
 * The beep transition is taken exactly at the Sophie Germain primes 3, 5, 11, ..., in order
   (the first 40, with the C simulator), and the tape at a beep is one block of n - 1 ones.
 * Variant 'halt' (the beep replaced by a halt) halts at the first beep, n = 3.
 * The 20-state reference design (variant 'ref') beeps at the same primes.
 * The machine runs 10^8 steps without halting."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm

def is_prime(m): return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))
def sg(p): return is_prime(p) and is_prime(2 * p + 1)
WANT = [p for p in range(3, 10**5) if sg(p)][:40]

def model(nmax):
    """(n, d) at each walk start and (n, d, c) at each check, for the candidates 5 .. nmax."""
    starts, checks = [], []
    for n in range(5, nmax + 1, 2):
        for d in range(3, n - 1, 2):
            starts.append((n, d))
            c = (2 * n - 2) % d
            checks.append((n, d, c))
            if c == d - 2 or c == d - 3: break
    return starts, checks

ok = True
starts, checks = model(301)
build.build()
S = build.ST
tape, head, q, prev = {}, 0, build.ORDER[0], None
ks = kc = 0
while ks < len(starts) or kc < len(checks):
    b = tape.get(head, 0)
    w, mv, q2 = S[q][b]
    tape[head] = w; head += 1 if mv == 'R' else -1; prev, q = q, q2
    if q == 'B2' and prev == 'G0' and tape.get(head, 0) == 1 and ks < len(starts):
        n, d = starts[ks]; r = n - 1 - d
        want = [0] * 3 + [0] + [1] * (d - 1) + [0] + [1] * r + [0] * 3
        got = [tape.get(head - 1 - d - 3 + i, 0) for i in range(len(want))]
        if got != want:
            print('FAIL at walk start', ks, (n, d), got); ok = False; break
        ks += 1
    rebuild = tape.get(head, 0) == 0 and tape.get(head - 2, 0) == 0   # X, K1 write 1 1 at the left end
    if q == 'K1' and prev == 'X' and not rebuild and kc < len(checks):
        n, d, c = checks[kc]
        # head on D's cell c + 1; D's cells all 1 now, the separator at d - c - 1 cells right
        D = [tape.get(head - 1 - c + i, 0) for i in range(d + 1)]
        if D != [1] * d + [0] or tape.get(head - 2 - c, 0) != 0:
            print('FAIL at check', kc, (n, d, c), D); ok = False; break
        kc += 1
print('walk starts and checks for n = 5 ..', starts[-1][0], f'({len(starts)} divisors):',
      'OK' if ok else 'FAIL')

def beeps(order, ST, bq):
    r = tm.run(order, ST, maxsteps=10**11, maxtrace=len(WANT), beep=(bq, 0))
    ns = [t.count('1') + 1 for s, t in r[5]]
    good = ns == WANT and all(t == '1' * (n - 1) for (s, t), n in zip(r[5], ns))
    return good, ns, r

if len(sys.argv) > 1:
    order, ST, _ = tm.parse(open(sys.argv[1]).read())
    bq = sys.argv[2] if len(sys.argv) > 2 else 'N'
    good, ns, r = beeps(order, ST, bq)
    print(sys.argv[1], 'beeps at the first 40 Sophie Germain primes:', 'OK' if good else 'FAIL'); ok &= good
build.build()
good, ns, r = beeps(build.ORDER, build.ST, 'G0')
print('beeps at', ns[:8], '...', ns[-1], f'(the first {len(WANT)} Sophie Germain primes; the last at step {r[5][-1][0]}):',
      'OK' if good else 'FAIL'); ok &= good

build.build(variant='ref')
good, ns, r = beeps(build.ORDER, build.ST, 'G0')
print("reference design ('ref') beeps at the same primes:", 'OK' if good else 'FAIL'); ok &= good

build.build(variant='halt')
h = tm.run(build.ORDER, build.ST, maxsteps=10**6)
good = h[0] == 'halt' and h[4].strip('0') == '11'
print("variant 'halt' halts at n = 3:", h[0], h[1], 'OK' if good else 'FAIL'); ok &= good

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
