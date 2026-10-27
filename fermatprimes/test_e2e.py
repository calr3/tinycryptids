"""End-to-end checks of the design.
 * Every walk start (each entry into B2 from G0 reading 1) is compared with a Python model
   of the algorithm: the candidate m and the divisor d, with the tape D 0 R as described in
   build.py (D's d - 1 ones with the hole on the blank cell left of them, the separator,
   R = m - 1 - d ones, then blanks), for every candidate up to m = 201.
 * At each check (each entry into X1 from V) the D hole is on cell (m - 1) mod d.
 * The passes (G0 reading 0) come exactly at the Fermat primes 3, 5, 17, 257 (with the C
   simulator), with one block of m - 1 ones and the counter (5, 4, 3, 2 cells) to its right;
   there is no other pass in the first 10^10 steps.
 * Variants with a counter of 2, 3, 4 cells halt at the 2nd, 3rd, 4th pass: m = 5, 17, 257.
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
        want = [0] * 3 + [0] + [1] * (d - 1) + [0] + [1] * r + [0]
        got = [tape.get(head - 1 - d - 3 + i, 0) for i in range(len(want))]
        if got != want:
            print('FAIL at walk start', ks, (m, d), got); ok = False; break
        ks += 1
    if q == 'X1' and prev == 'V' and kc < len(checks):
        m, d, c = checks[kc]
        Dcells = [tape.get(head - (d - 1) + i, 0) for i in range(d)]
        if Dcells != [0 if i == c else 1 for i in range(d)]:
            print('FAIL at check', kc, (m, d, c), Dcells); ok = False; break
        kc += 1
print('walk starts and checks for m = 5 ..', starts[-1][0], f'({len(starts)} divisors):',
      'OK' if ok else 'FAIL')

r = tm.run(build.ORDER, build.ST, maxsteps=10**10, maxtrace=5, beep=('G0', 0))
passes = []
for s, t in r[5]:
    block = t.split('0')[0]                 # the block, then blanks, then the counter
    passes.append((len(block) + 1, t.count('1') - len(block)))
want = [m for m in range(3, 300, 2) if fermat(m)]
good = r[0] == 'limit' and [m for m, k in passes] == want and [k for m, k in passes] == [6, 5, 4, 3]
print('passes (m, counter cells):', passes, ', none more in 10^10 steps:', 'OK' if good else 'FAIL')
ok &= good

for k, m in ((2, 5), (3, 17), (4, 257)):
    build.build(k)
    h = tm.run(build.ORDER, build.ST, maxsteps=10**9)
    good = h[0] == 'halt' and h[4].count('1') == m - 1
    print(f'counter of {k} cells halts at m = {m}:', h[0], h[1], 'OK' if good else 'FAIL'); ok &= good

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
