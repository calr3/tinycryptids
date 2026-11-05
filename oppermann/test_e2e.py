"""End-to-end checks of the design.
 * at each Q advance (state q1, once per candidate m) the tape is
   [1 0] Q 00 D 00 R with |Q| = j+2 and the Q hole at cell 2k+1, where m = q(j) + k is the
   k-th number of interval j (q(j) = floor(j^2/4), j >= 3), m = d + r from D and R, and the
   flag is set iff a prime was seen among the numbers of the interval up to m;
 * the test variant (intervals of 2 numbers: 2..3, 4..5, ...) halts on the first one without
   a prime, 8..9;
 * the real machine must run past 10^8 steps."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm

def is_prime(m): return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))

def q(j): return j * j // 4

def reference(count):
    out, j, k = [], 3, 0
    seen = False
    while len(out) < count:
        m = q(j) + k
        seen |= is_prime(m)
        out.append((j, k, m, seen))
        k += 1
        if q(j) + k == q(j + 1): j, k, seen = j + 1, 0, False
    return out

def decode(tr, j):
    FQ, D, R = tr.strip('0').split('00')
    flag = len(FQ) == j + 4          # the flag 1 and a 0 left of Q
    return (FQ[2:] if flag else FQ), D, R, flag and FQ.startswith('10')

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**9, trace='q1', maxtrace=10**6)
ref = reference(len(r[5]))
for tr, (j, k, m, seen) in zip(r[5], ref):
    Q, D, R, flag = decode(tr, j)
    good = (len(Q) == j + 2 and Q.count('0') == 1 and Q.index('0') == 2 * k + 1
            and D.count('0') == 1 and len(D) + len(R) - 4 == m and flag == seen)
    if not good: print('FAIL', j, k, m, seen, tr); ok = False; break
print('candidates m = 2 ..', ref[len(r[5]) - 1][2], 'checked', 'OK' if ok else 'FAIL')
build.build(grow=False)
h = tm.run(build.ORDER, build.ST, maxsteps=10**9)
D, R = h[4].strip('0').split('00')[1:3]
good = h[0] == 'halt' and len(D) + len(R) - 4 == 9
print('variant halts at 8..9:', h[0], h[1], 'OK' if good else 'FAIL'); ok &= good
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
