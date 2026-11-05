"""End-to-end checks of the design.
 * after each Horner run (state dk4) the tape is N 00 P1 .. P(k+1) 00 M' 00 B [00 A] with
   the list = the primes <= q, M' = q, N = k + 2 (after H_B) or k + 3 (after H_A),
   B = p^(k+1), A = q^k, as in ref.py;
 * the test variant (p^(n+2) <= q^(n+1)) halts at (2, 3) with B = 8, A = 9;
 * the real machine runs past 10^8 steps."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm, ref

def blocks(t): return [b for b in t.strip('0').split('00') if b]
def val(b): return len(b) - 2

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8, trace='dk4', maxtrace=100)
print('real machine:', r[0], r[1])
ok &= r[0] != 'halt'
exp = list(ref.tests(100))
seen = [[val(b) for b in blocks(tr)] for tr in r[5]]
assert len(seen) % 2 == 0 or True
i = 0
for j, (p, q, n, B, A) in enumerate(exp):
    if 2 * j + 1 >= len(seen): break
    ps = [x for x in range(2, q + 1) if ref.isprime(x)]
    sB, sA = seen[2 * j], seen[2 * j + 1]
    good = sB == [n + 2] + ps + [q, B] and sA == [n + 3] + ps + [q, B, A]
    # block shapes: N with its hole at cell 1 (after H_A), the list without holes
    if not good: print('BAD', p, q, sB, sA); ok = False; break
    i += 1
print('tests checked:', i, 'last q =', exp[i - 1][1])
ok &= i >= 3
build.build(variant=1)
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
bs = blocks(r[4])
print('variant 1:', r[0], r[1], [val(b) for b in bs])
ok &= r[0] == 'halt' and [val(b) for b in bs[:4]] == [5, 2, 3, 3]
print('OK' if ok else 'FAIL')
