"""End-to-end checks of the design.
 * each time the doubling ends (state a5, once per candidate P = k*2^n - 1) the
   tape is C 00 K 00 D 00 R with c = C0 - (k-3)/2, |K| = k + 7,
   D = 3 (hole at cell 1), R = P - 3 + 2 cells, holes at R[1] and at the
   separator cell being filled;
 * test variants with a small counter halt after k = 2*c0 + 3;
 * the real machine must run past 10^8 steps."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def is_prime(m): return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))

def reference(count, c0, kmax=10**9):
    out, k = [], 5
    while len(out) < count and k <= kmax:
        n = 1
        while True:
            P = k * 2 ** n - 1
            out.append((k, n, P, c0 - (k - 3) // 2))
            if is_prime(P) or len(out) >= count: break
            n += 1
        k += 2
    return out

def decode_c(s):
    s = s.rjust(25, '0')
    assert all(s[5 * g + 4] == '1' for g in range(5)), s
    return sum(int(s[5 * g:5 * g + 4], 2) << (4 * (4 - g)) for g in range(5))

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=3 * 10**8, trace='a5', maxtrace=400)
ref = reference(len(r[5]), build.C0)
for tr, (k, n, P, c) in zip(r[5], ref):
    Cs, K, D, R = tr.strip('0').rsplit('00', 3)
    R = R.ljust(P - 1, '0')              # the separator cell being filled may be the last
    good = (decode_c(Cs) == c and K == '1' * (k + 7) and D == '10111'
            and R[:2] == '10' and R[2:].count('0') == 1 and len(R) == P - 3 + 2)
    if not good: print('FAIL', k, n, P, c, tr); ok = False; break
print('candidates', len(r[5]), 'up to k =', ref[-1][0], 'checked', 'OK' if ok else 'FAIL')
for c0 in range(0, 6):
    build.build(c0=c0)
    h = tm.run(build.ORDER, build.ST, maxsteps=10**9)
    nk = len(reference(10**4, c0, 2 * c0 + 3))
    tr = tm.run(build.ORDER, build.ST, maxsteps=10**9, trace='a5', maxtrace=10**6)
    good = h[0] == 'halt' and len(tr[5]) == nk
    print(f'variant c0={c0} halts after k = {2 * c0 + 3}:', h[0], h[1], len(tr[5]), nk, 'OK' if good else 'FAIL'); ok &= good
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
