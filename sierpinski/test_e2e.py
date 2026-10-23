"""End-to-end checks of the design.
 * each time the loop stops on R (state t1 on the separator before R, once per
   candidate P = k*2^n + 1) the tape is C 0 K 0 D 00 R with c = C0 - (k-1)/2,
   |K| = k + 6, D = 3 (hole at cell 3, its last cell), and R = its hole at cell 0,
   the gap, X', a 0 and T = X', with 2|X'| + 3 = P - 2 (R gets P - 2 cells);
 * test variants with a small counter halt after k = 2*c0 + 1;
 * the real machine must run past 10^8 steps."""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def is_prime(m): return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))

def reference(count, c0, kmax=10**9):
    out, k = [], 3
    while len(out) < count and k <= kmax:
        n = 1
        while True:
            P = k * 2 ** n + 1
            out.append((k, n, P, c0 - (k - 1) // 2))
            if is_prime(P) or len(out) >= count: break
            n += 1
        k += 2
    return out

def decode_c(s):
    s = s.rjust(20, '0')
    assert all(s[5 * g + 4] == '1' for g in range(4)), s
    return sum(int(s[5 * g:5 * g + 4], 2) << (4 * (3 - g)) for g in range(4))

REGION = re.compile(r'(.*)0(1+)0(1110)0000(1+)0(1+)0*')      # X' and T not empty
REGION0 = re.compile(r'(.*)0(1+)0(1110)0000()()0*')           # R is its hole only

def regions(maxsteps, maxtr):
    """the tapes at t1 when the loop stopped on R (the region pattern matches)"""
    r = tm.run(build.ORDER, build.ST, maxsteps=maxsteps, trace='t1', maxtrace=maxtr)
    out = []
    for t in r[5]:
        t = t.strip('0') + '0' * 8
        m = REGION.fullmatch(t) or REGION0.fullmatch(t)
        if m: out.append(m)
    return out

ok = True
build.build()
trs = regions(3 * 10**8, 800)
# the pseudo-round (k = 1): R is its hole only, the candidate is 5
first = trs[0].groups()
good = first[1] == '1' * 7 and first[3] == first[4] == '' and decode_c(first[0]) == build.C0
print('pseudo-round for k = 1:', 'OK' if good else 'FAIL', first); ok &= good
trs = trs[1:]
ref = reference(len(trs), build.C0)
for m, (k, n, P, c) in zip(trs, ref):
    Cs, K, D, X1, T1 = m.groups()
    good = (decode_c(Cs) == c and K == '1' * (k + 6) and X1 == T1 and 2 * len(X1) + 3 == P - 2)
    if not good: print('FAIL', k, n, P, c, m.group(0)); ok = False; break
print('candidates', len(trs), 'up to k =', ref[-1][0], 'checked', 'OK' if ok else 'FAIL')
for c0 in range(0, 6):
    build.build(c0=c0)
    h = tm.run(build.ORDER, build.ST, maxsteps=10**9)
    nk = len(reference(10**4, c0, 2 * c0 + 1)) + 1
    good = h[0] == 'halt' and len(regions(10**9, 10**6)) == nk
    print(f'variant c0={c0} halts after k = {2 * c0 + 1}:', h[0], h[1], 'OK' if good else 'FAIL'); ok &= good
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
