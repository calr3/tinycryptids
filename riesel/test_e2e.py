"""End-to-end checks of the design.
 * each candidate Q = k*2^n - 1 is set up by the doubling; at the end of the
   doubling (state a6 on the separator before R) the tape is
   C 0 K 0 D 00 R with c = C0 - (k-3)/2, |K| = k + 4, D = 3 (hole at cell 3,
   its last cell), and R = its hole at cell 0 followed by Q - 3 cells;
 * test variants with a small counter halt after k = 2*c0 + 3;
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
            Q = k * 2 ** n - 1
            out.append((k, n, Q, c0 - (k - 3) // 2))
            if is_prime(Q) or len(out) >= count: break
            n += 1
        k += 2
    return out

def decode_c(s):
    s = s.rjust(25, '0')
    assert all(s[5 * g + 4] == '1' for g in range(5)), s
    return sum(int(s[5 * g:5 * g + 4], 2) << (4 * (4 - g)) for g in range(5))

# C 0 K 0 1110 000 R: D = 3 (hole home), then two separators, R's hole and cells
FRESH = re.compile(r'(.*)0(1+)0(1110)000(1*)0*')

def candidates(maxsteps, maxtr):
    """the (c, k, Q) of the tapes at a6, once per candidate (a6 scans left over R)"""
    r = tm.run(build.ORDER, build.ST, maxsteps=maxsteps, trace='a6', maxtrace=maxtr)
    out, prev = [], None
    for t in r[5]:
        if t == prev: continue                       # a6 runs over R without writing
        prev = t
        m = FRESH.fullmatch(t.strip('0') + '0' * 8)
        if not m: continue
        C, K, _, R = m.groups()
        try: c = decode_c(C)
        except AssertionError: continue
        out.append((c, len(K), 3 + len(R)))
    return out

ok = True
build.build()
trs = candidates(3 * 10**8, 50000)
ref = reference(len(trs), build.C0)
for (c, K, Q), (k, n, Q2, c2) in zip(trs, ref):
    good = (c == c2 and K == k + 4 and Q == Q2)
    if not good: print('FAIL', (c, K, Q), 'expected', (c2, k + 4, Q2)); ok = False; break
print('candidates', len(trs), 'up to k =', ref[-1][0], 'checked', 'OK' if ok else 'FAIL')

for c0 in range(0, 6):
    build.build(c0=c0)
    h = tm.run(build.ORDER, build.ST, maxsteps=10**9)
    refk = reference(10**4, c0, 2 * c0 + 3)
    got = candidates(h[1] + 1, 10**6)
    good = h[0] == 'halt' and got == [(c, k + 4, Q) for k, n, Q, c in refk]
    print(f'variant c0={c0} halts after k = {2 * c0 + 3}:', h[0], h[1], 'OK' if good else 'FAIL'); ok &= good
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
