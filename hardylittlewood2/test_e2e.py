"""End-to-end checks of the design.
 * at the end of each rebuild (state W11, once per candidate m = 7, 9, ...) the
   tape is B' 00 A 00 C 00 D 00 R with the half gaps of the primes below m
   (B' newest first, A oldest first with the parked hole in h_1), |C| = c + 2,
   D = 3 with its hole, R = m - 3 + 2 cells;
 * variants with made-up gap lists (q_1 = 1, q_2 = 3, then any odd numbers)
   halt exactly when the reference search finds a pair at the first prime
   check, and the 'tight' variant (halt iff some sums are equal) halts at m = 5;
 * the real machine must run past 10^8 steps."""
import os, sys, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def is_prime(m): return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))

def check_fails(g, tight=False):
    """E := 0 (or -1); for i = 1..G-1: E += h_{G+1-i}; E -= h_i: is E ever < 0?"""
    G, E = len(g), (-1 if tight else 0)
    for i in range(1, G):
        E += g[G - i]
        E -= g[i - 1]
        if E < 0: return True
    return False

def reference(gaps, m0, count, tight=False):
    """candidates (m, gaps before m, c) after the first prime m0; stops at a halt"""
    gaps = list(gaps); q = 1 + 2 * sum(gaps)
    out, m = [], m0
    while len(out) < count:
        if is_prime(m) or m == m0:
            gaps.append((m - q) // 2); q = m
            if check_fails(gaps, tight): return out, m
        m += 2
        out.append((m, list(gaps), (m - q) // 2))
    return out, None

def blk(h): return '1' * (h + 2)

def expect(m, gaps, c):
    Bp = '00'.join(blk(h) for h in reversed(gaps))
    A = '00'.join(('101' if i == 0 else blk(h)) for i, h in enumerate(gaps))
    return Bp + '00' + A + '00' + blk(c) + '00' + '10111' + '00' + '1' * (m - 1)

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**9, trace='W11', maxtrace=300)
ref, _ = reference([1], 5, len(r[5]))
for tr, (m, g, c) in zip(r[5], ref):
    if tr.strip('0') != expect(m, g, c):
        print('FAIL', m, g, c); print(tr.strip('0')); print(expect(m, g, c)); ok = False; break
print('candidates', len(r[5]), 'up to m =', ref[len(r[5]) - 1][0], 'OK' if ok else 'FAIL')

build.build(variant='tight')
h = tm.run(build.ORDER, build.ST, maxsteps=10**7)
print('tight variant:', h[0], h[1], 'OK' if h[0] == 'halt' else 'FAIL'); ok &= h[0] == 'halt'

random.seed(1)
nh = 0
for trial in range(300):
    while True:
        n = random.randint(1, 7)
        gaps = [1] + [random.randint(1, 6) for _ in range(n)]
        q = 1 + 2 * sum(gaps)
        m0 = q + 2 * random.randint(1, 8)
        if trial % 2 == 0 or not check_fails(gaps + [(m0 - q) // 2]): break
    ref, hm = reference(gaps, m0, 40)
    build.build(gaps=gaps, m0=m0)
    res = tm.run(build.ORDER, build.ST, maxsteps=10**8, trace='W11', maxtrace=len(ref) + 1)
    good = (res[0] == 'halt') == (hm is not None) and len(res[5]) >= min(len(ref), 1)
    for tr, (m, g, c) in zip(res[5], ref):
        if tr.strip('0') != expect(m, g, c): good = False
    if hm is not None: nh += 1; good &= len(res[5]) == len(ref)
    if not good:
        print('FAIL', gaps, m0, hm, res[:4], len(res[5]), len(ref)); ok = False; break
print('made-up gap lists: 300 runs,', nh, 'halt', 'OK' if ok else 'FAIL')

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
