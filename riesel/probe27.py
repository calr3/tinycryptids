"""The sequence of candidates the real machine tests (a6-tapes), with k and Q."""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

build.build()
def is_prime(m): return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))
def decode_c(s):
    s = s.rjust(25, '0')
    assert all(s[5 * g + 4] == '1' for g in range(5)), s
    return sum(int(s[5 * g:5 * g + 4], 2) << (4 * (4 - g)) for g in range(5))
FRESH = re.compile(r'(.*)0(1+)0(1110)000(1*)0*')
r = tm.run(build.ORDER, build.ST, maxsteps=3 * 10**6, trace='a6', maxtrace=4000)
prev, seen = None, 0
for t in r[5]:
    if t == prev: continue
    prev = t
    m = FRESH.fullmatch(t.strip('0') + '0' * 8)
    if not m: continue
    C, K, _, R = m.groups()
    try: c = decode_c(C)
    except AssertionError: continue
    Q = 3 + len(R)
    k = 2 * (build.C0 - c) + 3
    print('c', c, 'k', k, 'K', len(K), 'Q', Q, 'prime', is_prime(Q))
    seen += 1
print('events', seen, 'status', r[0], 'steps', r[1])
