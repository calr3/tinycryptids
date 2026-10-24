"""Exact shapes of the Riesel checkpoints (t1, dfin, b2/newk)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
ORDER, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())

def grp(u, s):
    return [1, u % 2, u // 2 % 2, u // 4 % 2, u // 8 % 2] + s
def cs(v):
    s = []
    for sh in (0, 4, 8, 12, 16):
        s = grp(v >> sh & 15, s)
    return s

class C:
    def __init__(self, q, left, right):
        self.q = q; self.t = {i: c for i, c in enumerate(right)}
        for i, c in enumerate(left): self.t[-1 - i] = c
        self.h = 0
    def step(self):
        t = ST[self.q][self.t.get(self.h, 0)]
        if t is None: return False
        w, d, q = t
        self.t[self.h] = w
        self.h += 1 if d == 'R' else -1
        self.q = q
        return True
    def runs(self):
        lo = min(list(self.t) + [self.h]) - 1
        hi = max(list(self.t) + [self.h]) + 1
        s = ''.join('1' if self.t.get(i, 0) else '0' for i in range(lo, hi + 1))
        out, i = [], 0
        while i < len(s):
            j = i
            while j < len(s) and s[j] == s[i]: j += 1
            out.append(f'{s[i]}^{j - i}@{i + lo - self.h}')
            i = j
        return ' '.join(out)

def sim(c, stop, maxn=10**6):
    n = 0
    while n < maxn and c.q not in stop:
        if not c.step(): return 'undef', n, c
        n += 1
    return c.q, n, c

def cfgL(q, s, R):
    # ⟨q, tl s, s0 ::: R⟩
    left = s[1:]
    right = [s[0]] + R
    return C(q, left, right)

def t1cfg(Y, m):
    s = [0, 0, 0, 1, 1, 1, 0] + Y
    R = [0, 0] + [1] * m + [0] + [1] * m
    return cfgL('t1', s, R)

def mw_shape(Y, d, r, h, j):
    left = [1] * h + [0] + Y
    right = [0] + [1] * (d - h) + [0, 0] + [1] * j + [0] + [1] * (r + 1 - j)
    return C('ma1', left, right)

for m in (0, 1, 3):
    Y = [1] * 9 + [0] + cs(254598)
    c = t1cfg(Y, m)
    print('dfin m =', m, 'start:', c.runs())
    q, n, c = sim(c, {'ma1'}, 1000)
    print('  ->', q, n, c.runs())

# MW (2m+1) vs (2m+3)
for m in (0, 1, 3):
    Y = [1] * 9 + [0] + cs(254598)
    print('MW r=2m+1:', mw_shape(Y, 3, 2 * m + 1, 3, 0).runs())
    print('MW r=2m+3:', mw_shape(Y, 3, 2 * m + 3, 3, 0).runs())
