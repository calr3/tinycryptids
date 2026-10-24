"""Step-by-step dump of the Riesel dfin configurations (abstract shapes)."""
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
    def __init__(self, q, s, R):
        # cfgL: head on s[0], left = tl s, right = s0 ::: R
        self.q = q
        self.t = {i: c for i, c in enumerate([s[0]] + R)}
        for i, c in enumerate(s[1:]): self.t[-1 - i] = c
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
        cells = list(self.t) + [self.h]
        lo, hi = min(cells), max(cells)
        s = ''.join('1' if self.t.get(i, 0) else '0' for i in range(lo, hi + 1))
        out, i = [], 0
        while i < len(s):
            j = i
            while j < len(s) and s[j] == s[i]: j += 1
            out.append(f'{s[i]}^{j - i}@{i + lo - self.h}')
            i = j
        return ' '.join(out)

def go(m, maxn=200):
    Y = [1] * (3 + 4) + [0] + cs(254598)   # K = k+4 = 7 ones for k=3, separator, C
    s = [0, 0, 0, 1, 1, 1, 0] + Y          # YR Y
    R = [0, 0] + [1] * m + [0] + [1] * m
    c = C('t1', s, R)
    print(f'--- m = {m} start: {c.runs()}  q={c.q}')
    for n in range(maxn):
        if c.q == 'ma1':
            print(f'  step {n}: ma1  {c.runs()}'); return
        if not c.step(): print('  UNDEF at', c.q); return
        if c.q in ('a1','a2','a4','a4b','a5','a5b','a6','PM1','PM2','t1'):
            print(f'  step {n+1}: {c.q}  {c.runs()}')

go(0)
go(1)
go(3)
