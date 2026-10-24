"""Trace composite rounds of the Riesel design: shapes at a6 (candidate start),
t1 (after comp_end+loop), and the next a6."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

build.build(c0=2)          # halts after k = 2*2+3 = 7
order, ST = build.ORDER, build.ST

class C:
    def __init__(self):
        self.q = order[0]; self.t = {}; self.h = 0
    def step(self):
        tr = ST[self.q][self.t.get(self.h, 0)]
        if tr is None: return False
        w, d, q = tr
        self.t[self.h] = w
        self.h += 1 if d == 'R' else -1
        self.q = q
        return True
    def runs(self, lo=None, hi=None):
        if lo is None:
            lo = min(list(self.t) + [self.h]) - 1
        if hi is None:
            hi = max(list(self.t) + [self.h]) + 1
        s = ''.join('1' if self.t.get(i, 0) else '0' for i in range(lo, hi + 1))
        out, i = [], 0
        while i < len(s):
            j = i
            while j < len(s) and s[j] == s[i]: j += 1
            out.append(f'{s[i]}^{j - i}@{i + lo - self.h}')
            i = j
        return ' '.join(out)

c = C()
want = {'a6', 't1'}
last = None
for n in range(10**7):
    if c.q in want:
        r = c.runs()
        if (c.q, r) != last:
            print(f'{n:8d} {c.q:4s} h={c.h:4d} {r}')
            last = (c.q, r)
    if not c.step():
        print('halt at step', n, 'state', c.q)
        break
